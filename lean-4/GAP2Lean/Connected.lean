import GAP2Lean.Graph

namespace GAP2Lean

-- Vertice are  connected if they're in the equivalence envelope of adjacency
@[simp]
def Graph.connected {G : Graph} : G.vertex → G.vertex → Prop := EqvGen G.adjacent

-- Neighbors are connected
lemma Graph.connected_of_adjacent {G : Graph} {u v : G.vertex} : G.adjacent u v → G.connected u v :=
  EqvGen.rel u v

-- Equal vertices are connected
lemma Graph.connected_of_eq {G : Graph} (u v : G.vertex) : u = v → G.connected u v := by
  intro eq
  rw [eq]
  apply EqvGen.refl

-- Connectedness is transitive
@[simp]
lemma Graph.connected_trans {G : Graph} (u v w : G.vertex) :
  G.connected u v → G.connected v w → G.connected u w :=
  EqvGen.trans u v w

lemma Graph.adjacentConnected {G : Graph} (u v w : G.vertex) :
  G.adjacent u v → G.connected v w → G.connected u w := by
  intros uv vw
  apply connected_trans (v := v)
  · apply EqvGen.rel ; assumption
  · exact vw

@[simp]
lemma Graph.connected_symm {G : Graph} (u v : G.vertex) :
  G.connected u v → G.connected v u :=
  EqvGen.symm u v

def Graph.is_connected (G : Graph) := ∀ (u v : G.vertex), G.connected u v

/--
A certificate for connected components is a rooted directed spanning tree rooted
at its component root.
-/
class ConnectedCertificate (G : Graph) : Type :=

  /-- the root of the spanning tree -/
  root : G.vertex

  /--
  for each vertex that is not a root, the next step of the path leading to the
  root (and the root maps to itself)
  -/
  next : G.vertex → G.vertex

  -- To ensure that next is cycle-free, we witness the fact that "next" takes us closer to the root.
  -- the distance of a vertex to its component root
  distToRoot : G.vertex → Nat
  -- a root is at distance 0 from itself
  distRootZero : distToRoot root = 0
  -- a vertex is a root if its distance to a root is 0
  distZeroRoot : ∀ (v : G.vertex), distToRoot v = 0 → v = root
  -- a root is a fixed point of next
  nextRoot : next root = root
  -- each vertex that is not a root is adjacent to the next one
  nextAdjacent : ∀ v, 0 < distToRoot v → G.adjacent v (next v)
  -- distance to root decreases as we travel along the path given by next
  distNext : ∀ v, 0 < distToRoot v → distToRoot (next v) < distToRoot v

-- Auxuliary induction principle (think of f x as a "height" of x)
theorem heightInduction {α : Type} (f : α → Nat) (P : α → Prop) :
  (∀ x, (∀ y, f y < f x → P y) → P x) → ∀ x, P x := by
  intros ind a
  let Q := fun n => ∀ a, f a = n → P a
  have Qstep : ∀ n, (∀ m, m < n → Q m) → Q n
  { intros n h a ξ
    apply (ind a)
    intros b fb_lt_fa
    rw [ξ] at fb_lt_fa
    apply (h (f b)) fb_lt_fa
    rfl
  }
  exact @WellFounded.fix _ Q Nat.lt (Nat.lt_wfRel.wf) Qstep (f a) a rfl

-- Is this silly lemma somewhere in the prelude?
lemma zero_or_lt : ∀ (n : Nat), n = 0 ∨ 0 < n := by
  intro n
  cases n
  · apply Or.inl ; simp
  · apply Or.inr ; simp

-- Given a connected certificate, each vertex is connected to the root
lemma connectedToRoot (G : Graph) [C : ConnectedCertificate G] :
  ∀ v, G.connected v C.root := by
  apply heightInduction C.distToRoot (fun v => G.connected v C.root)
  intros v ih
  cases (zero_or_lt (C.distToRoot v))
  · apply G.connected_of_eq
    apply C.distZeroRoot v
    assumption
  · apply G.adjacentConnected v (C.next v) C.root
    · apply C.nextAdjacent ; assumption
    · apply ih
      apply C.distNext
      assumption

-- From a components certificate we can derive the connected components
instance {G : Graph} [C : ConnectedCertificate G] : G.is_connected := by
  intros u v
  apply G.connected_trans u C.root v
  · apply connectedToRoot
  · apply G.connected_symm
    apply connectedToRoot

end GAP2Lean

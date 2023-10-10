import GAP2Lean.Graph
import GAP2Lean.Certificate

namespace GAP2Lean

/- Basic facts about connected and disconnected graphs. -/

/-- Vertices are connected iff they are relaeted by the equivalence envelope of adjacency -/
def Graph.connected {G : Graph} : G.vertex → G.vertex → Prop := EqvGen G.adjacent

/-- Adjacent vertices are connected -/
lemma Graph.connected_of_adjacent {G : Graph} {u v : G.vertex} :
    G.adjacent u v → G.connected u v :=
  EqvGen.rel u v

/-- Equal vertices are connected -/
lemma Graph.connected_of_eq {G : Graph} (u v : G.vertex) : u = v → G.connected u v := by
  intro eq
  rw [eq]
  apply EqvGen.refl

/-- Connectedness is transitive -/
lemma Graph.connected_trans {G : Graph} (u v w : G.vertex) :
  G.connected u v → G.connected v w → G.connected u w :=
  EqvGen.trans u v w

/-- We may extend connectedness by an edge -/
lemma Graph.adjacentConnected {G : Graph} (u v w : G.vertex) :
  G.adjacent u v → G.connected v w → G.connected u w := by
  intros uv vw
  apply connected_trans (v := v)
  · apply EqvGen.rel ; assumption
  · exact vw

/-- Connectedness is symmetric -/
lemma Graph.connected_symm {G : Graph} (u v : G.vertex) :
  G.connected u v → G.connected v u :=
  EqvGen.symm u v

/-- Auxuliary induction principle (think of f x as a "height" of x) -/
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

/-- Given a connected certificate, each vertex is connected to the root -/
lemma connectedToRoot (G : Graph) [C : ConnectivityCertificate G] :
  ∀ v, G.connected v C.root := by
  apply heightInduction C.distToRoot (fun v => G.connected v C.root)
  intros v ih
  have zero_or_lt : C.distToRoot v = 0 ∨ 0 < C.distToRoot v := by
    cases C.distToRoot v
    · apply Or.inl ; simp
    · apply Or.inr ; simp
  cases zero_or_lt
  · apply G.connected_of_eq
    apply C.distZeroRoot v
    assumption
  · apply G.adjacentConnected v (C.next v) C.root
    · apply C.nextAdjacent ; assumption
    · apply ih
      apply C.distNext
      assumption

/-- A graph is connected it is has a connectivity certificate.  -/
theorem Graph.is_connected (G : Graph) [C : ConnectivityCertificate G] : ∀ u v, G.connected u v := by
  intros u v
  apply G.connected_trans
  · apply connectedToRoot
  · apply G.connected_symm
    apply connectedToRoot

/-- Connected vertices have the same color -/
lemma connected_color {G : Graph} [D : DisconnectivityCertificate G] (u v : G.vertex) :
    G.connected u v → D.color u = D.color v  := by
  intro Cuv
  induction Cuv
  case rel a b adj =>
     apply G.allEdges (fun a b => D.color a = D.color b)
     · intros u v eq
       symm
       assumption
     · exact D.edge_color
     · assumption
  case refl a => rfl
  case symm a b _ eq => apply Eq.symm eq
  case trans a b c _ _ eq1 eq2 => apply Eq.trans eq1 eq2

theorem Graph.is_disconnected (G : Graph) [D : DisconnectivityCertificate G] : ∃ u v, ¬ G.connected u v := by
  exists D.vertex0, D.vertex1
  intro C01
  apply @absurd (D.color D.vertex0 = D.color D.vertex1)
  · apply connected_color
    assumption
  · simp [D.vertex0_color, D.vertex1_color]

end GAP2Lean

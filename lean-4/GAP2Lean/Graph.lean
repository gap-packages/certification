import GAP2Lean.SetTree
import GAP2Lean.MapTree
import GAP2Lean.Edge

namespace GAP2Lean

structure GraphData : Type where
  vertexSize : Nat
  edgeTree : SetTree (Edge vertexSize)
deriving Lean.FromJson, Inhabited

structure Graph extends GraphData where
  edgeCorrect : edgeTree.isCorrect := by rfl

instance: Inhabited Graph where
  default := Graph.mk default

instance Graph.fromJson : Lean.FromJson Graph where
  fromJson? := fun json => do
    let graphData ← Lean.FromJson.fromJson? json (α := GraphData)
    if h : graphData.edgeTree.isCorrect then
      pure (Graph.mk graphData h)
    else
      throw "invalid edges in a graph"

-- the type of graph vertices
@[simp, reducible]
def Graph.vertex (G : Graph) := Fin G.vertexSize

instance (G : Graph) : Lean.FromJson G.vertex where
  fromJson? := fun json => do
    let v ← json.getNat?
    Nat.ltByCases (a := v) (b := G.vertexSize)
      (fun v_lt_n => pure (Fin.mk v v_lt_n))
      (fun _ => throw "invalid json vertex")
      (fun _ => throw "invalid json vertex")

-- the underlying type of edges (pairs (i,j) such that j < i < G.vertexSize)
@[simp, reducible]
def Graph.edgeType (G : Graph) := Edge G.vertexSize

-- the type of edges
@[simp, reducible]
def Graph.edge (G : Graph) := { e : G.edgeType // G.edgeTree.mem e }

@[simp]
def Graph.fst {G : Graph} (e : G.edgeType) : G.vertex := e.fst

@[simp]
def Graph.snd {G : Graph} (e : G.edgeType) : G.vertex :=
  ⟨e.snd, e.snd.prop⟩

-- the number of eges in a graph
def Graph.edgeSize (G : Graph) := Fintype.card G.edge

-- the vertex adjacency relation
def Graph.badjacent {G : Graph} : G.vertex → G.vertex → Bool :=
  fun u v =>
    ltByCases u v
      (fun u_lt_v => G.edgeTree.mem (Edge.mk u v u_lt_v))
      (fun _ => false)
      (fun v_lt_u => G.edgeTree.mem (Edge.mk v u v_lt_u))

def Graph.adjacent {G : Graph} : G.vertex → G.vertex → Prop :=
  fun u v => G.badjacent u v

instance (G : Graph) : DecidableRel G.adjacent := by
  intros u v
  unfold Graph.adjacent
  infer_instance

-- adjacent vertices induce an edge
def Graph.adjacentEdge {G : Graph} {u v : G.vertex} :
  G.adjacent u v → G.edge := by
  apply ltByCases u v
  · intros u_lt_v uv
    constructor
    case val => exact Edge.mk u v u_lt_v
    case property => simp_all [u_lt_v, ltByCases, adjacent, badjacent]
  · intro u_eq_v
    intro H
    simp [u_eq_v, ltByCases, adjacent, badjacent] at H
  · intros v_lt_u uv
    constructor
    case val => exact Edge.mk v u v_lt_u
    case property => simp_all [v_lt_u, not_lt_of_lt, ltByCases, adjacent, badjacent]

lemma Graph.irreflexiveAdjacent (G : Graph) :
  ∀ (v : G.vertex), ¬ adjacent v v := by simp [ltByCases, adjacent, badjacent]

lemma Graph.symmetricNeighbor (G : Graph) :
  ∀ (u v : G.vertex), adjacent u v → adjacent v u := by
    intros u v
    apply ltByCases u v <;> (intro h ; simp [ltByCases, not_lt_of_lt, h, adjacent, badjacent])

/--
  For a symmetric relation on vertices, if it holds for all endpoints of all edges,
  then it holds for all pairs of adjacent vertices.
-/
def Graph.allEdges {G : Graph} (R : G.vertex → G.vertex → Prop) :
    (∀ u v, R u v → R v u) →
    (∀ (e : G.edge), R e.val.fst e.val.snd) →
    (∀ u v, G.adjacent u v → R u v)
  := by
  intro R_symm all_edge u v uv
  apply ltByCases u v
  · intro u_lt_v
    let A := all_edge (G.adjacentEdge uv)
    simp [adjacentEdge, ltByCases, u_lt_v] at A
    exact A
  · intro eq
    exfalso
    apply G.irreflexiveAdjacent u
    rw [←eq] at uv
    assumption
  · intro v_lt_u
    let A := all_edge (G.adjacentEdge uv)
    simp [adjacentEdge, ltByCases, v_lt_u, not_lt_of_lt] at A
    apply R_symm
    exact A

-- the neighborhood of a vertex, as a set
@[reducible]
def Graph.neighborhood (G : Graph) (v : G.vertex) :=
  { u : G.vertex // G.badjacent v u }

-- the degree of a vertex
def Graph.degree (G : Graph) (v : G.vertex) : Nat := Fintype.card (G.neighborhood v)

-- the minimal vertex degree, equals ⊤ for empty graph
def Graph.minDegree (G : Graph) : WithTop Nat :=
  Finset.inf (Fin.fintype G.vertexSize).elems (fun v => G.degree v)

-- the maximal vertex degree, equals ⊥ for empty graph
def Graph.maxDegree (G : Graph) : WithBot Nat :=
  Finset.sup (Fin.fintype G.vertexSize).elems (fun v => G.degree v)

end GAP2Lean

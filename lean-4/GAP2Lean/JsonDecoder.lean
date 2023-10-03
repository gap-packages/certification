import Qq
import GAP2Lean.TreeSet
import GAP2Lean.TreeMap
import GAP2Lean.Graph

namespace GAP2Lean

open Qq

def forallFin {n : Nat} (p : Fin n → Prop) [DecidablePred p] : Bool := decide (∀ x, p x)
def forallVertex {G : Graph} (p : G.vertex → Prop) [DecidablePred p] : Bool := decide (∀ v, p v)

def edgeOfJson (n : Q(Nat)) (j : Lean.Json) : Except String Q(Edge $n) := do
  let arr ← j.getArr? <|> throw "array expected in edgeOfJson"
  have a : Q(Nat) := Lean.mkRawNatLit (← arr[0]!.getNat?)
  have b : Q(Nat) := Lean.mkRawNatLit (← arr[1]!.getNat?)
  have H1 : Q(Nat.blt $a $b = true) := (q(Eq.refl true) : Lean.Expr)
  have H2 : Q(Nat.blt $b $n = true) := (q(Eq.refl true) : Lean.Expr)
  pure q(Edge.mk' $n $a $b $H1 $H2)

def natOfJson (j : Lean.Json) : Except String Q(Nat) := do
  have n : Q(Nat) := Lean.mkRawNatLit (← j.getNat?)
  pure n

def finOfJson (n : Q(Nat)) (j : Lean.Json) : Except String Q(Fin $n) := do
  have k : Q(Nat) := Lean.mkRawNatLit (← j.getNat?)
  have H : Q(Nat.blt $k $n = true) := (q(Eq.refl true) : Lean.Expr)
  pure q(Fin.mk $k (Nat.le_of_ble_eq_true $H))

def vertexOfJson (G : Q(Graph)) (j : Lean.Json) : Except String Q(Graph.vertex $G) := do
  finOfJson (q(Graph.vertexSize $G)) j

-- Convert a sub-array into a tree
partial def from_array {α : Q(Type)} (a : Array Q($α)) (low high : ℕ) : Q(STree $α) :=
  if low >= high then
    q(.empty)
  else if low + 1 = high then
    q(.leaf $(a[low]!))
  else
    let middle := (low + high) / 2
    let left := from_array a low middle
    let right := from_array a (middle + 1) high
    q(.node $(a[middle]!) $left $right)

partial def streeOfJson {α : Q(Type)}
  (valOfJson : Lean.Json → Except String Q($α))
  (j : Lean.Json)
  : Except String Q(STree $α) := do
  let arr ← j.getArr? <|> throw "array expected in streeOfJson"
  let arr ← arr.mapM valOfJson
  return from_array arr 0 arr.size

partial def mapTreeOfJson {α β : Q(Type)}
  (o : Q(Ord $α))
  (keyOfJson : Lean.Json → Except String Q($α))
  (valOfJson : Lean.Json → Except String Q($β))
  (j : Lean.Json) : Except String Q(Map $α $β) := do
  let arr ← j.getArr?  <|> throw "array expected in mapTreeOfJson"
  match arr with
  | #[] => pure q(Map.empty)
  | #[k, v] =>
    pure q(Map.leaf $(← keyOfJson k) $(← valOfJson v))
  | #[k, v, l, r] =>
    let key ← keyOfJson k
    let val ← valOfJson v
    let left ← mapTreeOfJson o keyOfJson valOfJson l
    let right ← mapTreeOfJson o keyOfJson valOfJson r
    pure q(Map.node $key $val $left $right)
  | _ => throw "invalid tree map format"

def emptyMap {α β : Type}
  [Decidable (α → False)]
  (H : (Decidable.decide (α → False)) = true) (x : α) : β := by
  simp at H
  exact (False.elim (H x))

partial def mapOfJson {α β : Q(Type)}
  (o : Q(Ord $α))
  (d : Q(Decidable ($α → False)))
  (keyOfJson : Lean.Json → Except String Q($α))
  (valOfJson : Lean.Json → Except String Q($β))
  (j : Lean.Json) : Except String Q($α → $β) := do
  let arr ← j.getArr? <|> throw "array expected in mapOfJson"
  match arr with
  | #[] =>
    have H : Q(@Decidable.decide ($α → False) $d = true) := (q(Eq.refl true) : Lean.Expr)
    pure q(emptyMap $H)
  | #[treeJ, defaultJ] =>
    let tree ← mapTreeOfJson o keyOfJson valOfJson treeJ
    let defaultValue ← valOfJson defaultJ
    pure q(Map.getD $tree $defaultValue)
  | _ => throw "invalid map format"

partial def graphOfJson (j : Lean.Json) : Except String Q(Graph) := do
    let vertexSizeJ ← j.getObjVal? "vertexSize"
    have vertexSize : Q(Nat) := Lean.mkRawNatLit (← vertexSizeJ.getNat?)
    let edges : Q(STree (Edge $vertexSize)) ←
      streeOfJson (edgeOfJson vertexSize) (← j.getObjVal? "edges")
    pure q(Graph.mk $vertexSize $edges)

-- lifting from exception monad to the Elab.Command monad
def liftExcept {α : Type} : Except String α → Lean.Elab.Command.CommandElabM α
  | .ok res => pure res
  | .error msg => throwError msg

elab "load_graph" graphName:ident fileName:str : command => do
  let graphName := graphName.getId
  let file ← IO.FS.readFile fileName.getString
  let json ← liftExcept <| Lean.Json.parse file
  let graphJ ← liftExcept <| json.getObjVal? "graph"
  let graphQ : Q(Graph) ← liftExcept <| graphOfJson graphJ
  -- load the graph
  Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
    name := graphName
    levelParams := []
    type := q(Graph)
    value := graphQ
    hints := .regular 0
    safety := .safe
  }
  Lean.setReducibleAttribute graphName

load_graph cow "GAP2Lean/example.json"

#print cow
#eval cow.adjacent 1 0

end GAP2Lean

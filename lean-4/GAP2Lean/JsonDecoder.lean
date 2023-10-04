import Qq
import GAP2Lean.TreeSet
import GAP2Lean.TreeMap
import GAP2Lean.Graph
import GAP2Lean.Connected
import GAP2Lean.GAPInfo

namespace GAP2Lean

open Qq

def forallFin {n : Nat} (p : Fin n → Prop) [DecidablePred p] : Bool := decide (∀ x, p x)
def forallVertex {G : Graph} (p : G.vertex → Prop) [DecidablePred p] : Bool := decide (∀ v, p v)

def edgeOfInfo (n : Q(Nat)) (p : Nat × Nat) : Except String Q(Edge $n) := do
  have a : Q(Nat) := Lean.mkRawNatLit p.1
  have b : Q(Nat) := Lean.mkRawNatLit p.2
  have H1 : Q(Nat.blt $a $b = true) := (q(Eq.refl true) : Lean.Expr)
  have H2 : Q(Nat.blt $b $n = true) := (q(Eq.refl true) : Lean.Expr)
  pure q(Edge.mk' $n $a $b $H1 $H2)

def finOfInfo (n : Q(Nat)) (k : Nat) : Except String Q(Fin $n) := do
  have k : Q(Nat) := Lean.mkRawNatLit k
  have H : Q(Nat.blt $k $n = true) := (q(Eq.refl true) : Lean.Expr)
  pure q(Fin.mk $k (Nat.le_of_ble_eq_true $H))

def vertexOfInfo (G : Q(Graph)) (k : Nat) : Except String Q(Graph.vertex $G) := do
  finOfInfo (q(Graph.vertexSize $G)) k

-- Convert a sub-array into a set tree
partial def stree_from_array {α : Q(Type)} (a : Array Q($α)) (low high : ℕ) : Q(STree $α) :=
  if low >= high then
    q(.empty)
  else if low + 1 = high then
    q(.leaf $(a[low]!))
  else
    let middle := (low + high) / 2
    let left := stree_from_array a low middle
    let right := stree_from_array a (middle + 1) high
    q(.node $(a[middle]!) $left $right)

partial def streeOfInfo {α : Q(Type)} {β : Type}
  (valOfInfo : β → Except String Q($α))
  (arr : Array β)
  : Except String Q(STree $α) := do
  let arr ← arr.mapM valOfInfo
  return stree_from_array arr 0 arr.size

partial def streeOfJson {α : Q(Type)}
  (valOfJson : Lean.Json → Except String Q($α))
  (j : Lean.Json)
  : Except String Q(STree $α) := do
  let arr ← j.getArr? <|> throw "array expected in streeOfJson"
  let arr ← arr.mapM valOfJson
  return stree_from_array arr 0 arr.size

def pairOfJson (j : Lean.Json) : Except String (Lean.Json × Lean.Json) := do
  let arr ← j.getArr? <|> throw "pair expected"
  pure (arr[0]!, arr[1]!)

-- Convert a sub-array into a map tree
partial def TreeMap_of_array {α β : Q(Type)}
  (arr : Array (Q($α) × Q($β))) (low high : ℕ) : Except String Q(Map $α $β) :=
  if low >= high then
    pure q(.empty)
  else if low + 1 = high then do
    let (k, v) := arr[low]!
    pure q(.leaf $k $v)
  else do
    let middle := (low + high) / 2
    let left ← TreeMap_of_array arr low middle
    let right ← TreeMap_of_array arr (middle + 1) high
    let (k, v) := arr[middle]!
    pure q(.node $k $v $left $right)

def emptyMap {α β : Type}
  [Decidable (α → False)]
  (H : (Decidable.decide (α → False)) = true) (x : α) : β := by
  simp at H
  exact (False.elim (H x))

partial def mapOfInfo {α β : Q(Type)}
  (_ : Q(Ord $α))
  (d : Q(Decidable ($α → False)))
  (arr : Array (Q($α) × Q($β))) : Except String Q($α → $β) := do
  match arr with
  | #[] =>
    have H : Q(@Decidable.decide ($α → False) $d = true) := (q(Eq.refl true) : Lean.Expr)
    pure q(emptyMap $H)
  | arr =>
    let (_, default) := arr[0]!
    let tree ← TreeMap_of_array arr 0 arr.size
    pure q($(tree).getD $default)

partial def graphOfInfo (info : GraphInfo) : Except String Q(Graph) := do
    have vertexSize : Q(Nat) := Lean.mkRawNatLit info.vertexSize
    let edges : Q(STree (Edge $vertexSize)) ← streeOfInfo (edgeOfInfo vertexSize) info.edges
    pure q(Graph.mk $vertexSize $edges)

def connectivityCertificateOfInfo (G : Q(Graph)) (info : ConnectivityCertificateInfo) : Except String Q(ConnectivityCertificate $G) := do
  let o := q(instOrdFin (Graph.vertexSize $G))
  let d := q(Fintype.decidableForallFintype)
  let root ← vertexOfInfo G info.root
  let nextInfo ← info.next.mapM (fun (u, v) => return (← vertexOfInfo G u, ← vertexOfInfo G v))
  let next ← mapOfInfo o d nextInfo
  let distInfo ← info.distToRoot.mapM (fun (v, k) => return (← vertexOfInfo G v, Lean.mkRawNatLit k))
  let distToRoot ← mapOfInfo o d distInfo
  have distRootZero : Q(decide ($distToRoot $root = 0) = true) := (q(Eq.refl true) : Lean.Expr)
  have distZeroRoot : Q(forallVertex (fun (v : Graph.vertex $G) => $distToRoot v = 0 → v = $root) = true) := (q(Eq.refl true) : Lean.Expr)
  have nextRoot : Q(decide ($next $root = $root) = true) := (q(Eq.refl true) : Lean.Expr)
  have nextAdjacent : Q(forallVertex (fun v => 0 < $distToRoot v → Graph.adjacent v ($next v)) = true) := (q(Eq.refl true) : Lean.Expr)
  have distNext : Q(decide (∀ v, 0 < $distToRoot v → $distToRoot ($next v) < $distToRoot v) = true) := (q(Eq.refl true) : Lean.Expr)
  pure q(@ConnectivityCertificate.mk
         $G
         $root
         $next
         $distToRoot
         (of_decide_eq_true $distRootZero)
         (of_decide_eq_true $distZeroRoot)
         (of_decide_eq_true $nextRoot)
         (of_decide_eq_true $nextAdjacent)
         (of_decide_eq_true $distNext)
        )

-- lifting from exception monad to the Elab.Command monad
def liftExcept {α : Type} : Except String α → Lean.Elab.Command.CommandElabM α
  | .ok res => pure res
  | .error msg => throwError msg

-- A name for a cerficicate
def certificateName (graphName: Lean.Name) (certName: String) : Lean.Name :=
  (.str graphName certName)

elab "load_graph" graphName:ident fileName:str : command => do
  let graphName := graphName.getId
  let info ← loadGAPInfo fileName.getString
  let graphQ : Q(Graph) ← liftExcept <| graphOfInfo info.graph
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
  have graph : Q(Graph) := Lean.mkConst graphName []
  -- load the connectivity certificate
  let connectivityCertificateName := certificateName graphName "connectivityCertificateI"
  let connectivityCertificateQ : Q(ConnectivityCertificate $graph) ←
    liftExcept <| connectivityCertificateOfInfo graph info.connectivityCertificate
  Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
    name := connectivityCertificateName
    levelParams := []
    type := q(ConnectivityCertificate $graph)
    value := connectivityCertificateQ
    hints := .regular 0
    safety := .safe
  }
  Lean.Elab.Command.liftTermElabM <| Lean.Meta.addInstance connectivityCertificateName .scoped 42


load_graph cow "cert.json"
#print cow
#check connected_of_certificate cow



end GAP2Lean

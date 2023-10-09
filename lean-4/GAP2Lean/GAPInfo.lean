import Lean
import GAP2Lean.Map
import GAP2Lean.Graph

namespace GAP2Lean

structure ConnectivityData (G : Graph) : Type where
  /-- The root of the spanning tree. -/
  root : G.vertex

  /--
  For each vertex that is not a root, the next step of the path leading to the
  root (and the root maps to itself).
  -/
  next : Map G.vertex G.vertex

  /--
  To ensure that next is cycle-free, we witness the fact that "next" takes us closer to the root.
  the distance of a vertex to its component root
  -/
  distToRoot : Map G.vertex Nat

deriving Lean.FromJson

structure ConnectivityCertificate (G : Graph) extends ConnectivityData G where
  /-- A root is at distance 0 from itself -/
  distRootZero : distToRoot root = 0

  /-- A vertex is a root if its distance to root is 0 -/
  distZeroRoot : ∀ (v : G.vertex), distToRoot v = 0 → v = root

  /--- A root is a fixed point of next -/
  nextRoot : next root = root

  /-- Each vertex that is not a root is adjacent to the next one -/
  nextAdjacent : ∀ v, 0 < distToRoot v → G.adjacent v (next v)

  /-- distance to root decreases as we travel along the path given by next -/
  distNext : ∀ v, 0 < distToRoot v → distToRoot (next v) < distToRoot v

instance ConnectivityCertificate.fromJson (G : Graph) : Lean.FromJson (ConnectivityCertificate G) where
  fromJson? := fun json => do
    let data ← Lean.FromJson.fromJson? json (α := ConnectivityData G)
    if h₁ : data.distToRoot data.root = 0 then
      if h₂ : ∀ (v : G.vertex), data.distToRoot v = 0 → v = data.root then
        if h₃ : (data.next data.root = data.root) then
          if h₄ : ∀ v, 0 < data.distToRoot v → G.adjacent v (data.next v) then
            if h₅ : ∀ v, 0 < data.distToRoot v → data.distToRoot (data.next v) < data.distToRoot v then
              pure (ConnectivityCertificate.mk data h₁ h₂ h₃ h₄ h₅)
            else
              throw "non-monotone distance"
          else
            throw "non-descreasing distance to root"
        else
          throw "root is at non-zero distance to root"
      else
        throw "a non-root has zero distance to root"
    else
      throw "invalid distance to root"

instance {n : Nat}: Lean.FromJson (Fin n) where
  fromJson? := fun json => do
    let k ← json.getNat?
    if h : k < n then
      pure (Fin.mk k h)
    else
      throw "invalid finite number"


structure DisconnectivityData (G : Graph) : Type where

  /-- A coloring of vertices by two colors -/
  color : Map G.vertex (Fin 2)

  /-- A vertex of color 0 -/
  vertex0 : G.vertex

  /-- A vertex of color 1-/
  vertex1 : G.vertex

deriving Lean.FromJson


class DisconnectivityCertificate (G : Graph) extends DisconnectivityData G where

  /-- Neighbors have the same color -/
  edge_color : ∀ (e : G.edge), color e.val.fst = color e.val.snd

  /-- Chosen vertices have the correct color -/
  vertex0_color : color vertex0 = 0
  vertex1_color : color vertex1 = 1

instance DisconnectivityCertificate.fromJson (G : Graph) : Lean.FromJson (DisconnectivityCertificate G) where
  fromJson? := fun json => do
    let data ← Lean.FromJson.fromJson? json (α := DisconnectivityData G)
    if h₁ : ∀ (e : G.edge), data.color e.val.fst = data.color e.val.snd then
      if h₂ : data.color data.vertex0 = 0 then
        if h₃ : data.color data.vertex1 = 1 then
          pure (DisconnectivityCertificate.mk data h₁ h₂ h₃)
        else
          throw "vertex1 does not have color 1"
      else
        throw "vertex0 does not have color 0"
    else
      throw "bi-colored edge encountered"

structure GraphInfo : Type where
  graph : Graph
  connectivityCertificate? : Option (ConnectivityCertificate graph)
  disconnectivityCertificate? : Option (DisconnectivityCertificate graph)
deriving Lean.FromJson

def loadGraphInfo (fileName : System.FilePath) : IO GraphInfo := do
  let file ← IO.FS.readFile fileName
  match (Lean.Json.parse file >>= Lean.fromJson?) with
  | .ok info => pure info
  | .error msg => throw (.userError msg)

end GAP2Lean
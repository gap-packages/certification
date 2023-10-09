import Lean

structure GraphInfo : Type where
  vertexSize : Nat
  edges : Array (Nat × Nat )
deriving Lean.FromJson, Repr

structure ConnectivityCertificateInfo : Type where
  root : Nat
  next : Array (Nat × Nat)
  distToRoot : Array (Nat × Nat)
deriving Lean.FromJson, Repr

structure DisconnectivityCertificateInfo : Type where
  color : Array (Nat × Nat)
  vertex0 : Nat
  vertex1 : Nat
deriving Lean.FromJson, Repr

structure GAPInfo : Type where
  graph : GraphInfo
  connectivityCertificate? : Option ConnectivityCertificateInfo
  disconnectivityCertificate? : Option DisconnectivityCertificateInfo
deriving Lean.FromJson, Repr

def loadGAPInfo (fileName : System.FilePath) : IO GAPInfo := do
  let file ← IO.FS.readFile fileName
  match (Lean.Json.parse file >>= Lean.fromJson?) with
  | .ok info => pure info
  | .error msg => throw (.userError msg)

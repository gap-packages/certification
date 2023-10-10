import Qq
import GAP2Lean.SetTree
import GAP2Lean.MapTree
import GAP2Lean.Graph
import GAP2Lean.Connectedness
import GAP2Lean.Certificate

namespace GAP2Lean

open Qq

-- lifting from exception monad to the Elab.Command monad
def liftExcept {α : Type} {m} [Monad m] [Lean.MonadError m] : Except String α → m α
  | .ok res => pure res
  | .error msg => throwError msg

-- A name for a certicicate
def certificateName (graphName: Lean.Name) (certName: String) : Lean.Name :=
  (.str graphName certName)

elab "load_graph" graphName:ident fileName:str : command => do
  let graphName := graphName.getId
  let graphCert ← loadGraphCertificate fileName.getString
  have graph := graphCert.graph
  -- load the graph
  Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
    name := graphName
    levelParams := []
    type := q(Graph)
    value := q($graph)
    hints := .regular 0
    safety := .safe
  }
  Lean.setReducibleAttribute graphName
  have graph : Q(Graph) := Lean.mkConst graphName []

  -- load the connectivity certificate, if present
  match info.connectivityCertificate? with
  | .none => pure ()
  | .some cert =>
    let connectivityCertificateName := certificateName graphName "connectivityCertificateI"
    let connectivityCertificateQ : Q(ConnectivityCertificate $graph) ←
      liftExcept <| connectivityCertificateOfInfo graph cert
    Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
      name := connectivityCertificateName
      levelParams := []
      type := q(ConnectivityCertificate $graph)
      value := connectivityCertificateQ
      hints := .regular 0
      safety := .safe
    }
    Lean.Elab.Command.liftTermElabM <| Lean.Meta.addInstance connectivityCertificateName .scoped 42

  -- load the disconnectivity certificate, if present
  match info.disconnectivityCertificate? with
  | .none => pure ()
  | .some cert =>
    let disconnectivityCertificateName := certificateName graphName "disconnectivityCertificateI"
    let disconnectivityCertificateQ : Q(ConnectivityCertificate $graph) ←
      liftExcept <| disconnectivityCertificateOfInfo graph cert
    Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
      name := disconnectivityCertificateName
      levelParams := []
      type := q(DisconnectivityCertificate $graph)
      value := disconnectivityCertificateQ
      hints := .regular 0
      safety := .safe
    }
    Lean.Elab.Command.liftTermElabM <| Lean.Meta.addInstance disconnectivityCertificateName .scoped 42


-- load_graph cow "cert.json"
-- #print cow
-- #check (connected cow)
-- load_graph bull "cube.json"

-- #check connected bull

end GAP2Lean

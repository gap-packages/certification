import Qq
import GAP2Lean.SetTree
import GAP2Lean.MapTree
import GAP2Lean.Graph
import GAP2Lean.Connectivity
import GAP2Lean.Certificate
import GAP2Lean.JsonData

namespace GAP2Lean

open Qq

/-- Lifting from exception monad to the Elab.Command monad -/
def liftExcept {α : Type} {m} [Monad m] [Lean.MonadError m] : Except String α → m α
  | .ok res => pure res
  | .error msg => throwError msg

/-- A Lean name for a certicicate -/
def certificateName (graphName: Lean.Name) (certName: String) : Lean.Name :=
  (.str graphName certName)

/-- A special command for loading a graph -/
elab "load_graph" graphName:ident fileName:str : command => do
  let graphName := graphName.getId
  let gapData ← loadGAPData fileName.getString
  have graphQ := graphOfData gapData.graph
  -- load the graph
  Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
    name := graphName
    levelParams := []
    type := q(Graph)
    value := q($graphQ)
    hints := .regular 0
    safety := .safe
  }
  Lean.setReducibleAttribute graphName
  have graph : Q(Graph) := Lean.mkConst graphName []

  -- load the connectivity certificate, if present
  match gapData.connectivityData? with
  | .none => pure ()
  | .some data =>
    let connectivityCertificateName := certificateName graphName "connectivityCertificateI"
    let connectivityCertificateQ : Q(ConnectivityCertificate $graph) := connectivityCertificateOfData graph data
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
  match gapData.disconnectivityData? with
  | .none => pure ()
  | .some data =>
    let disconnectivityCertificateName := certificateName graphName "disconnectivityCertificateI"
    let disconnectivityCertificateQ : Q(DisconnectivityCertificate $graph) := disconnectivityCertificateOfData graph data
    Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
      name := disconnectivityCertificateName
      levelParams := []
      type := q(DisconnectivityCertificate $graph)
      value := disconnectivityCertificateQ
      hints := .regular 0
      safety := .safe
    }
    Lean.Elab.Command.liftTermElabM <| Lean.Meta.addInstance disconnectivityCertificateName .scoped 42


load_graph cow "cert.json"

#check cow

-- load_graph bull "cube.json"

-- #check connected bull

end GAP2Lean

import Mathlib.Init.Order.Defs
import Mathlib.Tactic
import Mathlib.Data.Sigma.Order
import GAP2Lean.TreeSet
import GAP2Lean.OrdEq

namespace GAP2Lean

structure Edge (m : Nat) :=
  (fst : Fin m)
  (snd : Fin m)
  (ord : fst < snd)
deriving Fintype

def Edge.compare {m : Nat} (e1 e2 : Edge m) :=
  lexOrd.compare (e1.fst, e1.snd) (e2.fst, e2.snd)

instance (m : Nat): Ord (Edge m) := ⟨Edge.compare⟩

-- smart constructor used to load JSON files
def Edge.mk' (n a b : Nat) (H1 : Nat.blt a b = true) (H2 : Nat.blt b n = true) : Edge n :=
  let H1 := Nat.le_of_ble_eq_true H1
  let H2 := Nat.le_of_ble_eq_true H2
  ⟨⟨a, lt_trans H1 H2⟩, ⟨b, H2⟩, H1⟩

end GAP2Lean

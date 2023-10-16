import Lean
import Mathlib

namespace GAP2Lean

structure Edge (m : Nat) where
  fst : Fin m
  snd : Fin m
  ord : fst < snd
deriving Fintype, Ord -- assuming Ord derives the lexicographic order

-- smart constructor used to load JSON files
def Edge.mk' (n a b : Nat) (H1 : Nat.blt a b = true) (H2 : Nat.blt b n = true) : Edge n :=
  let H1 := Nat.le_of_ble_eq_true H1
  let H2 := Nat.le_of_ble_eq_true H2
  ⟨⟨a, lt_trans H1 H2⟩, ⟨b, H2⟩, H1⟩

end GAP2Lean

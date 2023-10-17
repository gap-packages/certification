import Lean
import Mathlib

namespace GAP2Lean

structure Edge (m : Nat) where
  fst : Fin m
  snd : Fin m
  ord : fst < snd
deriving Fintype

-- smart constructor used to load JSON files
def Edge.mk' (n a b : Nat) (H1 : Nat.blt a b = true) (H2 : Nat.blt b n = true) : Edge n :=
  let H1 := Nat.le_of_ble_eq_true H1
  let H2 := Nat.le_of_ble_eq_true H2
  ⟨⟨a, lt_trans H1 H2⟩, ⟨b, H2⟩, H1⟩

@[simp, reducible]
def fst_snd (m : Nat) (e : Edge m) : Lex (Fin m × Fin m) := (e.fst, e.snd)

def fst_snd_injective {m : Nat} : Function.Injective (fst_snd m) := by
  intro a b
  cases a ; cases b ; simp
  intro h ; injection h ; trivial

instance Edge.linearOrder {m : Nat} : LinearOrder (Edge m) :=
  LinearOrder.lift' (fst_snd m) fst_snd_injective

end GAP2Lean

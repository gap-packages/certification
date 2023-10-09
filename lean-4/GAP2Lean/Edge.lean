import Lean
import Mathlib.Init.Order.Defs
import Mathlib.Tactic
import Mathlib.Data.Sigma.Order
import GAP2Lean.OrdEq

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

/--
  Create an edge from the endpoints given as natural numbers, raise an exception if invalid.
-/
def Edge.mk_except (n a b : Nat) : Except String (Edge n) :=
  if h : a < n ∧ b < n then
    Nat.ltByCases (a := a) (b := b)
      (fun a_lt_b => pure (Edge.mk (Fin.mk a h.1) (Fin.mk b h.2) a_lt_b))
      (fun _ => throw "loops are not valid edges")
      (fun b_lt_a => pure (Edge.mk (Fin.mk b h.2) (Fin.mk a h.1) b_lt_a))
  else
    throw "edge endpoints out of bound" 

instance Edge.fromJson {m : Nat} : Lean.FromJson (Edge m) where
  fromJson? := fun json => do
    let uv ← json.getArr?
    let u ← Lean.instFromJsonNat.fromJson? uv[0]!
    let v ← Lean.instFromJsonNat.fromJson? uv[0]!
    Edge.mk_except m u v

end GAP2Lean

import Mathlib

namespace GAP2Lean

/---
  For the purposes of binary search trees we don't need a linear order.
  It suffices to have a class [Ord] which correctly classifies equality,
  defined here.
-/

class OrdEq (α : Type) [Ord α] where
  equiv : ∀ (x y : α), compare x y = .eq ↔ x = y

instance (α : Type) [LinearOrder α] : OrdEq α where
  equiv := fun x y => compare_eq_iff_eq (a := x) (b := y)

/-- Split into cases according to the result of Ord.compare -/
lemma OrdEq_cases {α : Type} [Ord α] [OrdEq α] (x y : α):
  (compare x y = .lt ∧ x ≠ y) ∨ (compare x y = .eq ∧ x = y) ∨ (compare x y = .gt ∧ x ≠ y) := by
  have e := OrdEq.equiv x y
  revert e
  cases (compare x y) <;> simp

end GAP2Lean

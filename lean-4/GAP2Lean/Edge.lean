import Lean
import Mathlib

namespace GAP2Lean

structure Edge (m : Nat) where
  fst : Fin m
  snd : Fin m
  ord : fst < snd
deriving Fintype -- assuming Ord derives the lexicographic order

-- smart constructor used to load JSON files
def Edge.mk' (n a b : Nat) (H1 : Nat.blt a b = true) (H2 : Nat.blt b n = true) : Edge n :=
  let H1 := Nat.le_of_ble_eq_true H1
  let H2 := Nat.le_of_ble_eq_true H2
  ⟨⟨a, lt_trans H1 H2⟩, ⟨b, H2⟩, H1⟩

instance Edge.linearOrder {m : Nat} : LinearOrder (Edge m) where

  le := fun d e => d.fst < e.fst ∨ (d.fst = e.fst ∧ d.snd ≤ e.snd)

  le_refl := by simp

  le_trans := by
    intros a b c
    simp
    intro h₁ h₂
    cases h₁ <;> cases h₂
    case inl.inl p q => left ; apply lt_trans p q
    case inl.inr p q => left; apply lt_of_lt_of_eq p q.1
    case inr.inr p q =>
      right
      apply And.intro
      · apply Eq.trans p.1 q.1
      · apply le_trans p.2 q.2
    case inr.inl p q => left ; apply lt_of_eq_of_lt p.1 q

  le_antisymm := by
    intros a b h₁ h₂
    cases h₁ <;> cases h₂
    case inl.inl p q => apply False.elim (lt_asymm p q)
    case inl.inr p q =>
      absurd (Eq.symm q.1) ; apply (ne_of_lt p)
    case inr.inr p q =>
      cases a <;> cases b <;> simp_all
      exact le_antisymm p.2 q      
    case inr.inl p q => cases a <;> cases b <;> simp_all
  
  le_total := by
    intros a b
    cases (lt_trichotomy a.fst b.fst)
    case inl p => left ; left ; assumption
    case inr p =>
      cases p
      case inl q =>
        cases (lt_or_le a.snd b.snd)
        · left ; right ; apply And.intro
          · assumption
          · apply le_of_lt ; assumption   
        · right ; right ; apply And.intro
          · symm ; assumption
          · assumption 
      case inr q => 
        right ; left ; assumption

  decidableLE := by
    intros a b
    sorry

end GAP2Lean

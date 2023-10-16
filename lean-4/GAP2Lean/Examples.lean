import GAP2Lean.Certificate

namespace GAP2Lean

initialize cert : GraphCertificate ← loadGraphCertificate "cert.json"

def involutive (f : α → α) := ∀ x, f (f x) = x

-- def rev : List α → List α
--   | [] => []
--   | x :: xs => rev xs ++ [x]

def rev : List α → List α :=
  fun x => match x with
  | [] => []
  | x :: xs => rev xs ++ [x]

#print rev

example : involutive (@rev α) := by
  intro xs
  induction xs
  . simp [rev]
  . rename_i h t IH
    rw [rev]         -- works. Maybe because in the inductive case we
                     --   know which branch of `rev` matches?

    unfold rev

theorem cow : True := by
  rfl

end GAP2Lean

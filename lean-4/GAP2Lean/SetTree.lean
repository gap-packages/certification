import Mathlib.Init.Order.Defs
import Mathlib.Tactic.Basic

import GAP2Lean.BoundedOrder
import GAP2Lean.OrdEq

namespace GAP2Lean

/--
  A finite set represented as a search tree.
--/
inductive SetTree.{u} (α : Type u) : Type u
  | empty : SetTree α
  | leaf : α → SetTree α
  | node : α → SetTree α → SetTree α → SetTree α
deriving Repr

instance {α : Type} : Inhabited (SetTree α) := ⟨.empty⟩

/--
  Given a subarray of key-value pairs, generate the corresponding balanced search tree.
  NB: The subarray must be sorted by keys.
-/
partial def SetTree.ofSubarray {α : Type} (arr : Array α) (low high : ℕ) : SetTree α :=
  if ltSize : low < arr.size ∧ high <= arr.size then
    if _ : low >= high then
      .empty
    else if low + 1 = high then
      let x := arr[low]'(ltSize.1)
      .leaf x
    else
      let middle := (low + high).div2
      let left :=  ofSubarray arr low middle
      let right := ofSubarray arr (middle + 1) high
      have middle_valid : (low + high).div2 < arr.size := (by
        rw [Nat.div2_val]
        have h : (low + high < arr.size + arr.size) → ((low + high) / 2 < arr.size) := (by
          intro ab_lt_nn
          rw [←Nat.two_mul] at ab_lt_nn
          apply Nat.div_lt_of_lt_mul ab_lt_nn)
        apply h
        apply Nat.lt_of_le_of_lt (Nat.add_le_add_left ltSize.2 low) (Nat.add_lt_add_right ltSize.1 arr.size))
      let x := arr[middle]'middle_valid
      .node x left right
  else
    .empty

/--
  Given an array of key-value pairs, generate the corresponding balanced search tree.
  NB: The array must be sorted by keys.
-/
def SetTree.ofArray {α : Type} (arr : Array α) : SetTree α :=
  ofSubarray arr 0 arr.size

/--
  Convert a JSON array of key-value pairs to a SetTree.
-/
instance SetTree.fromJson {α : Type} [Ord α] [jα : Lean.FromJson α] : Lean.FromJson (SetTree α) where
  fromJson? := fun json => do
    let arr ← json.getArr?
    let arr ← arr.mapM jα.fromJson?
    let arr := arr.qsort (fun u v => compare u v = .lt)
    pure (ofArray arr)

/--
  The given tree is a valid search tree with elements within given bounds.
-/
def SetTree.correctBound {α : Type} [Ord α] (low high : Bounded α) : SetTree α → Bool
  | empty => true
  | leaf x =>
    match compare low (.element x) with
    | .lt =>
      match compare (.element x) high with
      | .lt => true
      | _ => false
    | _ => false
  | node x left right =>
    match compare low x with
    | .lt =>
      match compare (.element x) high with
      | .lt => correctBound low (.element x) left && correctBound (.element x) high right
      | _ => false
    | _ => false

/--
  The given tree is a valid search tree.
-/
def SetTree.isCorrect {α : Type} [Ord α] (t : SetTree α) : Bool :=
  correctBound .bottom .top t

/-- The given element appears in the tree. -/
@[simp]
def SetTree.mem {α : Type} [Ord α] (x : α) : SetTree α → Bool
  | empty => false
  | leaf y =>
    match compare x y with
    | .eq => true
    | _ => false
  | node y left right =>
    match compare x y with
    | .lt => mem x left
    | .eq => true
    | .gt => mem x right

/-- The membership predicate for the set represented by a tree. -/
instance SetTree.hasMem {α : Type} [Ord α] : Membership α (SetTree α) where
  mem := fun x t => t.mem x

/-- The number of elements in the tree within the given bounds. -/
def SetTree.sizeBounded {α : Type} [Ord α] (low high : Bounded α) : SetTree α → Nat
  | empty => 0
  | leaf x  =>
    match compare low (.element x) with
    | .lt =>
      match compare (.element x) high with
      | .lt => 1
      | _ => 0
    | _ => 0
  | node x left right =>
    1 + sizeBounded low x left + sizeBounded x high right

/-- The number of elements in a tree. -/
@[simp]
def SetTree.size {α : Type} [Ord α] (t : SetTree α) : Nat :=
  sizeBounded .bottom .top t

/-- Universal quantification over the elements of a tree. -/
@[simp]
def SetTree.all {α : Type} [Ord α] (t : SetTree α) (p : α → Prop) [DecidablePred p] : Bool :=
  match t with
  | empty => true
  | leaf x => p x
  | node x left right => p x && left.all p && right.all p

theorem SetTree.all_forall {α : Type} [Ord α] [OrdEq α] (t : SetTree α) (p : α → Prop) [DecidablePred p] :
  t.all p → ∀ x, SetTree.mem x t → p x := by
  induction t
  case empty => simp
  case leaf y =>
    simp
    intros py x
    cases (OrdEq_cases x y) with
    | inl H => simp [H]
    | inr G =>
      cases G with
      | inl H => simp [H.left] ; rw [H.right] ; assumption
      | inr H => simp [H]
  case node y left right ihl ihr =>
    simp
    intros px all_left all_right x
    cases (OrdEq_cases x y) with
    | inl H => simp [H.left] ; apply ihl all_left
    | inr G =>
      cases G with
      | inl H => simp [H.left] ; rw [H.right] ; assumption
      | inr H => simp [H.left] ; apply ihr all_right

@[simp]
def SetTree.exi {α : Type} [Ord α] (t : SetTree α) (p : α → Prop) [DecidablePred p] : Bool :=
  match t with
  | empty => false
  | leaf x => p x
  | node x left right => p x || left.exi p || right.exi p

theorem SetTree.exists_exi {α : Type} [Ord α] [OrdEq α] (p : α → Prop) [DecidablePred p] :
  ∀ (t : SetTree α), (∃ x, SetTree.mem x t ∧ p x) → t.exi p = true := by
  intro t
  induction t
  case empty => simp
  case leaf y =>
    simp
    intro x
    cases (OrdEq_cases x y) with
    | inl H => simp [H.left]
    | inr G =>
      cases G with
      | inl H => simp [H.left] ; rw [H.right] ; intro ; assumption
      | inr H => simp [H.left]
  case node y left right ihl ihr =>
    simp
    intro x
    cases (OrdEq_cases x y) with
    | inl H => simp [H.left] ; intros ; apply Or.inl ; apply Or.inr ; apply ihl ; exists x
    | inr G =>
      cases G with
      | inl H => simp [H.left] ; rw [H.right] ; intro ; apply Or.inl ; apply Or.inl ; assumption
      | inr H => simp [H.left] ; intros ; apply Or.inr ; apply ihr ; exists x

-- The underlying set of the tree
@[reducible, simp]
def SetTree.set {α : Type} [Ord α] (t : SetTree α) := { x : α // t.mem x }

-- def SetTree.size_is_card {α : Type} [Ord α] [Fintype α] (t : SetTree α) :
--   Fintype.card t.set = t.size := sorry

end GAP2Lean

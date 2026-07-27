-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.AnchoredPowersetEnumeration.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Powerset
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `anchoredPowerset_sum_erase`

Let α be a type with `[DecidableEq α]`. For every finset `C : Finset α`, anchor `a : α`, proof `ha :
a ∈ C`, and weight `f : Finset α → ℕ`, the sum over subsets of `C` containing `a` is reindexed by
erasing the anchor:

`∑ S ∈ C.powerset.filter (fun S => a ∈ S), f S = ∑ T ∈ (C.erase a).powerset, f (insert a T)`.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Finset.filter` from `Mathlib.Data.Finset.Filter`
- `Finset.powerset` from `Mathlib.Data.Finset.Powerset`

## Proof outline

Apply `Finset.sum_bij` to the source finset `C.powerset.filter (fun S => a ∈ S)` and target
`(C.erase a).powerset`, sending an anchored subset `S` to `S.erase a`.

For a source member, `Finset.mem_powerset` gives `S ⊆ C`; erasing preserves this inclusion and
excludes `a`, so `S.erase a ⊆ C.erase a`, hence it is in the target powerset. Equality of images is
injective on the source because `Finset.insert_erase_invOn` gives the inverse law `insert a (S.erase
a) = S` for sets containing `a`. The summands then agree after this rewrite: `f S = f (insert a
(S.erase a))`.

For surjectivity, let `T ∈ (C.erase a).powerset`. From `Finset.mem_powerset`, `T ⊆ C.erase a`; in
particular `a ∉ T`. Map it back to `insert a T`. `Finset.insert_subset ha` shows this lies in `C`,
and it contains `a`, so it is in the filtered source. The other inverse law supplied by
`Finset.insert_erase_invOn` (equivalently the erase-after-insert law using `a ∉ T`) proves that its
image is `T`. These facts discharge `sum_bij` and yield the stated equality.

## Proof dependencies

- `Finset.sum_bij` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Finset.insert_erase_invOn` from `Mathlib.Data.Finset.Basic`
- `Finset.insert_subset` from `Mathlib.Data.Finset.Insert`
- `Finset.mem_powerset` from `Mathlib.Data.Finset.Powerset`
-/
theorem anchoredPowerset_sum_erase {α : Type*} [DecidableEq α] (C : Finset α) (a : α)
    (ha : a ∈ C) (f : Finset α → ℕ) :
    ∑ S ∈ C.powerset.filter (fun S => a ∈ S), f S =
      ∑ T ∈ (C.erase a).powerset, f (insert a T) := by
  refine Finset.sum_bij (fun S _ => S.erase a) ?_ ?_ ?_ ?_
  · intro S hS
    rw [Finset.mem_filter] at hS
    rw [Finset.mem_powerset] at hS ⊢
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hx).1, hS.1 (Finset.mem_erase.mp hx).2⟩
  · intro S₁ h₁ S₂ h₂ hEq
    have ha₁ : a ∈ S₁ := (Finset.mem_filter.mp h₁).2
    have ha₂ : a ∈ S₂ := (Finset.mem_filter.mp h₂).2
    calc
      S₁ = insert a (S₁.erase a) := (Finset.insert_erase ha₁).symm
      _ = insert a (S₂.erase a) := by rw [hEq]
      _ = S₂ := Finset.insert_erase ha₂
  · intro T hT
    refine ⟨insert a T, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset ha ((Finset.mem_powerset.mp hT).trans
        (Finset.erase_subset a C)), Finset.mem_insert_self _ _⟩
    · have hnot : a ∉ T := by
        intro hat
        exact (Finset.mem_erase.mp ((Finset.mem_powerset.mp hT) hat)).1 rfl
      simp [hnot]
  · intro S hS
    rw [Finset.insert_erase (Finset.mem_filter.mp hS).2]

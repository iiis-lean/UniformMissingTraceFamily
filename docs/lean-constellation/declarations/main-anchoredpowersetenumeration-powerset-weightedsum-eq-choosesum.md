[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `powerset_weightedSum_eq_chooseSum`

Evaluates a cardinality-filtered weighted powerset sum as a binomial convolution.

- Kind: `theorem`
- Node: `Main.AnchoredPowersetEnumeration`
- Module: `UniformMissingTraceFamily.Main.AnchoredPowersetEnumeration.Theorems.powerset_weightedSum_eq_chooseSum`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let α be a type with `[DecidableEq α]`. For every finsets `s U : Finset α` and natural `d`, the weighted sum over subsets of `s` whose cardinality is at most `d` decomposes into cardinality fibers:

`∑ T ∈ s.powerset.filter (fun T => T.card ≤ d), Nat.choose U.card (d - T.card) = ∑ j ∈ Finset.range (d + 1), Nat.choose s.card j * Nat.choose U.card (d - j)`.

The filter, the index range `Finset.range (d + 1)`, and every subtraction use the displayed natural-number forms; no cardinality, disjointness, or ambient-size assumptions are required.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.AnchoredPowersetEnumeration.Prelude
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `powerset_weightedSum_eq_chooseSum`

Let α be a type with `[DecidableEq α]`. For every finsets `s U : Finset α` and natural `d`, the
weighted sum over subsets of `s` whose cardinality is at most `d` decomposes into cardinality
fibers:

`∑ T ∈ s.powerset.filter (fun T => T.card ≤ d), Nat.choose U.card (d - T.card) = ∑ j ∈ Finset.range
(d + 1), Nat.choose s.card j * Nat.choose U.card (d - j)`.

The filter, the index range `Finset.range (d + 1)`, and every subtraction use the displayed
natural-number forms; no cardinality, disjointness, or ambient-size assumptions are required.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Finset.filter` from `Mathlib.Data.Finset.Filter`
- `Finset.powerset` from `Mathlib.Data.Finset.Powerset`
- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
-/
theorem powerset_weightedSum_eq_chooseSum {α : Type*} [inst : DecidableEq α]
    (s U : Finset α) (d : ℕ) :
    let _ : DecidableEq α := inst
    ∑ T ∈ s.powerset.filter (fun T => T.card ≤ d), Nat.choose U.card (d - T.card) =
      ∑ j ∈ Finset.range (d + 1), Nat.choose s.card j * Nat.choose U.card (d - j) := by
  sorry
```

## Proof NL

First use `Finset.sum_filter` to rewrite the filtered left-hand sum as a sum over all of `s.powerset` with the zero-extended summand
`F T := if T.card ≤ d then Nat.choose U.card (d - T.card) else 0`.
This preserves the original filter exactly.

Apply `Finset.sum_powerset s F`. It decomposes that sum into the fibers `s.powersetCard j` for `j ∈ Finset.range (s.card + 1)`. On a fixed fiber, `Finset.mem_powersetCard` rewrites every `T.card` to `j`. If `j ≤ d`, the resulting fiber is exactly
`∑ T ∈ s.powersetCard j, Nat.choose U.card (d - T.card)`,
so use the committed lower theorem `powersetCard_weightedSum_eq_choose` to obtain
`Nat.choose s.card j * Nat.choose U.card (d - j)`. If `d < j`, the conditional definition of `F` makes every summand zero.

It remains to replace the sum over `Finset.range (s.card + 1)` of these in-range fiber values by the stated sum over `Finset.range (d + 1)`. Split on the comparison of `s.card` and `d`. When `d ≤ s.card`, the latter range is a subset of the former and the extra indices have `d < j`, hence their zero-extended fiber values are zero. When `s.card ≤ d`, the former range is a subset of the latter; for an index in the added difference, `s.card < j`, so `Nat.choose_eq_zero_of_lt` makes the displayed binomial product zero. In both cases apply `Finset.sum_subset_zero_on_sdiff` to remove the zero terms. This yields exactly the required `range (d + 1)` convolution with the unchanged natural subtraction index.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.AnchoredPowersetEnumeration.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import UniformMissingTraceFamily.Main.AnchoredPowersetEnumeration.Theorems.powersetCard_weightedSum_eq_choose
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `powerset_weightedSum_eq_chooseSum`

Let α be a type with `[DecidableEq α]`. For every finsets `s U : Finset α` and natural `d`, the
weighted sum over subsets of `s` whose cardinality is at most `d` decomposes into cardinality
fibers:

`∑ T ∈ s.powerset.filter (fun T => T.card ≤ d), Nat.choose U.card (d - T.card) = ∑ j ∈ Finset.range
(d + 1), Nat.choose s.card j * Nat.choose U.card (d - j)`.

The filter, the index range `Finset.range (d + 1)`, and every subtraction use the displayed
natural-number forms; no cardinality, disjointness, or ambient-size assumptions are required.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Finset.filter` from `Mathlib.Data.Finset.Filter`
- `Finset.powerset` from `Mathlib.Data.Finset.Powerset`
- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`

## Proof outline

First use `Finset.sum_filter` to rewrite the filtered left-hand sum as a sum over all of
`s.powerset` with the zero-extended summand
`F T := if T.card ≤ d then Nat.choose U.card (d - T.card) else 0`.
This preserves the original filter exactly.

Apply `Finset.sum_powerset s F`. It decomposes that sum into the fibers `s.powersetCard j` for `j ∈
Finset.range (s.card + 1)`. On a fixed fiber, `Finset.mem_powersetCard` rewrites every `T.card` to
`j`. If `j ≤ d`, the resulting fiber is exactly
`∑ T ∈ s.powersetCard j, Nat.choose U.card (d - T.card)`,
so use the committed lower theorem `powersetCard_weightedSum_eq_choose` to obtain
`Nat.choose s.card j * Nat.choose U.card (d - j)`. If `d < j`, the conditional definition of `F`
makes every summand zero.

It remains to replace the sum over `Finset.range (s.card + 1)` of these in-range fiber values by the
stated sum over `Finset.range (d + 1)`. Split on the comparison of `s.card` and `d`. When `d ≤
s.card`, the latter range is a subset of the former and the extra indices have `d < j`, hence their
zero-extended fiber values are zero. When `s.card ≤ d`, the former range is a subset of the latter;
for an index in the added difference, `s.card < j`, so `Nat.choose_eq_zero_of_lt` makes the
displayed binomial product zero. In both cases apply `Finset.sum_subset_zero_on_sdiff` to remove the
zero terms. This yields exactly the required `range (d + 1)` convolution with the unchanged natural
subtraction index.

## Proof dependencies

- `Finset.sum_filter` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_subset_zero_on_sdiff` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_powerset` from `Mathlib.Algebra.BigOperators.Group.Finset.Powerset`
- `Finset.mem_powersetCard` from `Mathlib.Data.Finset.Powerset`
- `Nat.choose_eq_zero_of_lt` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.AnchoredPowersetEnumeration::powersetCard_weightedSum_eq_choose` →
  `powersetCard_weightedSum_eq_choose` from `UniformMissingTraceFamily.Main.AnchoredPowersetEnumerat
  ion.Theorems.powersetCard_weightedSum_eq_choose`
-/
theorem powerset_weightedSum_eq_chooseSum {α : Type*} [inst : DecidableEq α]
    (s U : Finset α) (d : ℕ) :
    let _ : DecidableEq α := inst
    ∑ T ∈ s.powerset.filter (fun T => T.card ≤ d), Nat.choose U.card (d - T.card) =
      ∑ j ∈ Finset.range (d + 1), Nat.choose s.card j * Nat.choose U.card (d - j) := by
  let F : Finset α → ℕ := fun T =>
    if T.card ≤ d then Nat.choose U.card (d - T.card) else 0
  have hfiltered :
      ∑ T ∈ s.powerset.filter (fun T => T.card ≤ d), Nat.choose U.card (d - T.card) =
        ∑ T ∈ s.powerset, F T := by
    simpa [F] using
      (Finset.sum_filter (s := s.powerset) (p := fun T => T.card ≤ d)
        (f := fun T => Nat.choose U.card (d - T.card)))
  have hfiber (j : ℕ) :
      ∑ T ∈ s.powersetCard j, F T =
        if j ≤ d then Nat.choose s.card j * Nat.choose U.card (d - j) else 0 := by
    by_cases hj : j ≤ d
    · rw [if_pos hj]
      calc
        ∑ T ∈ s.powersetCard j, F T =
            ∑ T ∈ s.powersetCard j, Nat.choose U.card (d - T.card) := by
              apply Finset.sum_congr rfl
              intro T hT
              simp [F, (Finset.mem_powersetCard.mp hT).2, hj]
        _ = Nat.choose s.card j * Nat.choose U.card (d - j) :=
          powersetCard_weightedSum_eq_choose s U d j
    · rw [if_neg hj]
      apply Finset.sum_eq_zero
      intro T hT
      simp [F, (Finset.mem_powersetCard.mp hT).2, hj]
  have hrange :
      ∑ j ∈ Finset.range (s.card + 1),
          (if j ≤ d then Nat.choose s.card j * Nat.choose U.card (d - j) else 0) =
        ∑ j ∈ Finset.range (d + 1), Nat.choose s.card j * Nat.choose U.card (d - j) := by
    by_cases hsd : s.card ≤ d
    · refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_range] at hj ⊢
        omega
      · intro j hj
        simp only [Finset.mem_sdiff, Finset.mem_range] at hj
        have hlt : s.card < j := by omega
        rw [Nat.choose_eq_zero_of_lt hlt]
        simp
      · intro j hj
        simp only [Finset.mem_range] at hj
        have hjle : j ≤ s.card := Nat.le_of_lt_succ hj
        simp [hjle.trans hsd]
    · have hds : d < s.card := Nat.lt_of_not_ge hsd
      symm
      refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_range] at hj ⊢
        omega
      · intro j hj
        simp only [Finset.mem_sdiff, Finset.mem_range] at hj
        have hlt : d < j := by omega
        simp [Nat.not_le_of_gt hlt]
      · intro j hj
        simp only [Finset.mem_range] at hj
        have hjle : j ≤ d := Nat.le_of_lt_succ hj
        simp [hjle]
  calc
    ∑ T ∈ s.powerset.filter (fun T => T.card ≤ d), Nat.choose U.card (d - T.card) =
        ∑ T ∈ s.powerset, F T := hfiltered
    _ = ∑ j ∈ Finset.range (s.card + 1), ∑ T ∈ s.powersetCard j, F T :=
      Finset.sum_powerset s F
    _ = ∑ j ∈ Finset.range (s.card + 1),
        (if j ≤ d then Nat.choose s.card j * Nat.choose U.card (d - j) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hfiber j
    _ = ∑ j ∈ Finset.range (d + 1), Nat.choose s.card j * Nat.choose U.card (d - j) := hrange
```

## Statement dependencies

- `Mathlib:Mathlib.Data.Finset.Filter.Finset.filter`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.powerset`
- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_filter`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_subset_zero_on_sdiff`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Powerset.Finset.sum_powerset`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.mem_powersetCard`
- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose_eq_zero_of_lt`
- `current repo:Main.AnchoredPowersetEnumeration.powersetCard_weightedSum_eq_choose`

## Sources

- `article/sections/02_proof.tex:49-49`

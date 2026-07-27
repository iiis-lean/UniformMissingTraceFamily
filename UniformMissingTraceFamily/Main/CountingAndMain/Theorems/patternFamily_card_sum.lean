-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.completionFiber_card
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.completionFibers_pairwiseDisjoint
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `patternFamily_card_sum`

For natural numbers n and d, a finite pattern family `patterns : Finset (Finset (Fin n))`, and a
filler `U : Finset (Fin n)`, if every `P ∈ patterns` is disjoint from `U`, then
`(patternFamily d patterns U).card = ∑ P ∈ patterns, Nat.choose U.card (d + 1 - P.card)`.
The sum is indexed by the unchanged Finset `patterns`, so this formula can be specialized directly
to `perturbedStarPatterns` and its complementary filler.

## Sources

- Source `article/sections/02_proof.tex`, lines 48–50

## Statement dependencies

- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PatternCriterion::patternFamily` → `patternFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily`

## Proof outline

Unfold the accepted definition `patternFamily d patterns U`, so the left-hand side is the
cardinality of `patterns.biUnion` of the exact completion fibers.  Apply `Finset.card_biUnion` with
`completionFibers_pairwiseDisjoint patterns U hdisj`; this changes the goal to the Finset sum of the
cardinalities of those fibers, indexed by the unchanged `patterns`.

For each summand `P` with `P ∈ patterns`, apply the committed theorem `completionFiber_card P U
(hdisj P hP)`.  Its right-hand side is exactly `Nat.choose U.card (d + 1 - P.card)`, so the
resulting sum is definitionally the required conclusion.  The formal proof is an unfold/rewrite
followed by a `Finset.sum_congr` (or equivalent simplification) and has no unresolved helper or
external dependency.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 48–50

## Proof dependencies

- `Finset.card_biUnion` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Main.CountingAndMain::completionFiber_card` → `completionFiber_card` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.completionFiber_card`
- `Main.CountingAndMain::completionFibers_pairwiseDisjoint` → `completionFibers_pairwiseDisjoint`
  from `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.completionFibers_pairwiseDisjoint`
- `Main.PatternCriterion::patternFamily` → `patternFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily`
-/
theorem patternFamily_card_sum {n d : ℕ}
    (patterns : Finset (Finset (Fin n))) (U : Finset (Fin n))
    (hdisj : ∀ P ∈ patterns, Disjoint P U) :
    (patternFamily d patterns U).card =
      ∑ P ∈ patterns, Nat.choose U.card (d + 1 - P.card) := by
  unfold patternFamily
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro P hP
    exact completionFiber_card P U (hdisj P hP)
  · exact completionFibers_pairwiseDisjoint patterns U hdisj

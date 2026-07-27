-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.AnchoredPowersetEnumeration.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `powersetCard_weightedSum_eq_choose`

Let α be a type with `[DecidableEq α]`. For every finsets `s U : Finset α` and naturals `d j`, the
constant-weight sum over the cardinality-`j` subsets of `s` is

`∑ T ∈ s.powersetCard j, Nat.choose U.card (d - T.card) = Nat.choose s.card j * Nat.choose U.card (d
- j)`.

No size or disjointness assumptions are required; all subtractions are natural-number subtraction.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Finset.powersetCard` from `Mathlib.Data.Finset.Powerset`
- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`

## Proof outline

Use `Finset.sum_powersetCard` with the cardinality-only function `g k := Nat.choose U.card (d - k)`.
That lemma replaces every occurrence of `g T.card` in the sum over `s.powersetCard j` by the single
value `g j` and multiplies it by the number of members of the fiber.

Its cardinality factor is `Nat.choose s.card j` (the same value supplied by
`Finset.card_powersetCard`; it is built into `Finset.sum_powersetCard`).  Substituting the
definition of `g` gives exactly `Nat.choose s.card j * Nat.choose U.card (d - j)`.  No inequality or
disjointness argument is needed: `Finset.mem_powersetCard` fixes `T.card = j`, so the natural
subtraction index is rewritten exactly, including the cases where `d < j`.

## Proof dependencies

- `Finset.sum_powersetCard` from `Mathlib.Algebra.BigOperators.Group.Finset.Powerset`
- `Finset.card_powersetCard` from `Mathlib.Data.Finset.Powerset`
- `Finset.mem_powersetCard` from `Mathlib.Data.Finset.Powerset`
-/
theorem powersetCard_weightedSum_eq_choose {α : Type*} [inst : DecidableEq α]
    (s U : Finset α) (d j : ℕ) :
    let _ : DecidableEq α := inst
    ∑ T ∈ s.powersetCard j, Nat.choose U.card (d - T.card) =
      Nat.choose s.card j * Nat.choose U.card (d - j) := by
  simpa using
    (Finset.sum_powersetCard j s (fun k => Nat.choose U.card (d - k)))

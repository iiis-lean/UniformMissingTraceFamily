[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `powersetCard_weightedSum_eq_choose`

Evaluates a binomial weight that is constant on a powersetCard fiber.

- Kind: `theorem`
- Node: `Main.AnchoredPowersetEnumeration`
- Module: `UniformMissingTraceFamily.Main.AnchoredPowersetEnumeration.Theorems.powersetCard_weightedSum_eq_choose`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

Let α be a type with `[DecidableEq α]`. For every finsets `s U : Finset α` and naturals `d j`, the constant-weight sum over the cardinality-`j` subsets of `s` is

`∑ T ∈ s.powersetCard j, Nat.choose U.card (d - T.card) = Nat.choose s.card j * Nat.choose U.card (d - j)`.

No size or disjointness assumptions are required; all subtractions are natural-number subtraction.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.AnchoredPowersetEnumeration.Prelude
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
-/
theorem powersetCard_weightedSum_eq_choose {α : Type*} [inst : DecidableEq α]
    (s U : Finset α) (d j : ℕ) :
    let _ : DecidableEq α := inst
    ∑ T ∈ s.powersetCard j, Nat.choose U.card (d - T.card) =
      Nat.choose s.card j * Nat.choose U.card (d - j) := by
  sorry
```

## Proof NL

Use `Finset.sum_powersetCard` with the cardinality-only function `g k := Nat.choose U.card (d - k)`.  That lemma replaces every occurrence of `g T.card` in the sum over `s.powersetCard j` by the single value `g j` and multiplies it by the number of members of the fiber.

Its cardinality factor is `Nat.choose s.card j` (the same value supplied by `Finset.card_powersetCard`; it is built into `Finset.sum_powersetCard`).  Substituting the definition of `g` gives exactly `Nat.choose s.card j * Nat.choose U.card (d - j)`.  No inequality or disjointness argument is needed: `Finset.mem_powersetCard` fixes `T.card = j`, so the natural subtraction index is rewritten exactly, including the cases where `d < j`.

## Proof Formal

```lean
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
```

## Statement dependencies

- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.powersetCard`
- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Powerset.Finset.sum_powersetCard`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.card_powersetCard`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.mem_powersetCard`

## Sources

- `article/sections/02_proof.tex:49-49`

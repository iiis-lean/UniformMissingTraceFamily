[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `perturbedStarBase_chooseSum`

The weighted anchored-core base patterns enumerate all star members and sum to choose(n−1,d).

- Kind: `theorem`
- Node: `Main.CountingAndMain`
- Module: `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarBase_chooseSum`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For natural numbers n, r, and d and construction data `B : PerturbedStarBlocks n r`,
`∑ P ∈ ((perturbedStarCore B).powerset.filter (fun P => B.a ∈ P ∧ P.card ≤ d + 1)), Nat.choose (perturbedStarFiller B).card (d + 1 - P.card) = Nat.choose (n - 1) d`.
Thus the anchored base in exactly the representation used by `perturbedStarPatterns` enumerates all `(d + 1)`-subsets of `Fin n` containing `B.a`, by their core and complementary-filler parts.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarBase_chooseSum`

For natural numbers n, r, and d and construction data `B : PerturbedStarBlocks n r`,
`∑ P ∈ ((perturbedStarCore B).powerset.filter (fun P => B.a ∈ P ∧ P.card ≤ d + 1)), Nat.choose
(perturbedStarFiller B).card (d + 1 - P.card) = Nat.choose (n - 1) d`.
Thus the anchored base in exactly the representation used by `perturbedStarPatterns` enumerates all
`(d + 1)`-subsets of `Fin n` containing `B.a`, by their core and complementary-filler parts.

## Sources

- Source `article/sections/02_proof.tex`, lines 48–49

## Statement dependencies

- `Finset.filter` from `Mathlib.Data.Finset.Filter`
- `Finset.powerset` from `Mathlib.Data.Finset.Powerset`
- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`
-/
theorem perturbedStarBase_chooseSum {n r d : ℕ} (B : PerturbedStarBlocks n r) :
    (∑ P ∈ (perturbedStarCore B).powerset.filter (fun P => B.a ∈ P ∧ P.card ≤ d + 1),
      Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)) = Nat.choose (n - 1) d := by
  sorry
```

## Proof NL

Let `C := perturbedStarCore B` and `U := perturbedStarFiller B`.  First derive `B.a ∈ C` by unfolding the accepted definition `perturbedStarCore`; this is a lightweight membership proof. Apply the proof-accepted provider `Main.AnchoredPowersetEnumeration::anchoredPowerset_weightedSum_eq_chooseSum C U B.a d ha`. Its filtered anchored-powerset sum is definitionally the left-hand side, so it reduces the goal to its displayed range convolution.

Rewrite the convolution parameters with the committed `perturbedStarCore_card B` and `perturbedStarFiller_card B`; use the verified `Finset.card_erase_of_mem ha` for `(C.erase B.a).card`. The resulting two cardinalities add to `n - 1`, by elementary natural-number normalization. Evaluate the range convolution as the Vandermonde convolution using verified `Nat.add_choose_eq`, converting the standard antidiagonal form to the displayed `Finset.range (d + 1)` form by the routine zero-boundary reindexing. This yields exactly `Nat.choose (n - 1) d`, with no extra hypothesis and without using the cleanup wrapper `anchoredPowerset_chooseSum_reindex`.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarCore_card
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarFiller_card
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarBase_chooseSum`

For natural numbers n, r, and d and construction data `B : PerturbedStarBlocks n r`,
`∑ P ∈ ((perturbedStarCore B).powerset.filter (fun P => B.a ∈ P ∧ P.card ≤ d + 1)), Nat.choose
(perturbedStarFiller B).card (d + 1 - P.card) = Nat.choose (n - 1) d`.
Thus the anchored base in exactly the representation used by `perturbedStarPatterns` enumerates all
`(d + 1)`-subsets of `Fin n` containing `B.a`, by their core and complementary-filler parts.

## Sources

- Source `article/sections/02_proof.tex`, lines 48–49

## Statement dependencies

- `Finset.filter` from `Mathlib.Data.Finset.Filter`
- `Finset.powerset` from `Mathlib.Data.Finset.Powerset`
- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`

## Proof outline

Let `C := perturbedStarCore B` and `U := perturbedStarFiller B`.  First derive `B.a ∈ C` by
unfolding the accepted definition `perturbedStarCore`; this is a lightweight membership proof. Apply
the proof-accepted provider
`Main.AnchoredPowersetEnumeration::anchoredPowerset_weightedSum_eq_chooseSum C U B.a d ha`. Its
filtered anchored-powerset sum is definitionally the left-hand side, so it reduces the goal to its
displayed range convolution.

Rewrite the convolution parameters with the committed `perturbedStarCore_card B` and
`perturbedStarFiller_card B`; use the verified `Finset.card_erase_of_mem ha` for `(C.erase
B.a).card`. The resulting two cardinalities add to `n - 1`, by elementary natural-number
normalization. Evaluate the range convolution as the Vandermonde convolution using verified
`Nat.add_choose_eq`, converting the standard antidiagonal form to the displayed `Finset.range (d +
1)` form by the routine zero-boundary reindexing. This yields exactly `Nat.choose (n - 1) d`, with
no extra hypothesis and without using the cleanup wrapper `anchoredPowerset_chooseSum_reindex`.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 48–49

## Proof dependencies

- `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` from
  `Mathlib.Algebra.BigOperators.NatAntidiagonal`
- `Finset.card_erase_of_mem` from `Mathlib.Data.Finset.Card`
- `Nat.add_choose_eq` from `Mathlib.Data.Nat.Choose.Vandermonde`
- `Main.AnchoredPowersetEnumeration::anchoredPowerset_weightedSum_eq_chooseSum` →
  `anchoredPowerset_weightedSum_eq_chooseSum` from `UniformMissingTraceFamily.Main.AnchoredPowersetE
  numeration.Theorems.anchoredPowerset_weightedSum_eq_chooseSum`
- `Main.CountingAndMain::perturbedStarCore_card` → `perturbedStarCore_card` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarCore_card`
- `Main.CountingAndMain::perturbedStarFiller_card` → `perturbedStarFiller_card` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarFiller_card`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
-/
theorem perturbedStarBase_chooseSum {n r d : ℕ} (B : PerturbedStarBlocks n r) :
    (∑ P ∈ (perturbedStarCore B).powerset.filter (fun P => B.a ∈ P ∧ P.card ≤ d + 1),
      Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)) = Nat.choose (n - 1) d := by
  have ha : B.a ∈ perturbedStarCore B := by
    simp [perturbedStarCore]
  have hcore_le : (perturbedStarCore B).card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ (perturbedStarCore B))
  have hnr : 2 + 2 * r ≤ n := by
    simpa only [perturbedStarCore_card] using hcore_le
  have herase : ((perturbedStarCore B).erase B.a).card = 1 + 2 * r := by
    rw [Finset.card_erase_of_mem ha, perturbedStarCore_card]
    omega
  have hsum : 1 + 2 * r + (n - (2 + 2 * r)) = n - 1 := by
    omega
  calc
    ∑ P ∈ (perturbedStarCore B).powerset.filter (fun P => B.a ∈ P ∧ P.card ≤ d + 1),
        Nat.choose (perturbedStarFiller B).card (d + 1 - P.card) =
      ∑ j ∈ Finset.range (d + 1),
        Nat.choose ((perturbedStarCore B).erase B.a).card j *
          Nat.choose (perturbedStarFiller B).card (d - j) :=
      anchoredPowerset_weightedSum_eq_chooseSum (perturbedStarCore B)
        (perturbedStarFiller B) B.a d ha
    _ = ∑ j ∈ Finset.range (d + 1),
        Nat.choose (1 + 2 * r) j * Nat.choose (n - (2 + 2 * r)) (d - j) := by
      rw [herase, perturbedStarFiller_card]
    _ = ∑ ij ∈ Finset.antidiagonal d,
        Nat.choose (1 + 2 * r) ij.1 * Nat.choose (n - (2 + 2 * r)) ij.2 := by
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    _ = Nat.choose (1 + 2 * r + (n - (2 + 2 * r))) d := by
      exact (Nat.add_choose_eq (1 + 2 * r) (n - (2 + 2 * r)) d).symm
    _ = Nat.choose (n - 1) d := by rw [hsum]
```

## Statement dependencies

- `Mathlib:Mathlib.Data.Finset.Filter.Finset.filter`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.powerset`
- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFiller`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.NatAntidiagonal.Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_erase_of_mem`
- `Mathlib:Mathlib.Data.Nat.Choose.Vandermonde.Nat.add_choose_eq`
- `current repo:Main.AnchoredPowersetEnumeration.anchoredPowerset_weightedSum_eq_chooseSum`
- `current repo:Main.CountingAndMain.perturbedStarCore_card`
- `current repo:Main.CountingAndMain.perturbedStarFiller_card`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`

## Sources

- `article/sections/02_proof.tex:48-49`

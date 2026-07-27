-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternA_injOn
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternB_injOn
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternB_properImage_eq_erase
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPattern_chooseWeight_eq
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedPattern_properWeights_add_full_eq_fullWeights`

For every `B : PerturbedStarBlocks n r` and every natural number `d`, let

`w(P) = Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)`,

`fₐ(Y) = {B.a} ∪ B.T ∪ Y`, and `fᵦ(Y) = {B.b} ∪ B.T ∪ Y`.

Then the proper deleted-pattern weight sum plus the sole full-`L` added-pattern weight equals the
full added-pattern image weight sum:

`(∑ P ∈ ({Y ∈ B.L.powerset | Y ≠ B.L}.image fₐ), w(P)) + w({B.b} ∪ B.T ∪ B.L) = ∑ P ∈
B.L.powerset.image fᵦ, w(P)`.

No additional hypotheses, including `hrd` or `hrn`, are assumed.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Finset.sum` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Finset.card` from `Mathlib.Data.Finset.Card`
- `Finset.filter` from `Mathlib.Data.Finset.Filter`
- `Finset.image` from `Mathlib.Data.Finset.Image`
- `Finset.powerset` from `Mathlib.Data.Finset.Powerset`
- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`

## Proof outline

Write `S = B.L.powerset`, `D = S.filter (fun Y => Y ≠ B.L)`, `fₐ(Y) = {B.a} ∪ B.T ∪ Y`, `fᵦ(Y) =
{B.b} ∪ B.T ∪ Y`, and `w(P) = Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)`.  First
restrict each accepted `Set.InjOn` theorem `perturbedPatternA_injOn B` and `perturbedPatternB_injOn
B` from `S` to `D`: `Finset.mem_filter` shows every member of `D` lies in `S`.  Apply
`Finset.sum_image` with the restricted a-injectivity to rewrite the left proper-a image sum as `∑ Y
∈ D, w (fₐ Y)`.

Use `Finset.sum_congr` on this common finite domain.  For each `Y ∈ D`, combine `Finset.mem_filter`
and `Finset.mem_powerset` to obtain `Y ⊆ B.L`, then apply the accepted theorem
`perturbedPattern_chooseWeight_eq B d Y` to replace `w (fₐ Y)` with `w (fᵦ Y)`.  Apply
`Finset.sum_image` with the restricted b-injectivity in the reverse direction, converting this sum
to the proper-b image sum `∑ P ∈ D.image fᵦ, w P`.

Rewrite the b-image index finset with the accepted `perturbedPatternB_properImage_eq_erase B`,
obtaining the sum over `(S.image fᵦ).erase (fᵦ B.L)`.  Establish `fᵦ B.L ∈ S.image fᵦ` by
`Finset.mem_image`, using `Finset.mem_powerset` for `B.L ∈ S`.  Finally apply `Finset.sum_erase_add`
to conclude that this erased b-image sum plus `w (fᵦ B.L)` is exactly the full b-image sum.  This
yields the stated proper-a-plus-full-b equals full-b direction with the exact maps and indices, no
`hrd`/ `hrn` assumptions, and no helper declaration.

## Proof sources

- Source `article/sections/02_proof.tex`, line 49

## Proof dependencies

- `Finset.sum_congr` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_erase_add` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_image` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.mem_filter` from `Mathlib.Data.Finset.Filter`
- `Finset.mem_image` from `Mathlib.Data.Finset.Image`
- `Finset.mem_powerset` from `Mathlib.Data.Finset.Powerset`
- `Main.PerturbedPatternCancellation::perturbedPatternA_injOn` → `perturbedPatternA_injOn` from
  `UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternA_injOn`
- `Main.PerturbedPatternCancellation::perturbedPatternB_injOn` → `perturbedPatternB_injOn` from
  `UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternB_injOn`
- `Main.PerturbedPatternCancellation::perturbedPatternB_properImage_eq_erase` →
  `perturbedPatternB_properImage_eq_erase` from `UniformMissingTraceFamily.Main.PerturbedPatternCanc
  ellation.Theorems.perturbedPatternB_properImage_eq_erase`
- `Main.PerturbedPatternCancellation::perturbedPattern_chooseWeight_eq` →
  `perturbedPattern_chooseWeight_eq` from `UniformMissingTraceFamily.Main.PerturbedPatternCancellati
  on.Theorems.perturbedPattern_chooseWeight_eq`
-/
theorem perturbedPattern_properWeights_add_full_eq_fullWeights {n r : ℕ}
    (B : PerturbedStarBlocks n r) (d : ℕ) :
    (∑ P ∈ (B.L.powerset.filter (fun Y => Y ≠ B.L)).image
        (fun Y : Finset (Fin n) ↦ {B.a} ∪ B.T ∪ Y),
      Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)) +
      Nat.choose (perturbedStarFiller B).card
        (d + 1 - ({B.b} ∪ B.T ∪ B.L).card) =
      ∑ P ∈ B.L.powerset.image (fun Y : Finset (Fin n) ↦ {B.b} ∪ B.T ∪ Y),
        Nat.choose (perturbedStarFiller B).card (d + 1 - P.card) := by
  classical
  let D := B.L.powerset.filter (fun Y => Y ≠ B.L)
  let fA : Finset (Fin n) → Finset (Fin n) := fun Y => {B.a} ∪ B.T ∪ Y
  let fB : Finset (Fin n) → Finset (Fin n) := fun Y => {B.b} ∪ B.T ∪ Y
  let w : Finset (Fin n) → ℕ :=
    fun P => Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)
  change (∑ P ∈ D.image fA, w P) + w (fB B.L) =
    ∑ P ∈ B.L.powerset.image fB, w P
  have memD (Y : Finset (Fin n)) (hY : Y ∈ D) : Y ∈ B.L.powerset := by
    have hY' : Y ∈ B.L.powerset.filter (fun Y => Y ≠ B.L) := by
      simpa only [D] using hY
    exact (Finset.mem_filter.mp hY').1
  have hAinj : Set.InjOn fA (↑D : Set (Finset (Fin n))) := by
    intro Y hY Z hZ hEq
    apply perturbedPatternA_injOn B
    · exact memD Y hY
    · exact memD Z hZ
    · simpa [fA] using hEq
  have hBinj : Set.InjOn fB (↑D : Set (Finset (Fin n))) := by
    intro Y hY Z hZ hEq
    apply perturbedPatternB_injOn B
    · exact memD Y hY
    · exact memD Z hZ
    · simpa [fB] using hEq
  have hWeights : (∑ Y ∈ D, w (fA Y)) = ∑ Y ∈ D, w (fB Y) := by
    apply Finset.sum_congr rfl
    intro Y hY
    have hYPow : Y ∈ B.L.powerset := memD Y hY
    simpa [w, fA, fB] using
      perturbedPattern_chooseWeight_eq B d Y (Finset.mem_powerset.mp hYPow)
  have hFull : fB B.L ∈ B.L.powerset.image fB := by
    refine Finset.mem_image.mpr ⟨B.L, ?_, rfl⟩
    exact Finset.mem_powerset.mpr (fun _ hx => hx)
  calc
    (∑ P ∈ D.image fA, w P) + w (fB B.L) =
        (∑ Y ∈ D, w (fA Y)) + w (fB B.L) := by
      rw [Finset.sum_image hAinj]
    _ = (∑ Y ∈ D, w (fB Y)) + w (fB B.L) := by rw [hWeights]
    _ = (∑ P ∈ D.image fB, w P) + w (fB B.L) := by
      rw [(Finset.sum_image hBinj).symm]
    _ = (∑ P ∈ (B.L.powerset.image fB).erase (fB B.L), w P) + w (fB B.L) := by
      rw [← perturbedPatternB_properImage_eq_erase B]
    _ = ∑ P ∈ B.L.powerset.image fB, w P := Finset.sum_erase_add _ _ hFull

-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Powerset
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarPatterns_disjoint_filler`

For natural numbers n, r, and d and construction data `B : PerturbedStarBlocks n r`, every pattern
`P ∈ perturbedStarPatterns d B` is disjoint from the complementary filler `perturbedStarFiller B`.
Equivalently, `Disjoint P (perturbedStarFiller B)` holds for each such P, because every base,
deleted, or inserted pattern lies in `perturbedStarCore B`, while the filler is its complement in
`Fin n`.  No parameter bounds are assumed.

## Sources

- Source `article/sections/02_proof.tex`, lines 34–39

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`

## Proof outline

Unfold `perturbedStarPatterns`, `perturbedStarCore`, and `perturbedStarFiller`.  From `hP`, split
membership in `(base \ deleted) ∪ inserted`.  In the left case, membership in `base \ deleted` gives
membership in `base`; then `Finset.mem_powerset` yields `P ⊆ perturbedStarCore B`.  In the inserted
case, extract `Y ∈ B.L.powerset` and the equality `P = {B.b} ∪ B.T ∪ Y`; `Finset.mem_powerset` gives
`Y ⊆ B.L`, and elementwise union membership proves that this displayed pattern is a subset of
`{B.a,B.b} ∪ B.T ∪ B.L = perturbedStarCore B`.

Having proved `P ⊆ perturbedStarCore B`, use `Finset.disjoint_left`.  If an element belongs both to
`P` and to `perturbedStarFiller B = Finset.univ \ perturbedStarCore B`, the subset fact puts it in
the core while its filler membership says it is not in the core, a contradiction.  The case split
and membership simplifications are lightweight local Finset reasoning; no parameter hypothesis or
additional helper is required.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 34–39

## Proof dependencies

- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Finset.mem_powerset` from `Mathlib.Data.Finset.Powerset`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
-/
theorem perturbedStarPatterns_disjoint_filler {n r d : ℕ}
    (B : PerturbedStarBlocks n r) (P : Finset (Fin n))
    (hP : P ∈ perturbedStarPatterns d B) : Disjoint P (perturbedStarFiller B) := by
  have hsub : P ⊆ perturbedStarCore B := by
    unfold perturbedStarPatterns at hP
    dsimp at hP
    rcases Finset.mem_union.mp hP with hbase | hins
    · have hPbase := (Finset.mem_sdiff.mp hbase).1
      exact Finset.mem_powerset.mp (Finset.mem_filter.mp hPbase).1
    · rcases Finset.mem_image.mp hins with ⟨Y, hY, hYP⟩
      have hYsub : Y ⊆ B.L := Finset.mem_powerset.mp hY
      intro x hx
      rw [← hYP] at hx
      unfold perturbedStarCore
      rcases Finset.mem_union.mp hx with hxbT | hxY
      · rcases Finset.mem_insert.mp hxbT with rfl | hxT
        · simp
        · simp [hxT]
      · simp [hYsub hxY]
  rw [Finset.disjoint_left]
  intro x hxP hxFiller
  have hxCore : x ∈ perturbedStarCore B := hsub hxP
  unfold perturbedStarFiller at hxFiller
  exact (Finset.mem_sdiff.mp hxFiller).2 hxCore

-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Nat.Choose.Basic
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarExtra_choose_pos
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarFamily_card
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `exists_uniformMissingTraceFamily_strictlyLargerThanStar`

For natural numbers `d`, `s`, and `n`, if `hd : 4 ≤ d`, `hslow : (d + 3) / 2 ≤ s`, `hshigh : s ≤ d -
1`, and `hn : 2 * (d + 1) ≤ n`, then there exists a family `family : Finset (Finset (Fin n))` such
that
`IsUniformMissingTraceFamily d s family ∧ family.card = Nat.choose (n - 1) d + Nat.choose (n - 2 *
(d + 1 - s) - 2) (2 * s - d - 2) ∧ Nat.choose (n - 1) d < family.card`.

## Sources

- Source `formal_target.lean`, lines 14–25
- Source `article/sections/02_proof.tex`, lines 75–79

## Statement dependencies

- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PatternCriterion::IsUniformMissingTraceFamily` → `IsUniformMissingTraceFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.IsUniformMissingTraceFamily`

## Proof outline

Instantiate the proof-accepted lower theorem
`Main.PerturbedStarCertificates::perturbedStar_isUniformMissingTraceFamily d s n hd hslow hshigh hn`
and obtain `B : PerturbedStarBlocks n (d + 1 - s)` together with `hB : IsUniformMissingTraceFamily d
s (perturbedStarFamily d B)`. Use `perturbedStarFamily d B` as the existential family and retain
`hB` unchanged.

Instantiate `Main.PerturbedStarCertificates::perturbedStarParameterBounds d s n hd hslow hshigh hn`.
Its r-form conclusions give `2 * (d + 1 - s) ≤ d`, `2 + 2 * (d + 1 - s) ≤ n`, and `d - 2 * (d + 1 -
s) = 2 * s - d - 2`. Supply the two bounds to the committed current-node theorem
`perturbedStarFamily_card B`; rewrite its second lower index with that equality to obtain the exact
immutable s-form cardinality conjunct.

Apply the committed current-node helper `perturbedStarExtra_choose_pos hd hslow hshigh hn` for
positivity of that same s-form second term. Substitute the proved cardinality equality and conclude
`Nat.choose (n - 1) d < (perturbedStarFamily d B).card` by elementary natural-number arithmetic.
This assembles only the ready certificate, count, and positivity interfaces; it does not re-prove
any certificate case or counting chain.

## Proof sources

- Source `formal_target.lean`, lines 14–25
- Source `article/sections/02_proof.tex`, lines 75–79

## Proof dependencies

- `Main.CountingAndMain::perturbedStarExtra_choose_pos` → `perturbedStarExtra_choose_pos` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarExtra_choose_pos`
- `Main.CountingAndMain::perturbedStarFamily_card` → `perturbedStarFamily_card` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarFamily_card`
- `Main.PerturbedStarCertificates::perturbedStarParameterBounds` → `perturbedStarParameterBounds`
  from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarParameterBounds`
- `Main.PerturbedStarCertificates::perturbedStar_isUniformMissingTraceFamily` →
  `perturbedStar_isUniformMissingTraceFamily` from `UniformMissingTraceFamily.Main.PerturbedStarCert
  ificates.Theorems.perturbedStar_isUniformMissingTraceFamily`
-/
theorem exists_uniformMissingTraceFamily_strictlyLargerThanStar (d s n : ℕ)
    (hd : 4 ≤ d) (hslow : (d + 3) / 2 ≤ s) (hshigh : s ≤ d - 1)
    (hn : 2 * (d + 1) ≤ n) :
    ∃ family : Finset (Finset (Fin n)),
      IsUniformMissingTraceFamily d s family ∧
        family.card =
          Nat.choose (n - 1) d +
          Nat.choose (n - 2 * (d + 1 - s) - 2) (2 * s - d - 2) ∧
          Nat.choose (n - 1) d < family.card := by
  rcases perturbedStar_isUniformMissingTraceFamily d s n hd hslow hshigh hn with ⟨B, hB⟩
  rcases perturbedStarParameterBounds d s n hd hslow hshigh hn with
    ⟨hr_two, hr_s, hrewrite, hrd, hrn⟩
  refine ⟨perturbedStarFamily d B, hB, ?_, ?_⟩
  · simpa [hrewrite] using perturbedStarFamily_card B hrd hrn
  · have hcard : (perturbedStarFamily d B).card =
        Nat.choose (n - 1) d +
          Nat.choose (n - 2 * (d + 1 - s) - 2) (2 * s - d - 2) := by
      simpa [hrewrite] using perturbedStarFamily_card B hrd hrn
    have hpos := perturbedStarExtra_choose_pos hd hslow hshigh hn
    rw [hcard]
    omega

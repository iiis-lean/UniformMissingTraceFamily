[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `perturbedStarPatterns_chooseSum`

The perturbed-star pattern completion weights equal the star count plus the final unpaired binomial term.

- Kind: `theorem`
- Node: `Main.CountingAndMain`
- Module: `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarPatterns_chooseSum`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For natural numbers n, r, and d, construction data `B : PerturbedStarBlocks n r`, and hypotheses `2 * r ≤ d` and `2 + 2 * r ≤ n`,
`∑ P ∈ perturbedStarPatterns d B, Nat.choose (perturbedStarFiller B).card (d + 1 - P.card) = Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r)`.
The anchored base star contributes the first term; each proper-`B.L` deletion at the first anchor cancels with its equal-cardinality insertion at the second anchor, leaving only the `Y = B.L` pattern as the second term.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Nat.Choose.Basic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarPatterns_chooseSum`

For natural numbers n, r, and d, construction data `B : PerturbedStarBlocks n r`, and hypotheses `2
* r ≤ d` and `2 + 2 * r ≤ n`,
`∑ P ∈ perturbedStarPatterns d B, Nat.choose (perturbedStarFiller B).card (d + 1 - P.card) =
Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r)`.
The anchored base star contributes the first term; each proper-`B.L` deletion at the first anchor
cancels with its equal-cardinality insertion at the second anchor, leaving only the `Y = B.L`
pattern as the second term.

## Sources

- Source `article/sections/02_proof.tex`, lines 41–51

## Statement dependencies

- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
-/
theorem perturbedStarPatterns_chooseSum {n r d : ℕ} (B : PerturbedStarBlocks n r)
    (hrd : 2 * r ≤ d) (hrn : 2 + 2 * r ≤ n) :
    ∑ P ∈ perturbedStarPatterns d B,
      Nat.choose (perturbedStarFiller B).card (d + 1 - P.card) =
        Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r) := by
  sorry
```

## Proof NL

Apply the committed theorem `perturbedStarPerturbation_chooseSum B hrd hrn`. Its left-hand side is exactly the target weighted sum, and it rewrites it to the explicit filtered anchored-base sum plus the unchanged unpaired term `Nat.choose (n - 2 * r - 2) (d - 2 * r)`. Rewrite that base sum with the committed theorem `perturbedStarBase_chooseSum B`, obtaining `Nat.choose (n - 1) d`.

The resulting equality is exactly the accepted conclusion, in the same r-form indices and equality direction. This is a two-provider composition; it introduces no assumptions and uses neither cleanup wrapper nor a local enumeration/cancellation argument.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Nat.Choose.Basic
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarBase_chooseSum
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarPerturbation_chooseSum
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarPatterns_chooseSum`

For natural numbers n, r, and d, construction data `B : PerturbedStarBlocks n r`, and hypotheses `2
* r ≤ d` and `2 + 2 * r ≤ n`,
`∑ P ∈ perturbedStarPatterns d B, Nat.choose (perturbedStarFiller B).card (d + 1 - P.card) =
Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r)`.
The anchored base star contributes the first term; each proper-`B.L` deletion at the first anchor
cancels with its equal-cardinality insertion at the second anchor, leaving only the `Y = B.L`
pattern as the second term.

## Sources

- Source `article/sections/02_proof.tex`, lines 41–51

## Statement dependencies

- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`

## Proof outline

Apply the committed theorem `perturbedStarPerturbation_chooseSum B hrd hrn`. Its left-hand side is
exactly the target weighted sum, and it rewrites it to the explicit filtered anchored-base sum plus
the unchanged unpaired term `Nat.choose (n - 2 * r - 2) (d - 2 * r)`. Rewrite that base sum with the
committed theorem `perturbedStarBase_chooseSum B`, obtaining `Nat.choose (n - 1) d`.

The resulting equality is exactly the accepted conclusion, in the same r-form indices and equality
direction. This is a two-provider composition; it introduces no assumptions and uses neither cleanup
wrapper nor a local enumeration/cancellation argument.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 41–51

## Proof dependencies

- `Main.CountingAndMain::perturbedStarBase_chooseSum` → `perturbedStarBase_chooseSum` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarBase_chooseSum`
- `Main.CountingAndMain::perturbedStarPerturbation_chooseSum` →
  `perturbedStarPerturbation_chooseSum` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarPerturbation_chooseSum`
-/
theorem perturbedStarPatterns_chooseSum {n r d : ℕ} (B : PerturbedStarBlocks n r)
    (hrd : 2 * r ≤ d) (hrn : 2 + 2 * r ≤ n) :
    ∑ P ∈ perturbedStarPatterns d B,
      Nat.choose (perturbedStarFiller B).card (d + 1 - P.card) =
        Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r) := by
  rw [perturbedStarPerturbation_chooseSum B hrd hrn, perturbedStarBase_chooseSum B]
```

## Statement dependencies

- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFiller`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`

## Proof dependencies

- `current repo:Main.CountingAndMain.perturbedStarBase_chooseSum`
- `current repo:Main.CountingAndMain.perturbedStarPerturbation_chooseSum`

## Sources

- `article/sections/02_proof.tex:41-51`

[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `perturbedStarFamily_card`

The explicit perturbed-star family has star cardinality plus the sole unpaired full-L binomial contribution.

- Kind: `theorem`
- Node: `Main.CountingAndMain`
- Module: `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarFamily_card`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For natural numbers `n`, `r`, and `d`, any `B : PerturbedStarBlocks n r`, and proofs `hrd : 2 * r ≤ d` and `hrn : 2 + 2 * r ≤ n`, the explicit family `perturbedStarFamily d B` has cardinality
`(perturbedStarFamily d B).card = Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r)`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Nat.Choose.Basic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarFamily_card`

For natural numbers `n`, `r`, and `d`, any `B : PerturbedStarBlocks n r`, and proofs `hrd : 2 * r ≤
d` and `hrn : 2 + 2 * r ≤ n`, the explicit family `perturbedStarFamily d B` has cardinality
`(perturbedStarFamily d B).card = Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r)`.

## Sources

- Source `article/sections/02_proof.tex`, lines 41–51

## Statement dependencies

- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarFamily` → `perturbedStarFamily` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFamily`
-/
theorem perturbedStarFamily_card {n r d : ℕ} (B : PerturbedStarBlocks n r)
    (hrd : 2 * r ≤ d) (hrn : 2 + 2 * r ≤ n) :
    (perturbedStarFamily d B).card =
      Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r) := by
  sorry
```

## Proof NL

Unfold the accepted definition `perturbedStarFamily d B` to `patternFamily d (perturbedStarPatterns d B) (perturbedStarFiller B)`. Apply the committed generic theorem `patternFamily_card_sum` to these patterns and filler, discharging its sole hypothesis pointwise with the committed theorem `perturbedStarPatterns_disjoint_filler B P hP`. This rewrites the family cardinality to exactly the weighted sum over `perturbedStarPatterns d B`.

Rewrite that weighted sum using the committed theorem `perturbedStarPatterns_chooseSum B hrd hrn`. The result is precisely `Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r)`, preserving the public object, both r-form hypotheses and indices, and the equality direction. No additional assumptions or local counting argument are introduced.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Nat.Choose.Basic
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.patternFamily_card_sum
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarPatterns_chooseSum
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarPatterns_disjoint_filler
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarFamily_card`

For natural numbers `n`, `r`, and `d`, any `B : PerturbedStarBlocks n r`, and proofs `hrd : 2 * r ≤
d` and `hrn : 2 + 2 * r ≤ n`, the explicit family `perturbedStarFamily d B` has cardinality
`(perturbedStarFamily d B).card = Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r)`.

## Sources

- Source `article/sections/02_proof.tex`, lines 41–51

## Statement dependencies

- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarFamily` → `perturbedStarFamily` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFamily`

## Proof outline

Unfold the accepted definition `perturbedStarFamily d B` to `patternFamily d (perturbedStarPatterns
d B) (perturbedStarFiller B)`. Apply the committed generic theorem `patternFamily_card_sum` to these
patterns and filler, discharging its sole hypothesis pointwise with the committed theorem
`perturbedStarPatterns_disjoint_filler B P hP`. This rewrites the family cardinality to exactly the
weighted sum over `perturbedStarPatterns d B`.

Rewrite that weighted sum using the committed theorem `perturbedStarPatterns_chooseSum B hrd hrn`.
The result is precisely `Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r)`, preserving
the public object, both r-form hypotheses and indices, and the equality direction. No additional
assumptions or local counting argument are introduced.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 41–51

## Proof dependencies

- `Main.CountingAndMain::patternFamily_card_sum` → `patternFamily_card_sum` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.patternFamily_card_sum`
- `Main.CountingAndMain::perturbedStarPatterns_chooseSum` → `perturbedStarPatterns_chooseSum` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarPatterns_chooseSum`
- `Main.CountingAndMain::perturbedStarPatterns_disjoint_filler` →
  `perturbedStarPatterns_disjoint_filler` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarPatterns_disjoint_filler`
- `Main.PerturbedStarCertificates::perturbedStarFamily` → `perturbedStarFamily` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFamily`
-/
theorem perturbedStarFamily_card {n r d : ℕ} (B : PerturbedStarBlocks n r)
    (hrd : 2 * r ≤ d) (hrn : 2 + 2 * r ≤ n) :
    (perturbedStarFamily d B).card =
      Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r) := by
  unfold perturbedStarFamily
  rw [patternFamily_card_sum (perturbedStarPatterns d B) (perturbedStarFiller B)
    (fun P hP => perturbedStarPatterns_disjoint_filler B P hP)]
  exact perturbedStarPatterns_chooseSum B hrd hrn
```

## Statement dependencies

- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFamily`

## Proof dependencies

- `current repo:Main.CountingAndMain.patternFamily_card_sum`
- `current repo:Main.CountingAndMain.perturbedStarPatterns_chooseSum`
- `current repo:Main.CountingAndMain.perturbedStarPatterns_disjoint_filler`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFamily`

## Sources

- `article/sections/02_proof.tex:41-51`

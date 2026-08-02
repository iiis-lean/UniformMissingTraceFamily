[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `perturbedStarFamily`

The explicit uniform family generated from the perturbed-star core patterns and complementary filler.

- Kind: `definition`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFamily`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final statement projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarFamily`

For natural numbers d, n, and r and construction data `B : PerturbedStarBlocks n r`,
`perturbedStarFamily d B` is the finite family of finite subsets of `Fin n` defined exactly by

`patternFamily d (perturbedStarPatterns d B) (perturbedStarFiller B)`.

Equivalently, it is the generic exact-cardinality completion of the accepted perturbed-star core
patterns using the complementary filler. This definition adds no parameter hypotheses: bounds on d,
s, and n are used only later to construct suitable data and certify the family, not to change its
members.

## Sources

- Source `article/sections/02_proof.tex`, lines 30–39

## Statement dependencies

- `Main.PatternCriterion::patternFamily` → `patternFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
-/
def perturbedStarFamily (d : ℕ) {n r : ℕ}
    (B : PerturbedStarBlocks n r) : Finset (Finset (Fin n)) :=
  patternFamily d (perturbedStarPatterns d B) (perturbedStarFiller B)
```

## Statement dependencies

- `current repo:Main.PatternCriterion.patternFamily`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFiller`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`

## Sources

- `article/sections/02_proof.tex:30-39`

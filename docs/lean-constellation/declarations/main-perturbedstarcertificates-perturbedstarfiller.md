[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `perturbedStarFiller`

The filler region complementary to the fixed perturbed-star core.

- Kind: `definition`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final statement projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarFiller`

For natural numbers n and r and construction data `B : PerturbedStarBlocks n r`,
`perturbedStarFiller B` is the finite subset of `Fin n` defined by

`(Finset.univ : Finset (Fin n)) \ perturbedStarCore B`.

Thus it is exactly the complement of the fixed core within `Fin n`; no additional elements,
hypotheses, or semantic conditions are introduced.

## Sources

- Source `article/sections/02_proof.tex`, line 34

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
-/
def perturbedStarFiller {n r : ℕ} (B : PerturbedStarBlocks n r) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)) \ perturbedStarCore B
```

## Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`

## Sources

- `article/sections/02_proof.tex:34-34`

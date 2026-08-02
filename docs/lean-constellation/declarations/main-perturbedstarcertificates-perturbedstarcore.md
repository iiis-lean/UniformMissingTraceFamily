[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `perturbedStarCore`

The fixed core formed by the two distinguished anchors and the disjoint T and L blocks.

- Kind: `definition`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final statement projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarCore`

For natural numbers n and r and construction data `B : PerturbedStarBlocks n r`, `perturbedStarCore
B` is the finite subset of `Fin n` defined by

`{B.a, B.b} ∪ B.T ∪ B.L`.

Equivalently, it is the union of the two distinguished anchors and the two blocks recorded by `B`;
the displayed union association is part of the definition and no additional elements or assumptions
are introduced.

## Sources

- Source `article/sections/02_proof.tex`, line 34

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
-/
def perturbedStarCore {n r : ℕ} (B : PerturbedStarBlocks n r) : Finset (Fin n) :=
  {B.a, B.b} ∪ B.T ∪ B.L
```

## Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

## Sources

- `article/sections/02_proof.tex:34-34`

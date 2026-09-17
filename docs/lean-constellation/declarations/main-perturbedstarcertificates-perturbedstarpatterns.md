[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `perturbedStarPatterns`

The allowed core patterns obtained by perturbing the anchored one-star along the T and L blocks.

- Kind: `definition`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final statement projection

## Statement NL

For natural numbers d, n, and r and construction data `B : PerturbedStarBlocks n r`, `perturbedStarPatterns d B` is a finite family of finite subsets of `Fin n`, defined from the following three components.

1. Its base anchored-star component consists of every finite set `P` with `P ⊆ perturbedStarCore B`, `B.a ∈ P`, and `P.card ≤ d + 1`.
2. From that base component, delete exactly the sets `{B.a} ∪ B.T ∪ Y` for which `Y` is a proper subset of `B.L`.
3. Insert exactly the sets `{B.b} ∪ B.T ∪ Y` for every subset `Y ⊆ B.L`.

The result is the base component after the stated deletions, union the stated inserted component. In particular, the insertion includes `Y = B.L` as the final added pattern, while the deletion excludes that non-proper choice. No filler elements or further hypotheses occur in this definition.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarPatterns`

For natural numbers d, n, and r and construction data `B : PerturbedStarBlocks n r`,
`perturbedStarPatterns d B` is a finite family of finite subsets of `Fin n`, defined from the
following three components.

1. Its base anchored-star component consists of every finite set `P` with `P ⊆ perturbedStarCore B`,
`B.a ∈ P`, and `P.card ≤ d + 1`.
2. From that base component, delete exactly the sets `{B.a} ∪ B.T ∪ Y` for which `Y` is a proper
subset of `B.L`.
3. Insert exactly the sets `{B.b} ∪ B.T ∪ Y` for every subset `Y ⊆ B.L`.

The result is the base component after the stated deletions, union the stated inserted component. In
particular, the insertion includes `Y = B.L` as the final added pattern, while the deletion excludes
that non-proper choice. No filler elements or further hypotheses occur in this definition.

## Sources

- Source `article/sections/02_proof.tex`, lines 35–39

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
-/
def perturbedStarPatterns (d : ℕ) {n r : ℕ}
    (B : PerturbedStarBlocks n r) : Finset (Finset (Fin n)) :=
  let base := (perturbedStarCore B).powerset.filter fun P =>
    B.a ∈ P ∧ P.card ≤ d + 1
  let deleted :=
    (B.L.powerset.filter fun Y => Y ⊆ B.L ∧ Y ≠ B.L).image fun Y =>
      {B.a} ∪ B.T ∪ Y
  let inserted := B.L.powerset.image fun Y =>
    {B.b} ∪ B.T ∪ Y
  (base \ deleted) ∪ inserted
```

## Proof NL

Not recorded.

## Proof Formal

Not recorded.

## Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`

## Sources

- `article/sections/02_proof.tex:35-39`

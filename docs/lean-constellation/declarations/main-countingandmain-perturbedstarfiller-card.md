[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `perturbedStarFiller_card`

The complementary filler has cardinality n minus the two-anchor, two-block core.

- Kind: `theorem`
- Node: `Main.CountingAndMain`
- Module: `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarFiller_card`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For natural numbers n and r and `B : PerturbedStarBlocks n r`, the complementary filler has cardinality
`(perturbedStarFiller B).card = n - (2 + 2 * r)`.
This uses only that the filler is the complement of the two-anchor, two-r-block core and introduces no additional ambient-size hypothesis.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarFiller_card`

For natural numbers n and r and `B : PerturbedStarBlocks n r`, the complementary filler has
cardinality
`(perturbedStarFiller B).card = n - (2 + 2 * r)`.
This uses only that the filler is the complement of the two-anchor, two-r-block core and introduces
no additional ambient-size hypothesis.

## Sources

- Source `article/sections/02_proof.tex`, lines 30–34
- Source `article/sections/02_proof.tex`, lines 48–50

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`
-/
theorem perturbedStarFiller_card {n r : ℕ} (B : PerturbedStarBlocks n r) :
    (perturbedStarFiller B).card = n - (2 + 2 * r) := by
  sorry
```

## Proof NL

Unfold the accepted definition `perturbedStarFiller B` as `(Finset.univ : Finset (Fin n)) \ perturbedStarCore B`.  Apply `Finset.card_sdiff` with ambient finset `Finset.univ` and deleted finset `perturbedStarCore B`; its intersection term simplifies to `perturbedStarCore B` because every `Fin n` element lies in `univ`.

Rewrite the universe cardinality using `Finset.card_univ` and `Fintype.card_fin`, then substitute the committed theorem `perturbedStarCore_card B`.  The remaining expression is exactly `n - (2 + 2 * r)`.  Simplifying `core ∩ univ = core` and the final natural-number arithmetic are lightweight local Lean steps; no ambient hypothesis or helper declaration is needed.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarCore_card
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarFiller_card`

For natural numbers n and r and `B : PerturbedStarBlocks n r`, the complementary filler has
cardinality
`(perturbedStarFiller B).card = n - (2 + 2 * r)`.
This uses only that the filler is the complement of the two-anchor, two-r-block core and introduces
no additional ambient-size hypothesis.

## Sources

- Source `article/sections/02_proof.tex`, lines 30–34
- Source `article/sections/02_proof.tex`, lines 48–50

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`

## Proof outline

Unfold the accepted definition `perturbedStarFiller B` as `(Finset.univ : Finset (Fin n)) \
perturbedStarCore B`.  Apply `Finset.card_sdiff` with ambient finset `Finset.univ` and deleted
finset `perturbedStarCore B`; its intersection term simplifies to `perturbedStarCore B` because
every `Fin n` element lies in `univ`.

Rewrite the universe cardinality using `Finset.card_univ` and `Fintype.card_fin`, then substitute
the committed theorem `perturbedStarCore_card B`.  The remaining expression is exactly `n - (2 + 2 *
r)`.  Simplifying `core ∩ univ = core` and the final natural-number arithmetic are lightweight local
Lean steps; no ambient hypothesis or helper declaration is needed.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 30–34
- Source `article/sections/02_proof.tex`, lines 48–50

## Proof dependencies

- `Finset.card_sdiff` from `Mathlib.Data.Finset.Card`
- `Finset.card_univ` from `Mathlib.Data.Fintype.Card`
- `Fintype.card_fin` from `Mathlib.Data.Fintype.Card`
- `Main.CountingAndMain::perturbedStarCore_card` → `perturbedStarCore_card` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarCore_card`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`
-/
theorem perturbedStarFiller_card {n r : ℕ} (B : PerturbedStarBlocks n r) :
    (perturbedStarFiller B).card = n - (2 + 2 * r) := by
  unfold perturbedStarFiller
  rw [Finset.card_sdiff]
  simp [perturbedStarCore_card]
```

## Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFiller`

## Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_sdiff`
- `Mathlib:Mathlib.Data.Fintype.Card.Finset.card_univ`
- `Mathlib:Mathlib.Data.Fintype.Card.Fintype.card_fin`
- `current repo:Main.CountingAndMain.perturbedStarCore_card`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFiller`

## Sources

- `article/sections/02_proof.tex:30-34`
- `article/sections/02_proof.tex:48-50`

[← Public API index](../PUBLIC_API.md)

# `mem_patternFamily`

Membership in patternFamily is equivalent to admitting an allowed pattern and an exact-cardinality filler whose union is the member.

- Kind: `theorem`
- Node: `Main.PatternCriterion`
- Module: `UniformMissingTraceFamily.Main.PatternCriterion.Theorems.mem_patternFamily`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PatternCriterion.Prelude
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `mem_patternFamily`

For natural numbers `n` and `d`, an allowed pattern family `patterns : Finset (Finset (Fin n))`, a
filler region `U : Finset (Fin n)`, and `F : Finset (Fin n)`, membership in the pattern-plus-filler
family is characterized by
```
F ∈ patternFamily d patterns U ↔
  ∃ P : Finset (Fin n), P ∈ patterns ∧
    ∃ A : Finset (Fin n), A ⊆ U ∧ A.card = d + 1 - P.card ∧ F = P ∪ A.
```
Thus a member is exactly the union of an allowed pattern and a filler subset of `U` whose
cardinality supplies the remaining positions to reach size `d + 1`.

## Sources

- Source `article/sections/02_proof.tex`, lines 3–7

## Statement dependencies

- `Main.PatternCriterion::patternFamily` → `patternFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily`

## Proof outline

Unfold `patternFamily d patterns U`. Apply `Finset.mem_biUnion` to membership in the outer biunion,
obtaining an allowed pattern `P ∈ patterns` and membership of `F` in the corresponding image. Apply
`Finset.mem_image` to that image membership, obtaining a filler `A ∈ U.powersetCard (d + 1 -
P.card)` and an equality `P ∪ A = F`. Take the symmetry of this image equality to obtain the
accepted witness conclusion `F = P ∪ A`. Finally, apply `Finset.mem_powersetCard` to split the
filler membership into `A ⊆ U` and `A.card = d + 1 - P.card`. This proves the forward implication.

Conversely, given `P ∈ patterns`, `A ⊆ U`, `A.card = d + 1 - P.card`, and `F = P ∪ A`, use
`Finset.mem_powersetCard` in the reverse direction to place `A` in `U.powersetCard (d + 1 -
P.card)`. To reintroduce `A` through `Finset.mem_image`, use the supplied equality in reverse,
namely `P ∪ A = F`. Then reintroduce `P` through `Finset.mem_biUnion` to obtain `F ∈ patternFamily d
patterns U`. The proof is generic in `Fin n` and uses no disjointness or perturbed-star-specific
data.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 3–7

## Proof dependencies

- `Finset.mem_image` from `Mathlib.Data.Finset.Image`
- `Finset.mem_powersetCard` from `Mathlib.Data.Finset.Powerset`
- `Finset.mem_biUnion` from `Mathlib.Data.Finset.Union`
- `Main.PatternCriterion::patternFamily` → `patternFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily`
-/
theorem mem_patternFamily {n d : ℕ} (patterns : Finset (Finset (Fin n)))
    (U F : Finset (Fin n)) :
    F ∈ patternFamily d patterns U ↔
      ∃ P : Finset (Fin n), P ∈ patterns ∧
        ∃ A : Finset (Fin n), A ⊆ U ∧ A.card = d + 1 - P.card ∧ F = P ∪ A := by
  simp [patternFamily, and_assoc, eq_comm]
```

## Statement dependencies

- `current repo:Main.PatternCriterion.patternFamily`

## Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Image.Finset.mem_image`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.mem_powersetCard`
- `Mathlib:Mathlib.Data.Finset.Union.Finset.mem_biUnion`
- `current repo:Main.PatternCriterion.patternFamily`

## Sources

- `article/sections/02_proof.tex:3-7`

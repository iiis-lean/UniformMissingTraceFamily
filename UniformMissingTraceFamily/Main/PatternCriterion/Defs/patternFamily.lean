-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PatternCriterion.Prelude
import Mathlib.Data.Finset.Powerset
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `patternFamily`

For a natural number `n`, a target size parameter `d`, an allowed pattern family `patterns : Finset
(Finset (Fin n))`, and a filler region `U : Finset (Fin n)`, `patternFamily d patterns U` is the
finite family of all unions `P ∪ A` where `P ∈ patterns` and `A` is a subset of `U` of cardinality
`d + 1 - P.card`; equivalently, `A ∈ U.powersetCard (d + 1 - P.card)`.

This construction records only the allowed core-pattern component and the exact-size filler
component. It does not itself impose disjointness or specialize the patterns to the later
perturbed-star construction.

## Sources

- Source `article/sections/02_proof.tex`, lines 3–7

## Statement dependencies

- `Finset.powersetCard` from `Mathlib.Data.Finset.Powerset`
-/
def patternFamily {n : ℕ} (d : ℕ) (patterns : Finset (Finset (Fin n)))
    (U : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  patterns.biUnion fun P => (U.powersetCard (d + 1 - P.card)).image fun A => P ∪ A

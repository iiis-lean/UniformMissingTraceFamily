-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Prelude
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Powerset
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedPattern_properDomain_eq_erase`

For every `B : PerturbedStarBlocks n r`, the finite collection of proper subsets of `B.L` is exactly
its powerset with the full block erased:

`{Y ∈ B.L.powerset | Y ≠ B.L} = B.L.powerset.erase B.L`.

Equivalently, this is the domain of all `Y ⊂ B.L`, leaving `Y = B.L` as the sole excluded index. No
additional construction assumptions beyond `B` are imposed.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Finset.erase` from `Mathlib.Data.Finset.Erase`
- `Finset.filter` from `Mathlib.Data.Finset.Filter`
- `Finset.powerset` from `Mathlib.Data.Finset.Powerset`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`

## Proof outline

Prove equality of the two Finsets by `Finset.ext`, fixing `Y`.  Normalize the left side with
`Finset.mem_filter` and `Finset.mem_powerset`: membership is exactly `Y ⊆ B.L ∧ Y ≠ B.L`.  Normalize
the right side with `Finset.mem_erase` and `Finset.mem_powerset`: membership is exactly `Y ≠ B.L ∧ Y
⊆ B.L`.  The two conditions are equivalent by swapping the conjunction components.

Thus the proof identifies precisely the proper subsets used by the source matching with
`B.L.powerset.erase B.L`, leaving `B.L` as the unique excluded index.  It uses no properties of `B`
beyond the displayed block `B.L`, no `hrd` or `hrn` assumptions, and no helper declaration.

## Proof sources

- Source `article/sections/02_proof.tex`, line 49

## Proof dependencies

- `Finset.ext` from `Mathlib.Data.Finset.Defs`
- `Finset.mem_erase` from `Mathlib.Data.Finset.Erase`
- `Finset.mem_filter` from `Mathlib.Data.Finset.Filter`
- `Finset.mem_powerset` from `Mathlib.Data.Finset.Powerset`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
-/
theorem perturbedPattern_properDomain_eq_erase {n r : ℕ} (B : PerturbedStarBlocks n r) :
    B.L.powerset.filter (fun Y => Y ≠ B.L) = B.L.powerset.erase B.L := by
  ext Y
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase]
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

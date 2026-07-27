-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Prelude
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Operations
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternB_inter_L
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedPatternB_injOn`

For every `B : PerturbedStarBlocks n r`, the map on `B.L.powerset` given by

`Y ↦ {B.b} ∪ B.T ∪ Y`

is injective. Equivalently, for all `Y₁, Y₂ ∈ B.L.powerset`, if `{B.b} ∪ B.T ∪ Y₁ = {B.b} ∪ B.T ∪
Y₂`, then `Y₁ = Y₂`.

No additional hypotheses, including `hrd` or `hrn`, are assumed.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Finset.powerset` from `Mathlib.Data.Finset.Powerset`
- `Set.InjOn` from `Mathlib.Data.Set.Operations`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`

## Proof outline

Unfold the restricted injectivity goal by introducing `Y₁`, its membership `hY₁ : Y₁ ∈
↑B.L.powerset`, `Y₂`, `hY₂`, and an equality of their b-anchored images. Change each coerced-set
membership to Finset membership in `B.L.powerset`, then use the verified theorem
`Finset.mem_powerset` to obtain `hY₁L : Y₁ ⊆ B.L` and `hY₂L : Y₂ ⊆ B.L`.

Apply the accepted project theorem `perturbedPatternB_inter_L B Y₁ hY₁L` and its counterpart for
`Y₂`. In a `calc` chain, rewrite `Y₁` as `(({B.b} ∪ B.T ∪ Y₁) ∩ B.L)`, use `congrArg (fun Z => Z ∩
B.L)` on the assumed equality of b-images, and rewrite the resulting right-hand intersection to `Y₂`
using `perturbedPatternB_inter_L B Y₂ hY₂L`. Coercion normalization and `congrArg` are lightweight
local Lean steps. This preserves exactly the required b-map, uses no `hrd` or `hrn` assumptions, and
needs no helper declaration.

## Proof sources

- Source `article/sections/02_proof.tex`, line 49

## Proof dependencies

- `Finset.mem_powerset` from `Mathlib.Data.Finset.Powerset`
- `Main.PerturbedPatternCancellation::perturbedPatternB_inter_L` → `perturbedPatternB_inter_L` from
  `UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternB_inter_L`
-/
theorem perturbedPatternB_injOn {n r : ℕ} (B : PerturbedStarBlocks n r) :
    Set.InjOn (fun Y : Finset (Fin n) ↦ {B.b} ∪ B.T ∪ Y) ↑B.L.powerset := by
  intro Y₁ hY₁ Y₂ hY₂ hEq
  have hY₁L : Y₁ ⊆ B.L := Finset.mem_powerset.mp hY₁
  have hY₂L : Y₂ ⊆ B.L := Finset.mem_powerset.mp hY₂
  calc
    Y₁ = (({B.b} ∪ B.T ∪ Y₁) ∩ B.L) := (perturbedPatternB_inter_L B Y₁ hY₁L).symm
    _ = (({B.b} ∪ B.T ∪ Y₂) ∩ B.L) := congrArg (fun Z => Z ∩ B.L) hEq
    _ = Y₂ := perturbedPatternB_inter_L B Y₂ hY₂L

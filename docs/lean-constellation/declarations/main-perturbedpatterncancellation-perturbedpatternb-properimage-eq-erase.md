[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `perturbedPatternB_properImage_eq_erase`

The proper b-pattern image is the full b-pattern image with its full-L pattern erased.

- Kind: `theorem`
- Node: `Main.PerturbedPatternCancellation`
- Module: `UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternB_properImage_eq_erase`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For every `B : PerturbedStarBlocks n r`, let `f(Y) = {B.b} ∪ B.T ∪ Y`. The image of the exact proper domain under `f` is the full `B.L.powerset` image with precisely the full-`L` pattern erased:

`({Y ∈ B.L.powerset | Y ≠ B.L}.image f) = (B.L.powerset.image f).erase ({B.b} ∪ B.T ∪ B.L)`.

No additional hypotheses, including `hrd` or `hrn`, are assumed.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Prelude
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedPatternB_properImage_eq_erase`

For every `B : PerturbedStarBlocks n r`, let `f(Y) = {B.b} ∪ B.T ∪ Y`. The image of the exact proper
domain under `f` is the full `B.L.powerset` image with precisely the full-`L` pattern erased:

`({Y ∈ B.L.powerset | Y ≠ B.L}.image f) = (B.L.powerset.image f).erase ({B.b} ∪ B.T ∪ B.L)`.

No additional hypotheses, including `hrd` or `hrn`, are assumed.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Finset.erase` from `Mathlib.Data.Finset.Erase`
- `Finset.filter` from `Mathlib.Data.Finset.Filter`
- `Finset.image` from `Mathlib.Data.Finset.Image`
- `Finset.powerset` from `Mathlib.Data.Finset.Powerset`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
-/
theorem perturbedPatternB_properImage_eq_erase {n r : ℕ}
    (B : PerturbedStarBlocks n r) :
    (B.L.powerset.filter (fun Y => Y ≠ B.L)).image
        (fun Y : Finset (Fin n) ↦ {B.b} ∪ B.T ∪ Y) =
      (B.L.powerset.image
          (fun Y : Finset (Fin n) ↦ {B.b} ∪ B.T ∪ Y)).erase
        ({B.b} ∪ B.T ∪ B.L) := by
  sorry
```

## Proof NL

Let `f(Y) = {B.b} ∪ B.T ∪ Y`.  First rewrite the filtered proper domain using the accepted theorem `perturbedPattern_properDomain_eq_erase B`, so the left side becomes `(B.L.powerset.erase B.L).image f`.  Prove the resulting equality by `Finset.ext`, fixing an output pattern `Z`, and normalize image/erase membership with `Finset.mem_image` and `Finset.mem_erase`.

For the forward direction, obtain a witness `Y ∈ B.L.powerset.erase B.L` with `f Y = Z`.  It gives `Y ∈ B.L.powerset`, hence `Y ⊆ B.L` by `Finset.mem_powerset`; also `B.L ∈ B.L.powerset`.  The witness supplies membership in the full image.  If `Z = f B.L`, then `perturbedPatternB_injOn B`, applied to `Y` and `B.L` in the powerset, gives `Y = B.L`, contradicting the erase membership.

For the reverse direction, unpack membership in the erased full image to a witness `Y ∈ B.L.powerset` with `f Y = Z` and `Z ≠ f B.L`.  If `Y = B.L`, its image equality contradicts the erased-image inequality; thus `Y ≠ B.L`.  Repack this with `Finset.mem_erase` as `Y ∈ B.L.powerset.erase B.L`, then with `Finset.mem_image` to finish.  This exact b-map argument uses no `hrd` or `hrn` assumptions and no helper declaration.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Prelude
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternB_injOn
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPattern_properDomain_eq_erase
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedPatternB_properImage_eq_erase`

For every `B : PerturbedStarBlocks n r`, let `f(Y) = {B.b} ∪ B.T ∪ Y`. The image of the exact proper
domain under `f` is the full `B.L.powerset` image with precisely the full-`L` pattern erased:

`({Y ∈ B.L.powerset | Y ≠ B.L}.image f) = (B.L.powerset.image f).erase ({B.b} ∪ B.T ∪ B.L)`.

No additional hypotheses, including `hrd` or `hrn`, are assumed.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Finset.erase` from `Mathlib.Data.Finset.Erase`
- `Finset.filter` from `Mathlib.Data.Finset.Filter`
- `Finset.image` from `Mathlib.Data.Finset.Image`
- `Finset.powerset` from `Mathlib.Data.Finset.Powerset`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`

## Proof outline

Let `f(Y) = {B.b} ∪ B.T ∪ Y`.  First rewrite the filtered proper domain using the accepted theorem
`perturbedPattern_properDomain_eq_erase B`, so the left side becomes `(B.L.powerset.erase B.L).image
f`.  Prove the resulting equality by `Finset.ext`, fixing an output pattern `Z`, and normalize
image/erase membership with `Finset.mem_image` and `Finset.mem_erase`.

For the forward direction, obtain a witness `Y ∈ B.L.powerset.erase B.L` with `f Y = Z`.  It gives
`Y ∈ B.L.powerset`, hence `Y ⊆ B.L` by `Finset.mem_powerset`; also `B.L ∈ B.L.powerset`.  The
witness supplies membership in the full image.  If `Z = f B.L`, then `perturbedPatternB_injOn B`,
applied to `Y` and `B.L` in the powerset, gives `Y = B.L`, contradicting the erase membership.

For the reverse direction, unpack membership in the erased full image to a witness `Y ∈
B.L.powerset` with `f Y = Z` and `Z ≠ f B.L`.  If `Y = B.L`, its image equality contradicts the
erased-image inequality; thus `Y ≠ B.L`.  Repack this with `Finset.mem_erase` as `Y ∈
B.L.powerset.erase B.L`, then with `Finset.mem_image` to finish.  This exact b-map argument uses no
`hrd` or `hrn` assumptions and no helper declaration.

## Proof sources

- Source `article/sections/02_proof.tex`, line 49

## Proof dependencies

- `Finset.ext` from `Mathlib.Data.Finset.Defs`
- `Finset.mem_erase` from `Mathlib.Data.Finset.Erase`
- `Finset.mem_image` from `Mathlib.Data.Finset.Image`
- `Finset.mem_powerset` from `Mathlib.Data.Finset.Powerset`
- `Main.PerturbedPatternCancellation::perturbedPatternB_injOn` → `perturbedPatternB_injOn` from
  `UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternB_injOn`
- `Main.PerturbedPatternCancellation::perturbedPattern_properDomain_eq_erase` →
  `perturbedPattern_properDomain_eq_erase` from `UniformMissingTraceFamily.Main.PerturbedPatternCanc
  ellation.Theorems.perturbedPattern_properDomain_eq_erase`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
-/
theorem perturbedPatternB_properImage_eq_erase {n r : ℕ}
    (B : PerturbedStarBlocks n r) :
    (B.L.powerset.filter (fun Y => Y ≠ B.L)).image
        (fun Y : Finset (Fin n) ↦ {B.b} ∪ B.T ∪ Y) =
      (B.L.powerset.image
          (fun Y : Finset (Fin n) ↦ {B.b} ∪ B.T ∪ Y)).erase
        ({B.b} ∪ B.T ∪ B.L) := by
  rw [perturbedPattern_properDomain_eq_erase B]
  ext Z
  constructor
  · intro hZ
    rcases Finset.mem_image.mp hZ with ⟨Y, hY, hYZ⟩
    have hY' : Y ≠ B.L ∧ Y ∈ B.L.powerset := Finset.mem_erase.mp hY
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image.mpr ⟨Y, hY'.2, hYZ⟩⟩
    intro hZL
    have hL : B.L ∈ B.L.powerset := Finset.mem_powerset.mpr (fun _ hx => hx)
    have hYL : Y = B.L := perturbedPatternB_injOn B hY'.2 hL (hYZ.trans hZL)
    exact hY'.1 hYL
  · intro hZ
    rcases Finset.mem_erase.mp hZ with ⟨hZL, hZ⟩
    rcases Finset.mem_image.mp hZ with ⟨Y, hY, hYZ⟩
    refine Finset.mem_image.mpr ⟨Y, ?_, hYZ⟩
    refine Finset.mem_erase.mpr ⟨?_, hY⟩
    intro hYL
    apply hZL
    subst Y
    exact hYZ.symm
```

## Statement dependencies

- `Mathlib:Mathlib.Data.Finset.Erase.Finset.erase`
- `Mathlib:Mathlib.Data.Finset.Filter.Finset.filter`
- `Mathlib:Mathlib.Data.Finset.Image.Finset.image`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.powerset`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

## Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Defs.Finset.ext`
- `Mathlib:Mathlib.Data.Finset.Erase.Finset.mem_erase`
- `Mathlib:Mathlib.Data.Finset.Image.Finset.mem_image`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.mem_powerset`
- `current repo:Main.PerturbedPatternCancellation.perturbedPatternB_injOn`
- `current repo:Main.PerturbedPatternCancellation.perturbedPattern_properDomain_eq_erase`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

## Sources

- `article/sections/02_proof.tex:49-49`

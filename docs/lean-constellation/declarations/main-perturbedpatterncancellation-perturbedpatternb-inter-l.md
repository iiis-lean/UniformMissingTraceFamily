[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `perturbedPatternB_inter_L`

Intersecting a b-anchored perturbed pattern with L recovers its L-subset.

- Kind: `theorem`
- Node: `Main.PerturbedPatternCancellation`
- Module: `UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternB_inter_L`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For every `B : PerturbedStarBlocks n r` and every finite set `Y` with `Y ⊆ B.L`, intersecting the exact added-pattern constructor with `B.L` recovers `Y`:

`(({B.b} ∪ B.T ∪ Y) ∩ B.L) = Y`.

No additional hypotheses, including `hrd` or `hrn`, are assumed.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedPatternB_inter_L`

For every `B : PerturbedStarBlocks n r` and every finite set `Y` with `Y ⊆ B.L`, intersecting the
exact added-pattern constructor with `B.L` recovers `Y`:

`(({B.b} ∪ B.T ∪ Y) ∩ B.L) = Y`.

No additional hypotheses, including `hrd` or `hrn`, are assumed.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
-/
theorem perturbedPatternB_inter_L {n r : ℕ} (B : PerturbedStarBlocks n r)
    (Y : Finset (Fin n)) (hY : Y ⊆ B.L) :
    (({B.b} ∪ B.T ∪ Y) ∩ B.L) = Y := by
  sorry
```

## Proof NL

Fix `B : PerturbedStarBlocks n r`, `Y : Finset (Fin n)`, and `hY : Y ⊆ B.L`.  Prove the equality by `Finset.ext`, fixing an element `x`, and normalize membership in the intersection, both unions, and the singleton with the verified equivalences `Finset.mem_inter`, `Finset.mem_union`, and `Finset.mem_singleton`.

For the forward implication, membership in `(({B.b} ∪ B.T ∪ Y) ∩ B.L)` gives membership in `B.L` and one of the anchor, `B.T`, or `Y` branches.  In the anchor branch, substitute the singleton equality and contradict `B.b_not_mem_L`.  In the `B.T` branch, apply `Finset.disjoint_left.mp B.T_disjoint_L` to the simultaneous memberships in `B.T` and `B.L`.  The remaining branch is exactly membership in `Y`.  Conversely, a member of `Y` belongs to the third branch of the union and belongs to `B.L` by `hY`.  This uses no `hrd` or `hrn` assumptions and requires no helper declaration.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Prelude
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedPatternB_inter_L`

For every `B : PerturbedStarBlocks n r` and every finite set `Y` with `Y ⊆ B.L`, intersecting the
exact added-pattern constructor with `B.L` recovers `Y`:

`(({B.b} ∪ B.T ∪ Y) ∩ B.L) = Y`.

No additional hypotheses, including `hrd` or `hrn`, are assumed.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`

## Proof outline

Fix `B : PerturbedStarBlocks n r`, `Y : Finset (Fin n)`, and `hY : Y ⊆ B.L`.  Prove the equality by
`Finset.ext`, fixing an element `x`, and normalize membership in the intersection, both unions, and
the singleton with the verified equivalences `Finset.mem_inter`, `Finset.mem_union`, and
`Finset.mem_singleton`.

For the forward implication, membership in `(({B.b} ∪ B.T ∪ Y) ∩ B.L)` gives membership in `B.L` and
one of the anchor, `B.T`, or `Y` branches.  In the anchor branch, substitute the singleton equality
and contradict `B.b_not_mem_L`.  In the `B.T` branch, apply `Finset.disjoint_left.mp B.T_disjoint_L`
to the simultaneous memberships in `B.T` and `B.L`.  The remaining branch is exactly membership in
`Y`.  Conversely, a member of `Y` belongs to the third branch of the union and belongs to `B.L` by
`hY`.  This uses no `hrd` or `hrn` assumptions and requires no helper declaration.

## Proof sources

- Source `article/sections/02_proof.tex`, line 49

## Proof dependencies

- `Finset.ext` from `Mathlib.Data.Finset.Defs`
- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Finset.mem_singleton` from `Mathlib.Data.Finset.Insert`
- `Finset.mem_inter` from `Mathlib.Data.Finset.Lattice.Basic`
- `Finset.mem_union` from `Mathlib.Data.Finset.Lattice.Basic`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
-/
theorem perturbedPatternB_inter_L {n r : ℕ} (B : PerturbedStarBlocks n r)
    (Y : Finset (Fin n)) (hY : Y ⊆ B.L) :
    (({B.b} ∪ B.T ∪ Y) ∩ B.L) = Y := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨(⟨hxb | hxT⟩ | hxY), hxL⟩
    · subst x
      exact (B.b_not_mem_L hxL).elim
    · exact (Finset.disjoint_left.mp B.T_disjoint_L hxT hxL).elim
    · exact hxY
  · intro hxY
    exact ⟨Or.inr hxY, hY hxY⟩
```

## Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

## Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Defs.Finset.ext`
- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `Mathlib:Mathlib.Data.Finset.Insert.Finset.mem_singleton`
- `Mathlib:Mathlib.Data.Finset.Lattice.Basic.Finset.mem_inter`
- `Mathlib:Mathlib.Data.Finset.Lattice.Basic.Finset.mem_union`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

## Sources

- `article/sections/02_proof.tex:49-49`

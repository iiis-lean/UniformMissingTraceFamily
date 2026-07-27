-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarCore_card`

For natural numbers n and r and `B : PerturbedStarBlocks n r`, the fixed core has cardinality `card
(perturbedStarCore B) = 2 + 2 * r`.  Thus its two distinct anchors together with its two disjoint
r-element blocks contribute exactly the stated number of elements.

## Sources

- Source `article/sections/02_proof.tex`, lines 30–34

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`

## Proof outline

Unfold `perturbedStarCore B` as `({B.a, B.b} ∪ B.T) ∪ B.L`.  From `B.a_not_mem_T`, `B.b_not_mem_T`,
`B.a_not_mem_L`, and `B.b_not_mem_L`, build the two disjointness facts `Disjoint {B.a,B.b} B.T` and
`Disjoint ({B.a,B.b} ∪ B.T) B.L`; the latter combines anchor/block avoidance with `B.T_disjoint_L`.
These are direct elementwise uses of `Finset.disjoint_left`.

Use `Finset.card_union_of_disjoint` twice.  `Finset.card_pair B.a_ne_b` gives the anchor cardinality
`2`; substitute `B.card_T` and `B.card_L`, then finish the natural-number normalization to obtain `2
+ 2 * r`.  This route consumes only the accepted `PerturbedStarBlocks` fields and the accepted
definition `perturbedStarCore`, as required.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 30–34

## Proof dependencies

- `Finset.card_pair` from `Mathlib.Data.Finset.Card`
- `Finset.card_union_of_disjoint` from `Mathlib.Data.Finset.Card`
- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
-/
theorem perturbedStarCore_card {n r : ℕ} (B : PerturbedStarBlocks n r) :
    (perturbedStarCore B).card = 2 + 2 * r := by
  have habT : Disjoint ({B.a, B.b} : Finset (Fin n)) B.T := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact B.a_not_mem_T hxT
    · exact B.b_not_mem_T hxT
  have habTL : Disjoint (({B.a, B.b} : Finset (Fin n)) ∪ B.T) B.L := by
    rw [Finset.disjoint_left]
    intro x hx hxL
    rcases Finset.mem_union.mp hx with hxab | hxT
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxab
      rcases hxab with rfl | rfl
      · exact B.a_not_mem_L hxL
      · exact B.b_not_mem_L hxL
    · exact (Finset.disjoint_left.mp B.T_disjoint_L) hxT hxL
  unfold perturbedStarCore
  calc
    (({B.a, B.b} ∪ B.T) ∪ B.L).card = ({B.a, B.b} ∪ B.T).card + B.L.card :=
      Finset.card_union_of_disjoint habTL
    _ = ({B.a, B.b} : Finset (Fin n)).card + B.T.card + B.L.card := by
      rw [Finset.card_union_of_disjoint habT]
    _ = 2 + 2 * r := by
      simp [Finset.card_pair B.a_ne_b, B.card_T, B.card_L]
      omega

-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Powerset
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `completionFiber_card`

For natural numbers n and d, a pattern `P : Finset (Fin n)`, and a filler `U : Finset (Fin n)` with
`Disjoint P U`, the image of `U.powersetCard (d + 1 - P.card)` under `A ↦ P ∪ A` has cardinality
`Nat.choose U.card (d + 1 - P.card)`.

## Sources

- Source `article/sections/02_proof.tex`, lines 48–50

## Statement dependencies

- `Finset.powersetCard` from `Mathlib.Data.Finset.Powerset`

## Proof outline

Let `k := d + 1 - P.card` and abbreviate the completion map by `f A := P ∪ A`.  Prove `Set.InjOn f
(↑(U.powersetCard k) : Set (Finset (Fin n)))`: if `A` and `A'` are members of this powerset-card
Finset and `P ∪ A = P ∪ A'`, then `Finset.mem_powersetCard` gives `A ⊆ U` and `A' ⊆ U`.  Since
`Disjoint P U`, elementwise extensionality (using `Finset.disjoint_left`) shows that removing `P`
from the equal unions recovers `A = A'`.  This is a lightweight local set calculation; no new helper
is needed.

Apply the restricted-domain cardinality transport `Finset.card_image_of_injOn` to obtain the
cardinality of the displayed image as `(U.powersetCard k).card`, then rewrite it with
`Finset.card_powersetCard`.  The global theorem `Finset.card_image_of_injective` is not applicable
directly because `A ↦ P ∪ A` is not injective on arbitrary Finsets; the verified `InjOn` variant
states exactly the required domain-local fact.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 48–50

## Proof dependencies

- `Finset.card_image_of_injOn` from `Mathlib.Data.Finset.Card`
- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Finset.card_powersetCard` from `Mathlib.Data.Finset.Powerset`
- `Finset.mem_powersetCard` from `Mathlib.Data.Finset.Powerset`
-/
theorem completionFiber_card {n d : ℕ} (P U : Finset (Fin n)) (hPU : Disjoint P U) :
    ((U.powersetCard (d + 1 - P.card)).image (fun A => P ∪ A)).card =
      Nat.choose U.card (d + 1 - P.card) := by
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_powersetCard _ _
  · intro A hA A' hA' hEq
    change P ∪ A = P ∪ A' at hEq
    apply Finset.ext
    intro x
    constructor
    · intro hxA
      have hxU : x ∈ U := (Finset.mem_powersetCard.mp hA).1 hxA
      have hxUnion : x ∈ P ∪ A' := by
        rw [← hEq]
        exact Finset.mem_union_right P hxA
      rcases Finset.mem_union.mp hxUnion with hxP | hxA'
      · exact False.elim ((Finset.disjoint_left.mp hPU) hxP hxU)
      · exact hxA'
    · intro hxA'
      have hxU : x ∈ U := (Finset.mem_powersetCard.mp hA').1 hxA'
      have hxUnion : x ∈ P ∪ A := by
        rw [hEq]
        exact Finset.mem_union_right P hxA'
      rcases Finset.mem_union.mp hxUnion with hxP | hxA
      · exact False.elim ((Finset.disjoint_left.mp hPU) hxP hxU)
      · exact hxA

[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `perturbedStarPerturbation_chooseSum`

The deleted/inserted perturbation preserves all proper-pattern weights and adds exactly the full-L binomial term.

- Kind: `theorem`
- Node: `Main.CountingAndMain`
- Module: `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarPerturbation_chooseSum`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For natural numbers n, r, and d, construction data `B : PerturbedStarBlocks n r`, and hypotheses `2 * r ≤ d` and `2 + 2 * r ≤ n`,
`∑ P ∈ perturbedStarPatterns d B, Nat.choose (perturbedStarFiller B).card (d + 1 - P.card) = (∑ P ∈ ((perturbedStarCore B).powerset.filter (fun P => B.a ∈ P ∧ P.card ≤ d + 1)), Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)) + Nat.choose (n - 2 * r - 2) (d - 2 * r)`.
Every proper-`B.L` deletion is paired with its equal-cardinality insertion at the other anchor; the insertion for `Y = B.L` is the sole unpaired term.  The statement retains the exact r-form bounds and Nat.choose indices.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarPerturbation_chooseSum`

For natural numbers n, r, and d, construction data `B : PerturbedStarBlocks n r`, and hypotheses `2
* r ≤ d` and `2 + 2 * r ≤ n`,
`∑ P ∈ perturbedStarPatterns d B, Nat.choose (perturbedStarFiller B).card (d + 1 - P.card) = (∑ P ∈
((perturbedStarCore B).powerset.filter (fun P => B.a ∈ P ∧ P.card ≤ d + 1)), Nat.choose
(perturbedStarFiller B).card (d + 1 - P.card)) + Nat.choose (n - 2 * r - 2) (d - 2 * r)`.
Every proper-`B.L` deletion is paired with its equal-cardinality insertion at the other anchor; the
insertion for `Y = B.L` is the sole unpaired term.  The statement retains the exact r-form bounds
and Nat.choose indices.

## Sources

- Source `article/sections/02_proof.tex`, lines 35–50

## Statement dependencies

- `Finset.filter` from `Mathlib.Data.Finset.Filter`
- `Finset.powerset` from `Mathlib.Data.Finset.Powerset`
- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
-/
theorem perturbedStarPerturbation_chooseSum {n r d : ℕ} (B : PerturbedStarBlocks n r)
    (hrd : 2 * r ≤ d) (hrn : 2 + 2 * r ≤ n) :
    (∑ P ∈ perturbedStarPatterns d B,
      Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)) =
        (∑ P ∈ (perturbedStarCore B).powerset.filter (fun P => B.a ∈ P ∧ P.card ≤ d + 1),
          Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)) +
          Nat.choose (n - 2 * r - 2) (d - 2 * r) := by
  sorry
```

## Proof NL

Unfold the accepted definition `perturbedStarPatterns d B` into `(base \ deleted) ∪ inserted`, where `base` is the stated filtered anchored powerset, `deleted` is the proper-L a/T image, and `inserted` is the full b/T image. From `hrd`, the powerset-cardinality bound, and the `PerturbedStarBlocks` avoidance/cardinality fields, prove elementwise that every deleted a-pattern belongs to `base`; this is the remaining local membership-and-natural-arithmetic step. Prove `Disjoint (base \ deleted) inserted` elementwise: a retained base pattern contains `B.a`, whereas a b/T/L insertion does not, by the accepted block-avoidance fields.

Use verified `Finset.sum_sdiff` and `Finset.sum_union` to transport the weighted sum over the unfolded pattern family. Apply the proof-accepted provider `Main.PerturbedPatternCancellation::perturbedPattern_properWeights_add_full_eq_fullWeights B d` directly to replace the proper deleted a-image together with the full-L b term by the inserted b-image; the provider has exactly the needed proper-L image, full `{B.b} ∪ B.T ∪ B.L` term, equality direction, and no `hrd` or `hrn` assumptions.

Finally normalize that full-L term. Use the block fields `B.card_T`, `B.card_L`, anchor avoidance, and `B.T_disjoint_L` with `Finset.disjoint_left` and `Finset.card_union_of_disjoint` to obtain `({B.b} ∪ B.T ∪ B.L).card = 1 + 2 * r`. Rewrite the upper index via committed `perturbedStarFiller_card B`; `hrd` and `hrn` make the natural subtractions normalize to `Nat.choose (n - 2 * r - 2) (d - 2 * r)`. These are local set-cardinality and arithmetic normalizations. No dependency on the cleanup wrapper `perturbedStarProperPatterns_chooseSum` is used.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarFiller_card
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarPerturbation_chooseSum`

For natural numbers n, r, and d, construction data `B : PerturbedStarBlocks n r`, and hypotheses `2
* r ≤ d` and `2 + 2 * r ≤ n`,
`∑ P ∈ perturbedStarPatterns d B, Nat.choose (perturbedStarFiller B).card (d + 1 - P.card) = (∑ P ∈
((perturbedStarCore B).powerset.filter (fun P => B.a ∈ P ∧ P.card ≤ d + 1)), Nat.choose
(perturbedStarFiller B).card (d + 1 - P.card)) + Nat.choose (n - 2 * r - 2) (d - 2 * r)`.
Every proper-`B.L` deletion is paired with its equal-cardinality insertion at the other anchor; the
insertion for `Y = B.L` is the sole unpaired term.  The statement retains the exact r-form bounds
and Nat.choose indices.

## Sources

- Source `article/sections/02_proof.tex`, lines 35–50

## Statement dependencies

- `Finset.filter` from `Mathlib.Data.Finset.Filter`
- `Finset.powerset` from `Mathlib.Data.Finset.Powerset`
- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`

## Proof outline

Unfold the accepted definition `perturbedStarPatterns d B` into `(base \ deleted) ∪ inserted`, where
`base` is the stated filtered anchored powerset, `deleted` is the proper-L a/T image, and `inserted`
is the full b/T image. From `hrd`, the powerset-cardinality bound, and the `PerturbedStarBlocks`
avoidance/cardinality fields, prove elementwise that every deleted a-pattern belongs to `base`; this
is the remaining local membership-and-natural-arithmetic step. Prove `Disjoint (base \ deleted)
inserted` elementwise: a retained base pattern contains `B.a`, whereas a b/T/L insertion does not,
by the accepted block-avoidance fields.

Use verified `Finset.sum_sdiff` and `Finset.sum_union` to transport the weighted sum over the
unfolded pattern family. Apply the proof-accepted provider
`Main.PerturbedPatternCancellation::perturbedPattern_properWeights_add_full_eq_fullWeights B d`
directly to replace the proper deleted a-image together with the full-L b term by the inserted
b-image; the provider has exactly the needed proper-L image, full `{B.b} ∪ B.T ∪ B.L` term, equality
direction, and no `hrd` or `hrn` assumptions.

Finally normalize that full-L term. Use the block fields `B.card_T`, `B.card_L`, anchor avoidance,
and `B.T_disjoint_L` with `Finset.disjoint_left` and `Finset.card_union_of_disjoint` to obtain
`({B.b} ∪ B.T ∪ B.L).card = 1 + 2 * r`. Rewrite the upper index via committed
`perturbedStarFiller_card B`; `hrd` and `hrn` make the natural subtractions normalize to `Nat.choose
(n - 2 * r - 2) (d - 2 * r)`. These are local set-cardinality and arithmetic normalizations. No
dependency on the cleanup wrapper `perturbedStarProperPatterns_chooseSum` is used.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 35–50

## Proof dependencies

- `Finset.sum_sdiff` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_union` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.card_union_of_disjoint` from `Mathlib.Data.Finset.Card`
- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Main.CountingAndMain::perturbedStarFiller_card` → `perturbedStarFiller_card` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarFiller_card`
- `Main.PerturbedPatternCancellation::perturbedPattern_properWeights_add_full_eq_fullWeights` →
  `perturbedPattern_properWeights_add_full_eq_fullWeights` from `UniformMissingTraceFamily.Main.Pert
  urbedPatternCancellation.Theorems.perturbedPattern_properWeights_add_full_eq_fullWeights`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
-/
theorem perturbedStarPerturbation_chooseSum {n r d : ℕ} (B : PerturbedStarBlocks n r)
    (hrd : 2 * r ≤ d) (hrn : 2 + 2 * r ≤ n) :
    (∑ P ∈ perturbedStarPatterns d B,
      Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)) =
        (∑ P ∈ (perturbedStarCore B).powerset.filter (fun P => B.a ∈ P ∧ P.card ≤ d + 1),
          Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)) +
          Nat.choose (n - 2 * r - 2) (d - 2 * r) := by
  classical
  let base := (perturbedStarCore B).powerset.filter fun P =>
    B.a ∈ P ∧ P.card ≤ d + 1
  let deleted :=
    (B.L.powerset.filter fun Y => Y ⊆ B.L ∧ Y ≠ B.L).image fun Y =>
      {B.a} ∪ B.T ∪ Y
  let inserted := B.L.powerset.image fun Y => {B.b} ∪ B.T ∪ Y
  let w : Finset (Fin n) → ℕ := fun P =>
    Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)
  have hdeleted : deleted ⊆ base := by
    intro P hP
    rcases Finset.mem_image.mp hP with ⟨Y, hY, rfl⟩
    have hYdata := Finset.mem_filter.mp hY
    have hYsub : Y ⊆ B.L := hYdata.2.1
    have hYne : Y ≠ B.L := hYdata.2.2
    have hYlt : Y.card < B.L.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hYsub, hYne⟩)
    have haT : Disjoint ({B.a} : Finset (Fin n)) B.T := by
      rw [Finset.disjoint_left]
      intro x hx hxT
      rcases Finset.mem_singleton.mp hx with rfl
      exact B.a_not_mem_T hxT
    have haTL : Disjoint (({B.a} : Finset (Fin n)) ∪ B.T) Y := by
      rw [Finset.disjoint_left]
      intro x hx hxY
      rcases Finset.mem_union.mp hx with hxa | hxT
      · rcases Finset.mem_singleton.mp hxa with rfl
        exact B.a_not_mem_L (hYsub hxY)
      · exact (Finset.disjoint_left.mp B.T_disjoint_L) hxT (hYsub hxY)
    have hcard : ({B.a} ∪ B.T ∪ Y : Finset (Fin n)).card = 1 + r + Y.card := by
      rw [Finset.card_union_of_disjoint haTL, Finset.card_union_of_disjoint haT]
      simp [B.card_T]
    rw [Finset.mem_filter]
    constructor
    · apply Finset.mem_powerset.mpr
      intro x hx
      unfold perturbedStarCore
      simp only [Finset.mem_union] at hx ⊢
      rcases hx with hAT | hxY
      · rcases hAT with hxa | hxT
        · rcases Finset.mem_singleton.mp hxa with rfl
          simp
        · exact Or.inl <| Or.inr hxT
      · exact Or.inr (hYsub hxY)
    · constructor
      · simp
      · rw [hcard]
        rw [B.card_L] at hYlt
        omega
  have hdisjoint : Disjoint (base \ deleted) inserted := by
    rw [Finset.disjoint_left]
    intro P hP hI
    have hbase : P ∈ base := (Finset.mem_sdiff.mp hP).1
    have hPa : B.a ∈ P := (Finset.mem_filter.mp hbase).2.1
    rcases Finset.mem_image.mp hI with ⟨Y, hY, rfl⟩
    have hYsub : Y ⊆ B.L := Finset.mem_powerset.mp hY
    simp only [Finset.mem_union, Finset.mem_singleton] at hPa
    rcases hPa with (hab | haT) | haY
    · exact B.a_ne_b hab
    · exact B.a_not_mem_T haT
    · exact B.a_not_mem_L (hYsub haY)
  have hdeleted_eq : deleted =
      (B.L.powerset.filter fun Y => Y ≠ B.L).image fun Y => {B.a} ∪ B.T ∪ Y := by
    dsimp [deleted]
    congr 1
    ext Y
    simp
  have hprovider : (∑ P ∈ deleted, w P) + w ({B.b} ∪ B.T ∪ B.L) =
      ∑ P ∈ inserted, w P := by
    rw [hdeleted_eq]
    simpa [inserted, w] using
      (perturbedPattern_properWeights_add_full_eq_fullWeights B d)
  have hfullcard : ({B.b} ∪ B.T ∪ B.L : Finset (Fin n)).card = 1 + 2 * r := by
    have hbT : Disjoint ({B.b} : Finset (Fin n)) B.T := by
      rw [Finset.disjoint_left]
      intro x hx hxT
      rcases Finset.mem_singleton.mp hx with rfl
      exact B.b_not_mem_T hxT
    have hbTL : Disjoint (({B.b} : Finset (Fin n)) ∪ B.T) B.L := by
      rw [Finset.disjoint_left]
      intro x hx hxL
      rcases Finset.mem_union.mp hx with hxb | hxT
      · rcases Finset.mem_singleton.mp hxb with rfl
        exact B.b_not_mem_L hxL
      · exact (Finset.disjoint_left.mp B.T_disjoint_L) hxT hxL
    rw [Finset.card_union_of_disjoint hbTL, Finset.card_union_of_disjoint hbT]
    simp [B.card_T, B.card_L]
    omega
  have hfull : w ({B.b} ∪ B.T ∪ B.L) = Nat.choose (n - 2 * r - 2) (d - 2 * r) := by
    dsimp [w]
    have hfullcard' : (insert B.b B.T ∪ B.L).card = 1 + 2 * r := by
      simpa only [Finset.singleton_union, Finset.union_assoc] using hfullcard
    rw [hfullcard', perturbedStarFiller_card]
    congr 1 <;> omega
  change (∑ P ∈ (base \ deleted) ∪ inserted, w P) =
    (∑ P ∈ base, w P) + Nat.choose (n - 2 * r - 2) (d - 2 * r)
  calc
    ∑ P ∈ (base \ deleted) ∪ inserted, w P =
        (∑ P ∈ base \ deleted, w P) + ∑ P ∈ inserted, w P :=
      Finset.sum_union hdisjoint
    _ = (∑ P ∈ base \ deleted, w P) +
        ((∑ P ∈ deleted, w P) + w ({B.b} ∪ B.T ∪ B.L)) := by rw [hprovider]
    _ = ((∑ P ∈ base \ deleted, w P) + ∑ P ∈ deleted, w P) +
        w ({B.b} ∪ B.T ∪ B.L) := by omega
    _ = (∑ P ∈ base, w P) + w ({B.b} ∪ B.T ∪ B.L) := by
      rw [Finset.sum_sdiff hdeleted]
    _ = (∑ P ∈ base, w P) + Nat.choose (n - 2 * r - 2) (d - 2 * r) := by rw [hfull]
```

## Statement dependencies

- `Mathlib:Mathlib.Data.Finset.Filter.Finset.filter`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.powerset`
- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFiller`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`

## Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_sdiff`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_union`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_union_of_disjoint`
- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `current repo:Main.CountingAndMain.perturbedStarFiller_card`
- `current repo:Main.PerturbedPatternCancellation.perturbedPattern_properWeights_add_full_eq_fullWeights`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`

## Sources

- `article/sections/02_proof.tex:35-50`

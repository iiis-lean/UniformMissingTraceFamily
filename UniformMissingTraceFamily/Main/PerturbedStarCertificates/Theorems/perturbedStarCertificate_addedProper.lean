-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Powerset
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarCertificate_addedProper`

For natural numbers d, s, n, and r, let `B : PerturbedStarBlocks n r` and let `Y : Finset (Fin n)`
satisfy `Y ⊆ B.L` and `Y ≠ B.L`. Assume `r = d + 1 - s`, `2 ≤ r`, and `r + 1 ≤ s`, and put `P =
{B.b} ∪ B.T ∪ Y`. Then the proper-added selector guard applies, so `perturbedStarTau B P = B.T`, and
the following four-clause certificate bundle holds:

1. `perturbedStarTau B P ⊂ P`.
2. `P.card - (perturbedStarTau B P).card ≤ d + 1 - s`.
3. `(perturbedStarTau B P).card ≤ s`.
4. There is no `Q ∈ perturbedStarPatterns d B` such that both `Q ∩ P = perturbedStarTau B P` and
`Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s)`.

This is the inserted-pattern case indexed by a proper subset of `B.L`; it supplies exactly the
certificate shape required by the generic pattern-family criterion.

## Sources

- Source `article/sections/02_proof.tex`, lines 60–61

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
- `Main.PerturbedStarCertificates::perturbedStarTau` → `perturbedStarTau` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau`

## Proof outline

Let `P := {B.b} ∪ B.T ∪ Y`. The proper-added selector in `perturbedStarTau` is true with witness
`Y`, using `hYsub`, `hYne`, and the defining equality for `P`. Unfolding that first selector gives
```
perturbedStarTau B P = B.T.
```

The fields of `B` make the unions in `P` disjoint: `B.b_not_mem_T` and `B.b_not_mem_L`, together
with `hYsub`, exclude `B.b` from the two blocks, while `B.T_disjoint_L`, transferred elementwise
with `Finset.disjoint_left`, gives `Disjoint B.T Y`. Therefore `B.T ⊂ P`: it is a subset of the
displayed union, while `B.b ∈ P` and `B.b ∉ B.T`.

For the first size bound, `hYsub` and `hYne` give the strict subset `Y ⊂ B.L`; `Finset.card_lt_card`
and `B.card_L` give `Y.card < r`. Apply `Finset.card_union_of_disjoint` twice to the
pairwise-disjoint displayed union:
```
P.card = 1 + r + Y.card.
```
After rewriting `B.T.card` as `r` and `d + 1 - s` as `r` using `hr`, natural-number arithmetic
proves
```
P.card - B.T.card = 1 + Y.card ≤ r.
```
The tau-cardinality clause is `B.card_T` followed by `r ≤ s`, which follows from `hrs : r + 1 ≤ s`.

For the exclusion clause, assume `Q ∈ perturbedStarPatterns d B`, `Q ∩ P = B.T`, and the stated size
bound. Unfold `perturbedStarPatterns` and simplify membership in `Finset.powerset`, images, filters,
the union, and the difference (using `Finset.mem_powerset`). This yields the two construction
branches below.

* In the inserted branch, there is `Z ⊆ B.L` with `Q = {B.b} ∪ B.T ∪ Z`. Thus `B.b ∈ Q ∩ P`, while
`B.b ∉ B.T` by `B.b_not_mem_T`, contradicting the intersection equality.

* In the base-minus-deleted branch, unfold `perturbedStarCore` in the base membership to obtain `Q ⊆
{B.a, B.b} ∪ B.T ∪ B.L` and `B.a ∈ Q`. The intersection equality, `B.a_ne_b`, the four
anchor-avoidance fields, and `B.T_disjoint_L` force `B.b ∉ Q`, `B.T ⊆ Q`, and the representation
  ```
  Q = {B.a} ∪ B.T ∪ Z,  Z ⊆ B.L,  Z ∩ Y = ∅,
  ```
  for `Z := Q ∩ B.L`. If `Z ≠ B.L`, this representation and `Finset.mem_powerset` put `Q` in the
exact deleted image, contradicting the base-minus-deleted membership. Hence `Z = B.L`. Then `B.L ∩ Y
= ∅` and `hYsub` force `Y = ∅`. Pairwise-disjoint union cardinalities, again from
`Finset.disjoint_left` and `Finset.card_union_of_disjoint`, give `Q.card = 1 + 2*r`. But the assumed
size bound, `B.card_T`, and `hr` give `Q.card ≤ 2*r`; `omega` is the final contradiction.

Rewriting by the tau equality supplies exactly the four requested conjuncts. The supplied hypothesis
`hrtwo` is retained unchanged; this case uses `hrs` for its only needed tau-size comparison.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 60–61

## Proof dependencies

- `Finset.card_lt_card` from `Mathlib.Data.Finset.Card`
- `Finset.card_union_of_disjoint` from `Mathlib.Data.Finset.Card`
- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Finset.mem_powerset` from `Mathlib.Data.Finset.Powerset`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
- `Main.PerturbedStarCertificates::perturbedStarTau` → `perturbedStarTau` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau`
-/
theorem perturbedStarCertificate_addedProper (d s n r : ℕ)
    (B : PerturbedStarBlocks n r) (Y : Finset (Fin n))
    (hYsub : Y ⊆ B.L) (hYne : Y ≠ B.L)
    (hr : r = d + 1 - s) (hrtwo : 2 ≤ r) (hrs : r + 1 ≤ s) :
    let P := {B.b} ∪ B.T ∪ Y
    perturbedStarTau B P ⊂ P ∧
      P.card - (perturbedStarTau B P).card ≤ d + 1 - s ∧
      (perturbedStarTau B P).card ≤ s ∧
      ¬ ∃ Q ∈ perturbedStarPatterns d B,
        Q ∩ P = perturbedStarTau B P ∧
          Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s) := by
  classical
  dsimp
  let P : Finset (Fin n) := {B.b} ∪ B.T ∪ Y
  change perturbedStarTau B P ⊂ P ∧
    P.card - (perturbedStarTau B P).card ≤ d + 1 - s ∧
    (perturbedStarTau B P).card ≤ s ∧
    ¬ ∃ Q ∈ perturbedStarPatterns d B,
      Q ∩ P = perturbedStarTau B P ∧
        Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s)
  have hproper : ∃ Z, Z ⊆ B.L ∧ Z ≠ B.L ∧ P = {B.b} ∪ B.T ∪ Z :=
    ⟨Y, hYsub, hYne, rfl⟩
  have hrtwo_used : 2 ≤ r := hrtwo
  have htau : perturbedStarTau B P = B.T := by
    simp only [perturbedStarTau, dif_pos hproper]
  have hTY : Disjoint B.T Y := by
    rw [Finset.disjoint_left]
    intro x hxT hxY
    exact (Finset.disjoint_left.mp B.T_disjoint_L) hxT (hYsub hxY)
  have hbTY : Disjoint ({B.b} ∪ B.T) Y := by
    rw [Finset.disjoint_left]
    intro x hx hxY
    simp only [Finset.mem_union, Finset.mem_singleton] at hx
    rcases hx with rfl | hxT
    · exact B.b_not_mem_L (hYsub hxY)
    · exact (Finset.disjoint_left.mp B.T_disjoint_L) hxT (hYsub hxY)
  have hbT : Disjoint ({B.b} : Finset (Fin n)) B.T := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    rcases Finset.mem_singleton.mp hx with rfl
    exact B.b_not_mem_T hxT
  have hcardP : P.card = 1 + r + Y.card := by
    calc
      P.card = ({B.b} ∪ B.T).card + Y.card := Finset.card_union_of_disjoint hbTY
      _ = ({B.b} : Finset (Fin n)).card + B.T.card + Y.card := by
        rw [Finset.card_union_of_disjoint hbT]
      _ = 1 + r + Y.card := by simp [B.card_T]
  have hYlt : Y.card < r := by
    have hYssub : Y ⊂ B.L := (Finset.ssubset_iff_subset_ne).mpr ⟨hYsub, hYne⟩
    simpa [B.card_L] using Finset.card_lt_card hYssub
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htau]
    apply (Finset.ssubset_iff_subset_ne).mpr
    refine ⟨?_, ?_⟩
    · intro x hx
      simp [P, hx]
    · intro hEq
      have hbP : B.b ∈ P := by simp [P]
      have hbT : B.b ∈ B.T := by simpa [← hEq] using hbP
      exact B.b_not_mem_T hbT
  · rw [htau, hcardP, B.card_T, ← hr]
    omega
  · rw [htau, B.card_T]
    omega
  · rintro ⟨Q, hQ, hQP, hQcard⟩
    rw [htau] at hQP hQcard
    rw [B.card_T, ← hr] at hQcard
    have hQcases :
        ((Q ⊆ insert B.a (insert B.b (B.T ∪ B.L)) ∧ B.a ∈ Q ∧ Q.card ≤ d + 1) ∧
          ∀ x ⊆ B.L, x ≠ B.L → ¬insert B.a (B.T ∪ x) = Q) ∨
        ∃ x ⊆ B.L, insert B.b (B.T ∪ x) = Q := by
      simpa [perturbedStarPatterns, perturbedStarCore] using hQ
    rcases hQcases with hbase | hins
    · rcases hbase with ⟨⟨hQsub, haQ, hQsize⟩, hnotdeleted⟩
      have hbnotQ : B.b ∉ Q := by
        intro hbQ
        have hbP : B.b ∈ P := by simp [P]
        have hbT : B.b ∈ B.T := by
          rw [← hQP]
          exact Finset.mem_inter.mpr ⟨hbQ, hbP⟩
        exact B.b_not_mem_T hbT
      have hTsubQ : B.T ⊆ Q := by
        intro x hxT
        have hxQP : x ∈ Q ∩ P := by
          rw [hQP]
          exact hxT
        exact Finset.mem_inter.mp hxQP |>.1
      have hZsub : Q ∩ B.L ⊆ B.L := Finset.inter_subset_right
      have hrepr : Q = {B.a} ∪ (B.T ∪ (Q ∩ B.L)) := by
        ext x
        constructor
        · intro hxQ
          have hxcore := hQsub hxQ
          simp only [Finset.mem_insert, Finset.mem_union] at hxcore
          simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_inter]
          rcases hxcore with hxa | hxb | hxT | hxL
          · exact Or.inl hxa
          · exact False.elim (hbnotQ (hxb ▸ hxQ))
          · exact Or.inr (Or.inl hxT)
          · exact Or.inr (Or.inr ⟨hxQ, hxL⟩)
        · simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_inter]
          intro hx
          rcases hx with hxa | hxT | ⟨hxQ, hxL⟩
          · simpa [hxa] using haQ
          · exact hTsubQ hxT
          · exact hxQ
      by_cases hZne : Q ∩ B.L ≠ B.L
      · exact hnotdeleted (Q ∩ B.L) hZsub hZne hrepr.symm
      · have hZY : Disjoint (Q ∩ B.L) Y := by
          rw [Finset.disjoint_left]
          intro x hxZ hxY
          have hxQ : x ∈ Q := Finset.mem_inter.mp hxZ |>.1
          have hxP : x ∈ P := by
            simp [P, Or.inr (Or.inr hxY)]
          have hxT : x ∈ B.T := by
            rw [← hQP]
            exact Finset.mem_inter.mpr ⟨hxQ, hxP⟩
          exact (Finset.disjoint_left.mp B.T_disjoint_L) hxT (hYsub hxY)
        have hZeq : Q ∩ B.L = B.L := by
          by_contra h
          exact hZne h
        have hYempty : Y = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hYnonempty
          obtain ⟨x, hxY⟩ := hYnonempty
          have hxZ : x ∈ Q ∩ B.L := by
            rw [hZeq]
            exact hYsub hxY
          exact (Finset.disjoint_left.mp hZY) hxZ hxY
        have haT : Disjoint ({B.a} : Finset (Fin n)) B.T := by
          rw [Finset.disjoint_left]
          intro x hx hxT
          rcases Finset.mem_singleton.mp hx with rfl
          exact B.a_not_mem_T hxT
        have haTL : Disjoint ({B.a} ∪ B.T) B.L := by
          rw [Finset.disjoint_left]
          intro x hx hxL
          simp only [Finset.mem_union, Finset.mem_singleton] at hx
          rcases hx with rfl | hxT
          · exact B.a_not_mem_L hxL
          · exact (Finset.disjoint_left.mp B.T_disjoint_L) hxT hxL
        have hcardQeq : Q.card = 1 + 2 * r := by
          rw [hrepr, hZeq]
          calc
            ({B.a} ∪ (B.T ∪ B.L)).card = ({B.a} ∪ B.T).card + B.L.card := by
              rw [← Finset.union_assoc]
              exact Finset.card_union_of_disjoint haTL
            _ = ({B.a} : Finset (Fin n)).card + B.T.card + B.L.card := by
              rw [Finset.card_union_of_disjoint haT]
            _ = 1 + 2 * r := by simp [B.card_T, B.card_L]; omega
        omega
    · rcases hins with ⟨Z, hZsub, hQeq⟩
      have hbQ : B.b ∈ Q := by
        rw [← hQeq]
        simp
      have hbP : B.b ∈ P := by simp [P]
      have hbT : B.b ∈ B.T := by
        rw [← hQP]
        exact Finset.mem_inter.mpr ⟨hbQ, hbP⟩
      exact B.b_not_mem_T hbT

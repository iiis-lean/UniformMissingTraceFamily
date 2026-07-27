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
# lean-constellation target: `perturbedStarCertificate_smallStar`

For natural numbers `d`, `s`, `n`, and `r`, let `B : PerturbedStarBlocks n r` and `P : Finset (Fin
n)`. Assume `P ∈ perturbedStarPatterns d B`, `B.a ∈ P`, `P.card ≤ r`, and `r = d + 1 - s`. The
accepted small-star selector branch applies, so `perturbedStarTau B P = ∅`. Then the following
four-clause certificate bundle holds:

1. `perturbedStarTau B P ⊂ P`.
2. `P.card - (perturbedStarTau B P).card ≤ d + 1 - s`.
3. `(perturbedStarTau B P).card ≤ s`.
4. There is no `Q ∈ perturbedStarPatterns d B` such that both `Q ∩ P = perturbedStarTau B P` and
`Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s)`.

This is the distinct small a-anchored case of the source certificate: an a-anchored competing
pattern meets `P` at `B.a`, while an inserted b/T pattern cannot meet the required size bound.

## Sources

- Source `article/sections/02_proof.tex`, line 65

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
- `Main.PerturbedStarCertificates::perturbedStarTau` → `perturbedStarTau` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau`

## Proof outline

First identify the selector value. The proper-added guard is false: any set `{B.b} ∪ B.T ∪ Y` with
`Y ⊆ B.L` omits `B.a`, by `B.a_ne_b`, `B.a_not_mem_T`, and `B.a_not_mem_L`, whereas `ha : B.a ∈ P`.
The final-added guard is false for the same reason, since `B.a ∉ {B.b} ∪ B.T ∪ B.L`. The next
small-star guard is exactly `ha ∧ hcard`; unfolding the ordered cases in `perturbedStarTau` gives
```
perturbedStarTau B P = ∅.
```

After this rewrite, `∅ ⊂ P` follows from `ha`. The gap is
```
P.card - ∅.card = P.card ≤ r = d + 1 - s,
```
using `hcard` and `hr`. The tau-cardinality clause is the immediate natural-number inequality `0 ≤
s`.

For the exclusion clause, suppose `Q ∈ perturbedStarPatterns d B`,
`Q ∩ P = ∅`, and `Q.card ≤ r` (after the same tau and `hr` rewrites). Unfold `perturbedStarPatterns`
and simplify powerset, image, filter, union, and difference membership with `Finset.mem_powerset`.

* If `Q` comes from the base-minus-deleted component, the base filter supplies `B.a ∈ Q`. Together
with `ha : B.a ∈ P`, this gives `B.a ∈ Q ∩ P`, contradicting the empty intersection.

* If `Q` comes from the inserted component, then for some `Z ⊆ B.L`,
  ```
  Q = {B.b} ∪ B.T ∪ Z.
  ```
  The fields `B.b_not_mem_T`, `B.b_not_mem_L`, `B.T_disjoint_L`, and `Z ⊆ B.L` give the required
pairwise disjointness (elementwise through `Finset.disjoint_left`). Applying
`Finset.card_union_of_disjoint` with `B.card_T = r` shows
  `Q.card = 1 + r + Z.card ≥ r + 1`, contradicting `Q.card ≤ r`.

Thus both construction branches are impossible. Rewriting by the empty small-star selector gives
exactly the four required conjuncts. No expansion of `perturbedStarCore` is needed in this branch:
the base filter's `B.a ∈ Q` condition already supplies the source exclusion.

## Proof sources

- Source `article/sections/02_proof.tex`, line 65

## Proof dependencies

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
theorem perturbedStarCertificate_smallStar (d s n r : ℕ)
    (B : PerturbedStarBlocks n r) (P : Finset (Fin n))
    (hP : P ∈ perturbedStarPatterns d B) (ha : B.a ∈ P)
    (hcard : P.card ≤ r) (hr : r = d + 1 - s) :
    perturbedStarTau B P ⊂ P ∧
      P.card - (perturbedStarTau B P).card ≤ d + 1 - s ∧
      (perturbedStarTau B P).card ≤ s ∧
      ¬ ∃ Q ∈ perturbedStarPatterns d B,
        Q ∩ P = perturbedStarTau B P ∧
          Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s) := by
  classical
  have _ := hP
  have hnotproper :
      ¬ ∃ Y, Y ⊆ B.L ∧ Y ≠ B.L ∧ P = {B.b} ∪ B.T ∪ Y := by
    rintro ⟨Y, hYsub, _, hPY⟩
    have haform : B.a ∈ {B.b} ∪ B.T ∪ Y := by
      rw [← hPY]
      exact ha
    rcases Finset.mem_union.mp haform with habT | haY
    · rcases Finset.mem_union.mp habT with hab | haT
      · exact B.a_ne_b (Finset.mem_singleton.mp hab)
      · exact B.a_not_mem_T haT
    · exact B.a_not_mem_L (hYsub haY)
  have hnotfinal :
      ¬ (P = {B.b} ∪ B.T ∪ B.L ∧ ∃ ell0, ell0 ∈ B.L) := by
    rintro ⟨hPfinal, _⟩
    have haform : B.a ∈ {B.b} ∪ B.T ∪ B.L := by
      rw [← hPfinal]
      exact ha
    rcases Finset.mem_union.mp haform with habT | haL
    · rcases Finset.mem_union.mp habT with hab | haT
      · exact B.a_ne_b (Finset.mem_singleton.mp hab)
      · exact B.a_not_mem_T haT
    · exact B.a_not_mem_L haL
  have hsmall : B.a ∈ P ∧ P.card ≤ r := ⟨ha, hcard⟩
  have htau : perturbedStarTau B P = ∅ := by
    simp only [perturbedStarTau, dif_neg hnotproper, dif_neg hnotfinal,
      dif_pos hsmall]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htau]
    apply (Finset.ssubset_iff_subset_ne).mpr
    refine ⟨Finset.empty_subset _, ?_⟩
    intro hPempty
    have : B.a ∈ (∅ : Finset (Fin n)) := by
      simpa [hPempty] using ha
    simp at this
  · rw [htau]
    simp only [Finset.card_empty, Nat.sub_zero]
    rw [← hr]
    exact hcard
  · rw [htau]
    simp
  · rintro ⟨Q, hQ, hQP, hQcard⟩
    rw [htau] at hQP hQcard
    have hQcard' : Q.card ≤ r := by
      rw [← hr] at hQcard
      simpa using hQcard
    have hQcases :
        ((Q ⊆ insert B.a (insert B.b (B.T ∪ B.L)) ∧ B.a ∈ Q ∧
            Q.card ≤ d + 1) ∧
          ∀ Z ⊆ B.L, Z ≠ B.L → ¬ insert B.a (B.T ∪ Z) = Q) ∨
        ∃ Z ⊆ B.L, insert B.b (B.T ∪ Z) = Q := by
      simpa [perturbedStarPatterns, perturbedStarCore] using hQ
    rcases hQcases with hbase | hinsertion
    · rcases hbase with ⟨⟨_, haQ, _⟩, _⟩
      have haintersection : B.a ∈ Q ∩ P :=
        Finset.mem_inter.mpr ⟨haQ, ha⟩
      rw [hQP] at haintersection
      simp at haintersection
    · rcases hinsertion with ⟨Z, hZsub, hQeq⟩
      have hbT : Disjoint ({B.b} : Finset (Fin n)) B.T := by
        rw [Finset.disjoint_left]
        intro x hxb hxT
        have hx_eq : x = B.b := Finset.mem_singleton.mp hxb
        subst x
        exact B.b_not_mem_T hxT
      have hTZ : Disjoint B.T Z := by
        rw [Finset.disjoint_left]
        intro x hxT hxZ
        exact Finset.disjoint_left.mp B.T_disjoint_L hxT (hZsub hxZ)
      have hbTZ : Disjoint ({B.b} : Finset (Fin n)) (B.T ∪ Z) := by
        rw [Finset.disjoint_left]
        intro x hxb hxTZ
        have hx_eq : x = B.b := Finset.mem_singleton.mp hxb
        subst x
        rcases Finset.mem_union.mp hxTZ with hxT | hxZ
        · exact B.b_not_mem_T hxT
        · exact B.b_not_mem_L (hZsub hxZ)
      have hcardQ : Q.card = 1 + r + Z.card := by
        rw [← hQeq]
        calc
          (insert B.b (B.T ∪ Z)).card =
              ({B.b} : Finset (Fin n)).card + (B.T ∪ Z).card :=
            Finset.card_union_of_disjoint hbTZ
          _ = ({B.b} : Finset (Fin n)).card + (B.T.card + Z.card) := by
            rw [Finset.card_union_of_disjoint hTZ]
          _ = 1 + r + Z.card := by simp [B.card_T]; omega
      omega

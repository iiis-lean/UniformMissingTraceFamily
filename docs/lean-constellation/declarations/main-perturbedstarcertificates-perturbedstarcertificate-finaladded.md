[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `perturbedStarCertificate_finalAdded`

The tau certificate satisfies the generic criterion for the final inserted b/T/L pattern.

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_finalAdded`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For natural numbers `d`, `s`, `n`, and `r`, let `B : PerturbedStarBlocks n r`. Assume `r = d + 1 - s`, `2 ≤ r`, and `r + 1 ≤ s`, and put `P = {B.b} ∪ B.T ∪ B.L`. The lower bound together with `B.card_L = r` makes `B.L` nonempty, so the final-added selector guard applies: for the selector's chosen `ell0 ∈ B.L`, `perturbedStarTau B P = B.T ∪ {ell0}`. Then the following four-clause certificate bundle holds:

1. `perturbedStarTau B P ⊂ P`.
2. `P.card - (perturbedStarTau B P).card ≤ d + 1 - s`.
3. `(perturbedStarTau B P).card ≤ s`.
4. There is no `Q ∈ perturbedStarPatterns d B` such that both `Q ∩ P = perturbedStarTau B P` and `Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s)`.

This is the final inserted `b/T/L` pattern case and supplies exactly the certificate shape required by the generic pattern-family criterion.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarCertificate_finalAdded`

For natural numbers `d`, `s`, `n`, and `r`, let `B : PerturbedStarBlocks n r`. Assume `r = d + 1 -
s`, `2 ≤ r`, and `r + 1 ≤ s`, and put `P = {B.b} ∪ B.T ∪ B.L`. The lower bound together with
`B.card_L = r` makes `B.L` nonempty, so the final-added selector guard applies: for the selector's
chosen `ell0 ∈ B.L`, `perturbedStarTau B P = B.T ∪ {ell0}`. Then the following four-clause
certificate bundle holds:

1. `perturbedStarTau B P ⊂ P`.
2. `P.card - (perturbedStarTau B P).card ≤ d + 1 - s`.
3. `(perturbedStarTau B P).card ≤ s`.
4. There is no `Q ∈ perturbedStarPatterns d B` such that both `Q ∩ P = perturbedStarTau B P` and
`Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s)`.

This is the final inserted `b/T/L` pattern case and supplies exactly the certificate shape required
by the generic pattern-family criterion.

## Sources

- Source `article/sections/02_proof.tex`, line 63

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
- `Main.PerturbedStarCertificates::perturbedStarTau` → `perturbedStarTau` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau`
-/
theorem perturbedStarCertificate_finalAdded (d s n r : ℕ)
    (B : PerturbedStarBlocks n r)
    (hr : r = d + 1 - s) (hrtwo : 2 ≤ r) (hrs : r + 1 ≤ s) :
    let P := {B.b} ∪ B.T ∪ B.L
    perturbedStarTau B P ⊂ P ∧
      P.card - (perturbedStarTau B P).card ≤ d + 1 - s ∧
      (perturbedStarTau B P).card ≤ s ∧
      ¬ ∃ Q ∈ perturbedStarPatterns d B,
        Q ∩ P = perturbedStarTau B P ∧
          Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s) := by
  sorry
```

## Proof NL

Let `P := {B.b} ∪ B.T ∪ B.L`. From `hrtwo : 2 ≤ r` and `B.card_L = r`, prove `B.L.Nonempty`: if `B.L = ∅`, its cardinality is zero, contradicting `2 ≤ r`. Fix
```
ell0 := Classical.choose hL,   hell0 : ell0 ∈ B.L.
```

First show that the earlier proper-added guard in `perturbedStarTau` is false. If `P = {B.b} ∪ B.T ∪ Y` with `Y ⊆ B.L` and `Y ≠ B.L`, intersect the equality with `B.L`. The anchor-avoidance fields and `B.T_disjoint_L` reduce its left side to `B.L` and its right side to `Y`, contradicting `Y ≠ B.L`. The next guard is true, with the displayed equality for `P` and `hL`. Unfolding the two selectors therefore gives
```
perturbedStarTau B P = B.T ∪ {ell0}.
```

Use `B.T_disjoint_L` and `hell0`, via `Finset.disjoint_left`, to obtain `Disjoint B.T {ell0}`. Together with the two b-avoidance fields, this makes the displayed unions pairwise disjoint. Hence `Finset.card_union_of_disjoint`, `B.card_T`, and `B.card_L` give
```
(perturbedStarTau B P).card = r + 1,
P.card = 1 + 2*r,
P.card - (perturbedStarTau B P).card = r.
```
The properness clause follows because the tau is contained in `P`, while `B.b ∈ P` but `B.b ∉ B.T ∪ {ell0}`. Rewrite `r` as `d + 1 - s` with `hr` for the gap clause, and use `hrs : r + 1 ≤ s` for the tau-cardinality clause.

For the exclusion clause, assume `Q ∈ perturbedStarPatterns d B`, `Q ∩ P = B.T ∪ {ell0}`, and the criterion size bound. Unfold `perturbedStarPatterns` and simplify the powerset, image, filter, union, and difference membership (using `Finset.mem_powerset`).

* In the inserted branch, `Q = {B.b} ∪ B.T ∪ Z` for some `Z ⊆ B.L`. Then `B.b ∈ Q ∩ P`, but `B.b ∉ B.T ∪ {ell0}` by `B.b_not_mem_T`, `B.b_not_mem_L`, and `hell0`, a contradiction.

* In the base-minus-deleted branch, unfold `perturbedStarCore`. It gives `B.a ∈ Q` and `Q ⊆ {B.a, B.b} ∪ B.T ∪ B.L`. The intersection equality forces `B.b ∉ Q`, `B.T ∪ {ell0} ⊆ Q`, and excludes every member of `B.L \ {ell0}` from `Q`. With the core containment, extensionality gives
  ```
  Q = {B.a} ∪ B.T ∪ {ell0}.
  ```
  The singleton is a proper subset of `B.L`: it is contained by `hell0`, and equality would make `B.L.card = 1`, contrary to `B.card_L` and `hrtwo`. Therefore this exact representation is in the deleted powerset image, contradicting the base-minus-deleted membership.

Thus no such `Q` exists (the final branch is already contradictory before its size hypothesis is needed), and rewriting by the selector equality yields the four requested conjuncts.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Powerset
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarFinalIntersection_excluded
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarCertificate_finalAdded`

For natural numbers `d`, `s`, `n`, and `r`, let `B : PerturbedStarBlocks n r`. Assume `r = d + 1 -
s`, `2 ≤ r`, and `r + 1 ≤ s`, and put `P = {B.b} ∪ B.T ∪ B.L`. The lower bound together with
`B.card_L = r` makes `B.L` nonempty, so the final-added selector guard applies: for the selector's
chosen `ell0 ∈ B.L`, `perturbedStarTau B P = B.T ∪ {ell0}`. Then the following four-clause
certificate bundle holds:

1. `perturbedStarTau B P ⊂ P`.
2. `P.card - (perturbedStarTau B P).card ≤ d + 1 - s`.
3. `(perturbedStarTau B P).card ≤ s`.
4. There is no `Q ∈ perturbedStarPatterns d B` such that both `Q ∩ P = perturbedStarTau B P` and
`Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s)`.

This is the final inserted `b/T/L` pattern case and supplies exactly the certificate shape required
by the generic pattern-family criterion.

## Sources

- Source `article/sections/02_proof.tex`, line 63

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
- `Main.PerturbedStarCertificates::perturbedStarTau` → `perturbedStarTau` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau`

## Proof outline

Let `P := {B.b} ∪ B.T ∪ B.L`. From `hrtwo : 2 ≤ r` and `B.card_L = r`, prove `B.L.Nonempty`: if `B.L
= ∅`, its cardinality is zero, contradicting `2 ≤ r`. Fix
```
ell0 := Classical.choose hL,   hell0 : ell0 ∈ B.L.
```

First show that the earlier proper-added guard in `perturbedStarTau` is false. If `P = {B.b} ∪ B.T ∪
Y` with `Y ⊆ B.L` and `Y ≠ B.L`, intersect the equality with `B.L`. The anchor-avoidance fields and
`B.T_disjoint_L` reduce its left side to `B.L` and its right side to `Y`, contradicting `Y ≠ B.L`.
The next guard is true, with the displayed equality for `P` and `hL`. Unfolding the two selectors
therefore gives
```
perturbedStarTau B P = B.T ∪ {ell0}.
```

Use `B.T_disjoint_L` and `hell0`, via `Finset.disjoint_left`, to obtain `Disjoint B.T {ell0}`.
Together with the two b-avoidance fields, this makes the displayed unions pairwise disjoint. Hence
`Finset.card_union_of_disjoint`, `B.card_T`, and `B.card_L` give
```
(perturbedStarTau B P).card = r + 1,
P.card = 1 + 2*r,
P.card - (perturbedStarTau B P).card = r.
```
The properness clause follows because the tau is contained in `P`, while `B.b ∈ P` but `B.b ∉ B.T ∪
{ell0}`. Rewrite `r` as `d + 1 - s` with `hr` for the gap clause, and use `hrs : r + 1 ≤ s` for the
tau-cardinality clause.

For the exclusion clause, assume `Q ∈ perturbedStarPatterns d B`, `Q ∩ P = B.T ∪ {ell0}`, and the
criterion size bound. Unfold `perturbedStarPatterns` and simplify the powerset, image, filter,
union, and difference membership (using `Finset.mem_powerset`).

* In the inserted branch, `Q = {B.b} ∪ B.T ∪ Z` for some `Z ⊆ B.L`. Then `B.b ∈ Q ∩ P`, but `B.b ∉
B.T ∪ {ell0}` by `B.b_not_mem_T`, `B.b_not_mem_L`, and `hell0`, a contradiction.

* In the base-minus-deleted branch, unfold `perturbedStarCore`. It gives `B.a ∈ Q` and `Q ⊆ {B.a,
B.b} ∪ B.T ∪ B.L`. The intersection equality forces `B.b ∉ Q`, `B.T ∪ {ell0} ⊆ Q`, and excludes
every member of `B.L \ {ell0}` from `Q`. With the core containment, extensionality gives
  ```
  Q = {B.a} ∪ B.T ∪ {ell0}.
  ```
  The singleton is a proper subset of `B.L`: it is contained by `hell0`, and equality would make
`B.L.card = 1`, contrary to `B.card_L` and `hrtwo`. Therefore this exact representation is in the
deleted powerset image, contradicting the base-minus-deleted membership.

Thus no such `Q` exists (the final branch is already contradictory before its size hypothesis is
needed), and rewriting by the selector equality yields the four requested conjuncts.

## Proof sources

- Source `article/sections/02_proof.tex`, line 63

## Proof dependencies

- `Finset.card_union_of_disjoint` from `Mathlib.Data.Finset.Card`
- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Finset.mem_powerset` from `Mathlib.Data.Finset.Powerset`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
- `Main.PerturbedStarCertificates::perturbedStarFinalIntersection_excluded` →
  `perturbedStarFinalIntersection_excluded` from `UniformMissingTraceFamily.Main.PerturbedStarCertif
  icates.Theorems.perturbedStarFinalIntersection_excluded`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
- `Main.PerturbedStarCertificates::perturbedStarTau` → `perturbedStarTau` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau`
-/
theorem perturbedStarCertificate_finalAdded (d s n r : ℕ)
    (B : PerturbedStarBlocks n r)
    (hr : r = d + 1 - s) (hrtwo : 2 ≤ r) (hrs : r + 1 ≤ s) :
    let P := {B.b} ∪ B.T ∪ B.L
    perturbedStarTau B P ⊂ P ∧
      P.card - (perturbedStarTau B P).card ≤ d + 1 - s ∧
      (perturbedStarTau B P).card ≤ s ∧
      ¬ ∃ Q ∈ perturbedStarPatterns d B,
        Q ∩ P = perturbedStarTau B P ∧
          Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s) := by
  classical
  dsimp
  let P : Finset (Fin n) := {B.b} ∪ B.T ∪ B.L
  change perturbedStarTau B P ⊂ P ∧
    P.card - (perturbedStarTau B P).card ≤ d + 1 - s ∧
    (perturbedStarTau B P).card ≤ s ∧
    ¬ ∃ Q ∈ perturbedStarPatterns d B,
      Q ∩ P = perturbedStarTau B P ∧
        Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s)
  have hLnonempty : B.L.Nonempty := by
    by_contra hLempty
    have hLzero : B.L.card = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hLempty]
      simp
    rw [B.card_L] at hLzero
    omega
  have hnotproper :
      ¬ ∃ Y, Y ⊆ B.L ∧ Y ≠ B.L ∧ P = {B.b} ∪ B.T ∪ Y := by
    rintro ⟨Y, hYsub, hYne, hPY⟩
    apply hYne
    apply Finset.Subset.antisymm hYsub
    intro x hxL
    have hxP : x ∈ P := by
      simp [P, hxL]
    have hxYform : x ∈ {B.b} ∪ B.T ∪ Y := by
      rw [← hPY]
      exact hxP
    rcases Finset.mem_union.mp hxYform with hxbT | hxY
    · rcases Finset.mem_union.mp hxbT with hxb | hxT
      · exfalso
        apply B.b_not_mem_L
        exact Finset.mem_singleton.mp hxb ▸ hxL
      · exact False.elim (Finset.disjoint_left.mp B.T_disjoint_L hxT hxL)
    · exact hxY
  have hfinal : P = {B.b} ∪ B.T ∪ B.L ∧ ∃ ell0, ell0 ∈ B.L :=
    ⟨rfl, hLnonempty⟩
  let ell0 : Fin n := Classical.choose hfinal.2
  have hell0 : ell0 ∈ B.L := Classical.choose_spec hfinal.2
  have htau : perturbedStarTau B P = B.T ∪ {ell0} := by
    simp only [perturbedStarTau, dif_neg hnotproper, dif_pos hfinal]
    rfl
  have hTell0 : Disjoint B.T ({ell0} : Finset (Fin n)) := by
    rw [Finset.disjoint_left]
    intro x hxT hxell0
    have hx_eq : x = ell0 := Finset.mem_singleton.mp hxell0
    subst x
    exact Finset.disjoint_left.mp B.T_disjoint_L hxT hell0
  have hbT : Disjoint ({B.b} : Finset (Fin n)) B.T := by
    rw [Finset.disjoint_left]
    intro x hxb hxT
    have hx_eq : x = B.b := Finset.mem_singleton.mp hxb
    subst x
    exact B.b_not_mem_T hxT
  have hbTL : Disjoint ({B.b} ∪ B.T) B.L := by
    rw [Finset.disjoint_left]
    intro x hx hxL
    simp only [Finset.mem_union, Finset.mem_singleton] at hx
    rcases hx with hxb | hxT
    · subst x
      exact B.b_not_mem_L hxL
    · exact Finset.disjoint_left.mp B.T_disjoint_L hxT hxL
  have hcardtau : (perturbedStarTau B P).card = r + 1 := by
    rw [htau]
    calc
      (B.T ∪ {ell0}).card = B.T.card + ({ell0} : Finset (Fin n)).card :=
        Finset.card_union_of_disjoint hTell0
      _ = r + 1 := by simp [B.card_T]
  have hcardP : P.card = 1 + 2 * r := by
    calc
      P.card = ({B.b} ∪ B.T).card + B.L.card :=
        Finset.card_union_of_disjoint hbTL
      _ = ({B.b} : Finset (Fin n)).card + B.T.card + B.L.card := by
        rw [Finset.card_union_of_disjoint hbT]
      _ = 1 + 2 * r := by simp [B.card_T, B.card_L]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htau]
    apply (Finset.ssubset_iff_subset_ne).mpr
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hxT | hxell0
      · simp [P, hxT]
      · have hx_eq : x = ell0 := Finset.mem_singleton.mp hxell0
        subst x
        simp [P, hell0]
    · intro hEq
      have hbP : B.b ∈ P := by simp [P]
      have hbtau : B.b ∈ B.T ∪ {ell0} := by
        rw [hEq]
        exact hbP
      simp only [Finset.mem_union, Finset.mem_singleton] at hbtau
      rcases hbtau with hbT | hbell0
      · exact B.b_not_mem_T hbT
      · apply B.b_not_mem_L
        simpa [hbell0] using hell0
  · rw [hcardP, hcardtau, ← hr]
    omega
  · rw [hcardtau]
    exact hrs
  · rintro ⟨Q, hQ, hQP, _⟩
    rw [htau] at hQP
    apply perturbedStarFinalIntersection_excluded d n r B ell0 hell0 hrtwo
    refine ⟨Q, hQ, ?_⟩
    simpa [P] using hQP
```

## Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

## Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_union_of_disjoint`
- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.mem_powerset`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFinalIntersection_excluded`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

## Sources

- `article/sections/02_proof.tex:63-63`

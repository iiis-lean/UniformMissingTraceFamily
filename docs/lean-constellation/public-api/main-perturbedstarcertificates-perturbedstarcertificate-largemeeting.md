[← Public API index](../PUBLIC_API.md)

# `perturbedStarCertificate_largeMeeting`

The tau certificate satisfies the generic criterion for a large a-anchored pattern meeting T.

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_largeMeeting`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import Mathlib.Data.Finset.Card
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarCertificate_largeMeeting`

For natural numbers `d`, `s`, `n`, and `r`, let `B : PerturbedStarBlocks n r` and `P : Finset (Fin
n)`. Assume `P ∈ perturbedStarPatterns d B`, `B.a ∈ P`, `r < P.card`, `P ∩ B.T ≠ ∅`, `r = d + 1 -
s`, and `2 ≤ r`. The accepted fifth selector branch applies: for its chosen `t0 ∈ P ∩ B.T`,
`perturbedStarTau B P` is the chosen subset of `P \ {B.a, t0}` of cardinality `P.card - r`. Then the
following four-clause certificate bundle holds:

1. `perturbedStarTau B P ⊂ P`.
2. `P.card - (perturbedStarTau B P).card ≤ d + 1 - s`.
3. `(perturbedStarTau B P).card ≤ s`.
4. There is no `Q ∈ perturbedStarPatterns d B` such that both `Q ∩ P = perturbedStarTau B P` and
`Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s)`.

This is the distinct large a-anchored case meeting `T`: the selector omits both `B.a` and `t0`,
which excludes the competing base and inserted pattern branches.

## Sources

- Source `article/sections/02_proof.tex`, line 72

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
- `Main.PerturbedStarCertificates::perturbedStarTau` → `perturbedStarTau` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau`

## Proof outline

First unfold `perturbedStarPatterns` at `hP`. The inserted branch is impossible because every
inserted set has the form `{B.b} ∪ B.T ∪ Z` with `Z ⊆ B.L` and therefore omits `B.a`, by `B.a_ne_b`,
`B.a_not_mem_T`, and `B.a_not_mem_L`. Thus `P` lies in the bounded a-anchored base-minus-deleted
component. Retain
```
hcore : P ⊆ perturbedStarCore B,   hbasecard : P.card ≤ d + 1.
```

Use `hmeeting : P ∩ B.T ≠ ∅` to choose an initial witness `t0w ∈ P ∩ B.T`. Hence `t0w ∈ P`, `t0w ∈
B.T`, and `t0w ≠ B.a` by `B.a_not_mem_T`. The anchor itself is in `P`, so two applications of
`Finset.card_erase_of_mem`, first for `B.a` and then for `t0w`, identify the cardinality of
```
P \ {B.a, t0w}
```
as `P.card - 2`. Since `2 ≤ r`, natural-number arithmetic yields
```
P.card - r ≤ (P \ {B.a, t0w}).card.
```
Apply `Finset.exists_subset_card_eq` to obtain `Qw ⊆ P \ {B.a,t0w}` with
`Qw.card = P.card-r`. This establishes the fifth guard existential
```
hpair : ∃ t0, t0 ∈ P ∩ B.T ∧
  ∃ Q, Q ⊆ P \ {B.a,t0} ∧ Q.card = P.card-r.
```

For the actual selector, define the exact true guard
```
hlarge : B.a ∈ P ∧ r < P.card ∧ P ∩ B.T ≠ ∅ ∧ hpair
  := ⟨ha, hrlt, hmeeting, hpair⟩,
t0 := Classical.choose hlarge.2.2.2,
tau := Classical.choose (Classical.choose_spec hlarge.2.2.2).2.
```
These are deliberately the canonical `Classical.choose` values in the fifth branch of
`perturbedStarTau`, not the preliminary witnesses `t0w,Qw`. The two successive
`Classical.choose_spec` facts give
```
ht0 : t0 ∈ P ∩ B.T,
htau_sub : tau ⊆ P \ {B.a,t0},
htau_card : tau.card = P.card-r.
```

The proper-added and final-added guards are false because they omit `B.a`, the small-star guard is
false by `hrlt`, and the fourth (large-avoiding) guard is false because it requires `P ∩ B.T = ∅`,
contradicting `hmeeting`. Unfold `perturbedStarTau` with these false guards and the true `hlarge`.
Its fifth branch returns the displayed two canonical choices, yielding
```
htau : perturbedStarTau B P = tau.
```
Rewrite the requested four clauses using `htau`.

From `htau_sub`, `tau ⊆ P`, but `B.a ∈ P` and `B.a ∉ tau` because the selector lies in `P \
{B.a,t0}`; therefore `tau ⊂ P`. Using `htau_card` and `hrlt`, derive
```
P.card - tau.card = r.
```
Rewrite `r` with `hr` for the gap clause. For the selector-size clause, `hbasecard` and `r < P.card`
imply `r < d+1`; with `hr` and `htau_card`, natural-number arithmetic proves `tau.card ≤ s`.

For the exclusion clause, assume `Q ∈ perturbedStarPatterns d B`,
`Q ∩ P = tau`, and the stated size bound. Unfold the pattern definition and split the two branches.

* A base-minus-deleted `Q` contains `B.a`. Since `B.a ∈ P` while `B.a ∉ tau` by `htau_sub`, its
intersection with `P` cannot equal `tau`.

* An inserted `Q` is `{B.b} ∪ B.T ∪ Z`. The canonical `ht0` gives `t0 ∈ P ∩ B.T`, so `t0 ∈ Q ∩ P`.
But `t0 ∉ tau` because `htau_sub` avoids `{B.a,t0}`. Thus this intersection also cannot equal `tau`.

Both pattern branches are impossible, proving the fourth clause. Rewriting back by `htau` gives the
exact required bundle.

## Proof sources

- Source `article/sections/02_proof.tex`, line 72

## Proof dependencies

- `Finset.card_erase_of_mem` from `Mathlib.Data.Finset.Card`
- `Finset.exists_subset_card_eq` from `Mathlib.Data.Finset.Card`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
- `Main.PerturbedStarCertificates::perturbedStarTau` → `perturbedStarTau` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau`
-/
theorem perturbedStarCertificate_largeMeeting (d s n r : ℕ)
    (B : PerturbedStarBlocks n r) (P : Finset (Fin n))
    (hP : P ∈ perturbedStarPatterns d B) (ha : B.a ∈ P)
    (hrlt : r < P.card) (hmeeting : P ∩ B.T ≠ ∅)
    (hr : r = d + 1 - s) (hrtwo : 2 ≤ r) :
    perturbedStarTau B P ⊂ P ∧
      P.card - (perturbedStarTau B P).card ≤ d + 1 - s ∧
      (perturbedStarTau B P).card ≤ s ∧
      ¬ ∃ Q ∈ perturbedStarPatterns d B,
        Q ∩ P = perturbedStarTau B P ∧
          Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s) := by
  classical
  have hPcases :
      ((P ⊆ insert B.a (insert B.b (B.T ∪ B.L)) ∧ B.a ∈ P ∧
          P.card ≤ d + 1) ∧
        ∀ Z ⊆ B.L, Z ≠ B.L → ¬ insert B.a (B.T ∪ Z) = P) ∨
      ∃ Z ⊆ B.L, insert B.b (B.T ∪ Z) = P := by
    simpa [perturbedStarPatterns, perturbedStarCore] using hP
  have hbase :
      P ⊆ insert B.a (insert B.b (B.T ∪ B.L)) ∧ P.card ≤ d + 1 := by
    rcases hPcases with hbase | hinsertion
    · exact ⟨hbase.1.1, hbase.1.2.2⟩
    · rcases hinsertion with ⟨Z, hZsub, hZeq⟩
      have haform : B.a ∈ insert B.b (B.T ∪ Z) := by
        rw [hZeq]
        exact ha
      simp only [Finset.mem_insert, Finset.mem_union] at haform
      rcases haform with hab | haTZ
      · exact False.elim (B.a_ne_b hab)
      · rcases haTZ with haT | haZ
        · exact False.elim (B.a_not_mem_T haT)
        · exact False.elim (B.a_not_mem_L (hZsub haZ))
  have hPTnonempty : (P ∩ B.T).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hmeeting
  obtain ⟨t0w, ht0w⟩ := hPTnonempty
  have ht0wP : t0w ∈ P := Finset.mem_inter.mp ht0w |>.1
  have ht0wT : t0w ∈ B.T := Finset.mem_inter.mp ht0w |>.2
  have ht0w_ne_a : t0w ≠ B.a := by
    intro h
    subst t0w
    exact B.a_not_mem_T ht0wT
  have ht0w_mem_erase : t0w ∈ P.erase B.a := by
    exact Finset.mem_erase.mpr ⟨ht0w_ne_a, ht0wP⟩
  have herase : P \ {B.a, t0w} = (P.erase B.a).erase t0w := by
    ext x
    simp [and_assoc, and_comm]
  have hremovedcard : (P \ {B.a, t0w}).card = P.card - 2 := by
    rw [herase, Finset.card_erase_of_mem ht0w_mem_erase]
    rw [Finset.card_erase_of_mem ha]
    omega
  have hsubsetcard : P.card - r ≤ (P \ {B.a, t0w}).card := by
    rw [hremovedcard]
    omega
  obtain ⟨witness, hwitnesssub, hwitnesscard⟩ :=
    Finset.exists_subset_card_eq hsubsetcard
  have hnotproper :
      ¬ ∃ Z, Z ⊆ B.L ∧ Z ≠ B.L ∧ P = {B.b} ∪ B.T ∪ Z := by
    rintro ⟨Z, hZsub, _, hPZ⟩
    have haform : B.a ∈ {B.b} ∪ B.T ∪ Z := by
      rw [← hPZ]
      exact ha
    rcases Finset.mem_union.mp haform with habT | haZ
    · rcases Finset.mem_union.mp habT with hab | haT
      · exact B.a_ne_b (Finset.mem_singleton.mp hab)
      · exact B.a_not_mem_T haT
    · exact B.a_not_mem_L (hZsub haZ)
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
  have hnotsmall : ¬ (B.a ∈ P ∧ P.card ≤ r) := by
    intro hsmall
    omega
  have hnotavoid :
      ¬ (B.a ∈ P ∧ r < P.card ∧ P ∩ B.T = ∅ ∧
        ∃ Q, Q ⊆ P ∩ B.L ∧ Q.card = P.card - r) := by
    rintro ⟨_, _, havoid, _⟩
    exact hmeeting havoid
  have hpair :
      ∃ t0, t0 ∈ P ∩ B.T ∧
        ∃ Q, Q ⊆ P \ {B.a, t0} ∧ Q.card = P.card - r :=
    ⟨t0w, ht0w, ⟨witness, hwitnesssub, hwitnesscard⟩⟩
  have hlarge :
      B.a ∈ P ∧ r < P.card ∧ P ∩ B.T ≠ ∅ ∧
        ∃ t0, t0 ∈ P ∩ B.T ∧
          ∃ Q, Q ⊆ P \ {B.a, t0} ∧ Q.card = P.card - r :=
    ⟨ha, hrlt, hmeeting, hpair⟩
  let t0 : Fin n := Classical.choose hlarge.2.2.2
  have ht0spec := Classical.choose_spec hlarge.2.2.2
  have ht0 : t0 ∈ P ∩ B.T := ht0spec.1
  let tau : Finset (Fin n) := Classical.choose ht0spec.2
  have htausub : tau ⊆ P \ {B.a, t0} := (Classical.choose_spec ht0spec.2).1
  have htaucard : tau.card = P.card - r := (Classical.choose_spec ht0spec.2).2
  have htau : perturbedStarTau B P = tau := by
    simp only [perturbedStarTau, dif_neg hnotproper, dif_neg hnotfinal,
      dif_neg hnotsmall, dif_neg hnotavoid, dif_pos hlarge]
    rfl
  have htau_sub_P : tau ⊆ P := fun x hx => Finset.mem_sdiff.mp (htausub hx) |>.1
  have htau_not_a : B.a ∉ tau := by
    intro ha_tau
    have : B.a ∉ {B.a, t0} := Finset.mem_sdiff.mp (htausub ha_tau) |>.2
    exact this (by simp)
  have htau_not_t0 : t0 ∉ tau := by
    intro ht0_tau
    have : t0 ∉ {B.a, t0} := Finset.mem_sdiff.mp (htausub ht0_tau) |>.2
    exact this (by simp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htau]
    apply (Finset.ssubset_iff_subset_ne).mpr
    refine ⟨htau_sub_P, ?_⟩
    intro hEq
    have ha_tau : B.a ∈ tau := by
      rw [hEq]
      exact ha
    exact htau_not_a ha_tau
  · rw [htau, htaucard, ← hr]
    omega
  · rw [htau, htaucard]
    have hle := hbase.2
    omega
  · rintro ⟨Q, hQ, hQP, _⟩
    rw [htau] at hQP
    have hQcases :
        ((Q ⊆ insert B.a (insert B.b (B.T ∪ B.L)) ∧ B.a ∈ Q ∧
            Q.card ≤ d + 1) ∧
          ∀ Z ⊆ B.L, Z ≠ B.L → ¬ insert B.a (B.T ∪ Z) = Q) ∨
        ∃ Z ⊆ B.L, insert B.b (B.T ∪ Z) = Q := by
      simpa [perturbedStarPatterns, perturbedStarCore] using hQ
    rcases hQcases with hbaseQ | hinsertion
    · have haQ : B.a ∈ Q := hbaseQ.1.2.1
      have ha_inter : B.a ∈ Q ∩ P := Finset.mem_inter.mpr ⟨haQ, ha⟩
      rw [hQP] at ha_inter
      exact htau_not_a ha_inter
    · rcases hinsertion with ⟨Z, _, hQeq⟩
      have ht0Q : t0 ∈ Q := by
        rw [← hQeq]
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_inter.mp ht0).2)
      have ht0inter : t0 ∈ Q ∩ P :=
        Finset.mem_inter.mpr ⟨ht0Q, (Finset.mem_inter.mp ht0).1⟩
      rw [hQP] at ht0inter
      exact htau_not_t0 ht0inter
```

## Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

## Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_erase_of_mem`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.exists_subset_card_eq`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

## Sources

- `article/sections/02_proof.tex:72-72`

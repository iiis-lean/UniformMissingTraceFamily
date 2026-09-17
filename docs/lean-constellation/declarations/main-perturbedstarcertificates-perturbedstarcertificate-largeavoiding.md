[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `perturbedStarCertificate_largeAvoiding`

The tau certificate satisfies the generic criterion for a large a-anchored pattern avoiding T.

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_largeAvoiding`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For natural numbers `d`, `s`, `n`, and `r`, let `B : PerturbedStarBlocks n r` and `P : Finset (Fin n)`. Assume `P ∈ perturbedStarPatterns d B`, `B.a ∈ P`, `r < P.card`, `P ∩ B.T = ∅`, `r = d + 1 - s`, and `2 ≤ r`. The accepted fourth selector branch applies: `perturbedStarTau B P` is the chosen subset of `P ∩ B.L` of cardinality `P.card - r`. Then the following four-clause certificate bundle holds:

1. `perturbedStarTau B P ⊂ P`.
2. `P.card - (perturbedStarTau B P).card ≤ d + 1 - s`.
3. `(perturbedStarTau B P).card ≤ s`.
4. There is no `Q ∈ perturbedStarPatterns d B` such that both `Q ∩ P = perturbedStarTau B P` and `Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s)`.

This is the distinct large a-anchored case avoiding `T`: the selected subset omits the anchor, while any competing base pattern contains the anchor and any inserted pattern exceeds the permitted size threshold.

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
# lean-constellation target: `perturbedStarCertificate_largeAvoiding`

For natural numbers `d`, `s`, `n`, and `r`, let `B : PerturbedStarBlocks n r` and `P : Finset (Fin
n)`. Assume `P ∈ perturbedStarPatterns d B`, `B.a ∈ P`, `r < P.card`, `P ∩ B.T = ∅`, `r = d + 1 -
s`, and `2 ≤ r`. The accepted fourth selector branch applies: `perturbedStarTau B P` is the chosen
subset of `P ∩ B.L` of cardinality `P.card - r`. Then the following four-clause certificate bundle
holds:

1. `perturbedStarTau B P ⊂ P`.
2. `P.card - (perturbedStarTau B P).card ≤ d + 1 - s`.
3. `(perturbedStarTau B P).card ≤ s`.
4. There is no `Q ∈ perturbedStarPatterns d B` such that both `Q ∩ P = perturbedStarTau B P` and
`Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s)`.

This is the distinct large a-anchored case avoiding `T`: the selected subset omits the anchor, while
any competing base pattern contains the anchor and any inserted pattern exceeds the permitted size
threshold.

## Sources

- Source `article/sections/02_proof.tex`, lines 67–70

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
- `Main.PerturbedStarCertificates::perturbedStarTau` → `perturbedStarTau` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau`
-/
theorem perturbedStarCertificate_largeAvoiding (d s n r : ℕ)
    (B : PerturbedStarBlocks n r) (P : Finset (Fin n))
    (hP : P ∈ perturbedStarPatterns d B) (ha : B.a ∈ P)
    (hrlt : r < P.card) (havoid : P ∩ B.T = ∅)
    (hr : r = d + 1 - s) (hrtwo : 2 ≤ r) :
    perturbedStarTau B P ⊂ P ∧
      P.card - (perturbedStarTau B P).card ≤ d + 1 - s ∧
      (perturbedStarTau B P).card ≤ s ∧
      ¬ ∃ Q ∈ perturbedStarPatterns d B,
        Q ∩ P = perturbedStarTau B P ∧
          Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s) := by
  sorry
```

## Proof NL

Write `R := P ∩ B.L`. First unfold `perturbedStarPatterns` at `hP`. The inserted branch is impossible because every inserted set is `{B.b} ∪ B.T ∪ Z` with `Z ⊆ B.L`, hence omits `B.a` by `B.a_ne_b`, `B.a_not_mem_T`, and `B.a_not_mem_L`, contrary to `ha`. Thus `P` is in the bounded a-anchored base-minus-deleted component. Retain
```
hcore : P ⊆ perturbedStarCore B,   hbasecard : P.card ≤ d + 1.
```
Unfolding `perturbedStarCore` and using `havoid : P ∩ B.T = ∅`, every element of `P \\ B.L` is one of the two anchors `B.a,B.b`. Hence
```
P \\ B.L ⊆ {B.a, B.b},   (P \\ B.L).card ≤ 2.
```
The partition identity `Finset.card_inter_add_card_sdiff P B.L`, together with `hrtwo : 2 ≤ r`, gives
```
P.card - r ≤ R.card.
```
Use `Finset.exists_subset_card_eq` only to establish the fourth selector guard:
```
hExists : ∃ Q, Q ⊆ P ∩ B.L ∧ Q.card = P.card - r.
```

Define the exact guard proof
```
hlarge : B.a ∈ P ∧ r < P.card ∧ P ∩ B.T = ∅ ∧ hExists
  := ⟨ha, hrlt, havoid, hExists⟩,
tau := Classical.choose hlarge.2.2.2.
```
This `tau` is deliberately the canonical value used by the definition, not an arbitrary witness. From `Classical.choose_spec hlarge.2.2.2`, retain
```
htau_sub : tau ⊆ P ∩ B.L,
htau_card : tau.card = P.card - r.
```
The two earlier selector guards are false because `B.a ∈ P` whereas both added forms omit `B.a`; the small-star guard is false by `hrlt : r < P.card`. Unfold `perturbedStarTau` with those false guards and the true guard `hlarge`. Its large-avoiding branch returns `Classical.choose hlarge.2.2.2`, so obtain the definitional selector equality
```
htau : perturbedStarTau B P = tau.
```
Rewrite the requested four clauses by `htau`; every subsequent assertion is about this canonical selector.

Since `htau_sub` places `tau` in `P ∩ B.L`, it is a subset of `P`, but it omits `B.a` because `B.a_not_mem_L` while `ha : B.a ∈ P`; hence `tau ⊂ P`. Its chosen cardinality and `hrlt` give
```
P.card - tau.card = r.
```
Rewrite `r` with `hr` for the gap clause. For the tau-size clause, `hbasecard` and `r < P.card` give `r < d+1`; after `hr`, natural-number arithmetic derives
```
tau.card = P.card - r ≤ s.
```

For the exclusion clause, assume `Q ∈ perturbedStarPatterns d B`, `Q ∩ P = tau`, and `Q.card ≤ tau.card + r`. Unfold the pattern definition.

* A base-minus-deleted `Q` contains `B.a`, while `B.a ∈ P` but `B.a ∉ tau` by `htau_sub` and `B.a_not_mem_L`. Thus its intersection cannot equal `tau`.

* An inserted `Q` has the form `{B.b} ∪ B.T ∪ Z`. From `Q ∩ P = tau` and `htau_sub.1`, obtain `tau ⊆ Q`; independently `B.T ⊆ Q`. The block `B.T`, the canonical `tau ⊆ B.L`, and `B.b` are pairwise disjoint by the anchor-avoidance fields and `B.T_disjoint_L` (using `Finset.disjoint_left`). Hence `Finset.card_union_of_disjoint` and `Finset.card_le_card` give
  ```
  tau.card + r + 1 ≤ Q.card,
  ```
  contradicting `Q.card ≤ tau.card + r`.

This proves the fourth clause. Rewriting back by `htau` supplies the exact requested four-clause bundle.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarCertificate_largeAvoiding`

For natural numbers `d`, `s`, `n`, and `r`, let `B : PerturbedStarBlocks n r` and `P : Finset (Fin
n)`. Assume `P ∈ perturbedStarPatterns d B`, `B.a ∈ P`, `r < P.card`, `P ∩ B.T = ∅`, `r = d + 1 -
s`, and `2 ≤ r`. The accepted fourth selector branch applies: `perturbedStarTau B P` is the chosen
subset of `P ∩ B.L` of cardinality `P.card - r`. Then the following four-clause certificate bundle
holds:

1. `perturbedStarTau B P ⊂ P`.
2. `P.card - (perturbedStarTau B P).card ≤ d + 1 - s`.
3. `(perturbedStarTau B P).card ≤ s`.
4. There is no `Q ∈ perturbedStarPatterns d B` such that both `Q ∩ P = perturbedStarTau B P` and
`Q.card ≤ (perturbedStarTau B P).card + (d + 1 - s)`.

This is the distinct large a-anchored case avoiding `T`: the selected subset omits the anchor, while
any competing base pattern contains the anchor and any inserted pattern exceeds the permitted size
threshold.

## Sources

- Source `article/sections/02_proof.tex`, lines 67–70

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
- `Main.PerturbedStarCertificates::perturbedStarTau` → `perturbedStarTau` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau`

## Proof outline

Write `R := P ∩ B.L`. First unfold `perturbedStarPatterns` at `hP`. The inserted branch is
impossible because every inserted set is `{B.b} ∪ B.T ∪ Z` with `Z ⊆ B.L`, hence omits `B.a` by
`B.a_ne_b`, `B.a_not_mem_T`, and `B.a_not_mem_L`, contrary to `ha`. Thus `P` is in the bounded
a-anchored base-minus-deleted component. Retain
```
hcore : P ⊆ perturbedStarCore B,   hbasecard : P.card ≤ d + 1.
```
Unfolding `perturbedStarCore` and using `havoid : P ∩ B.T = ∅`, every element of `P \\ B.L` is one
of the two anchors `B.a,B.b`. Hence
```
P \\ B.L ⊆ {B.a, B.b},   (P \\ B.L).card ≤ 2.
```
The partition identity `Finset.card_inter_add_card_sdiff P B.L`, together with `hrtwo : 2 ≤ r`,
gives
```
P.card - r ≤ R.card.
```
Use `Finset.exists_subset_card_eq` only to establish the fourth selector guard:
```
hExists : ∃ Q, Q ⊆ P ∩ B.L ∧ Q.card = P.card - r.
```

Define the exact guard proof
```
hlarge : B.a ∈ P ∧ r < P.card ∧ P ∩ B.T = ∅ ∧ hExists
  := ⟨ha, hrlt, havoid, hExists⟩,
tau := Classical.choose hlarge.2.2.2.
```
This `tau` is deliberately the canonical value used by the definition, not an arbitrary witness.
From `Classical.choose_spec hlarge.2.2.2`, retain
```
htau_sub : tau ⊆ P ∩ B.L,
htau_card : tau.card = P.card - r.
```
The two earlier selector guards are false because `B.a ∈ P` whereas both added forms omit `B.a`; the
small-star guard is false by `hrlt : r < P.card`. Unfold `perturbedStarTau` with those false guards
and the true guard `hlarge`. Its large-avoiding branch returns `Classical.choose hlarge.2.2.2`, so
obtain the definitional selector equality
```
htau : perturbedStarTau B P = tau.
```
Rewrite the requested four clauses by `htau`; every subsequent assertion is about this canonical
selector.

Since `htau_sub` places `tau` in `P ∩ B.L`, it is a subset of `P`, but it omits `B.a` because
`B.a_not_mem_L` while `ha : B.a ∈ P`; hence `tau ⊂ P`. Its chosen cardinality and `hrlt` give
```
P.card - tau.card = r.
```
Rewrite `r` with `hr` for the gap clause. For the tau-size clause, `hbasecard` and `r < P.card` give
`r < d+1`; after `hr`, natural-number arithmetic derives
```
tau.card = P.card - r ≤ s.
```

For the exclusion clause, assume `Q ∈ perturbedStarPatterns d B`, `Q ∩ P = tau`, and `Q.card ≤
tau.card + r`. Unfold the pattern definition.

* A base-minus-deleted `Q` contains `B.a`, while `B.a ∈ P` but `B.a ∉ tau` by `htau_sub` and
`B.a_not_mem_L`. Thus its intersection cannot equal `tau`.

* An inserted `Q` has the form `{B.b} ∪ B.T ∪ Z`. From `Q ∩ P = tau` and `htau_sub.1`, obtain `tau ⊆
Q`; independently `B.T ⊆ Q`. The block `B.T`, the canonical `tau ⊆ B.L`, and `B.b` are pairwise
disjoint by the anchor-avoidance fields and `B.T_disjoint_L` (using `Finset.disjoint_left`). Hence
`Finset.card_union_of_disjoint` and `Finset.card_le_card` give
  ```
  tau.card + r + 1 ≤ Q.card,
  ```
  contradicting `Q.card ≤ tau.card + r`.

This proves the fourth clause. Rewriting back by `htau` supplies the exact requested four-clause
bundle.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 67–70

## Proof dependencies

- `Finset.card_inter_add_card_sdiff` from `Mathlib.Data.Finset.Card`
- `Finset.card_le_card` from `Mathlib.Data.Finset.Card`
- `Finset.card_union_of_disjoint` from `Mathlib.Data.Finset.Card`
- `Finset.exists_subset_card_eq` from `Mathlib.Data.Finset.Card`
- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
- `Main.PerturbedStarCertificates::perturbedStarTau` → `perturbedStarTau` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau`
-/
theorem perturbedStarCertificate_largeAvoiding (d s n r : ℕ)
    (B : PerturbedStarBlocks n r) (P : Finset (Fin n))
    (hP : P ∈ perturbedStarPatterns d B) (ha : B.a ∈ P)
    (hrlt : r < P.card) (havoid : P ∩ B.T = ∅)
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
  have hPdiffsub : P \ B.L ⊆ {B.a, B.b} := by
    intro x hx
    have hxP : x ∈ P := Finset.mem_sdiff.mp hx |>.1
    have hxnotL : x ∉ B.L := Finset.mem_sdiff.mp hx |>.2
    have hxcore := hbase.1 hxP
    simp only [Finset.mem_insert, Finset.mem_union] at hxcore
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hxcore with hxa | hxb | hxT | hxL
    · exact Or.inl hxa
    · exact Or.inr hxb
    · have hxinter : x ∈ P ∩ B.T := Finset.mem_inter.mpr ⟨hxP, hxT⟩
      rw [havoid] at hxinter
      simp at hxinter
    · exact False.elim (hxnotL hxL)
  have hPdiffcard : (P \ B.L).card ≤ 2 := by
    calc
      (P \ B.L).card ≤ ({B.a, B.b} : Finset (Fin n)).card :=
        Finset.card_le_card hPdiffsub
      _ ≤ 2 := by
        calc
          ({B.a, B.b} : Finset (Fin n)).card ≤
              ({B.b} : Finset (Fin n)).card + 1 := Finset.card_insert_le _ _
          _ = 2 := by simp
  have hRcard : P.card - r ≤ (P ∩ B.L).card := by
    have hpartition := Finset.card_inter_add_card_sdiff P B.L
    omega
  obtain ⟨witness, hwitnesssub, hwitnesscard⟩ :=
    Finset.exists_subset_card_eq hRcard
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
  have hlarge :
      B.a ∈ P ∧ r < P.card ∧ P ∩ B.T = ∅ ∧
        ∃ Q, Q ⊆ P ∩ B.L ∧ Q.card = P.card - r :=
    ⟨ha, hrlt, havoid, ⟨witness, hwitnesssub, hwitnesscard⟩⟩
  let tau : Finset (Fin n) := Classical.choose hlarge.2.2.2
  have htausub : tau ⊆ P ∩ B.L := (Classical.choose_spec hlarge.2.2.2).1
  have htaucard : tau.card = P.card - r :=
    (Classical.choose_spec hlarge.2.2.2).2
  have htau : perturbedStarTau B P = tau := by
    simp only [perturbedStarTau, dif_neg hnotproper, dif_neg hnotfinal,
      dif_neg hnotsmall, dif_pos hlarge]
    rfl
  have htau_sub_P : tau ⊆ P := fun x hx =>
    (Finset.mem_inter.mp (htausub hx)).1
  have htau_not_a : B.a ∉ tau := by
    intro ha_tau
    exact B.a_not_mem_L (Finset.mem_inter.mp (htausub ha_tau)).2
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
  · rintro ⟨Q, hQ, hQP, hQcard⟩
    rw [htau] at hQP hQcard
    rw [← hr] at hQcard
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
    · rcases hinsertion with ⟨Z, hZsub, hQeq⟩
      have htau_sub_Q : tau ⊆ Q := by
        intro x hx
        have hxP : x ∈ P := htau_sub_P hx
        have hxinter : x ∈ Q ∩ P := by
          rw [hQP]
          exact hx
        exact Finset.mem_inter.mp hxinter |>.1
      have hTsubQ : B.T ⊆ Q := by
        intro x hxT
        rw [← hQeq]
        simp [hxT]
      have hTtau : Disjoint B.T tau := by
        rw [Finset.disjoint_left]
        intro x hxT hxtau
        exact Finset.disjoint_left.mp B.T_disjoint_L hxT
          (Finset.mem_inter.mp (htausub hxtau)).2
      have hbtau : Disjoint ({B.b} : Finset (Fin n)) tau := by
        rw [Finset.disjoint_left]
        intro x hxb hxtau
        have hx_eq : x = B.b := Finset.mem_singleton.mp hxb
        subst x
        exact B.b_not_mem_L (Finset.mem_inter.mp (htausub hxtau)).2
      have hbT : Disjoint ({B.b} : Finset (Fin n)) B.T := by
        rw [Finset.disjoint_left]
        intro x hxb hxT
        have hx_eq : x = B.b := Finset.mem_singleton.mp hxb
        subst x
        exact B.b_not_mem_T hxT
      have hbtauT : Disjoint ({B.b} ∪ B.T) tau := by
        rw [Finset.disjoint_left]
        intro x hx hxtau
        rcases Finset.mem_union.mp hx with hxb | hxT
        · exact Finset.disjoint_left.mp hbtau hxb hxtau
        · exact Finset.disjoint_left.mp hTtau hxT hxtau
      have hcardUnion : ({B.b} ∪ B.T ∪ tau).card = 1 + r + tau.card := by
        calc
          ({B.b} ∪ B.T ∪ tau).card = ({B.b} ∪ B.T).card + tau.card :=
            Finset.card_union_of_disjoint hbtauT
          _ = ({B.b} : Finset (Fin n)).card + B.T.card + tau.card := by
            rw [Finset.card_union_of_disjoint hbT]
          _ = 1 + r + tau.card := by simp [B.card_T]
      have hUnionSub : {B.b} ∪ B.T ∪ tau ⊆ Q := by
        intro x hx
        rcases Finset.mem_union.mp hx with hxbT | hxtau
        · rcases Finset.mem_union.mp hxbT with hxb | hxT
          · rw [← hQeq]
            have hx_eq : x = B.b := Finset.mem_singleton.mp hxb
            subst x
            exact Finset.mem_insert_self B.b (B.T ∪ Z)
          · exact hTsubQ hxT
        · exact htau_sub_Q hxtau
      have hUnionCard := Finset.card_le_card hUnionSub
      omega
```

## Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

## Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_inter_add_card_sdiff`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_le_card`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_union_of_disjoint`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.exists_subset_card_eq`
- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

## Sources

- `article/sections/02_proof.tex:67-70`

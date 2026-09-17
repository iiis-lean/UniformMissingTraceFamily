[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `perturbedStar_isUniformMissingTraceFamily`

The explicit perturbed-star construction yields a uniform family with the fixed missing-trace property.

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStar_isUniformMissingTraceFamily`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For natural numbers `d`, `s`, and `n`, assume `hd : 4 ≤ d`, `hslow : (d + 3) / 2 ≤ s`, `hshigh : s ≤ d - 1`, and `hn : 2 * (d + 1) ≤ n`. Then there exists construction data

`B : PerturbedStarBlocks n (d + 1 - s)`

such that

`IsUniformMissingTraceFamily d s (perturbedStarFamily d B)`.

The existential construction preserves the explicit perturbed-star family needed by downstream counting; its missing-trace certificate is supplied by the five separate source cases through the generic pattern-family criterion.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFamily
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStar_isUniformMissingTraceFamily`

For natural numbers `d`, `s`, and `n`, assume `hd : 4 ≤ d`, `hslow : (d + 3) / 2 ≤ s`, `hshigh : s ≤
d - 1`, and `hn : 2 * (d + 1) ≤ n`. Then there exists construction data

`B : PerturbedStarBlocks n (d + 1 - s)`

such that

`IsUniformMissingTraceFamily d s (perturbedStarFamily d B)`.

The existential construction preserves the explicit perturbed-star family needed by downstream
counting; its missing-trace certificate is supplied by the five separate source cases through the
generic pattern-family criterion.

## Sources

- Source `article/sections/02_proof.tex`, lines 30–39
- Source `article/sections/02_proof.tex`, lines 53–73

## Statement dependencies

- `Main.PatternCriterion::IsUniformMissingTraceFamily` → `IsUniformMissingTraceFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.IsUniformMissingTraceFamily`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarFamily` → `perturbedStarFamily` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFamily`
-/
theorem perturbedStar_isUniformMissingTraceFamily (d s n : ℕ) (hd : 4 ≤ d)
    (hslow : (d + 3) / 2 ≤ s) (hshigh : s ≤ d - 1)
    (hn : 2 * (d + 1) ≤ n) :
    ∃ B : PerturbedStarBlocks n (d + 1 - s),
      IsUniformMissingTraceFamily d s (perturbedStarFamily d B) := by
  sorry
```

## Proof NL

Put `r := d + 1 - s`. Apply `perturbedStarParameterBounds d s n hd hslow hshigh hn` and retain
```
hrtwo : 2 ≤ r,  hrs : r + 1 ≤ s,  hroom : 2 + 2*r ≤ n.
```
(The theorem’s truncation-safe equality and `2*r≤d` remain available but are not needed in this final assembly.)  Extract `B : PerturbedStarBlocks n r` from `exists_perturbedStarBlocks n r hroom`, and use this exact witness for the existential conclusion.

Unfold `perturbedStarFamily` at the final step and apply the visible theorem
`patternFamily_isUniformMissingTraceFamily` with
```
C := perturbedStarCore B,
U := perturbedStarFiller B,
patterns := perturbedStarPatterns d B,
tau := perturbedStarTau B.
```
For the first premise, use `perturbedStarFiller B = Finset.univ \\ perturbedStarCore B` and `Finset.disjoint_left`: a point in the core cannot belong to its complement.  For the second, unfold `perturbedStarPatterns`.  A base-minus-deleted pattern carries the base containment in `perturbedStarCore B`; an inserted pattern is `{B.b} ∪ B.T ∪ Y` for `Y ⊆ B.L`, hence lies in `{B.a,B.b} ∪ B.T ∪ B.L = perturbedStarCore B`.

For the generic theorem’s universal four-clause certificate premise, fix `P ∈ perturbedStarPatterns d B` and expose the accepted base-minus-deleted versus inserted definition branches.

* An inserted branch has `Y ⊆ B.L` and `P = {B.b} ∪ B.T ∪ Y`.  If `Y = B.L`, substitute and invoke `perturbedStarCertificate_finalAdded d s n r B hr hrtwo hrs`.  If `Y ≠ B.L`, substitute and invoke `perturbedStarCertificate_addedProper d s n r B Y hYsub hYne hr hrtwo hrs`.
* A base-minus-deleted branch supplies `B.a ∈ P` and `P.card ≤ d+1`.  Split on `P.card ≤ r` and invoke `perturbedStarCertificate_smallStar d s n r B P hP ha hcard hr`.  Otherwise obtain `r < P.card`; split on `P ∩ B.T = ∅`.  The empty case is `perturbedStarCertificate_largeAvoiding`, and the nonempty case is `perturbedStarCertificate_largeMeeting`, both applied with `hP, ha, hrlt, hr, hrtwo` and their corresponding intersection hypothesis.

These cases exhaust the exact accepted pattern definition and yield the required properness, gap, selector-cardinality, and excluded-intersection bundle.  The generic conclusion is definitionally `IsUniformMissingTraceFamily d s (perturbedStarFamily d B)`, so it closes the unchanged existential theorem.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import Mathlib.Data.Finset.Disjoint
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFamily
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.exists_perturbedStarBlocks
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_addedProper
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_finalAdded
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_largeAvoiding
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_largeMeeting
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_smallStar
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarParameterBounds
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStar_isUniformMissingTraceFamily`

For natural numbers `d`, `s`, and `n`, assume `hd : 4 ≤ d`, `hslow : (d + 3) / 2 ≤ s`, `hshigh : s ≤
d - 1`, and `hn : 2 * (d + 1) ≤ n`. Then there exists construction data

`B : PerturbedStarBlocks n (d + 1 - s)`

such that

`IsUniformMissingTraceFamily d s (perturbedStarFamily d B)`.

The existential construction preserves the explicit perturbed-star family needed by downstream
counting; its missing-trace certificate is supplied by the five separate source cases through the
generic pattern-family criterion.

## Sources

- Source `article/sections/02_proof.tex`, lines 30–39
- Source `article/sections/02_proof.tex`, lines 53–73

## Statement dependencies

- `Main.PatternCriterion::IsUniformMissingTraceFamily` → `IsUniformMissingTraceFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.IsUniformMissingTraceFamily`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarFamily` → `perturbedStarFamily` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFamily`

## Proof outline

Put `r := d + 1 - s`. Apply `perturbedStarParameterBounds d s n hd hslow hshigh hn` and retain
```
hrtwo : 2 ≤ r,  hrs : r + 1 ≤ s,  hroom : 2 + 2*r ≤ n.
```
(The theorem’s truncation-safe equality and `2*r≤d` remain available but are not needed in this
final assembly.)  Extract `B : PerturbedStarBlocks n r` from `exists_perturbedStarBlocks n r hroom`,
and use this exact witness for the existential conclusion.

Unfold `perturbedStarFamily` at the final step and apply the visible theorem
`patternFamily_isUniformMissingTraceFamily` with
```
C := perturbedStarCore B,
U := perturbedStarFiller B,
patterns := perturbedStarPatterns d B,
tau := perturbedStarTau B.
```
For the first premise, use `perturbedStarFiller B = Finset.univ \\ perturbedStarCore B` and
`Finset.disjoint_left`: a point in the core cannot belong to its complement.  For the second, unfold
`perturbedStarPatterns`.  A base-minus-deleted pattern carries the base containment in
`perturbedStarCore B`; an inserted pattern is `{B.b} ∪ B.T ∪ Y` for `Y ⊆ B.L`, hence lies in
`{B.a,B.b} ∪ B.T ∪ B.L = perturbedStarCore B`.

For the generic theorem’s universal four-clause certificate premise, fix `P ∈ perturbedStarPatterns
d B` and expose the accepted base-minus-deleted versus inserted definition branches.

* An inserted branch has `Y ⊆ B.L` and `P = {B.b} ∪ B.T ∪ Y`.  If `Y = B.L`, substitute and invoke
`perturbedStarCertificate_finalAdded d s n r B hr hrtwo hrs`.  If `Y ≠ B.L`, substitute and invoke
`perturbedStarCertificate_addedProper d s n r B Y hYsub hYne hr hrtwo hrs`.
* A base-minus-deleted branch supplies `B.a ∈ P` and `P.card ≤ d+1`.  Split on `P.card ≤ r` and
invoke `perturbedStarCertificate_smallStar d s n r B P hP ha hcard hr`.  Otherwise obtain `r <
P.card`; split on `P ∩ B.T = ∅`.  The empty case is `perturbedStarCertificate_largeAvoiding`, and
the nonempty case is `perturbedStarCertificate_largeMeeting`, both applied with `hP, ha, hrlt, hr,
hrtwo` and their corresponding intersection hypothesis.

These cases exhaust the exact accepted pattern definition and yield the required properness, gap,
selector-cardinality, and excluded-intersection bundle.  The generic conclusion is definitionally
`IsUniformMissingTraceFamily d s (perturbedStarFamily d B)`, so it closes the unchanged existential
theorem.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 30–39
- Source `article/sections/02_proof.tex`, lines 53–73

## Proof dependencies

- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Main.PatternCriterion::patternFamily_isUniformMissingTraceFamily` →
  `patternFamily_isUniformMissingTraceFamily` from `UniformMissingTraceFamily.Main.PatternCriterion.
  Theorems.patternFamily_isUniformMissingTraceFamily`
- `Main.PerturbedStarCertificates::exists_perturbedStarBlocks` → `exists_perturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.exists_perturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCertificate_addedProper` →
  `perturbedStarCertificate_addedProper` from `UniformMissingTraceFamily.Main.PerturbedStarCertifica
  tes.Theorems.perturbedStarCertificate_addedProper`
- `Main.PerturbedStarCertificates::perturbedStarCertificate_finalAdded` →
  `perturbedStarCertificate_finalAdded` from `UniformMissingTraceFamily.Main.PerturbedStarCertificat
  es.Theorems.perturbedStarCertificate_finalAdded`
- `Main.PerturbedStarCertificates::perturbedStarCertificate_largeAvoiding` →
  `perturbedStarCertificate_largeAvoiding` from `UniformMissingTraceFamily.Main.PerturbedStarCertifi
  cates.Theorems.perturbedStarCertificate_largeAvoiding`
- `Main.PerturbedStarCertificates::perturbedStarCertificate_largeMeeting` →
  `perturbedStarCertificate_largeMeeting` from `UniformMissingTraceFamily.Main.PerturbedStarCertific
  ates.Theorems.perturbedStarCertificate_largeMeeting`
- `Main.PerturbedStarCertificates::perturbedStarCertificate_smallStar` →
  `perturbedStarCertificate_smallStar` from `UniformMissingTraceFamily.Main.PerturbedStarCertificate
  s.Theorems.perturbedStarCertificate_smallStar`
- `Main.PerturbedStarCertificates::perturbedStarParameterBounds` → `perturbedStarParameterBounds`
  from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarParameterBounds`
-/
theorem perturbedStar_isUniformMissingTraceFamily (d s n : ℕ) (hd : 4 ≤ d)
    (hslow : (d + 3) / 2 ≤ s) (hshigh : s ≤ d - 1)
    (hn : 2 * (d + 1) ≤ n) :
    ∃ B : PerturbedStarBlocks n (d + 1 - s),
      IsUniformMissingTraceFamily d s (perturbedStarFamily d B) := by
  classical
  rcases perturbedStarParameterBounds d s n hd hslow hshigh hn with
    ⟨hrtwo, hrs, _, _, hroom⟩
  obtain ⟨B⟩ := exists_perturbedStarBlocks n (d + 1 - s) hroom
  refine ⟨B, ?_⟩
  unfold perturbedStarFamily
  refine patternFamily_isUniformMissingTraceFamily (perturbedStarCore B)
    (perturbedStarFiller B) (perturbedStarPatterns d B) (perturbedStarTau B) ?_ ?_ ?_
  · rw [Finset.disjoint_left]
    intro x hxcore hxfiller
    simp only [perturbedStarFiller, Finset.mem_sdiff, Finset.mem_univ, true_and] at hxfiller
    exact hxfiller hxcore
  · intro P hP
    have hPcases :
        ((P ⊆ insert B.a (insert B.b (B.T ∪ B.L)) ∧ B.a ∈ P ∧
            P.card ≤ d + 1) ∧
          ∀ Y ⊆ B.L, Y ≠ B.L → ¬ insert B.a (B.T ∪ Y) = P) ∨
        ∃ Y ⊆ B.L, insert B.b (B.T ∪ Y) = P := by
      simpa [perturbedStarPatterns, perturbedStarCore] using hP
    rcases hPcases with hbase | hinserted
    · simpa [perturbedStarCore, Finset.union_assoc] using hbase.1.1
    · rcases hinserted with ⟨Y, hYsub, hYP⟩
      intro x hx
      rw [← hYP] at hx
      simp only [Finset.mem_insert, Finset.mem_union] at hx
      simp only [perturbedStarCore, Finset.mem_insert, Finset.mem_union,
        Finset.mem_singleton]
      rcases hx with hxb | hxTY
      · exact Or.inl (Or.inl (Or.inr hxb))
      · rcases hxTY with hxT | hxY
        · exact Or.inl (Or.inr hxT)
        · exact Or.inr (hYsub hxY)
  · intro P hP
    have hPcases :
        ((P ⊆ insert B.a (insert B.b (B.T ∪ B.L)) ∧ B.a ∈ P ∧
            P.card ≤ d + 1) ∧
          ∀ Y ⊆ B.L, Y ≠ B.L → ¬ insert B.a (B.T ∪ Y) = P) ∨
        ∃ Y ⊆ B.L, insert B.b (B.T ∪ Y) = P := by
      simpa [perturbedStarPatterns, perturbedStarCore] using hP
    rcases hPcases with hbase | hinserted
    · have ha : B.a ∈ P := hbase.1.2.1
      by_cases hsmall : P.card ≤ d + 1 - s
      · exact perturbedStarCertificate_smallStar d s n (d + 1 - s) B P hP ha hsmall rfl
      · have hrlt : d + 1 - s < P.card := Nat.lt_of_not_ge hsmall
        by_cases havoid : P ∩ B.T = ∅
        · exact perturbedStarCertificate_largeAvoiding d s n (d + 1 - s) B P hP ha hrlt
            havoid rfl hrtwo
        · exact perturbedStarCertificate_largeMeeting d s n (d + 1 - s) B P hP ha hrlt
            havoid rfl hrtwo
    · rcases hinserted with ⟨Y, hYsub, hYP⟩
      by_cases hYeq : Y = B.L
      · subst Y
        rw [← hYP]
        simpa [Finset.union_assoc] using
          (perturbedStarCertificate_finalAdded d s n (d + 1 - s) B rfl hrtwo hrs)
      · rw [← hYP]
        simpa [Finset.union_assoc] using
          (perturbedStarCertificate_addedProper d s n (d + 1 - s) B Y hYsub hYeq rfl hrtwo hrs)
```

## Statement dependencies

- `current repo:Main.PatternCriterion.IsUniformMissingTraceFamily`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFamily`

## Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `current repo:Main.PatternCriterion.patternFamily_isUniformMissingTraceFamily`
- `current repo:Main.PerturbedStarCertificates.exists_perturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCertificate_addedProper`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCertificate_finalAdded`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCertificate_largeAvoiding`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCertificate_largeMeeting`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCertificate_smallStar`
- `current repo:Main.PerturbedStarCertificates.perturbedStarParameterBounds`

## Sources

- `article/sections/02_proof.tex:30-39`
- `article/sections/02_proof.tex:53-73`

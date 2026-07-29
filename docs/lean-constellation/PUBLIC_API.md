# Public API

- Repository completion: `graph_proved`
- Proof availability: `proved`

## `anchoredPowerset_weightedSum_eq_chooseSum`

Rewrites a filtered anchored-powerset filler-weight sum as its exact binomial convolution.

- Kind: `theorem`
- Node: `Main.AnchoredPowersetEnumeration`
- Module: `UniformMissingTraceFamily.Main.AnchoredPowersetEnumeration.Theorems.anchoredPowerset_weightedSum_eq_chooseSum`
- Status: `proved` (`committed`)
- Formal code: final proof projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.AnchoredPowersetEnumeration.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import UniformMissingTraceFamily.Main.AnchoredPowersetEnumeration.Theorems.anchoredPowerset_sum_erase
import UniformMissingTraceFamily.Main.AnchoredPowersetEnumeration.Theorems.powerset_weightedSum_eq_chooseSum
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `anchoredPowerset_weightedSum_eq_chooseSum`

Let α be a type with `[DecidableEq α]`. For every finsets `C U : Finset α`, anchor `a : α`, natural
`d`, and proof `ha : a ∈ C`, the weighted filtered anchored-powerset sum equals the
cardinality-fiber binomial convolution:

`∑ P ∈ C.powerset.filter (fun P => a ∈ P ∧ P.card ≤ d + 1), Nat.choose U.card (d + 1 - P.card) = ∑ j
∈ Finset.range (d + 1), Nat.choose (C.erase a).card j * Nat.choose U.card (d - j)`.

No disjointness, cardinality, or ambient-size assumptions are required. The bounds and both
subtraction expressions are natural-number expressions exactly as displayed.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Finset.filter` from `Mathlib.Data.Finset.Filter`
- `Finset.powerset` from `Mathlib.Data.Finset.Powerset`
- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`

## Proof outline

First split the conjunction in the left-hand filter into the anchored filter followed by the
cardinality filter; this is a direct extensional simplification of finsets. Apply
`Finset.sum_filter` to the second filter, with the zero-extended weight
`F P := if P.card ≤ d + 1 then Nat.choose U.card (d + 1 - P.card) else 0`.
Then apply the committed theorem `anchoredPowerset_sum_erase C a ha F`. This reindexes the sum over
anchored subsets as a sum over `T ∈ (C.erase a).powerset` of `F (insert a T)`.

For such a target member, `Finset.mem_powerset` gives `T ⊆ C.erase a`, hence `a ∉ T`. Use
`Finset.card_erase_add_one` on `insert a T`, together with `Finset.erase_insert`, to obtain the
cardinality shift
`(insert a T).card = T.card + 1`.
Consequently `(insert a T).card ≤ d + 1` is equivalent to `T.card ≤ d`, and the exact subtraction
rewrites as
`d + 1 - (insert a T).card = d - T.card`.
Thus the reindexed zero-extended summand is
`if T.card ≤ d then Nat.choose U.card (d - T.card) else 0`.

Use `Finset.sum_filter` in the reverse direction to turn this back into the filtered sum over
`(C.erase a).powerset.filter (fun T => T.card ≤ d)`. The accepted theorem
`powerset_weightedSum_eq_chooseSum (C.erase a) U d` then evaluates it as
`∑ j ∈ Finset.range (d + 1), Nat.choose (C.erase a).card j * Nat.choose U.card (d - j)`.
This is precisely the stated right-hand side, with no extra hypotheses or normalization.

## Proof dependencies

- `Finset.sum_filter` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.erase_insert` from `Mathlib.Data.Finset.Basic`
- `Finset.card_erase_add_one` from `Mathlib.Data.Finset.Card`
- `Finset.mem_powerset` from `Mathlib.Data.Finset.Powerset`
- `Main.AnchoredPowersetEnumeration::anchoredPowerset_sum_erase` → `anchoredPowerset_sum_erase` from
  `UniformMissingTraceFamily.Main.AnchoredPowersetEnumeration.Theorems.anchoredPowerset_sum_erase`
- `Main.AnchoredPowersetEnumeration::powerset_weightedSum_eq_chooseSum` →
  `powerset_weightedSum_eq_chooseSum` from `UniformMissingTraceFamily.Main.AnchoredPowersetEnumerati
  on.Theorems.powerset_weightedSum_eq_chooseSum`
-/
theorem anchoredPowerset_weightedSum_eq_chooseSum {α : Type*} [DecidableEq α]
    (C U : Finset α) (a : α) (d : ℕ) (ha : a ∈ C) :
    ∑ P ∈ C.powerset.filter (fun P => a ∈ P ∧ P.card ≤ d + 1),
        Nat.choose U.card (d + 1 - P.card) =
      ∑ j ∈ Finset.range (d + 1),
        Nat.choose (C.erase a).card j * Nat.choose U.card (d - j) := by
  let F : Finset α → ℕ := fun P =>
    if P.card ≤ d + 1 then Nat.choose U.card (d + 1 - P.card) else 0
  calc
    ∑ P ∈ C.powerset.filter (fun P => a ∈ P ∧ P.card ≤ d + 1),
          Nat.choose U.card (d + 1 - P.card) =
        ∑ P ∈ (C.powerset.filter (fun P => a ∈ P)).filter (fun P => P.card ≤ d + 1),
          Nat.choose U.card (d + 1 - P.card) := by
          simp only [Finset.filter_filter]
    _ =
        ∑ P ∈ C.powerset.filter (fun P => a ∈ P), F P := by
          simpa [F] using
            (Finset.sum_filter
              (s := C.powerset.filter (fun P => a ∈ P))
              (p := fun P => P.card ≤ d + 1)
              (f := fun P => Nat.choose U.card (d + 1 - P.card)))
    _ = ∑ T ∈ (C.erase a).powerset, F (insert a T) :=
      anchoredPowerset_sum_erase C a ha F
    _ = ∑ T ∈ (C.erase a).powerset.filter (fun T => T.card ≤ d),
          Nat.choose U.card (d - T.card) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro T hT
          have hnot : a ∉ T := by
            intro hat
            exact (Finset.mem_erase.mp ((Finset.mem_powerset.mp hT) hat)).1 rfl
          have hcard : (insert a T).card = T.card + 1 := by
            rw [← Finset.card_erase_add_one (Finset.mem_insert_self a T),
              Finset.erase_insert hnot]
          have hle : T.card + 1 ≤ d + 1 ↔ T.card ≤ d := by omega
          have hsub : d + 1 - (T.card + 1) = d - T.card := by omega
          simp [F, hcard, hle, hsub]
    _ = ∑ j ∈ Finset.range (d + 1),
          Nat.choose (C.erase a).card j * Nat.choose U.card (d - j) :=
      powerset_weightedSum_eq_chooseSum (C.erase a) U d
```

### Statement dependencies

- `Mathlib:Mathlib.Data.Finset.Filter.Finset.filter`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.powerset`
- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose`

### Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_filter`
- `Mathlib:Mathlib.Data.Finset.Basic.Finset.erase_insert`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_erase_add_one`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.mem_powerset`
- `current repo:Main.AnchoredPowersetEnumeration.anchoredPowerset_sum_erase`
- `current repo:Main.AnchoredPowersetEnumeration.powerset_weightedSum_eq_chooseSum`

### Sources

- `article/sections/02_proof.tex:49-49`

## `exists_uniformMissingTraceFamily_strictlyLargerThanStar`

In the middle parameter range, an explicit uniform missing-trace family has the exact perturbed-star cardinality and strictly exceeds a star.

- Kind: `theorem`
- Node: `Main.CountingAndMain`
- Module: `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.exists_uniformMissingTraceFamily_strictlyLargerThanStar`
- Status: `proved` (`committed`)
- Formal code: final proof projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Nat.Choose.Basic
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarExtra_choose_pos
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarFamily_card
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `exists_uniformMissingTraceFamily_strictlyLargerThanStar`

For natural numbers `d`, `s`, and `n`, if `hd : 4 ≤ d`, `hslow : (d + 3) / 2 ≤ s`, `hshigh : s ≤ d -
1`, and `hn : 2 * (d + 1) ≤ n`, then there exists a family `family : Finset (Finset (Fin n))` such
that
`IsUniformMissingTraceFamily d s family ∧ family.card = Nat.choose (n - 1) d + Nat.choose (n - 2 *
(d + 1 - s) - 2) (2 * s - d - 2) ∧ Nat.choose (n - 1) d < family.card`.

## Sources

- Source `formal_target.lean`, lines 14–25
- Source `article/sections/02_proof.tex`, lines 75–79

## Statement dependencies

- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PatternCriterion::IsUniformMissingTraceFamily` → `IsUniformMissingTraceFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.IsUniformMissingTraceFamily`

## Proof outline

Instantiate the proof-accepted lower theorem
`Main.PerturbedStarCertificates::perturbedStar_isUniformMissingTraceFamily d s n hd hslow hshigh hn`
and obtain `B : PerturbedStarBlocks n (d + 1 - s)` together with `hB : IsUniformMissingTraceFamily d
s (perturbedStarFamily d B)`. Use `perturbedStarFamily d B` as the existential family and retain
`hB` unchanged.

Instantiate `Main.PerturbedStarCertificates::perturbedStarParameterBounds d s n hd hslow hshigh hn`.
Its r-form conclusions give `2 * (d + 1 - s) ≤ d`, `2 + 2 * (d + 1 - s) ≤ n`, and `d - 2 * (d + 1 -
s) = 2 * s - d - 2`. Supply the two bounds to the committed current-node theorem
`perturbedStarFamily_card B`; rewrite its second lower index with that equality to obtain the exact
immutable s-form cardinality conjunct.

Apply the committed current-node helper `perturbedStarExtra_choose_pos hd hslow hshigh hn` for
positivity of that same s-form second term. Substitute the proved cardinality equality and conclude
`Nat.choose (n - 1) d < (perturbedStarFamily d B).card` by elementary natural-number arithmetic.
This assembles only the ready certificate, count, and positivity interfaces; it does not re-prove
any certificate case or counting chain.

## Proof sources

- Source `formal_target.lean`, lines 14–25
- Source `article/sections/02_proof.tex`, lines 75–79

## Proof dependencies

- `Main.CountingAndMain::perturbedStarExtra_choose_pos` → `perturbedStarExtra_choose_pos` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarExtra_choose_pos`
- `Main.CountingAndMain::perturbedStarFamily_card` → `perturbedStarFamily_card` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarFamily_card`
- `Main.PerturbedStarCertificates::perturbedStarParameterBounds` → `perturbedStarParameterBounds`
  from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarParameterBounds`
- `Main.PerturbedStarCertificates::perturbedStar_isUniformMissingTraceFamily` →
  `perturbedStar_isUniformMissingTraceFamily` from `UniformMissingTraceFamily.Main.PerturbedStarCert
  ificates.Theorems.perturbedStar_isUniformMissingTraceFamily`
-/
theorem exists_uniformMissingTraceFamily_strictlyLargerThanStar (d s n : ℕ)
    (hd : 4 ≤ d) (hslow : (d + 3) / 2 ≤ s) (hshigh : s ≤ d - 1)
    (hn : 2 * (d + 1) ≤ n) :
    ∃ family : Finset (Finset (Fin n)),
      IsUniformMissingTraceFamily d s family ∧
        family.card =
          Nat.choose (n - 1) d +
          Nat.choose (n - 2 * (d + 1 - s) - 2) (2 * s - d - 2) ∧
          Nat.choose (n - 1) d < family.card := by
  rcases perturbedStar_isUniformMissingTraceFamily d s n hd hslow hshigh hn with ⟨B, hB⟩
  rcases perturbedStarParameterBounds d s n hd hslow hshigh hn with
    ⟨hr_two, hr_s, hrewrite, hrd, hrn⟩
  refine ⟨perturbedStarFamily d B, hB, ?_, ?_⟩
  · simpa [hrewrite] using perturbedStarFamily_card B hrd hrn
  · have hcard : (perturbedStarFamily d B).card =
        Nat.choose (n - 1) d +
          Nat.choose (n - 2 * (d + 1 - s) - 2) (2 * s - d - 2) := by
      simpa [hrewrite] using perturbedStarFamily_card B hrd hrn
    have hpos := perturbedStarExtra_choose_pos hd hslow hshigh hn
    rw [hcard]
    omega
```

### Statement dependencies

- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose`
- `current repo:Main.PatternCriterion.IsUniformMissingTraceFamily`

### Proof dependencies

- `current repo:Main.CountingAndMain.perturbedStarExtra_choose_pos`
- `current repo:Main.CountingAndMain.perturbedStarFamily_card`
- `current repo:Main.PerturbedStarCertificates.perturbedStarParameterBounds`
- `current repo:Main.PerturbedStarCertificates.perturbedStar_isUniformMissingTraceFamily`

### Sources

- `formal_target.lean:14-25`
- `article/sections/02_proof.tex:75-79`

## `perturbedStarFamily_card`

The explicit perturbed-star family has star cardinality plus the sole unpaired full-L binomial contribution.

- Kind: `theorem`
- Node: `Main.CountingAndMain`
- Module: `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarFamily_card`
- Status: `proved` (`committed`)
- Formal code: final proof projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Nat.Choose.Basic
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.patternFamily_card_sum
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarPatterns_chooseSum
import UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarPatterns_disjoint_filler
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarFamily_card`

For natural numbers `n`, `r`, and `d`, any `B : PerturbedStarBlocks n r`, and proofs `hrd : 2 * r ≤
d` and `hrn : 2 + 2 * r ≤ n`, the explicit family `perturbedStarFamily d B` has cardinality
`(perturbedStarFamily d B).card = Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r)`.

## Sources

- Source `article/sections/02_proof.tex`, lines 41–51

## Statement dependencies

- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarFamily` → `perturbedStarFamily` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFamily`

## Proof outline

Unfold the accepted definition `perturbedStarFamily d B` to `patternFamily d (perturbedStarPatterns
d B) (perturbedStarFiller B)`. Apply the committed generic theorem `patternFamily_card_sum` to these
patterns and filler, discharging its sole hypothesis pointwise with the committed theorem
`perturbedStarPatterns_disjoint_filler B P hP`. This rewrites the family cardinality to exactly the
weighted sum over `perturbedStarPatterns d B`.

Rewrite that weighted sum using the committed theorem `perturbedStarPatterns_chooseSum B hrd hrn`.
The result is precisely `Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r)`, preserving
the public object, both r-form hypotheses and indices, and the equality direction. No additional
assumptions or local counting argument are introduced.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 41–51

## Proof dependencies

- `Main.CountingAndMain::patternFamily_card_sum` → `patternFamily_card_sum` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.patternFamily_card_sum`
- `Main.CountingAndMain::perturbedStarPatterns_chooseSum` → `perturbedStarPatterns_chooseSum` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarPatterns_chooseSum`
- `Main.CountingAndMain::perturbedStarPatterns_disjoint_filler` →
  `perturbedStarPatterns_disjoint_filler` from
  `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarPatterns_disjoint_filler`
- `Main.PerturbedStarCertificates::perturbedStarFamily` → `perturbedStarFamily` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFamily`
-/
theorem perturbedStarFamily_card {n r d : ℕ} (B : PerturbedStarBlocks n r)
    (hrd : 2 * r ≤ d) (hrn : 2 + 2 * r ≤ n) :
    (perturbedStarFamily d B).card =
      Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r) := by
  unfold perturbedStarFamily
  rw [patternFamily_card_sum (perturbedStarPatterns d B) (perturbedStarFiller B)
    (fun P hP => perturbedStarPatterns_disjoint_filler B P hP)]
  exact perturbedStarPatterns_chooseSum B hrd hrn
```

### Statement dependencies

- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFamily`

### Proof dependencies

- `current repo:Main.CountingAndMain.patternFamily_card_sum`
- `current repo:Main.CountingAndMain.perturbedStarPatterns_chooseSum`
- `current repo:Main.CountingAndMain.perturbedStarPatterns_disjoint_filler`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFamily`

### Sources

- `article/sections/02_proof.tex:41-51`

## `IsUniformMissingTraceFamily`

A Finset family on Fin n is (d+1)-uniform and has an s-element missing intersection trace inside every member.

- Kind: `definition`
- Node: `Main.PatternCriterion`
- Module: `UniformMissingTraceFamily.Main.PatternCriterion.Defs.IsUniformMissingTraceFamily`
- Status: `declared` (`committed`)
- Formal code: statement projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PatternCriterion.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `IsUniformMissingTraceFamily`

For natural numbers `n`, `d`, and `s`, and a finite family `family : Finset (Finset (Fin n))`,
`IsUniformMissingTraceFamily d s family` holds exactly when:

1. every member `F` of `family` has cardinality `d + 1`; and
2. every `F ∈ family` has a finite set `B : Finset (Fin n)` with `B ⊆ F` and `B.card = s` such that,
for every `F' ∈ family`, the intersection trace `F ∩ F'` is not `B`.

## Sources

- Source `formal_target.lean`, lines 3–9
-/
def IsUniformMissingTraceFamily {n : ℕ} (d s : ℕ)
    (family : Finset (Finset (Fin n))) : Prop :=
  (∀ F ∈ family, F.card = d + 1) ∧
    ∀ F ∈ family, ∃ B : Finset (Fin n), B ⊆ F ∧ B.card = s ∧
      ∀ F' ∈ family, B ≠ F ∩ F'
```

### Sources

- `formal_target.lean:3-9`

## `card_eq_of_mem_patternFamily`

Every member of a pattern family has cardinality d+1 when allowed patterns lie in a core disjoint from the filler region and have size at most d+1.

- Kind: `theorem`
- Node: `Main.PatternCriterion`
- Module: `UniformMissingTraceFamily.Main.PatternCriterion.Theorems.card_eq_of_mem_patternFamily`
- Status: `proved` (`committed`)
- Formal code: final proof projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PatternCriterion.Prelude
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
import UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily
import UniformMissingTraceFamily.Main.PatternCriterion.Theorems.mem_patternFamily
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `card_eq_of_mem_patternFamily`

For natural numbers `n` and `d`, finite sets `C U F : Finset (Fin n)`, and an allowed pattern family
`patterns : Finset (Finset (Fin n))`, assume:

1. `C` and `U` are disjoint;
2. every `P ∈ patterns` satisfies `P ⊆ C`;
3. every `P ∈ patterns` satisfies `P.card ≤ d + 1`; and
4. `F ∈ patternFamily d patterns U`.

Then `F.card = d + 1`.

In particular, the core/filler disjointness makes the cardinality of a represented member `F = P ∪
A` the sum of the allowed pattern size and its prescribed filler size, so every such member has the
target uniform cardinality.

## Sources

- Source `article/sections/02_proof.tex`, lines 3–17

## Statement dependencies

- `Main.PatternCriterion::patternFamily` → `patternFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily`

## Proof outline

Apply the proved `mem_patternFamily` characterization to `hF`. This yields a pattern `P ∈ patterns`,
a filler `A ⊆ U`, the exact filler cardinality `A.card = d + 1 - P.card`, and `F = P ∪ A`.

Use `h_patterns_subset P hP` to obtain `P ⊆ C`. The disjointness `Disjoint C U`, together with `P ⊆
C` and `A ⊆ U`, implies `Disjoint P A`: using `Finset.disjoint_left`, any element lying in both `P`
and `A` would lie in both `C` and `U`, contradicting `hCU`.

Rewrite `F` as `P ∪ A` and apply `Finset.card_union_of_disjoint` to get `F.card = P.card + A.card`.
Substitute the exact filler-cardinality witness. Finally, use `h_patterns_card P hP : P.card ≤ d +
1` to simplify the natural-number expression `P.card + (d + 1 - P.card)` to `d + 1` (the standard
truncated-subtraction cancellation, discharged in Lean by arithmetic normalization such as `omega`).
Thus every member has cardinality `d + 1`, with no perturbed-star-specific assumptions.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 3–17

## Proof dependencies

- `Finset.card_union_of_disjoint` from `Mathlib.Data.Finset.Card`
- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Main.PatternCriterion::mem_patternFamily` → `mem_patternFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Theorems.mem_patternFamily`
-/
theorem card_eq_of_mem_patternFamily {n d : ℕ} (C U : Finset (Fin n))
    (patterns : Finset (Finset (Fin n))) (F : Finset (Fin n))
    (hCU : Disjoint C U) (h_patterns_subset : ∀ P ∈ patterns, P ⊆ C)
    (h_patterns_card : ∀ P ∈ patterns, P.card ≤ d + 1)
    (hF : F ∈ patternFamily d patterns U) : F.card = d + 1 := by
  rcases (mem_patternFamily patterns U F).mp hF with ⟨P, hP, A, hAU, hAcard, rfl⟩
  rw [Finset.card_union_of_disjoint (hCU.mono (h_patterns_subset P hP) hAU), hAcard]
  exact Nat.add_sub_of_le (h_patterns_card P hP)
```

### Statement dependencies

- `current repo:Main.PatternCriterion.patternFamily`

### Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_union_of_disjoint`
- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `current repo:Main.PatternCriterion.mem_patternFamily`

### Sources

- `article/sections/02_proof.tex:3-17`

## `mem_patternFamily`

Membership in patternFamily is equivalent to admitting an allowed pattern and an exact-cardinality filler whose union is the member.

- Kind: `theorem`
- Node: `Main.PatternCriterion`
- Module: `UniformMissingTraceFamily.Main.PatternCriterion.Theorems.mem_patternFamily`
- Status: `proved` (`committed`)
- Formal code: final proof projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PatternCriterion.Prelude
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `mem_patternFamily`

For natural numbers `n` and `d`, an allowed pattern family `patterns : Finset (Finset (Fin n))`, a
filler region `U : Finset (Fin n)`, and `F : Finset (Fin n)`, membership in the pattern-plus-filler
family is characterized by
```
F ∈ patternFamily d patterns U ↔
  ∃ P : Finset (Fin n), P ∈ patterns ∧
    ∃ A : Finset (Fin n), A ⊆ U ∧ A.card = d + 1 - P.card ∧ F = P ∪ A.
```
Thus a member is exactly the union of an allowed pattern and a filler subset of `U` whose
cardinality supplies the remaining positions to reach size `d + 1`.

## Sources

- Source `article/sections/02_proof.tex`, lines 3–7

## Statement dependencies

- `Main.PatternCriterion::patternFamily` → `patternFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily`

## Proof outline

Unfold `patternFamily d patterns U`. Apply `Finset.mem_biUnion` to membership in the outer biunion,
obtaining an allowed pattern `P ∈ patterns` and membership of `F` in the corresponding image. Apply
`Finset.mem_image` to that image membership, obtaining a filler `A ∈ U.powersetCard (d + 1 -
P.card)` and an equality `P ∪ A = F`. Take the symmetry of this image equality to obtain the
accepted witness conclusion `F = P ∪ A`. Finally, apply `Finset.mem_powersetCard` to split the
filler membership into `A ⊆ U` and `A.card = d + 1 - P.card`. This proves the forward implication.

Conversely, given `P ∈ patterns`, `A ⊆ U`, `A.card = d + 1 - P.card`, and `F = P ∪ A`, use
`Finset.mem_powersetCard` in the reverse direction to place `A` in `U.powersetCard (d + 1 -
P.card)`. To reintroduce `A` through `Finset.mem_image`, use the supplied equality in reverse,
namely `P ∪ A = F`. Then reintroduce `P` through `Finset.mem_biUnion` to obtain `F ∈ patternFamily d
patterns U`. The proof is generic in `Fin n` and uses no disjointness or perturbed-star-specific
data.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 3–7

## Proof dependencies

- `Finset.mem_image` from `Mathlib.Data.Finset.Image`
- `Finset.mem_powersetCard` from `Mathlib.Data.Finset.Powerset`
- `Finset.mem_biUnion` from `Mathlib.Data.Finset.Union`
- `Main.PatternCriterion::patternFamily` → `patternFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily`
-/
theorem mem_patternFamily {n d : ℕ} (patterns : Finset (Finset (Fin n)))
    (U F : Finset (Fin n)) :
    F ∈ patternFamily d patterns U ↔
      ∃ P : Finset (Fin n), P ∈ patterns ∧
        ∃ A : Finset (Fin n), A ⊆ U ∧ A.card = d + 1 - P.card ∧ F = P ∪ A := by
  simp [patternFamily, and_assoc, eq_comm]
```

### Statement dependencies

- `current repo:Main.PatternCriterion.patternFamily`

### Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Image.Finset.mem_image`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.mem_powersetCard`
- `Mathlib:Mathlib.Data.Finset.Union.Finset.mem_biUnion`
- `current repo:Main.PatternCriterion.patternFamily`

### Sources

- `article/sections/02_proof.tex:3-7`

## `patternFamily`

The Finset family of unions P ∪ A where P is an allowed core pattern and A is a fixed-cardinality filler from U.

- Kind: `definition`
- Node: `Main.PatternCriterion`
- Module: `UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily`
- Status: `declared` (`committed`)
- Formal code: statement projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PatternCriterion.Prelude
import Mathlib.Data.Finset.Powerset
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `patternFamily`

For a natural number `n`, a target size parameter `d`, an allowed pattern family `patterns : Finset
(Finset (Fin n))`, and a filler region `U : Finset (Fin n)`, `patternFamily d patterns U` is the
finite family of all unions `P ∪ A` where `P ∈ patterns` and `A` is a subset of `U` of cardinality
`d + 1 - P.card`; equivalently, `A ∈ U.powersetCard (d + 1 - P.card)`.

This construction records only the allowed core-pattern component and the exact-size filler
component. It does not itself impose disjointness or specialize the patterns to the later
perturbed-star construction.

## Sources

- Source `article/sections/02_proof.tex`, lines 3–7

## Statement dependencies

- `Finset.powersetCard` from `Mathlib.Data.Finset.Powerset`
-/
def patternFamily {n : ℕ} (d : ℕ) (patterns : Finset (Finset (Fin n)))
    (U : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  patterns.biUnion fun P => (U.powersetCard (d + 1 - P.card)).image fun A => P ∪ A
```

### Statement dependencies

- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.powersetCard`

### Sources

- `article/sections/02_proof.tex:3-7`

## `patternFamily_isUniformMissingTraceFamily`

The generic proper-subpattern tau certificates make the disjoint pattern-plus-filler construction a uniform missing-trace family.

- Kind: `theorem`
- Node: `Main.PatternCriterion`
- Module: `UniformMissingTraceFamily.Main.PatternCriterion.Theorems.patternFamily_isUniformMissingTraceFamily`
- Status: `proved` (`committed`)
- Formal code: final proof projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PatternCriterion.Prelude
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Lattice.Basic
import UniformMissingTraceFamily.Main.PatternCriterion.Defs.IsUniformMissingTraceFamily
import UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily
import UniformMissingTraceFamily.Main.PatternCriterion.Theorems.card_eq_of_mem_patternFamily
import UniformMissingTraceFamily.Main.PatternCriterion.Theorems.mem_patternFamily
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `patternFamily_isUniformMissingTraceFamily`

For natural numbers `n`, `d`, and `s`; finite core and filler regions `C U : Finset (Fin n)`; an
allowed pattern family `patterns : Finset (Finset (Fin n))`; and a certificate function `tau :
Finset (Fin n) → Finset (Fin n)`, assume:

1. `C` and `U` are disjoint;
2. every `P ∈ patterns` satisfies `P ⊆ C`; and
3. every `P ∈ patterns` has the bundled certificate
```
tau P ⊂ P ∧
P.card - (tau P).card ≤ d + 1 - s ∧
(tau P).card ≤ s ∧
¬ ∃ Q ∈ patterns,
    Q ∩ P = tau P ∧
    Q.card ≤ (tau P).card + (d + 1 - s).
```

Then
```
IsUniformMissingTraceFamily d s (patternFamily d patterns U).
```

The bundled certificate is exactly the source’s proper-subpattern, difference-bound, size-bound, and
excluded-intersection data, while leaving the generic core/filler construction and conclusion
unchanged.

## Sources

- Source `article/sections/02_proof.tex`, lines 3–28

## Statement dependencies

- `Main.PatternCriterion::IsUniformMissingTraceFamily` → `IsUniformMissingTraceFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.IsUniformMissingTraceFamily`
- `Main.PatternCriterion::patternFamily` → `patternFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily`

## Proof outline

For each use of the bundled certificate, destruct `hτ R hR` as
`⟨hproper, hgap, htaucard, hexcl⟩`, preserving the four source clauses with no additional
assumptions.

First establish the universal source line-17 bound
`h_pattern_card : ∀ R ∈ patterns, R.card ≤ d + 1`.
For arbitrary `R ∈ patterns`, project its `hproper : tau R ⊂ R`, `hgap : R.card - (tau R).card ≤ d +
1 - s`, and `htaucard : (tau R).card ≤ s`. Apply `Finset.card_lt_card hproper` to get `(tau R).card
< R.card`, hence the difference is non-truncated. Natural-number arithmetic gives
`R.card ≤ (tau R).card + (d + 1 - s) ≤ s + (d + 1 - s) = d + 1`.
Use this `h_pattern_card` with `card_eq_of_mem_patternFamily C U patterns` to prove the
uniform-cardinality conjunct of `IsUniformMissingTraceFamily`.

For the missing-trace conjunct, fix `F ∈ patternFamily d patterns U` and apply `mem_patternFamily`
to obtain `P ∈ patterns`, `A ⊆ U`, `A.card = d + 1 - P.card`, and `F = P ∪ A`. Project the
certificate for `P` as `⟨hproperP, hgapP, htaucardP, hexclP⟩`. Its gap and size clauses, together
with the non-truncated cardinal relation from `hproperP` and the filler-cardinality equality, give
`s - (tau P).card ≤ A.card`.
Use `Finset.exists_subset_card_eq` to choose `X ⊆ A` with `X.card = s - (tau P).card`; set `B = tau
P ∪ X`. The inclusions `tau P ⊆ P ⊆ C` and `X ⊆ A ⊆ U` and `hCU` make this union disjoint. Thus `B ⊆
F`, and `Finset.card_union_of_disjoint` plus `htaucardP` gives `B.card = s`.

Fix `F' ∈ patternFamily d patterns U`, and unpack it as `F' = Q ∪ A'`, with `Q ∈ patterns`, `A' ⊆
U`, and `A'.card = d + 1 - Q.card`. Suppose `B = F ∩ F'`. Substitute both representations and expand
the intersection with `Finset.inter_union_distrib_left`. Intersect the resulting equality with `C`:
on the witness side, the `X` component vanishes because `X ⊆ U` and `C` is disjoint from `U`; on the
trace side, every term involving a filler vanishes, leaving `P ∩ Q`. Hence `Q ∩ P = tau P`.
Intersect the same equality with `U`: all core-containing terms vanish, leaving `A' ∩ A = X`.

The latter equality and `Finset.inter_subset_left` yield `X.card ≤ A'.card` by
`Finset.card_le_card`. Invoke the universal bound `h_pattern_card Q hQ : Q.card ≤ d + 1`; together
with `A'.card = d + 1 - Q.card`, this makes the subtraction a genuine complement. Substitute the
exact cards of `X` and `A'`, and use `htaucardP`; natural-number arithmetic gives
`Q.card ≤ (tau P).card + (d + 1 - s)`.
This bound, `Q ∈ patterns`, and `Q ∩ P = tau P` contradict the projected exclusion clause `hexclP`.
Therefore `B ≠ F ∩ F'` for every `F'`, proving the unchanged generic conclusion.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 9–28

## Proof dependencies

- `Finset.card_le_card` from `Mathlib.Data.Finset.Card`
- `Finset.card_lt_card` from `Mathlib.Data.Finset.Card`
- `Finset.card_union_of_disjoint` from `Mathlib.Data.Finset.Card`
- `Finset.exists_subset_card_eq` from `Mathlib.Data.Finset.Card`
- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Finset.inter_subset_left` from `Mathlib.Data.Finset.Lattice.Basic`
- `Finset.inter_union_distrib_left` from `Mathlib.Data.Finset.Lattice.Basic`
- `Main.PatternCriterion::IsUniformMissingTraceFamily` → `IsUniformMissingTraceFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.IsUniformMissingTraceFamily`
- `Main.PatternCriterion::card_eq_of_mem_patternFamily` → `card_eq_of_mem_patternFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Theorems.card_eq_of_mem_patternFamily`
- `Main.PatternCriterion::mem_patternFamily` → `mem_patternFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Theorems.mem_patternFamily`
-/
theorem patternFamily_isUniformMissingTraceFamily {n d s : ℕ}
    (C U : Finset (Fin n)) (patterns : Finset (Finset (Fin n)))
    (tau : Finset (Fin n) → Finset (Fin n)) (hCU : Disjoint C U)
    (hPC : ∀ P ∈ patterns, P ⊆ C)
    (hτ : ∀ P ∈ patterns, tau P ⊂ P ∧
      P.card - (tau P).card ≤ d + 1 - s ∧ (tau P).card ≤ s ∧
      ¬ ∃ Q ∈ patterns, Q ∩ P = tau P ∧
        Q.card ≤ (tau P).card + (d + 1 - s)) :
    IsUniformMissingTraceFamily d s (patternFamily d patterns U) := by
  have h_pattern_card : ∀ R ∈ patterns, R.card ≤ d + 1 := by
    intro R hR
    rcases hτ R hR with ⟨hproper, hgap, hcard, _⟩
    have hlt := Finset.card_lt_card hproper
    have hle : (tau R).card ≤ R.card := Nat.le_of_lt hlt
    omega
  unfold IsUniformMissingTraceFamily
  constructor
  · intro F hF
    exact card_eq_of_mem_patternFamily C U patterns F hCU hPC h_pattern_card hF
  · intro F hF
    rcases (mem_patternFamily patterns U F).mp hF with ⟨P, hP, A, hAU, hAcard, rfl⟩
    rcases hτ P hP with ⟨hproperP, hgapP, hcardP, hexclP⟩
    have hXle : s - (tau P).card ≤ A.card := by
      have hlt := Finset.card_lt_card hproperP
      have hle : (tau P).card ≤ P.card := Nat.le_of_lt hlt
      omega
    rcases Finset.exists_subset_card_eq hXle with ⟨X, hXA, hXcard⟩
    refine ⟨tau P ∪ X, ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (hproperP.1 hx)
      · exact Or.inr (hXA hx)
    · rw [Finset.card_union_of_disjoint
        (hCU.mono (hproperP.1.trans (hPC P hP)) (hXA.trans hAU)), hXcard]
      exact Nat.add_sub_of_le hcardP
    · intro F' hF'
      rcases (mem_patternFamily patterns U F').mp hF' with ⟨Q, hQ, A', hA'U, hA'card, rfl⟩
      intro hEq
      apply hexclP
      refine ⟨Q, hQ, ?_, ?_⟩
      · ext x
        constructor
        · intro hx
          rw [Finset.mem_inter] at hx
          have hxI : x ∈ (P ∪ A) ∩ (Q ∪ A') := by
            rw [Finset.mem_inter, Finset.mem_union, Finset.mem_union]
            exact ⟨Or.inl hx.2, Or.inl hx.1⟩
          have hxB : x ∈ tau P ∪ X := hEq.symm ▸ hxI
          rw [Finset.mem_union] at hxB
          rcases hxB with hxT | hxX
          · exact hxT
          · exact False.elim ((Finset.disjoint_left.mp hCU (hPC P hP hx.2))
              (hAU (hXA hxX)))
        · intro hxT
          have hxI : x ∈ (P ∪ A) ∩ (Q ∪ A') := hEq ▸ by
            rw [Finset.mem_union]
            exact Or.inl hxT
          rw [Finset.mem_inter, Finset.mem_union, Finset.mem_union] at hxI
          rw [Finset.mem_inter]
          refine ⟨?_, hproperP.1 hxT⟩
          rcases hxI.2 with hxQ | hxA'
          · exact hxQ
          · exact False.elim ((Finset.disjoint_left.mp hCU
              (hproperP.1.trans (hPC P hP) hxT)) (hA'U hxA'))
      · have hXA' : X ⊆ A' := by
          intro x hxX
          have hxI : x ∈ (P ∪ A) ∩ (Q ∪ A') := hEq ▸ by
            rw [Finset.mem_union]
            exact Or.inr hxX
          rw [Finset.mem_inter, Finset.mem_union, Finset.mem_union] at hxI
          rcases hxI.2 with hxQ | hxA'
          · exact False.elim ((Finset.disjoint_left.mp hCU (hPC Q hQ hxQ))
              (hAU (hXA hxX)))
          · exact hxA'
        have hle := Finset.card_le_card hXA'
        have hQcard := h_pattern_card Q hQ
        omega
```

### Statement dependencies

- `current repo:Main.PatternCriterion.IsUniformMissingTraceFamily`
- `current repo:Main.PatternCriterion.patternFamily`

### Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_le_card`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_lt_card`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_union_of_disjoint`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.exists_subset_card_eq`
- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `Mathlib:Mathlib.Data.Finset.Lattice.Basic.Finset.inter_subset_left`
- `Mathlib:Mathlib.Data.Finset.Lattice.Basic.Finset.inter_union_distrib_left`
- `current repo:Main.PatternCriterion.IsUniformMissingTraceFamily`
- `current repo:Main.PatternCriterion.card_eq_of_mem_patternFamily`
- `current repo:Main.PatternCriterion.mem_patternFamily`

### Sources

- `article/sections/02_proof.tex:3-28`

## `perturbedPattern_properWeights_add_full_eq_fullWeights`

Proper a-pattern weights plus the full-L b-pattern weight equal the full b-pattern image weights.

- Kind: `theorem`
- Node: `Main.PerturbedPatternCancellation`
- Module: `UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPattern_properWeights_add_full_eq_fullWeights`
- Status: `proved` (`committed`)
- Formal code: final proof projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternA_injOn
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternB_injOn
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternB_properImage_eq_erase
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPattern_chooseWeight_eq
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedPattern_properWeights_add_full_eq_fullWeights`

For every `B : PerturbedStarBlocks n r` and every natural number `d`, let

`w(P) = Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)`,

`fₐ(Y) = {B.a} ∪ B.T ∪ Y`, and `fᵦ(Y) = {B.b} ∪ B.T ∪ Y`.

Then the proper deleted-pattern weight sum plus the sole full-`L` added-pattern weight equals the
full added-pattern image weight sum:

`(∑ P ∈ ({Y ∈ B.L.powerset | Y ≠ B.L}.image fₐ), w(P)) + w({B.b} ∪ B.T ∪ B.L) = ∑ P ∈
B.L.powerset.image fᵦ, w(P)`.

No additional hypotheses, including `hrd` or `hrn`, are assumed.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Finset.sum` from `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- `Finset.card` from `Mathlib.Data.Finset.Card`
- `Finset.filter` from `Mathlib.Data.Finset.Filter`
- `Finset.image` from `Mathlib.Data.Finset.Image`
- `Finset.powerset` from `Mathlib.Data.Finset.Powerset`
- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`

## Proof outline

Write `S = B.L.powerset`, `D = S.filter (fun Y => Y ≠ B.L)`, `fₐ(Y) = {B.a} ∪ B.T ∪ Y`, `fᵦ(Y) =
{B.b} ∪ B.T ∪ Y`, and `w(P) = Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)`.  First
restrict each accepted `Set.InjOn` theorem `perturbedPatternA_injOn B` and `perturbedPatternB_injOn
B` from `S` to `D`: `Finset.mem_filter` shows every member of `D` lies in `S`.  Apply
`Finset.sum_image` with the restricted a-injectivity to rewrite the left proper-a image sum as `∑ Y
∈ D, w (fₐ Y)`.

Use `Finset.sum_congr` on this common finite domain.  For each `Y ∈ D`, combine `Finset.mem_filter`
and `Finset.mem_powerset` to obtain `Y ⊆ B.L`, then apply the accepted theorem
`perturbedPattern_chooseWeight_eq B d Y` to replace `w (fₐ Y)` with `w (fᵦ Y)`.  Apply
`Finset.sum_image` with the restricted b-injectivity in the reverse direction, converting this sum
to the proper-b image sum `∑ P ∈ D.image fᵦ, w P`.

Rewrite the b-image index finset with the accepted `perturbedPatternB_properImage_eq_erase B`,
obtaining the sum over `(S.image fᵦ).erase (fᵦ B.L)`.  Establish `fᵦ B.L ∈ S.image fᵦ` by
`Finset.mem_image`, using `Finset.mem_powerset` for `B.L ∈ S`.  Finally apply `Finset.sum_erase_add`
to conclude that this erased b-image sum plus `w (fᵦ B.L)` is exactly the full b-image sum.  This
yields the stated proper-a-plus-full-b equals full-b direction with the exact maps and indices, no
`hrd`/ `hrn` assumptions, and no helper declaration.

## Proof sources

- Source `article/sections/02_proof.tex`, line 49

## Proof dependencies

- `Finset.sum_congr` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_erase_add` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.sum_image` from `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Finset.mem_filter` from `Mathlib.Data.Finset.Filter`
- `Finset.mem_image` from `Mathlib.Data.Finset.Image`
- `Finset.mem_powerset` from `Mathlib.Data.Finset.Powerset`
- `Main.PerturbedPatternCancellation::perturbedPatternA_injOn` → `perturbedPatternA_injOn` from
  `UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternA_injOn`
- `Main.PerturbedPatternCancellation::perturbedPatternB_injOn` → `perturbedPatternB_injOn` from
  `UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPatternB_injOn`
- `Main.PerturbedPatternCancellation::perturbedPatternB_properImage_eq_erase` →
  `perturbedPatternB_properImage_eq_erase` from `UniformMissingTraceFamily.Main.PerturbedPatternCanc
  ellation.Theorems.perturbedPatternB_properImage_eq_erase`
- `Main.PerturbedPatternCancellation::perturbedPattern_chooseWeight_eq` →
  `perturbedPattern_chooseWeight_eq` from `UniformMissingTraceFamily.Main.PerturbedPatternCancellati
  on.Theorems.perturbedPattern_chooseWeight_eq`
-/
theorem perturbedPattern_properWeights_add_full_eq_fullWeights {n r : ℕ}
    (B : PerturbedStarBlocks n r) (d : ℕ) :
    (∑ P ∈ (B.L.powerset.filter (fun Y => Y ≠ B.L)).image
        (fun Y : Finset (Fin n) ↦ {B.a} ∪ B.T ∪ Y),
      Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)) +
      Nat.choose (perturbedStarFiller B).card
        (d + 1 - ({B.b} ∪ B.T ∪ B.L).card) =
      ∑ P ∈ B.L.powerset.image (fun Y : Finset (Fin n) ↦ {B.b} ∪ B.T ∪ Y),
        Nat.choose (perturbedStarFiller B).card (d + 1 - P.card) := by
  classical
  let D := B.L.powerset.filter (fun Y => Y ≠ B.L)
  let fA : Finset (Fin n) → Finset (Fin n) := fun Y => {B.a} ∪ B.T ∪ Y
  let fB : Finset (Fin n) → Finset (Fin n) := fun Y => {B.b} ∪ B.T ∪ Y
  let w : Finset (Fin n) → ℕ :=
    fun P => Nat.choose (perturbedStarFiller B).card (d + 1 - P.card)
  change (∑ P ∈ D.image fA, w P) + w (fB B.L) =
    ∑ P ∈ B.L.powerset.image fB, w P
  have memD (Y : Finset (Fin n)) (hY : Y ∈ D) : Y ∈ B.L.powerset := by
    have hY' : Y ∈ B.L.powerset.filter (fun Y => Y ≠ B.L) := by
      simpa only [D] using hY
    exact (Finset.mem_filter.mp hY').1
  have hAinj : Set.InjOn fA (↑D : Set (Finset (Fin n))) := by
    intro Y hY Z hZ hEq
    apply perturbedPatternA_injOn B
    · exact memD Y hY
    · exact memD Z hZ
    · simpa [fA] using hEq
  have hBinj : Set.InjOn fB (↑D : Set (Finset (Fin n))) := by
    intro Y hY Z hZ hEq
    apply perturbedPatternB_injOn B
    · exact memD Y hY
    · exact memD Z hZ
    · simpa [fB] using hEq
  have hWeights : (∑ Y ∈ D, w (fA Y)) = ∑ Y ∈ D, w (fB Y) := by
    apply Finset.sum_congr rfl
    intro Y hY
    have hYPow : Y ∈ B.L.powerset := memD Y hY
    simpa [w, fA, fB] using
      perturbedPattern_chooseWeight_eq B d Y (Finset.mem_powerset.mp hYPow)
  have hFull : fB B.L ∈ B.L.powerset.image fB := by
    refine Finset.mem_image.mpr ⟨B.L, ?_, rfl⟩
    exact Finset.mem_powerset.mpr (fun _ hx => hx)
  calc
    (∑ P ∈ D.image fA, w P) + w (fB B.L) =
        (∑ Y ∈ D, w (fA Y)) + w (fB B.L) := by
      rw [Finset.sum_image hAinj]
    _ = (∑ Y ∈ D, w (fB Y)) + w (fB B.L) := by rw [hWeights]
    _ = (∑ P ∈ D.image fB, w P) + w (fB B.L) := by
      rw [(Finset.sum_image hBinj).symm]
    _ = (∑ P ∈ (B.L.powerset.image fB).erase (fB B.L), w P) + w (fB B.L) := by
      rw [← perturbedPatternB_properImage_eq_erase B]
    _ = ∑ P ∈ B.L.powerset.image fB, w P := Finset.sum_erase_add _ _ hFull
```

### Statement dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Finset.sum`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.card`
- `Mathlib:Mathlib.Data.Finset.Filter.Finset.filter`
- `Mathlib:Mathlib.Data.Finset.Image.Finset.image`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.powerset`
- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFiller`

### Proof dependencies

- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_congr`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_erase_add`
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Basic.Finset.sum_image`
- `Mathlib:Mathlib.Data.Finset.Filter.Finset.mem_filter`
- `Mathlib:Mathlib.Data.Finset.Image.Finset.mem_image`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.mem_powerset`
- `current repo:Main.PerturbedPatternCancellation.perturbedPatternA_injOn`
- `current repo:Main.PerturbedPatternCancellation.perturbedPatternB_injOn`
- `current repo:Main.PerturbedPatternCancellation.perturbedPatternB_properImage_eq_erase`
- `current repo:Main.PerturbedPatternCancellation.perturbedPattern_chooseWeight_eq`

### Sources

- `article/sections/02_proof.tex:49-49`

## `PerturbedStarBlocks`

Construction data consisting of two distinguished points and two disjoint equal-size blocks in Fin n.

- Kind: `structure`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- Status: `declared` (`committed`)
- Formal code: statement projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `PerturbedStarBlocks`

For natural numbers n and r, `PerturbedStarBlocks n r` is public construction data consisting of two
distinguished elements `a` and `b` of `Fin n` and two finite sets `T` and `L` of `Fin n`.  It
records explicitly that `a ≠ b`, that `T` and `L` each have cardinality `r`, that `T` and `L` are
disjoint, and that neither `T` nor `L` contains either distinguished element.  Thus all anchor
distinctness and block-avoidance requirements are fields of the data, rather than implicit
conventions.

## Sources

- Source `article/sections/02_proof.tex`, lines 30–32
-/
structure PerturbedStarBlocks (n r : ℕ) where
  a : Fin n
  b : Fin n
  T : Finset (Fin n)
  L : Finset (Fin n)
  a_ne_b : a ≠ b
  card_T : T.card = r
  card_L : L.card = r
  T_disjoint_L : Disjoint T L
  a_not_mem_T : a ∉ T
  b_not_mem_T : b ∉ T
  a_not_mem_L : a ∉ L
  b_not_mem_L : b ∉ L
```

### Sources

- `article/sections/02_proof.tex:30-32`

## `exists_perturbedStarBlocks`

Sufficient ambient size yields explicit perturbed-star block data.

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.exists_perturbedStarBlocks`
- Status: `proved` (`committed`)
- Formal code: final proof projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `exists_perturbedStarBlocks`

For natural numbers n and r, if `2 + 2*r ≤ n`, then there exists `PerturbedStarBlocks n r`.  The
asserted data may be chosen by reserving two distinguished points of `Fin n` and embedding two
consecutive, shifted ranges of length `r`; consequently its two blocks have cardinality `r`, are
disjoint, avoid both distinguished points, and the distinguished points are distinct.

## Sources

- Source `article/sections/02_proof.tex`, line 32

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`

## Proof outline

Set `e : Fin (2 + 2*r) ↪ Fin n := Fin.castLEEmb hroom`.  Let `hT : 2 + r ≤ 2 + 2*r` and `hL : 2 + r
+ r ≤ 2 + 2*r` be the elementary arithmetic bounds.  Define the two embeddings with their full
types:
```
t : Fin r ↪ Fin (2 + 2*r) :=
  (Fin.castLEEmb hT).comp (Fin.natAddEmb 2)
l : Fin r ↪ Fin (2 + 2*r) :=
  (Fin.castLEEmb hL).comp (Fin.natAddEmb (2 + r)).
```
Thus `t i` has value `2 + i.val`, while `l j` has value `2 + r + j.val`.  Use the checked base
finset
```
B : Finset (Fin r) := Finset.univ
T₀ := B.map t
L₀ := B.map l
T  := T₀.map e
L  := L₀.map e.
```
All maps are between explicitly displayed `Fin` types.  Take anchors `a := e ⟨0, by omega⟩` and `b
:= e ⟨1, by omega⟩`.

The base-cardinality calculation is `B.card = r` by `simp [B, Finset.card_univ, Fintype.card_fin]`.
Apply `Finset.card_map` first to `B.map t` and `B.map l`, then to the two maps by `e`, yielding both
required block-cardinality fields.  For `Disjoint T₀ L₀`, apply `Finset.disjoint_left.mpr`; if an
element belongs to both maps, map-membership gives `i j : Fin r` with `t i = l j`.  Comparing values
produces `2 + i.val = 2 + r + j.val`, which contradicts `i.val < r`.  Then use the `.mpr` direction
of `Finset.disjoint_map e` to obtain `Disjoint T L`.

Finally, prove `a ≠ b` by injectivity of `e` and the distinct values `0,1`.  For each
anchor-avoidance field, eliminate map membership to an `i : Fin r` or `j : Fin r`, cancel `e` by
injectivity, and compare values: every `t i` or `l j` is at least `2`, so it cannot equal either
anchor coordinate.  Package `a,b,T,L` and these fields in `PerturbedStarBlocks n r`.

## Proof sources

- Source `article/sections/02_proof.tex`, line 32

## Proof dependencies

- `Fin.castLEEmb` from `Mathlib.Data.Fin.Embedding`
- `Fin.natAddEmb` from `Mathlib.Data.Fin.Embedding`
- `Finset.card_map` from `Mathlib.Data.Finset.Card`
- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Finset.disjoint_map` from `Mathlib.Data.Finset.Image`
- `Finset.card_univ` from `Mathlib.Data.Fintype.Card`
- `Fintype.card_fin` from `Mathlib.Data.Fintype.Card`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
-/
theorem exists_perturbedStarBlocks (n r : ℕ) (hroom : 2 + 2 * r ≤ n) :
    Nonempty (PerturbedStarBlocks n r) := by
  let e : Fin (2 + 2 * r) ↪ Fin n := Fin.castLEEmb hroom
  have hT : 2 + r ≤ 2 + 2 * r := by omega
  have hL : 2 + r + r ≤ 2 + 2 * r := by omega
  let t : Fin r ↪ Fin (2 + 2 * r) :=
    (Fin.natAddEmb 2).trans (Fin.castLEEmb hT)
  let l : Fin r ↪ Fin (2 + 2 * r) :=
    (Fin.natAddEmb (2 + r)).trans (Fin.castLEEmb hL)
  let B : Finset (Fin r) := Finset.univ
  let T₀ : Finset (Fin (2 + 2 * r)) := B.map t
  let L₀ : Finset (Fin (2 + 2 * r)) := B.map l
  let a : Fin n := e ⟨0, by omega⟩
  let b : Fin n := e ⟨1, by omega⟩
  have T₀_ge_two (x : Fin (2 + 2 * r)) (hx : x ∈ T₀) : 2 ≤ x.val := by
    change x ∈ B.map t at hx
    rw [Finset.mem_map] at hx
    rcases hx with ⟨i, hiB, hi⟩
    have hval := congrArg Fin.val hi
    simp [t] at hval
    omega
  have L₀_ge_two (x : Fin (2 + 2 * r)) (hx : x ∈ L₀) : 2 ≤ x.val := by
    change x ∈ B.map l at hx
    rw [Finset.mem_map] at hx
    rcases hx with ⟨j, hjB, hj⟩
    have hval := congrArg Fin.val hj
    simp [l] at hval
    omega
  refine ⟨{
    a := a
    b := b
    T := T₀.map e
    L := L₀.map e
    a_ne_b := ?_
    card_T := ?_
    card_L := ?_
    T_disjoint_L := ?_
    a_not_mem_T := ?_
    b_not_mem_T := ?_
    a_not_mem_L := ?_
    b_not_mem_L := ?_ }⟩
  · intro hab
    simpa [a, b, e] using congrArg Fin.val (e.injective hab)
  · simp [T₀, B]
  · simp [L₀, B]
  · apply (Finset.disjoint_map e).mpr
    rw [Finset.disjoint_left]
    intro x hxT hxL
    change x ∈ B.map t at hxT
    change x ∈ B.map l at hxL
    rw [Finset.mem_map] at hxT hxL
    rcases hxT with ⟨i, hiB, hi⟩
    rcases hxL with ⟨j, hjB, hj⟩
    have hval := congrArg Fin.val (hi.trans hj.symm)
    simp [t, l] at hval
    omega
  · intro ha
    rw [Finset.mem_map] at ha
    rcases ha with ⟨x, hx, hxa⟩
    have hxa' : x = ⟨0, by omega⟩ := by
      apply e.injective
      simpa [a] using hxa
    have hval : x.val = 0 := by
      simpa using congrArg Fin.val hxa'
    have htwo := T₀_ge_two x hx
    omega
  · intro hb
    rw [Finset.mem_map] at hb
    rcases hb with ⟨x, hx, hxb⟩
    have hxb' : x = ⟨1, by omega⟩ := by
      apply e.injective
      simpa [b] using hxb
    have hval : x.val = 1 := by
      simpa using congrArg Fin.val hxb'
    have htwo := T₀_ge_two x hx
    omega
  · intro ha
    rw [Finset.mem_map] at ha
    rcases ha with ⟨x, hx, hxa⟩
    have hxa' : x = ⟨0, by omega⟩ := by
      apply e.injective
      simpa [a] using hxa
    have hval : x.val = 0 := by
      simpa using congrArg Fin.val hxa'
    have htwo := L₀_ge_two x hx
    omega
  · intro hb
    rw [Finset.mem_map] at hb
    rcases hb with ⟨x, hx, hxb⟩
    have hxb' : x = ⟨1, by omega⟩ := by
      apply e.injective
      simpa [b] using hxb
    have hval : x.val = 1 := by
      simpa using congrArg Fin.val hxb'
    have htwo := L₀_ge_two x hx
    omega
```

### Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

### Proof dependencies

- `Mathlib:Mathlib.Data.Fin.Embedding.Fin.castLEEmb`
- `Mathlib:Mathlib.Data.Fin.Embedding.Fin.natAddEmb`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_map`
- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `Mathlib:Mathlib.Data.Finset.Image.Finset.disjoint_map`
- `Mathlib:Mathlib.Data.Fintype.Card.Finset.card_univ`
- `Mathlib:Mathlib.Data.Fintype.Card.Fintype.card_fin`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

### Sources

- `article/sections/02_proof.tex:32-32`

## `perturbedStarCertificate_addedProper`

The tau certificate satisfies the generic criterion for an inserted b/T pattern indexed by a proper subset of L.

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_addedProper`
- Status: `proved` (`committed`)
- Formal code: final proof projection

```lean
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
```

### Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

### Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_lt_card`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_union_of_disjoint`
- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.mem_powerset`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

### Sources

- `article/sections/02_proof.tex:60-61`

## `perturbedStarCertificate_finalAdded`

The tau certificate satisfies the generic criterion for the final inserted b/T/L pattern.

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_finalAdded`
- Status: `proved` (`committed`)
- Formal code: final proof projection

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

### Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

### Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_union_of_disjoint`
- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.mem_powerset`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFinalIntersection_excluded`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

### Sources

- `article/sections/02_proof.tex:63-63`

## `perturbedStarCertificate_largeAvoiding`

The tau certificate satisfies the generic criterion for a large a-anchored pattern avoiding T.

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_largeAvoiding`
- Status: `proved` (`committed`)
- Formal code: final proof projection

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

### Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

### Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_inter_add_card_sdiff`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_le_card`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_union_of_disjoint`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.exists_subset_card_eq`
- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

### Sources

- `article/sections/02_proof.tex:67-70`

## `perturbedStarCertificate_largeMeeting`

The tau certificate satisfies the generic criterion for a large a-anchored pattern meeting T.

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_largeMeeting`
- Status: `proved` (`committed`)
- Formal code: final proof projection

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

### Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

### Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_erase_of_mem`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.exists_subset_card_eq`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

### Sources

- `article/sections/02_proof.tex:72-72`

## `perturbedStarCertificate_smallStar`

The tau certificate satisfies the generic criterion for a small a-anchored perturbed-star pattern.

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_smallStar`
- Status: `proved` (`committed`)
- Formal code: final proof projection

```lean
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
```

### Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

### Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_union_of_disjoint`
- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.mem_powerset`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

### Sources

- `article/sections/02_proof.tex:65-65`

## `perturbedStarCore`

The fixed core formed by the two distinguished anchors and the disjoint T and L blocks.

- Kind: `definition`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
- Status: `declared` (`committed`)
- Formal code: statement projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarCore`

For natural numbers n and r and construction data `B : PerturbedStarBlocks n r`, `perturbedStarCore
B` is the finite subset of `Fin n` defined by

`{B.a, B.b} ∪ B.T ∪ B.L`.

Equivalently, it is the union of the two distinguished anchors and the two blocks recorded by `B`;
the displayed union association is part of the definition and no additional elements or assumptions
are introduced.

## Sources

- Source `article/sections/02_proof.tex`, line 34

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
-/
def perturbedStarCore {n r : ℕ} (B : PerturbedStarBlocks n r) : Finset (Fin n) :=
  {B.a, B.b} ∪ B.T ∪ B.L
```

### Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

### Sources

- `article/sections/02_proof.tex:34-34`

## `perturbedStarFamily`

The explicit uniform family generated from the perturbed-star core patterns and complementary filler.

- Kind: `definition`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFamily`
- Status: `declared` (`committed`)
- Formal code: statement projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarFamily`

For natural numbers d, n, and r and construction data `B : PerturbedStarBlocks n r`,
`perturbedStarFamily d B` is the finite family of finite subsets of `Fin n` defined exactly by

`patternFamily d (perturbedStarPatterns d B) (perturbedStarFiller B)`.

Equivalently, it is the generic exact-cardinality completion of the accepted perturbed-star core
patterns using the complementary filler. This definition adds no parameter hypotheses: bounds on d,
s, and n are used only later to construct suitable data and certify the family, not to change its
members.

## Sources

- Source `article/sections/02_proof.tex`, lines 30–39

## Statement dependencies

- `Main.PatternCriterion::patternFamily` → `patternFamily` from
  `UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
-/
def perturbedStarFamily (d : ℕ) {n r : ℕ}
    (B : PerturbedStarBlocks n r) : Finset (Finset (Fin n)) :=
  patternFamily d (perturbedStarPatterns d B) (perturbedStarFiller B)
```

### Statement dependencies

- `current repo:Main.PatternCriterion.patternFamily`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFiller`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`

### Sources

- `article/sections/02_proof.tex:30-39`

## `perturbedStarFiller`

The filler region complementary to the fixed perturbed-star core.

- Kind: `definition`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`
- Status: `declared` (`committed`)
- Formal code: statement projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarFiller`

For natural numbers n and r and construction data `B : PerturbedStarBlocks n r`,
`perturbedStarFiller B` is the finite subset of `Fin n` defined by

`(Finset.univ : Finset (Fin n)) \ perturbedStarCore B`.

Thus it is exactly the complement of the fixed core within `Fin n`; no additional elements,
hypotheses, or semantic conditions are introduced.

## Sources

- Source `article/sections/02_proof.tex`, line 34

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
-/
def perturbedStarFiller {n r : ℕ} (B : PerturbedStarBlocks n r) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)) \ perturbedStarCore B
```

### Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`

### Sources

- `article/sections/02_proof.tex:34-34`

## `perturbedStarFinalIntersection_excluded`

No allowed perturbed-star pattern intersects the final b/T/L pattern in T plus exactly one L-element.

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarFinalIntersection_excluded`
- Status: `proved` (`committed`)
- Formal code: final proof projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Powerset
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarFinalIntersection_excluded`

For natural numbers `d`, `n`, and `r`, let `B : PerturbedStarBlocks n r` and let `ell0 : Fin n`
satisfy `ell0 ∈ B.L`. If `2 ≤ r`, then there is no `Q ∈ perturbedStarPatterns d B` for which

`Q ∩ ({B.b} ∪ B.T ∪ B.L) = B.T ∪ {ell0}`.

Equivalently, no allowed perturbed-star pattern has intersection with the final inserted `b/T/L`
pattern equal to all of `T` together with exactly the single L-element `ell0`. This isolates the
source line-63 exclusion: inserted patterns contain `B.b`, while a base pattern with this
intersection would be the deleted proper-L pattern `{B.a} ∪ B.T ∪ {ell0}`.

## Sources

- Source `article/sections/02_proof.tex`, line 63

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`

## Proof outline

Assume `Q ∈ perturbedStarPatterns d B` and
```
Q ∩ ({B.b} ∪ B.T ∪ B.L) = B.T ∪ {ell0}.
```
Unfold `perturbedStarPatterns` and simplify membership in its powersets, images, filters, union, and
difference (using `Finset.mem_powerset`). This gives the inserted and base-minus-deleted branches of
the accepted definition.

* In the inserted branch, for some `Z ⊆ B.L`,
  `Q = {B.b} ∪ B.T ∪ Z`. The point `B.b` belongs to both `Q` and the final set `{B.b} ∪ B.T ∪ B.L`,
hence to their intersection. But `B.b ∉ B.T ∪ {ell0}`: use `B.b_not_mem_T`, `B.b_not_mem_L`, and
`hell0`. This contradicts the displayed intersection equality.

* In the base-minus-deleted branch, unfold `perturbedStarCore` in the base membership. It gives `B.a
∈ Q` and
  `Q ⊆ {B.a, B.b} ∪ B.T ∪ B.L`. The intersection equality forces `B.b ∉ Q`, forces every element of
`B.T ∪ {ell0}` into `Q`, and excludes every element of `B.L \ {ell0}` from `Q`. For the last two
claims use the anchor-avoidance fields and `B.T_disjoint_L` elementwise through
`Finset.disjoint_left`. Extensionality with the core containment now yields
  ```
  Q = {B.a} ∪ B.T ∪ {ell0}.
  ```

It remains to show that this exact set is deleted. The singleton `{ell0}` is contained in `B.L` by
`hell0`. If it equalled `B.L`, simp would give `B.L.card = 1`; after rewriting with `B.card_L`, this
contradicts `hrtwo : 2 ≤ r`. Thus `{ell0} ⊂ B.L`. Its powerset and filter witnesses therefore place
`{B.a} ∪ B.T ∪ {ell0}` in the deleted image. This contradicts the base-minus-deleted membership of
`Q`.

Both raw construction branches are impossible, proving the exact no-`Q` conclusion.

## Proof sources

- Source `article/sections/02_proof.tex`, line 63

## Proof dependencies

- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Finset.mem_powerset` from `Mathlib.Data.Finset.Powerset`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
- `Main.PerturbedStarCertificates::perturbedStarPatterns` → `perturbedStarPatterns` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
-/
theorem perturbedStarFinalIntersection_excluded (d n r : ℕ)
    (B : PerturbedStarBlocks n r) (ell0 : Fin n)
    (hell0 : ell0 ∈ B.L) (hrtwo : 2 ≤ r) :
    ¬ ∃ Q ∈ perturbedStarPatterns d B,
      Q ∩ ({B.b} ∪ B.T ∪ B.L) = B.T ∪ {ell0} := by
  classical
  rintro ⟨Q, hQ, hintersection⟩
  let P := {B.b} ∪ B.T ∪ B.L
  change Q ∩ P = B.T ∪ {ell0} at hintersection
  have hQcases :
      ((Q ⊆ insert B.a (insert B.b (B.T ∪ B.L)) ∧ B.a ∈ Q ∧
          Q.card ≤ d + 1) ∧
        ∀ Y ⊆ B.L, Y ≠ B.L → ¬ insert B.a (B.T ∪ Y) = Q) ∨
      ∃ Y ⊆ B.L, insert B.b (B.T ∪ Y) = Q := by
    simpa [perturbedStarPatterns, perturbedStarCore] using hQ
  rcases hQcases with hbase | hinsertion
  · rcases hbase with ⟨⟨hQsub, haQ, _⟩, hnotdeleted⟩
    have hbnotQ : B.b ∉ Q := by
      intro hbQ
      have hbP : B.b ∈ P := by
        simp [P]
      have hbintersection : B.b ∈ B.T ∪ {ell0} := by
        rw [← hintersection]
        exact Finset.mem_inter.mpr ⟨hbQ, hbP⟩
      simp only [Finset.mem_union, Finset.mem_singleton] at hbintersection
      rcases hbintersection with hbT | hbell0
      · exact B.b_not_mem_T hbT
      · apply B.b_not_mem_L
        simpa [hbell0] using hell0
    have hTellsingleton_sub_Q : B.T ∪ {ell0} ⊆ Q := by
      intro x hx
      have hxP : x ∈ P := by
        rcases Finset.mem_union.mp hx with hxT | hxell0
        · simp [P, hxT]
        · have hx_eq : x = ell0 := Finset.mem_singleton.mp hxell0
          subst x
          simp [P, hell0]
      have hxintersection : x ∈ Q ∩ P := by
        rw [hintersection]
        exact hx
      exact (Finset.mem_inter.mp hxintersection).1
    have hrepr : Q = insert B.a (B.T ∪ {ell0}) := by
      ext x
      constructor
      · intro hxQ
        have hxcore := hQsub hxQ
        simp only [Finset.mem_insert, Finset.mem_union] at hxcore
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
        rcases hxcore with hxa | hxb | hxT | hxL
        · exact Or.inl hxa
        · exact False.elim (hbnotQ (hxb ▸ hxQ))
        · exact Or.inr (Or.inl hxT)
        · have hxP : x ∈ P := by
            simp [P, hxL]
          have hxintersection : x ∈ Q ∩ P :=
            Finset.mem_inter.mpr ⟨hxQ, hxP⟩
          have hxright : x ∈ B.T ∪ {ell0} := by
            rw [← hintersection]
            exact hxintersection
          simp only [Finset.mem_union, Finset.mem_singleton] at hxright
          rcases hxright with hxT | hxell0
          · exact False.elim (Finset.disjoint_left.mp B.T_disjoint_L hxT hxL)
          · exact Or.inr (Or.inr hxell0)
      · simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
        intro hx
        rcases hx with hxa | hxT | hxell0
        · simpa [hxa] using haQ
        · exact hTellsingleton_sub_Q (Finset.mem_union_left _ hxT)
        · exact hTellsingleton_sub_Q
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr hxell0))
    have hsingleton_sub : ({ell0} : Finset (Fin n)) ⊆ B.L := by
      intro x hx
      simpa only [Finset.mem_singleton.mp hx] using hell0
    have hsingleton_ne : ({ell0} : Finset (Fin n)) ≠ B.L := by
      intro hsingleton
      have hcard : B.L.card = 1 := by
        rw [← hsingleton]
        simp
      rw [B.card_L] at hcard
      omega
    exact hnotdeleted {ell0} hsingleton_sub hsingleton_ne hrepr.symm
  · rcases hinsertion with ⟨Y, _, hQeq⟩
    have hbQ : B.b ∈ Q := by
      rw [← hQeq]
      simp
    have hbP : B.b ∈ P := by
      simp [P]
    have hbintersection : B.b ∈ B.T ∪ {ell0} := by
      rw [← hintersection]
      exact Finset.mem_inter.mpr ⟨hbQ, hbP⟩
    simp only [Finset.mem_union, Finset.mem_singleton] at hbintersection
    rcases hbintersection with hbT | hbell0
    · exact B.b_not_mem_T hbT
    · apply B.b_not_mem_L
      simpa [hbell0] using hell0
```

### Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`

### Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.mem_powerset`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`

### Sources

- `article/sections/02_proof.tex:63-63`

## `perturbedStarParameterBounds`

The immutable d,s,n hypotheses imply the arithmetic bounds required by the perturbed-star construction.

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarParameterBounds`
- Status: `proved` (`committed`)
- Formal code: final proof projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarParameterBounds`

For natural numbers d, s, and n, assume `hd : 4 ≤ d`, `hslow : (d + 3) / 2 ≤ s`, `hshigh : s ≤ d -
1`, and `hn : 2 * (d + 1) ≤ n`. Put `r = d + 1 - s`. Then `2 ≤ r`, `r + 1 ≤ s`, `d - 2*r = 2*s - d -
2`, `2*r ≤ d`, and `2 + 2*r ≤ n`. All subtractions are natural-number subtraction; the theorem
establishes the displayed equality and bounds with the needed nontruncation consequences explicit
under exactly these hypotheses.

## Sources

- Source `article/sections/02_proof.tex`, lines 30–32

## Proof outline

Unfold the `let r := d + 1 - s`.  First use `hshigh : s ≤ d - 1` to obtain `s ≤ d + 1` and the lower
bound `2 ≤ d + 1 - s`; this makes the first subtraction nontruncating.  Next apply `omega` to the
corrected half-bound `hslow : (d + 3) / 2 ≤ s`.  It yields both `d + 2 ≤ 2*s` and hence `r + 1 ≤ s`
and `2*r ≤ d`.

Record the two nontruncation facts before proving the displayed equality: `2*r ≤ d` certifies the
left subtraction `d - 2*r`, while `d + 2 ≤ 2*s` certifies `2*s - d - 2`.  With `r = d + 1 - s`
expanded, `omega` proves the truncation-safe natural-number identity `d - 2*r = 2*s - d - 2`.

Finally combine `2*r ≤ d` with `hn : 2*(d+1) ≤ n`; linear arithmetic gives `2 + 2*r ≤ n`.  Conjoin,
in order, the lower bound for `r`, `r+1≤s`, the subtraction equality, `2*r≤d`, and the ambient-size
inequality.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 30–32
-/
theorem perturbedStarParameterBounds (d s n : ℕ) (hd : 4 ≤ d)
    (hslow : (d + 3) / 2 ≤ s) (hshigh : s ≤ d - 1)
    (hn : 2 * (d + 1) ≤ n) :
    let r := d + 1 - s
    2 ≤ r ∧ r + 1 ≤ s ∧ d - 2 * r = 2 * s - d - 2 ∧
      2 * r ≤ d ∧ 2 + 2 * r ≤ n := by
  dsimp
  have htwo : 2 ≤ d + 1 - s := by omega
  have hhalf : d + 2 ≤ 2 * s := by omega
  have hr_le_d : 2 * (d + 1 - s) ≤ d := by omega
  have hleft : 2 * (d + 1 - s) ≤ d := hr_le_d
  have hright : d + 2 ≤ 2 * s := hhalf
  refine ⟨htwo, ?_, ?_, hr_le_d, ?_⟩
  · omega
  · omega
  · omega
```

### Sources

- `article/sections/02_proof.tex:30-32`

## `perturbedStarPatterns`

The allowed core patterns obtained by perturbing the anchored one-star along the T and L blocks.

- Kind: `definition`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`
- Status: `declared` (`committed`)
- Formal code: statement projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarPatterns`

For natural numbers d, n, and r and construction data `B : PerturbedStarBlocks n r`,
`perturbedStarPatterns d B` is a finite family of finite subsets of `Fin n`, defined from the
following three components.

1. Its base anchored-star component consists of every finite set `P` with `P ⊆ perturbedStarCore B`,
`B.a ∈ P`, and `P.card ≤ d + 1`.
2. From that base component, delete exactly the sets `{B.a} ∪ B.T ∪ Y` for which `Y` is a proper
subset of `B.L`.
3. Insert exactly the sets `{B.b} ∪ B.T ∪ Y` for every subset `Y ⊆ B.L`.

The result is the base component after the stated deletions, union the stated inserted component. In
particular, the insertion includes `Y = B.L` as the final added pattern, while the deletion excludes
that non-proper choice. No filler elements or further hypotheses occur in this definition.

## Sources

- Source `article/sections/02_proof.tex`, lines 35–39

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarCore` → `perturbedStarCore` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`
-/
def perturbedStarPatterns (d : ℕ) {n r : ℕ}
    (B : PerturbedStarBlocks n r) : Finset (Finset (Fin n)) :=
  let base := (perturbedStarCore B).powerset.filter fun P =>
    B.a ∈ P ∧ P.card ≤ d + 1
  let deleted :=
    (B.L.powerset.filter fun Y => Y ⊆ B.L ∧ Y ≠ B.L).image fun Y =>
      {B.a} ∪ B.T ∪ Y
  let inserted := B.L.powerset.image fun Y =>
    {B.b} ∪ B.T ∪ Y
  (base \ deleted) ∪ inserted
```

### Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`

### Sources

- `article/sections/02_proof.tex:35-39`

## `perturbedStarTau`

The source case-defined proper-subpattern certificate selector for perturbed-star patterns.

- Kind: `definition`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau`
- Status: `declared` (`committed`)
- Formal code: statement projection

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarTau`

For natural numbers n and r, construction data `B : PerturbedStarBlocks n r`, and every finite set
`P : Finset (Fin n)`, `perturbedStarTau B P` is a total finite-set-valued selector. It evaluates the
following guarded cases in the displayed priority order. A classical choice is made only after the
indicated witness is available.

1. If `P = {B.b} ∪ B.T ∪ Y` for a proper subset `Y ⊂ B.L`, it returns `B.T`.
2. If `P = {B.b} ∪ B.T ∪ B.L` and there exists `ell0 ∈ B.L`, it chooses such an `ell0` and returns
`B.T ∪ {ell0}`. If this pattern equality holds but `B.L` is empty, this guarded branch is
unavailable and the selector falls through to the empty default.
3. If `B.a ∈ P` and `P.card ≤ r`, it returns `∅`.
4. If `B.a ∈ P`, `P.card > r`, `P ∩ B.T = ∅`, and there exists `Q ⊆ P ∩ B.L` with `Q.card = P.card -
r`, it chooses such a `Q` and returns it. If no such subset exists, this guarded branch falls
through to the empty default.
5. If `B.a ∈ P`, `P.card > r`, `P ∩ B.T ≠ ∅`, and there exist `t0 ∈ P ∩ B.T` and `Q ⊆ P \ {B.a, t0}`
with `Q.card = P.card - r`, it chooses such a pair and returns `Q`. If either required witness is
unavailable, this guarded branch falls through to the empty default.

When none of the preceding guarded cases applies, `perturbedStarTau B P` is `∅`. Later certificate
lemmas prove, for members of `perturbedStarPatterns d B` under the perturbed-star parameter
hypotheses, that the relevant guards and witnesses hold; therefore the intended five source values
apply there while the selector remains total for arbitrary data and inputs.

## Sources

- Source `article/sections/02_proof.tex`, lines 58–72

## Statement dependencies

- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
-/
noncomputable def perturbedStarTau {n r : ℕ}
    (B : PerturbedStarBlocks n r) (P : Finset (Fin n)) : Finset (Fin n) := by
  classical
  by_cases hproperAdded :
    ∃ Y, Y ⊆ B.L ∧ Y ≠ B.L ∧ P = {B.b} ∪ B.T ∪ Y
  · exact B.T
  by_cases hfinalAdded : P = {B.b} ∪ B.T ∪ B.L ∧ ∃ ell0, ell0 ∈ B.L
  · let ell0 := Classical.choose hfinalAdded.2
    exact B.T ∪ {ell0}
  by_cases hsmallStar : B.a ∈ P ∧ P.card ≤ r
  · exact ∅
  by_cases hlargeAvoiding :
    B.a ∈ P ∧ r < P.card ∧ P ∩ B.T = ∅ ∧
      ∃ Q, Q ⊆ P ∩ B.L ∧ Q.card = P.card - r
  · let Q := Classical.choose hlargeAvoiding.2.2.2
    exact Q
  by_cases hlargeMeeting :
    B.a ∈ P ∧ r < P.card ∧ P ∩ B.T ≠ ∅ ∧
      ∃ t0, t0 ∈ P ∩ B.T ∧ ∃ Q, Q ⊆ P \ {B.a, t0} ∧ Q.card = P.card - r
  · let t0 := Classical.choose hlargeMeeting.2.2.2
    let Q := Classical.choose (Classical.choose_spec hlargeMeeting.2.2.2).2
    exact Q
  · exact ∅
```

### Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

### Sources

- `article/sections/02_proof.tex:58-72`

## `perturbedStar_isUniformMissingTraceFamily`

The explicit perturbed-star construction yields a uniform family with the fixed missing-trace property.

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStar_isUniformMissingTraceFamily`
- Status: `proved` (`committed`)
- Formal code: final proof projection

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

### Statement dependencies

- `current repo:Main.PatternCriterion.IsUniformMissingTraceFamily`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFamily`

### Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `current repo:Main.PatternCriterion.patternFamily_isUniformMissingTraceFamily`
- `current repo:Main.PerturbedStarCertificates.exists_perturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCertificate_addedProper`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCertificate_finalAdded`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCertificate_largeAvoiding`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCertificate_largeMeeting`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCertificate_smallStar`
- `current repo:Main.PerturbedStarCertificates.perturbedStarParameterBounds`

### Sources

- `article/sections/02_proof.tex:30-39`
- `article/sections/02_proof.tex:53-73`

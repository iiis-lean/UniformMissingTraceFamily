# Public API

## `anchoredPowerset_weightedSum_eq_chooseSum`

- Kind: `theorem`
- Node: `Main.AnchoredPowersetEnumeration`
- Module: `UniformMissingTraceFamily.Main.AnchoredPowersetEnumeration.Theorems.anchoredPowerset_weightedSum_eq_chooseSum`

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.AnchoredPowersetEnumeration.Prelude
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
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
-/
theorem anchoredPowerset_weightedSum_eq_chooseSum {α : Type*} [DecidableEq α]
    (C U : Finset α) (a : α) (d : ℕ) (ha : a ∈ C) :
    ∑ P ∈ C.powerset.filter (fun P => a ∈ P ∧ P.card ≤ d + 1),
        Nat.choose U.card (d + 1 - P.card) =
      ∑ j ∈ Finset.range (d + 1),
        Nat.choose (C.erase a).card j * Nat.choose U.card (d - j) := by
  sorry
```

Statement dependencies:
- `Mathlib:Mathlib.Data.Finset.Filter.Finset.filter`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.powerset`
- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose`

## `exists_uniformMissingTraceFamily_strictlyLargerThanStar`

- Kind: `theorem`
- Node: `Main.CountingAndMain`
- Module: `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.exists_uniformMissingTraceFamily_strictlyLargerThanStar`

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Nat.Choose.Basic
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
  sorry
```

Statement dependencies:
- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose`
- `current repo:Main.PatternCriterion.IsUniformMissingTraceFamily`

## `perturbedStarFamily_card`

- Kind: `theorem`
- Node: `Main.CountingAndMain`
- Module: `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarFamily_card`

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Nat.Choose.Basic
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
-/
theorem perturbedStarFamily_card {n r d : ℕ} (B : PerturbedStarBlocks n r)
    (hrd : 2 * r ≤ d) (hrn : 2 + 2 * r ≤ n) :
    (perturbedStarFamily d B).card =
      Nat.choose (n - 1) d + Nat.choose (n - 2 * r - 2) (d - 2 * r) := by
  sorry
```

Statement dependencies:
- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFamily`

## `IsUniformMissingTraceFamily`

- Kind: `definition`
- Node: `Main.PatternCriterion`
- Module: `UniformMissingTraceFamily.Main.PatternCriterion.Defs.IsUniformMissingTraceFamily`

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

## `card_eq_of_mem_patternFamily`

- Kind: `theorem`
- Node: `Main.PatternCriterion`
- Module: `UniformMissingTraceFamily.Main.PatternCriterion.Theorems.card_eq_of_mem_patternFamily`

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PatternCriterion.Prelude
import UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily
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
-/
theorem card_eq_of_mem_patternFamily {n d : ℕ} (C U : Finset (Fin n))
    (patterns : Finset (Finset (Fin n))) (F : Finset (Fin n))
    (hCU : Disjoint C U) (h_patterns_subset : ∀ P ∈ patterns, P ⊆ C)
    (h_patterns_card : ∀ P ∈ patterns, P.card ≤ d + 1)
    (hF : F ∈ patternFamily d patterns U) : F.card = d + 1 := by
  sorry
```

Statement dependencies:
- `current repo:Main.PatternCriterion.patternFamily`

## `mem_patternFamily`

- Kind: `theorem`
- Node: `Main.PatternCriterion`
- Module: `UniformMissingTraceFamily.Main.PatternCriterion.Theorems.mem_patternFamily`

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PatternCriterion.Prelude
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
-/
theorem mem_patternFamily {n d : ℕ} (patterns : Finset (Finset (Fin n)))
    (U F : Finset (Fin n)) :
    F ∈ patternFamily d patterns U ↔
      ∃ P : Finset (Fin n), P ∈ patterns ∧
        ∃ A : Finset (Fin n), A ⊆ U ∧ A.card = d + 1 - P.card ∧ F = P ∪ A := by
  sorry
```

Statement dependencies:
- `current repo:Main.PatternCriterion.patternFamily`

## `patternFamily`

- Kind: `definition`
- Node: `Main.PatternCriterion`
- Module: `UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily`

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

Statement dependencies:
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.powersetCard`

## `patternFamily_isUniformMissingTraceFamily`

- Kind: `theorem`
- Node: `Main.PatternCriterion`
- Module: `UniformMissingTraceFamily.Main.PatternCriterion.Theorems.patternFamily_isUniformMissingTraceFamily`

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PatternCriterion.Prelude
import UniformMissingTraceFamily.Main.PatternCriterion.Defs.IsUniformMissingTraceFamily
import UniformMissingTraceFamily.Main.PatternCriterion.Defs.patternFamily
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
  sorry
```

Statement dependencies:
- `current repo:Main.PatternCriterion.IsUniformMissingTraceFamily`
- `current repo:Main.PatternCriterion.patternFamily`

## `perturbedPattern_properWeights_add_full_eq_fullWeights`

- Kind: `theorem`
- Node: `Main.PerturbedPatternCancellation`
- Module: `UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPattern_properWeights_add_full_eq_fullWeights`

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
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
  sorry
```

Statement dependencies:
- `Mathlib:Mathlib.Algebra.BigOperators.Group.Finset.Defs.Finset.sum`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.card`
- `Mathlib:Mathlib.Data.Finset.Filter.Finset.filter`
- `Mathlib:Mathlib.Data.Finset.Image.Finset.image`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.powerset`
- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFiller`

## `PerturbedStarBlocks`

- Kind: `structure`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`

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

## `exists_perturbedStarBlocks`

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.exists_perturbedStarBlocks`

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
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
-/
theorem exists_perturbedStarBlocks (n r : ℕ) (hroom : 2 + 2 * r ≤ n) :
    Nonempty (PerturbedStarBlocks n r) := by
  sorry
```

Statement dependencies:
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

## `perturbedStarCertificate_addedProper`

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_addedProper`

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
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
  sorry
```

Statement dependencies:
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

## `perturbedStarCertificate_finalAdded`

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_finalAdded`

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

Statement dependencies:
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

## `perturbedStarCertificate_largeAvoiding`

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_largeAvoiding`

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

Statement dependencies:
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

## `perturbedStarCertificate_largeMeeting`

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_largeMeeting`

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
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
  sorry
```

Statement dependencies:
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

## `perturbedStarCertificate_smallStar`

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarCertificate_smallStar`

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
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
  sorry
```

Statement dependencies:
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`
- `current repo:Main.PerturbedStarCertificates.perturbedStarTau`

## `perturbedStarCore`

- Kind: `definition`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarCore`

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

Statement dependencies:
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

## `perturbedStarFamily`

- Kind: `definition`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFamily`

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

Statement dependencies:
- `current repo:Main.PatternCriterion.patternFamily`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFiller`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`

## `perturbedStarFiller`

- Kind: `definition`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`

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

Statement dependencies:
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`

## `perturbedStarFinalIntersection_excluded`

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarFinalIntersection_excluded`

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
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
-/
theorem perturbedStarFinalIntersection_excluded (d n r : ℕ)
    (B : PerturbedStarBlocks n r) (ell0 : Fin n)
    (hell0 : ell0 ∈ B.L) (hrtwo : 2 ≤ r) :
    ¬ ∃ Q ∈ perturbedStarPatterns d B,
      Q ∩ ({B.b} ∪ B.T ∪ B.L) = B.T ∪ {ell0} := by
  sorry
```

Statement dependencies:
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`

## `perturbedStarParameterBounds`

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarParameterBounds`

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
-/
theorem perturbedStarParameterBounds (d s n : ℕ) (hd : 4 ≤ d)
    (hslow : (d + 3) / 2 ≤ s) (hshigh : s ≤ d - 1)
    (hn : 2 * (d + 1) ≤ n) :
    let r := d + 1 - s
    2 ≤ r ∧ r + 1 ≤ s ∧ d - 2 * r = 2 * s - d - 2 ∧
      2 * r ≤ d ∧ 2 + 2 * r ≤ n := by
  sorry
```

## `perturbedStarPatterns`

- Kind: `definition`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarPatterns`

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

Statement dependencies:
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`

## `perturbedStarTau`

- Kind: `definition`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau`

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

Statement dependencies:
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

## `perturbedStar_isUniformMissingTraceFamily`

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStar_isUniformMissingTraceFamily`

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

Statement dependencies:
- `current repo:Main.PatternCriterion.IsUniformMissingTraceFamily`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarFamily`

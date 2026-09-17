[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `perturbedStarExtra_choose_pos`

The unpaired perturbed-star binomial contribution is positive in the immutable middle parameter range.

- Kind: `theorem`
- Node: `Main.CountingAndMain`
- Module: `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.perturbedStarExtra_choose_pos`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For natural numbers `d`, `s`, and `n`, if `hd : 4 ≤ d`, `hslow : (d + 3) / 2 ≤ s`, `hshigh : s ≤ d - 1`, and `hn : 2 * (d + 1) ≤ n`, then
`0 < Nat.choose (n - 2 * (d + 1 - s) - 2) (2 * s - d - 2)`.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Nat.Choose.Basic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarExtra_choose_pos`

For natural numbers `d`, `s`, and `n`, if `hd : 4 ≤ d`, `hslow : (d + 3) / 2 ≤ s`, `hshigh : s ≤ d -
1`, and `hn : 2 * (d + 1) ≤ n`, then
`0 < Nat.choose (n - 2 * (d + 1 - s) - 2) (2 * s - d - 2)`.

## Sources

- Source `article/sections/02_proof.tex`, lines 75–79
- Source `formal_target.lean`, lines 14–24

## Statement dependencies

- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
-/
theorem perturbedStarExtra_choose_pos {d s n : ℕ} (hd : 4 ≤ d)
    (hslow : (d + 3) / 2 ≤ s) (hshigh : s ≤ d - 1)
    (hn : 2 * (d + 1) ≤ n) :
    0 < Nat.choose (n - 2 * (d + 1 - s) - 2) (2 * s - d - 2) := by
  sorry
```

## Proof NL

Set `r := d + 1 - s` and instantiate the proof-accepted lower interface `Main.PerturbedStarCertificates::perturbedStarParameterBounds d s n hd hslow hshigh hn`. Destructure its conclusions to obtain the exact rewrite `d - 2 * r = 2 * s - d - 2`, together with `2 * r ≤ d`, `2 + 2 * r ≤ n`, and the stated nontruncation bounds for `r`.

Use `hn` and `hd` in elementary natural-number arithmetic to derive `d - 2 * r ≤ n - 2 * r - 2`; the provider’s `2 * r ≤ d` ensures this is the intended lower index. Apply verified `Nat.choose_pos` to get `0 < Nat.choose (n - 2 * r - 2) (d - 2 * r)`. Finally unfold `r` and rewrite its lower choice index with the provider equality, yielding exactly `0 < Nat.choose (n - 2 * (d + 1 - s) - 2) (2 * s - d - 2)`. No construction or cardinality result is reproved.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Nat.Choose.Basic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarExtra_choose_pos`

For natural numbers `d`, `s`, and `n`, if `hd : 4 ≤ d`, `hslow : (d + 3) / 2 ≤ s`, `hshigh : s ≤ d -
1`, and `hn : 2 * (d + 1) ≤ n`, then
`0 < Nat.choose (n - 2 * (d + 1 - s) - 2) (2 * s - d - 2)`.

## Sources

- Source `article/sections/02_proof.tex`, lines 75–79
- Source `formal_target.lean`, lines 14–24

## Statement dependencies

- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`

## Proof outline

Set `r := d + 1 - s` and instantiate the proof-accepted lower interface
`Main.PerturbedStarCertificates::perturbedStarParameterBounds d s n hd hslow hshigh hn`. Destructure
its conclusions to obtain the exact rewrite `d - 2 * r = 2 * s - d - 2`, together with `2 * r ≤ d`,
`2 + 2 * r ≤ n`, and the stated nontruncation bounds for `r`.

Use `hn` and `hd` in elementary natural-number arithmetic to derive `d - 2 * r ≤ n - 2 * r - 2`; the
provider’s `2 * r ≤ d` ensures this is the intended lower index. Apply verified `Nat.choose_pos` to
get `0 < Nat.choose (n - 2 * r - 2) (d - 2 * r)`. Finally unfold `r` and rewrite its lower choice
index with the provider equality, yielding exactly `0 < Nat.choose (n - 2 * (d + 1 - s) - 2) (2 * s
- d - 2)`. No construction or cardinality result is reproved.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 75–79

## Proof dependencies

- `Nat.choose_pos` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PerturbedStarCertificates::perturbedStarParameterBounds` → `perturbedStarParameterBounds`
  from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarParameterBounds`
-/
theorem perturbedStarExtra_choose_pos {d s n : ℕ} (hd : 4 ≤ d)
    (hslow : (d + 3) / 2 ≤ s) (hshigh : s ≤ d - 1)
    (hn : 2 * (d + 1) ≤ n) :
    0 < Nat.choose (n - 2 * (d + 1 - s) - 2) (2 * s - d - 2) := by
  rcases perturbedStarParameterBounds d s n hd hslow hshigh hn with
    ⟨hr_two, hr_s, hrewrite, hrd, hrn⟩
  apply Nat.choose_pos
  omega
```

## Statement dependencies

- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose`

## Proof dependencies

- `Mathlib:Mathlib.Data.Nat.Choose.Basic.Nat.choose_pos`
- `current repo:Main.PerturbedStarCertificates.perturbedStarParameterBounds`

## Sources

- `article/sections/02_proof.tex:75-79`
- `formal_target.lean:14-24`

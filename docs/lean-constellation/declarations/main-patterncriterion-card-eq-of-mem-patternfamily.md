[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md)

# `card_eq_of_mem_patternFamily`

Every member of a pattern family has cardinality d+1 when allowed patterns lie in a core disjoint from the filler region and have size at most d+1.

- Kind: `theorem`
- Node: `Main.PatternCriterion`
- Module: `UniformMissingTraceFamily.Main.PatternCriterion.Theorems.card_eq_of_mem_patternFamily`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

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

## Statement dependencies

- `current repo:Main.PatternCriterion.patternFamily`

## Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_union_of_disjoint`
- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `current repo:Main.PatternCriterion.mem_patternFamily`

## Sources

- `article/sections/02_proof.tex:3-17`

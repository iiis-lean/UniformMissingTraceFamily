[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `completionFibers_pairwiseDisjoint`

Distinct patterns disjoint from a common filler have disjoint completion fibers.

- Kind: `theorem`
- Node: `Main.CountingAndMain`
- Module: `UniformMissingTraceFamily.Main.CountingAndMain.Theorems.completionFibers_pairwiseDisjoint`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For natural numbers n and d, a finite pattern family `patterns : Finset (Finset (Fin n))`, and a filler `U : Finset (Fin n)`, suppose every `P ∈ patterns` is disjoint from `U`.  Then the completion fibers `(U.powersetCard (d + 1 - P.card)).image (fun A => P ∪ A)`, indexed by `P ∈ patterns`, are pairwise disjoint: whenever `P` and `Q` are distinct members of `patterns`, the corresponding two image Finsets are disjoint.  This generic conclusion specializes to the perturbed-star patterns and their complementary filler after establishing the stated disjointness premise.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Finset.Powerset
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `completionFibers_pairwiseDisjoint`

For natural numbers n and d, a finite pattern family `patterns : Finset (Finset (Fin n))`, and a
filler `U : Finset (Fin n)`, suppose every `P ∈ patterns` is disjoint from `U`.  Then the completion
fibers `(U.powersetCard (d + 1 - P.card)).image (fun A => P ∪ A)`, indexed by `P ∈ patterns`, are
pairwise disjoint: whenever `P` and `Q` are distinct members of `patterns`, the corresponding two
image Finsets are disjoint.  This generic conclusion specializes to the perturbed-star patterns and
their complementary filler after establishing the stated disjointness premise.

## Sources

- Source `article/sections/02_proof.tex`, lines 41–50

## Statement dependencies

- `Finset.powersetCard` from `Mathlib.Data.Finset.Powerset`
-/
theorem completionFibers_pairwiseDisjoint {n d : ℕ}
    (patterns : Finset (Finset (Fin n))) (U : Finset (Fin n))
    (hdisj : ∀ P ∈ patterns, Disjoint P U) :
    (patterns : Set (Finset (Fin n))).PairwiseDisjoint (fun P =>
      (U.powersetCard (d + 1 - P.card)).image (fun A => P ∪ A)) := by
  sorry
```

## Proof NL

Unfold `Set.PairwiseDisjoint` and take distinct `P,Q ∈ patterns`.  To show the two image Finsets are disjoint, use `Finset.disjoint_left` and suppose a set `X` belongs to both images.  Obtain witnesses `A ∈ U.powersetCard (d + 1 - P.card)` and `A' ∈ U.powersetCard (d + 1 - Q.card)` with `X = P ∪ A = Q ∪ A'`.  By `Finset.mem_powersetCard`, both fillers are subsets of `U`; by `hdisj`, both patterns are disjoint from `U`.

Take the difference of the equality with `U`, or equivalently argue pointwise: for every element, membership in `(P ∪ A) \ U` is equivalent to membership in `P`, and membership in `(Q ∪ A') \ U` is equivalent to membership in `Q`.  Thus `P = Q`, contradicting the pairwise distinctness hypothesis.  All witness extraction and the recovery-by-difference argument are lightweight local Finset reasoning, so no extra helper declaration is required.  The resulting pairwise-disjoint statement is exactly the hypothesis later consumed by `Finset.card_biUnion`.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.CountingAndMain.Prelude
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Powerset
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `completionFibers_pairwiseDisjoint`

For natural numbers n and d, a finite pattern family `patterns : Finset (Finset (Fin n))`, and a
filler `U : Finset (Fin n)`, suppose every `P ∈ patterns` is disjoint from `U`.  Then the completion
fibers `(U.powersetCard (d + 1 - P.card)).image (fun A => P ∪ A)`, indexed by `P ∈ patterns`, are
pairwise disjoint: whenever `P` and `Q` are distinct members of `patterns`, the corresponding two
image Finsets are disjoint.  This generic conclusion specializes to the perturbed-star patterns and
their complementary filler after establishing the stated disjointness premise.

## Sources

- Source `article/sections/02_proof.tex`, lines 41–50

## Statement dependencies

- `Finset.powersetCard` from `Mathlib.Data.Finset.Powerset`

## Proof outline

Unfold `Set.PairwiseDisjoint` and take distinct `P,Q ∈ patterns`.  To show the two image Finsets are
disjoint, use `Finset.disjoint_left` and suppose a set `X` belongs to both images.  Obtain witnesses
`A ∈ U.powersetCard (d + 1 - P.card)` and `A' ∈ U.powersetCard (d + 1 - Q.card)` with `X = P ∪ A = Q
∪ A'`.  By `Finset.mem_powersetCard`, both fillers are subsets of `U`; by `hdisj`, both patterns are
disjoint from `U`.

Take the difference of the equality with `U`, or equivalently argue pointwise: for every element,
membership in `(P ∪ A) \ U` is equivalent to membership in `P`, and membership in `(Q ∪ A') \ U` is
equivalent to membership in `Q`.  Thus `P = Q`, contradicting the pairwise distinctness hypothesis.
All witness extraction and the recovery-by-difference argument are lightweight local Finset
reasoning, so no extra helper declaration is required.  The resulting pairwise-disjoint statement is
exactly the hypothesis later consumed by `Finset.card_biUnion`.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 41–50

## Proof dependencies

- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Finset.mem_powersetCard` from `Mathlib.Data.Finset.Powerset`
-/
theorem completionFibers_pairwiseDisjoint {n d : ℕ}
    (patterns : Finset (Finset (Fin n))) (U : Finset (Fin n))
    (hdisj : ∀ P ∈ patterns, Disjoint P U) :
    (patterns : Set (Finset (Fin n))).PairwiseDisjoint (fun P =>
      (U.powersetCard (d + 1 - P.card)).image (fun A => P ∪ A)) := by
  intro P hP Q hQ hPQ
  change Disjoint
    ((U.powersetCard (d + 1 - P.card)).image (fun A => P ∪ A))
    ((U.powersetCard (d + 1 - Q.card)).image (fun A => Q ∪ A))
  rw [Finset.disjoint_left]
  intro X hXP hXQ
  rcases Finset.mem_image.mp hXP with ⟨A, hA, hXA⟩
  rcases Finset.mem_image.mp hXQ with ⟨A', hA', hXA'⟩
  apply hPQ
  apply Finset.ext
  intro x
  constructor
  · intro hxP
    have hxUnionP : x ∈ P ∪ A := Finset.mem_union_left A hxP
    have hxUnionQ : x ∈ Q ∪ A' := by
      have hxX : x ∈ X := hXA ▸ hxUnionP
      rw [hXA']
      exact hxX
    rcases Finset.mem_union.mp hxUnionQ with hxQ | hxA'
    · exact hxQ
    · have hxU : x ∈ U := (Finset.mem_powersetCard.mp hA').1 hxA'
      exact False.elim ((Finset.disjoint_left.mp (hdisj P hP)) hxP hxU)
  · intro hxQ
    have hxUnionQ : x ∈ Q ∪ A' := Finset.mem_union_left A' hxQ
    have hxUnionP : x ∈ P ∪ A := by
      have hxX : x ∈ X := hXA' ▸ hxUnionQ
      rw [hXA]
      exact hxX
    rcases Finset.mem_union.mp hxUnionP with hxP | hxA
    · exact hxP
    · have hxU : x ∈ U := (Finset.mem_powersetCard.mp hA).1 hxA
      exact False.elim ((Finset.disjoint_left.mp (hdisj Q hQ)) hxQ hxU)
```

## Statement dependencies

- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.powersetCard`

## Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.mem_powersetCard`

## Sources

- `article/sections/02_proof.tex:41-50`

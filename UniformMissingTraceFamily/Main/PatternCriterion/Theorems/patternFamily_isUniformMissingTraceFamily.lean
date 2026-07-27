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

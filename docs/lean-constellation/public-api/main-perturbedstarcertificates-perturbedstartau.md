[← Public API index](../PUBLIC_API.md)

# `perturbedStarTau`

The source case-defined proper-subpattern certificate selector for perturbed-star patterns.

- Kind: `definition`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarTau`
- State: `declared`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final statement projection

## Lean code

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

## Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

## Sources

- `article/sections/02_proof.tex:58-72`

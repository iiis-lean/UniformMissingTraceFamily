[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `perturbedStarFinalIntersection_excluded`

No allowed perturbed-star pattern intersects the final b/T/L pattern in T plus exactly one L-element.

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.perturbedStarFinalIntersection_excluded`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For natural numbers `d`, `n`, and `r`, let `B : PerturbedStarBlocks n r` and let `ell0 : Fin n` satisfy `ell0 ∈ B.L`. If `2 ≤ r`, then there is no `Q ∈ perturbedStarPatterns d B` for which

`Q ∩ ({B.b} ∪ B.T ∪ B.L) = B.T ∪ {ell0}`.

Equivalently, no allowed perturbed-star pattern has intersection with the final inserted `b/T/L` pattern equal to all of `T` together with exactly the single L-element `ell0`. This isolates the source line-63 exclusion: inserted patterns contain `B.b`, while a base pattern with this intersection would be the deleted proper-L pattern `{B.a} ∪ B.T ∪ {ell0}`.

## Statement Formal

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

## Proof NL

Assume `Q ∈ perturbedStarPatterns d B` and
```
Q ∩ ({B.b} ∪ B.T ∪ B.L) = B.T ∪ {ell0}.
```
Unfold `perturbedStarPatterns` and simplify membership in its powersets, images, filters, union, and difference (using `Finset.mem_powerset`). This gives the inserted and base-minus-deleted branches of the accepted definition.

* In the inserted branch, for some `Z ⊆ B.L`,
  `Q = {B.b} ∪ B.T ∪ Z`. The point `B.b` belongs to both `Q` and the final set `{B.b} ∪ B.T ∪ B.L`, hence to their intersection. But `B.b ∉ B.T ∪ {ell0}`: use `B.b_not_mem_T`, `B.b_not_mem_L`, and `hell0`. This contradicts the displayed intersection equality.

* In the base-minus-deleted branch, unfold `perturbedStarCore` in the base membership. It gives `B.a ∈ Q` and
  `Q ⊆ {B.a, B.b} ∪ B.T ∪ B.L`. The intersection equality forces `B.b ∉ Q`, forces every element of `B.T ∪ {ell0}` into `Q`, and excludes every element of `B.L \ {ell0}` from `Q`. For the last two claims use the anchor-avoidance fields and `B.T_disjoint_L` elementwise through `Finset.disjoint_left`. Extensionality with the core containment now yields
  ```
  Q = {B.a} ∪ B.T ∪ {ell0}.
  ```

It remains to show that this exact set is deleted. The singleton `{ell0}` is contained in `B.L` by `hell0`. If it equalled `B.L`, simp would give `B.L.card = 1`; after rewriting with `B.card_L`, this contradicts `hrtwo : 2 ≤ r`. Thus `{ell0} ⊂ B.L`. Its powerset and filter witnesses therefore place
`{B.a} ∪ B.T ∪ {ell0}` in the deleted image. This contradicts the base-minus-deleted membership of `Q`.

Both raw construction branches are impossible, proving the exact no-`Q` conclusion.

## Proof Formal

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

## Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`

## Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `Mathlib:Mathlib.Data.Finset.Powerset.Finset.mem_powerset`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`
- `current repo:Main.PerturbedStarCertificates.perturbedStarCore`
- `current repo:Main.PerturbedStarCertificates.perturbedStarPatterns`

## Sources

- `article/sections/02_proof.tex:63-63`

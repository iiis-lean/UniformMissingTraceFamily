[← Public API index](../PUBLIC_API.md)

# `exists_perturbedStarBlocks`

Sufficient ambient size yields explicit perturbed-star block data.

- Kind: `theorem`
- Node: `Main.PerturbedStarCertificates`
- Module: `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Theorems.exists_perturbedStarBlocks`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Formal code: final proof projection

## Lean code

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

## Statement dependencies

- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

## Proof dependencies

- `Mathlib:Mathlib.Data.Fin.Embedding.Fin.castLEEmb`
- `Mathlib:Mathlib.Data.Fin.Embedding.Fin.natAddEmb`
- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_map`
- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `Mathlib:Mathlib.Data.Finset.Image.Finset.disjoint_map`
- `Mathlib:Mathlib.Data.Fintype.Card.Finset.card_univ`
- `Mathlib:Mathlib.Data.Fintype.Card.Fintype.card_fin`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

## Sources

- `article/sections/02_proof.tex:32-32`

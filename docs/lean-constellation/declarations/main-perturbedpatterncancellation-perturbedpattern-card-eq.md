[← Public API](../PUBLIC_API.md) · [Public boundaries](../PUBLIC_BOUNDARIES.md) · [Complete graph](../DECLARATION_GRAPH.md)

# `perturbedPattern_card_eq`

Matched a- and b-anchored perturbed patterns have equal cardinality.

- Kind: `theorem`
- Node: `Main.PerturbedPatternCancellation`
- Module: `UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPattern_card_eq`
- State: `proved`
- Revision status: `committed`
- Repository completion: `graph_proved`
- Compatibility `formal_code`: final proof projection

## Statement NL

For every `B : PerturbedStarBlocks n r` and every finite set `Y` with `Y ⊆ B.L`, the exact deleted and added pattern constructors have equal cardinality:

`({B.a} ∪ B.T ∪ Y).card = ({B.b} ∪ B.T ∪ Y).card`.

No additional hypotheses, including `hrd` or `hrn`, are assumed.

## Statement Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Prelude
import Mathlib.Data.Finset.Card
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedPattern_card_eq`

For every `B : PerturbedStarBlocks n r` and every finite set `Y` with `Y ⊆ B.L`, the exact deleted
and added pattern constructors have equal cardinality:

`({B.a} ∪ B.T ∪ Y).card = ({B.b} ∪ B.T ∪ Y).card`.

No additional hypotheses, including `hrd` or `hrn`, are assumed.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Finset.card` from `Mathlib.Data.Finset.Card`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
-/
theorem perturbedPattern_card_eq {n r : ℕ} (B : PerturbedStarBlocks n r)
    (Y : Finset (Fin n)) (hY : Y ⊆ B.L) :
    ({B.a} ∪ B.T ∪ Y).card = ({B.b} ∪ B.T ∪ Y).card := by
  sorry
```

## Proof NL

Fix `B`, `Y`, and `hY : Y ⊆ B.L`.  Prove four disjointness facts with `Finset.disjoint_left`: `{B.a}` is disjoint from `B.T` by `B.a_not_mem_T`; `{B.b}` is disjoint from `B.T` by `B.b_not_mem_T`; and each of `{B.a} ∪ B.T` and `{B.b} ∪ B.T` is disjoint from `Y`.  For the latter two, normalize the singleton/union membership branches with `Finset.mem_singleton` and `Finset.mem_union`; use `hY` to place a member of `Y` in `B.L`; then contradict the relevant anchor-avoidance field or `B.T_disjoint_L`.

Use `Finset.card_union_of_disjoint` first on each outer union `({B.a} ∪ B.T) ∪ Y` and `({B.b} ∪ B.T) ∪ Y`, and then on the singleton–`B.T` unions.  Both cardinalities reduce to the same expression `1 + B.T.card + Y.card`; finish by the lightweight simplification of singleton cardinality and associativity.  This uses exactly the required constructors and only the recorded block-avoidance/disjointness data, with no `hrd` or `hrn` assumptions and no helper declaration.

## Proof Formal

```lean
-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Prelude
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedPattern_card_eq`

For every `B : PerturbedStarBlocks n r` and every finite set `Y` with `Y ⊆ B.L`, the exact deleted
and added pattern constructors have equal cardinality:

`({B.a} ∪ B.T ∪ Y).card = ({B.b} ∪ B.T ∪ Y).card`.

No additional hypotheses, including `hrd` or `hrn`, are assumed.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Finset.card` from `Mathlib.Data.Finset.Card`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`

## Proof outline

Fix `B`, `Y`, and `hY : Y ⊆ B.L`.  Prove four disjointness facts with `Finset.disjoint_left`:
`{B.a}` is disjoint from `B.T` by `B.a_not_mem_T`; `{B.b}` is disjoint from `B.T` by
`B.b_not_mem_T`; and each of `{B.a} ∪ B.T` and `{B.b} ∪ B.T` is disjoint from `Y`.  For the latter
two, normalize the singleton/union membership branches with `Finset.mem_singleton` and
`Finset.mem_union`; use `hY` to place a member of `Y` in `B.L`; then contradict the relevant
anchor-avoidance field or `B.T_disjoint_L`.

Use `Finset.card_union_of_disjoint` first on each outer union `({B.a} ∪ B.T) ∪ Y` and `({B.b} ∪ B.T)
∪ Y`, and then on the singleton–`B.T` unions.  Both cardinalities reduce to the same expression `1 +
B.T.card + Y.card`; finish by the lightweight simplification of singleton cardinality and
associativity.  This uses exactly the required constructors and only the recorded
block-avoidance/disjointness data, with no `hrd` or `hrn` assumptions and no helper declaration.

## Proof sources

- Source `article/sections/02_proof.tex`, line 49

## Proof dependencies

- `Finset.card_union_of_disjoint` from `Mathlib.Data.Finset.Card`
- `Finset.disjoint_left` from `Mathlib.Data.Finset.Disjoint`
- `Finset.mem_singleton` from `Mathlib.Data.Finset.Insert`
- `Finset.mem_union` from `Mathlib.Data.Finset.Lattice.Basic`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
-/
theorem perturbedPattern_card_eq {n r : ℕ} (B : PerturbedStarBlocks n r)
    (Y : Finset (Fin n)) (hY : Y ⊆ B.L) :
    ({B.a} ∪ B.T ∪ Y).card = ({B.b} ∪ B.T ∪ Y).card := by
  have haT : Disjoint ({B.a} : Finset (Fin n)) B.T := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxa hxT
    have hxa' : x = B.a := Finset.mem_singleton.mp hxa
    subst x
    exact B.a_not_mem_T hxT
  have hbT : Disjoint ({B.b} : Finset (Fin n)) B.T := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxb hxT
    have hxb' : x = B.b := Finset.mem_singleton.mp hxb
    subst x
    exact B.b_not_mem_T hxT
  have haTY : Disjoint ({B.a} ∪ B.T) Y := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hxY
    rcases Finset.mem_union.mp hx with hxa | hxT
    · have hxa' : x = B.a := Finset.mem_singleton.mp hxa
      subst x
      exact B.a_not_mem_L (hY hxY)
    · exact (Finset.disjoint_left.mp B.T_disjoint_L hxT (hY hxY)).elim
  have hbTY : Disjoint ({B.b} ∪ B.T) Y := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hxY
    rcases Finset.mem_union.mp hx with hxb | hxT
    · have hxb' : x = B.b := Finset.mem_singleton.mp hxb
      subst x
      exact B.b_not_mem_L (hY hxY)
    · exact (Finset.disjoint_left.mp B.T_disjoint_L hxT (hY hxY)).elim
  rw [Finset.card_union_of_disjoint haTY, Finset.card_union_of_disjoint hbTY,
    Finset.card_union_of_disjoint haT, Finset.card_union_of_disjoint hbT]
  simp
```

## Statement dependencies

- `Mathlib:Mathlib.Data.Finset.Card.Finset.card`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

## Proof dependencies

- `Mathlib:Mathlib.Data.Finset.Card.Finset.card_union_of_disjoint`
- `Mathlib:Mathlib.Data.Finset.Disjoint.Finset.disjoint_left`
- `Mathlib:Mathlib.Data.Finset.Insert.Finset.mem_singleton`
- `Mathlib:Mathlib.Data.Finset.Lattice.Basic.Finset.mem_union`
- `current repo:Main.PerturbedStarCertificates.PerturbedStarBlocks`

## Sources

- `article/sections/02_proof.tex:49-49`

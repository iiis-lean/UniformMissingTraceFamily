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

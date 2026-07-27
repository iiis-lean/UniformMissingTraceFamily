-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Prelude
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPattern_card_eq
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedPattern_chooseWeight_eq`

For every `B : PerturbedStarBlocks n r`, every natural number `d`, and every finite set `Y` with `Y
⊆ B.L`, the exact completion weights of the matched deleted and added patterns are equal:

`Nat.choose (perturbedStarFiller B).card (d + 1 - ({B.a} ∪ B.T ∪ Y).card) = Nat.choose
(perturbedStarFiller B).card (d + 1 - ({B.b} ∪ B.T ∪ Y).card)`.

No additional hypotheses, including `hrd` or `hrn`, are assumed.

## Sources

- Source `article/sections/02_proof.tex`, line 49

## Statement dependencies

- `Finset.card` from `Mathlib.Data.Finset.Card`
- `Nat.choose` from `Mathlib.Data.Nat.Choose.Basic`
- `Main.PerturbedStarCertificates::PerturbedStarBlocks` → `PerturbedStarBlocks` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Types.PerturbedStarBlocks`
- `Main.PerturbedStarCertificates::perturbedStarFiller` → `perturbedStarFiller` from
  `UniformMissingTraceFamily.Main.PerturbedStarCertificates.Defs.perturbedStarFiller`

## Proof outline

Fix `B`, `d`, `Y`, and `hY : Y ⊆ B.L`.  Apply the accepted project theorem `perturbedPattern_card_eq
B Y hY` to rewrite the cardinality of the exact a-anchored constructor `{B.a} ∪ B.T ∪ Y` to the
cardinality of the exact b-anchored constructor `{B.b} ∪ B.T ∪ Y`.

After this rewrite, the two subtraction arguments to `Nat.choose (perturbedStarFiller B).card` are
definitionally identical, so the equality closes by reflexivity (or `simpa`).  No property of
`perturbedStarFiller` beyond its occurrence in the unchanged common first argument is used.  This
preserves the required constructors, uses no `hrd` or `hrn` assumptions, and needs no helper
declaration.

## Proof sources

- Source `article/sections/02_proof.tex`, line 49

## Proof dependencies

- `Main.PerturbedPatternCancellation::perturbedPattern_card_eq` → `perturbedPattern_card_eq` from
  `UniformMissingTraceFamily.Main.PerturbedPatternCancellation.Theorems.perturbedPattern_card_eq`
-/
theorem perturbedPattern_chooseWeight_eq {n r : ℕ} (B : PerturbedStarBlocks n r)
    (d : ℕ) (Y : Finset (Fin n)) (hY : Y ⊆ B.L) :
    Nat.choose (perturbedStarFiller B).card
        (d + 1 - ({B.a} ∪ B.T ∪ Y).card) =
      Nat.choose (perturbedStarFiller B).card
        (d + 1 - ({B.b} ∪ B.T ∪ Y).card) := by
  rw [perturbedPattern_card_eq B Y hY]

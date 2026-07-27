-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `perturbedStarParameterBounds`

For natural numbers d, s, and n, assume `hd : 4 ≤ d`, `hslow : (d + 3) / 2 ≤ s`, `hshigh : s ≤ d -
1`, and `hn : 2 * (d + 1) ≤ n`. Put `r = d + 1 - s`. Then `2 ≤ r`, `r + 1 ≤ s`, `d - 2*r = 2*s - d -
2`, `2*r ≤ d`, and `2 + 2*r ≤ n`. All subtractions are natural-number subtraction; the theorem
establishes the displayed equality and bounds with the needed nontruncation consequences explicit
under exactly these hypotheses.

## Sources

- Source `article/sections/02_proof.tex`, lines 30–32

## Proof outline

Unfold the `let r := d + 1 - s`.  First use `hshigh : s ≤ d - 1` to obtain `s ≤ d + 1` and the lower
bound `2 ≤ d + 1 - s`; this makes the first subtraction nontruncating.  Next apply `omega` to the
corrected half-bound `hslow : (d + 3) / 2 ≤ s`.  It yields both `d + 2 ≤ 2*s` and hence `r + 1 ≤ s`
and `2*r ≤ d`.

Record the two nontruncation facts before proving the displayed equality: `2*r ≤ d` certifies the
left subtraction `d - 2*r`, while `d + 2 ≤ 2*s` certifies `2*s - d - 2`.  With `r = d + 1 - s`
expanded, `omega` proves the truncation-safe natural-number identity `d - 2*r = 2*s - d - 2`.

Finally combine `2*r ≤ d` with `hn : 2*(d+1) ≤ n`; linear arithmetic gives `2 + 2*r ≤ n`.  Conjoin,
in order, the lower bound for `r`, `r+1≤s`, the subtraction equality, `2*r≤d`, and the ambient-size
inequality.

## Proof sources

- Source `article/sections/02_proof.tex`, lines 30–32
-/
theorem perturbedStarParameterBounds (d s n : ℕ) (hd : 4 ≤ d)
    (hslow : (d + 3) / 2 ≤ s) (hshigh : s ≤ d - 1)
    (hn : 2 * (d + 1) ≤ n) :
    let r := d + 1 - s
    2 ≤ r ∧ r + 1 ≤ s ∧ d - 2 * r = 2 * s - d - 2 ∧
      2 * r ≤ d ∧ 2 + 2 * r ≤ n := by
  dsimp
  have htwo : 2 ≤ d + 1 - s := by omega
  have hhalf : d + 2 ≤ 2 * s := by omega
  have hr_le_d : 2 * (d + 1 - s) ≤ d := by omega
  have hleft : 2 * (d + 1 - s) ≤ d := hr_le_d
  have hright : d + 2 ≤ 2 * s := hhalf
  refine ⟨htwo, ?_, ?_, hr_le_d, ?_⟩
  · omega
  · omega
  · omega

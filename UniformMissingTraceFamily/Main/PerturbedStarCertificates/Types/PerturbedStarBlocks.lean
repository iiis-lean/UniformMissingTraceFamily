-- lean-constellation: managed-imports-begin
import UniformMissingTraceFamily.Main.PerturbedStarCertificates.Prelude
-- lean-constellation: managed-imports-end

-- lean-constellation: declaration-source-begin

/--
# lean-constellation target: `PerturbedStarBlocks`

For natural numbers n and r, `PerturbedStarBlocks n r` is public construction data consisting of two
distinguished elements `a` and `b` of `Fin n` and two finite sets `T` and `L` of `Fin n`.  It
records explicitly that `a ≠ b`, that `T` and `L` each have cardinality `r`, that `T` and `L` are
disjoint, and that neither `T` nor `L` contains either distinguished element.  Thus all anchor
distinctness and block-avoidance requirements are fields of the data, rather than implicit
conventions.

## Sources

- Source `article/sections/02_proof.tex`, lines 30–32
-/
structure PerturbedStarBlocks (n r : ℕ) where
  a : Fin n
  b : Fin n
  T : Finset (Fin n)
  L : Finset (Fin n)
  a_ne_b : a ≠ b
  card_T : T.card = r
  card_L : L.card = r
  T_disjoint_L : Disjoint T L
  a_not_mem_T : a ∉ T
  b_not_mem_T : b ∉ T
  a_not_mem_L : a ∉ L
  b_not_mem_L : b ∉ L

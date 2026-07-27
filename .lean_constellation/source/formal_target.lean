import Mathlib

/-- A family of finite subsets is uniform of size `d + 1` and every member has
a missing intersection trace of the same fixed size `s`. -/
def IsUniformMissingTraceFamily {n : ℕ} (d s : ℕ)
    (family : Finset (Finset (Fin n))) : Prop :=
  (∀ F ∈ family, F.card = d + 1) ∧
    ∀ F ∈ family, ∃ B : Finset (Fin n),
      B ⊆ F ∧ B.card = s ∧ ∀ F' ∈ family, F ∩ F' ≠ B

/-- In the stated middle parameter range there is a uniform missing-trace
family having the exact cardinality of the explicit construction and strictly
more members than a star. -/
theorem exists_uniformMissingTraceFamily_strictlyLargerThanStar
    (d s n : ℕ)
    (hd : 4 ≤ d)
    (hslow : (d + 3) / 2 ≤ s)
    (hshigh : s ≤ d - 1)
    (hn : 2 * (d + 1) ≤ n) :
    ∃ family : Finset (Finset (Fin n)),
      IsUniformMissingTraceFamily d s family ∧
      family.card =
        Nat.choose (n - 1) d +
          Nat.choose (n - 2 * (d + 1 - s) - 2) (2 * s - d - 2) ∧
      Nat.choose (n - 1) d < family.card := by
  sorry

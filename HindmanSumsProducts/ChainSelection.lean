import Mathlib

/-!
# Selection of a product chain (paper Lemma `lem:chain-selection`, §2)

A chain of length `m` in `Fin n` is given by tails `T d` and pivots `piv d` (`d : Fin m`) with
`∅ ≠ T 0 < T 1 < ⋯ < T (m-1) < piv 0 < ⋯ < piv (m-1)`, where `S < S'` means every element of `S`
is below every element of `S'`. Block `d` is `insert (piv d) (T d)`.
-/

namespace HindmanSumsProducts

/-- The ordering condition `(eq:block-chain)` of the paper on tails and pivots. -/
def IsChain {n m : ℕ} (T : Fin m → Finset (Fin n)) (piv : Fin m → Fin n) : Prop :=
  (∀ d, (T d).Nonempty) ∧
  (∀ d d', d < d' → ∀ a ∈ T d, ∀ b ∈ T d', a < b) ∧
  (∀ d d', ∀ a ∈ T d, a < piv d') ∧
  StrictMono piv

/-- Finite sums theorem, finite form (Folkman–Rado–Sanders), as used in §2: for every `m, r`
there is `F` such that every `r`-colouring has positive `u 0, …, u (m-1)` whose nonempty subset
sums lie in `[1, F]` and have one colour. -/
theorem finite_sums_finite_form (m r : ℕ) : ∃ F : ℕ, ∀ χ : ℕ → Fin r,
    ∃ (u : Fin m → ℕ) (c : Fin r), (∀ d, 0 < u d) ∧
      ∀ J : Finset (Fin m), J.Nonempty → ∑ d ∈ J, u d ≤ F ∧ χ (∑ d ∈ J, u d) = c := by
  sorry

/-- Paper Lemma `lem:chain-selection`: for every `m, r` there is `n` such that for every
colouring `χ` and every list `x : Fin n → ℕ` some chain has all nonempty products of its block
products `x_{B_d} = ∏_{j ∈ B_d} x j` in one colour. -/
theorem chain_selection (m r : ℕ) : ∃ n : ℕ, ∀ (χ : ℕ → Fin r) (x : Fin n → ℕ),
    ∃ (T : Fin m → Finset (Fin n)) (piv : Fin m → Fin n) (c : Fin r), IsChain T piv ∧
      ∀ J : Finset (Fin m), J.Nonempty →
        χ (∏ d ∈ J, ∏ j ∈ insert (piv d) (T d), x j) = c := by
  sorry

end HindmanSumsProducts

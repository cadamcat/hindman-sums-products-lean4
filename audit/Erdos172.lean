import HindmanSumsProducts.Main

/-!
# Erdős Problem 172

`Erdos172.erdos_172_rhs` is the right-hand side of `Erdos172.erdos_172` in Google DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/172.lean`), copied verbatim from commit
`9d259649abe0b02d7a25f7589b872db679b35e21` (Copyright 2025 The Formal Conjectures Authors,
Apache-2.0; see `THIRD_PARTY.md`). It follows from `HindmanSumsProducts.hindman_finite_sums_products`,
so `erdos_172` holds with `answer(True)`.

Run `lake env lean audit/Erdos172.lean` after the build; it prints the theorem's axioms.
-/

namespace Erdos172

theorem erdos_172_rhs :
    ∀ (n : ℕ) (color : ℕ → Fin n) (m), ∃ (A : Finset ℕ), A.card ≥ m ∧ ∃ c, ∀ (S : Finset A),
    S.Nonempty → color (∑ x ∈ S, x) = c ∧ color (∏ x ∈ S, x) = c := by
  intro n color m
  obtain ⟨A, c, hcard, _, hmono⟩ := HindmanSumsProducts.hindman_finite_sums_products n color m
  refine ⟨A, hcard.ge, c, fun S hS => ?_⟩
  have h := hmono (S.map (Function.Embedding.subtype _)) (by
      intro x hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_map.1 hx
      exact p.2) hS.map
  rw [Finset.sum_map, Finset.prod_map] at h
  exact h

end Erdos172

#print axioms Erdos172.erdos_172_rhs

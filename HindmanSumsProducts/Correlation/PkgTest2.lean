import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside

/-! Helper lemmas for the uniform correlation test proof (lane `c-test2`). -/

namespace HindmanSumsProducts

open Filter

/-- If every sequence of parameters eventually satisfies a property, the property eventually
holds uniformly for all parameters. -/
theorem c_test2_eventually_forall_of_sequences {α : Type*} [Inhabited α]
    (P : ℕ → α → Prop)
    (hseq : ∀ a : ℕ → α, ∀ᶠ N in atTop, P N (a N)) :
    ∀ᶠ N in atTop, ∀ x : α, P N x := by
  classical
  by_contra h
  have hbad : ∀ N₀, ∃ N, N₀ ≤ N ∧ ∃ x, ¬ P N x := by
    intro N₀
    by_contra hN
    apply h
    apply eventually_atTop.2
    refine ⟨N₀, ?_⟩
    intro N hN₀ x
    by_contra hx
    exact hN ⟨N, hN₀, x, hx⟩
  let a : ℕ → α := fun N =>
    if hN : ∃ x, ¬ P N x then Classical.choose hN else default
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hseq a)
  obtain ⟨N, hN₀N, x, hx⟩ := hbad N₀
  have hp : P N (a N) := hN₀ N hN₀N
  have hnot : ¬ P N (a N) := by
    dsimp [a]
    by_cases hN : ∃ x, ¬ P N x
    · simp only [dif_pos hN]
      exact Classical.choose_spec hN
    · simp only [dif_neg hN]
      exact False.elim (hN ⟨x, hx⟩)
  exact hnot hp

end HindmanSumsProducts

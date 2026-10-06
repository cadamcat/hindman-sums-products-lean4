import Challenge

/-!
Statement-fidelity probes for `Challenge.lean` (not part of the proof).
Run from the repository root: `lake env lean audit/ChallengeProbes.lean`.
-/

namespace HindmanSumsProducts.Probes

/-- The body of the target, copied from `Challenge.lean`. -/
def Body (r : ℕ) (χ : ℕ → Fin r) (m : ℕ) (A : Finset ℕ) (c : Fin r) : Prop :=
  A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
    ∀ B ⊆ A, B.Nonempty → χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c

/-- The copy is the target's statement, checked by the kernel. -/
example : type_of% @HindmanSumsProducts.hindman_finite_sums_products =
    ∀ (r : ℕ) (χ : ℕ → Fin r) (m : ℕ), ∃ (A : Finset ℕ) (c : Fin r), Body r χ m A c := rfl

instance (r : ℕ) (χ : ℕ → Fin r) (m : ℕ) (A : Finset ℕ) (c : Fin r) :
    Decidable (Body r χ m A c) :=
  decidable_of_iff (A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
      ∀ B ∈ A.powerset, B.Nonempty → χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c)
    (by simp only [Body, Finset.mem_powerset])

/-- Parity colouring. -/
def parity : ℕ → Fin 2 := fun n => ⟨n % 2, Nat.mod_lt _ (by norm_num)⟩

/-- Probe 1: a witness satisfies every clause (constant colouring, `m = 3`). -/
example : Body 1 (fun _ => 0) 3 {1, 2, 3} 0 := by decide

/-- Probe 2: a nontrivial witness (parity colouring, `m = 2`, `A = {2, 4}`). -/
example : Body 2 parity 2 {2, 4} 0 := by decide

/-- Probe 3: the property is not vacuous: `{1, 2}` fails for the parity colouring in every colour. -/
example : ∀ c, ¬ Body 2 parity 2 {1, 2} c := by decide

/-- Probe 4: sums are included: `{1, 3}` has odd products but the even sum `4`. -/
example : ∀ c, ¬ Body 2 parity 2 {1, 3} c := by decide

/-- Probe 5: products are included: under `n ↦ [n ≤ 10]`, `{2, 6}` has sums `2, 6, 8 ≤ 10`
but the product `12 > 10`. -/
example : ∀ c, ¬ Body 2 (fun n => if n ≤ 10 then 0 else 1) 2 {2, 6} c := by decide

/-- Probe 6: `card = m` forces `m` distinct elements; `{2, 2}` is the one-element set `{2}`. -/
example : ¬ Body 1 (fun _ => 0) 2 {2, 2} 0 := by decide

/-- Probe 7: the colour of `0` never matters. -/
example (r : ℕ) (χ χ' : ℕ → Fin r) (h : ∀ n, 0 < n → χ n = χ' n) (m : ℕ) (A : Finset ℕ)
    (c : Fin r) : Body r χ m A c ↔ Body r χ' m A c := by
  unfold Body
  constructor <;> rintro ⟨hcard, hpos, hB⟩ <;> refine ⟨hcard, hpos, fun B hBA hne => ?_⟩ <;>
    have hs : 0 < ∑ b ∈ B, b := Finset.sum_pos (fun b hb => hpos b (hBA hb)) hne <;>
    have hp : 0 < ∏ b ∈ B, b := Finset.prod_pos (fun b hb => hpos b (hBA hb)) <;>
    obtain ⟨h1, h2⟩ := hB B hBA hne
  · exact ⟨(h _ hs) ▸ h1, (h _ hp) ▸ h2⟩
  · exact ⟨(h _ hs).symm ▸ h1, (h _ hp).symm ▸ h2⟩

end HindmanSumsProducts.Probes

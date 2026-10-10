import HindmanSumsProducts.Main

/-!
Non-vacuity audit for `HindmanSumsProducts.hindman_finite_sums_products`.
Run from the repository root: `lake env lean audit/NonVacuity.lean`.
-/

namespace HindmanSumsProducts.NonVacuity

open Finset

/-- The parity two-colouring used by the concrete probes. -/
def parity : ℕ → Fin 2 := fun n => ⟨n % 2, Nat.mod_lt _ (by norm_num)⟩

/-- The threshold two-colouring distinguishing `n ≤ 10` from `n > 10`. -/
def threshold : ℕ → Fin 2 := fun n => if n ≤ 10 then (0 : Fin 2) else (1 : Fin 2)

/-- Hypotheses are inhabited: there is a two-colouring of `ℕ`. -/
theorem colourings_inhabited : Nonempty (ℕ → Fin 2) :=
  ⟨parity⟩

/-- Zero colours have no colouring, so `r = 0` is vacuous for a different reason. -/
theorem zero_colours_empty : IsEmpty (ℕ → Fin 0) :=
  ⟨fun χ => (χ 0).elim0⟩

/-- Hypotheses are jointly satisfiable: the main theorem applies to the constant one-colouring. -/
theorem hypotheses_applied :
    ∃ (A : Finset ℕ) (c : Fin 1), A.card = 3 ∧ (∀ a ∈ A, 0 < a) ∧
      ∀ B ⊆ A, B.Nonempty →
        (fun _ => (0 : Fin 1)) (∑ b ∈ B, b) = c ∧
        (fun _ => (0 : Fin 1)) (∏ b ∈ B, b) = c :=
  HindmanSumsProducts.hindman_finite_sums_products 1 (fun _ => 0) 3

/-- Subset sums compute as intended on `{2, 4}`. -/
theorem sum_computes : ∑ b ∈ ({2, 4} : Finset ℕ), b = 6 := by
  decide

/-- Subset products compute as intended on `{2, 4}`. -/
theorem prod_computes : ∏ b ∈ ({2, 4} : Finset ℕ), b = 8 := by
  decide

/-- Singleton sums and products are the element itself. -/
theorem singleton_sum_prod :
    (∑ b ∈ ({5} : Finset ℕ), b = 5) ∧ (∏ b ∈ ({5} : Finset ℕ), b = 5) := by
  decide

/-- Empty sum and product are the junk values excluded by the `Nonempty` guard. -/
theorem empty_junk :
    (∑ _b ∈ (∅ : Finset ℕ), _b = 0) ∧ (∏ _b ∈ (∅ : Finset ℕ), _b = 1) :=
  ⟨rfl, rfl⟩

/-- `Finset.card` counts distinct elements. -/
theorem card_distinct : ({2, 2} : Finset ℕ).card = 1 := by
  decide

/-- Positivity holds for `{2, 4}` and fails once `0` is present. -/
theorem positivity_checked :
    (∀ a ∈ ({2, 4} : Finset ℕ), 0 < a) ∧ ¬ ∀ a ∈ ({0, 2} : Finset ℕ), 0 < a := by
  decide

/-- Conclusion is not trivially true: `{1, 2}` is monochromatic in no colour under parity. -/
theorem monochromatic_nontrivial (c : Fin 2) :
    ¬ ∀ B ⊆ ({1, 2} : Finset ℕ), B.Nonempty →
      parity (∑ b ∈ B, b) = c ∧ parity (∏ b ∈ B, b) = c := by
  intro hc
  have h1 := (hc {1} (by decide) (by decide)).1
  have h2 := (hc {2} (by decide) (by decide)).1
  have e1 : ∑ b ∈ ({1} : Finset ℕ), b = 1 := by decide
  have e2 : ∑ b ∈ ({2} : Finset ℕ), b = 2 := by decide
  have p1 : parity 1 = 1 := by decide
  have p2 : parity 2 = 0 := by decide
  rw [e1, p1] at h1
  rw [e2, p2] at h2
  rw [← h1] at h2
  exact absurd h2 (by decide)

/-- Sums are load-bearing: `{1, 3}` has monochromatic products but no monochromatic sums. -/
theorem sums_essential (c : Fin 2) :
    ¬ ∀ B ⊆ ({1, 3} : Finset ℕ), B.Nonempty →
      parity (∑ b ∈ B, b) = c ∧ parity (∏ b ∈ B, b) = c := by
  intro hc
  have h1 := (hc {1} (by decide) (by decide)).1
  have h13 := (hc {1, 3} (by decide) (by decide)).1
  have e1 : ∑ b ∈ ({1} : Finset ℕ), b = 1 := by decide
  have e13 : ∑ b ∈ ({1, 3} : Finset ℕ), b = 4 := by decide
  have p1 : parity 1 = 1 := by decide
  have p4 : parity 4 = 0 := by decide
  rw [e1, p1] at h1
  rw [e13, p4] at h13
  rw [← h1] at h13
  exact absurd h13 (by decide)

/-- Products are load-bearing: `{2, 6}` has small sums but its product exceeds `10`. -/
theorem products_essential (c : Fin 2) :
    ¬ ∀ B ⊆ ({2, 6} : Finset ℕ), B.Nonempty →
      threshold (∑ b ∈ B, b) = c ∧ threshold (∏ b ∈ B, b) = c := by
  intro hc
  have h2 := (hc {2} (by decide) (by decide)).2
  have h26 := (hc {2, 6} (by decide) (by decide)).2
  have e2 : ∏ b ∈ ({2} : Finset ℕ), b = 2 := by decide
  have e26 : ∏ b ∈ ({2, 6} : Finset ℕ), b = 12 := by decide
  have t2 : threshold 2 = 0 := by decide
  have t12 : threshold 12 = 1 := by decide
  rw [e2, t2] at h2
  rw [e26, t12] at h26
  rw [← h2] at h26
  exact absurd h26 (by decide)

/-- The `Nonempty` guard is load-bearing: without it the statement is false. -/
theorem nonempty_guard_load_bearing :
    ¬ ∀ (r : ℕ) (χ : ℕ → Fin r) (m : ℕ), ∃ (A : Finset ℕ) (c : Fin r),
      A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
        ∀ B ⊆ A, χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c := by
  intro h
  obtain ⟨A, c, _, _, hmono⟩ := h 2 (fun n => if n = 0 then (0 : Fin 2) else 1) 1
  have h0 := hmono ∅ (Finset.empty_subset _)
  simp at h0
  obtain ⟨h0a, h0b⟩ := h0
  rw [← h0a] at h0b
  exact absurd h0b (by decide)

/-- The colour of `0` never matters for monochromatic sets. -/
theorem zero_colour_irrelevant (r : ℕ) (χ χ' : ℕ → Fin r)
    (hχ : ∀ n, 0 < n → χ n = χ' n) (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (c : Fin r) :
    (∀ B ⊆ A, B.Nonempty → χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c) ↔
      (∀ B ⊆ A, B.Nonempty → χ' (∑ b ∈ B, b) = c ∧ χ' (∏ b ∈ B, b) = c) := by
  have key : ∀ B ⊆ A, B.Nonempty →
      χ (∑ b ∈ B, b) = χ' (∑ b ∈ B, b) ∧ χ (∏ b ∈ B, b) = χ' (∏ b ∈ B, b) :=
    fun B hB hne =>
      ⟨hχ _ (Finset.sum_pos (fun b hb => hA b (hB hb)) hne),
        hχ _ (Finset.prod_pos (fun b hb => hA b (hB hb)))⟩
  constructor
  · intro h B hB hne
    rw [← (key B hB hne).1, ← (key B hB hne).2]
    exact h B hB hne
  · intro h B hB hne
    rw [(key B hB hne).1, (key B hB hne).2]
    exact h B hB hne

/-- Plain reading for arbitrary finite colour types. -/
theorem hindman_finite_type {κ : Type*} [Fintype κ] [Nonempty κ] (χ : ℕ → κ)
    (m : ℕ) :
    ∃ (A : Finset ℕ) (c : κ), A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
      ∀ B ⊆ A, B.Nonempty → χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c := by
  let e := Fintype.equivFin κ
  obtain ⟨A, c', hcard, hpos, hmono⟩ :=
    HindmanSumsProducts.hindman_finite_sums_products _ (fun n => e (χ n)) m
  refine ⟨A, e.symm c', hcard, hpos, fun B hB hne => ?_⟩
  obtain ⟨hs, hp⟩ := hmono B hB hne
  constructor
  · apply e.injective (a₁ := χ (∑ b ∈ B, b))
    calc e (χ (∑ b ∈ B, b)) = c' := hs
      _ = e (e.symm c') := (e.apply_symm_apply c').symm
  · apply e.injective (a₁ := χ (∏ b ∈ B, b))
    calc e (χ (∏ b ∈ B, b)) = c' := hp
      _ = e (e.symm c') := (e.apply_symm_apply c').symm

/-- Auxiliary: coercion of a `ℕ+` product is the product of coercions. -/
theorem coe_prod_pnat_aux (B : Finset ℕ+) :
    ((∏ b ∈ B, b : ℕ+) : ℕ) = ∏ b ∈ B, (b : ℕ) :=
  map_prod PNat.coeMonoidHom (fun b => b) B

/-- Plain reading for colourings of the positive integers only. -/
theorem hindman_pnat {κ : Type*} [Fintype κ] [Nonempty κ] (χ : ℕ+ → κ)
    (m : ℕ) :
    ∃ (A : Finset ℕ+) (c : κ), A.card = m ∧
      ∀ B ⊆ A, B.Nonempty →
        (∃ s : ℕ+, (s : ℕ) = ∑ b ∈ B, (b : ℕ) ∧ χ s = c) ∧
          χ (∏ b ∈ B, b) = c := by
  let e := Fintype.equivFin κ
  obtain ⟨A, c', hcard, hpos, hmono⟩ :=
    HindmanSumsProducts.hindman_finite_sums_products _
      (fun n => e (χ n.toPNat')) m
  let A' : Finset ℕ+ := A.subtype (fun n => 0 < n)
  have hmemA' : ∀ p : ℕ+, p ∈ A' ↔ (p : ℕ) ∈ A := fun p => Finset.mem_subtype
  refine ⟨A', e.symm c', ?_, ?_⟩
  · change (A.subtype (fun n => 0 < n)).card = m
    rw [Finset.card_subtype, Finset.filter_true_of_mem hpos, hcard]
  · intro B hB hne
    let B₀ : Finset ℕ := B.map ⟨fun p : ℕ+ => (p : ℕ), PNat.coe_injective⟩
    have hB₀ : B₀ ⊆ A := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.1 hx
      exact (hmemA' p).1 (hB hp)
    obtain ⟨hs, hp⟩ := hmono B₀ hB₀ (hne.map)
    have hsum : ∑ x ∈ B₀, x = ∑ b ∈ B, (b : ℕ) := Finset.sum_map _ _ _
    have hprod : ∏ x ∈ B₀, x = ∏ b ∈ B, (b : ℕ) := Finset.prod_map _ _ _
    rw [hsum] at hs
    rw [hprod, ← coe_prod_pnat_aux, PNat.coe_toPNat'] at hp
    have hpos' : 0 < ∑ b ∈ B, (b : ℕ) :=
      Finset.sum_pos (fun b _ => b.pos) hne
    refine ⟨⟨(∑ b ∈ B, (b : ℕ)).toPNat', PNat.toPNat'_coe hpos', ?_⟩, ?_⟩
    · apply e.injective (a₁ := χ (∑ b ∈ B, (b : ℕ)).toPNat')
      calc e (χ (∑ b ∈ B, (b : ℕ)).toPNat') = c' := hs
        _ = e (e.symm c') := (e.apply_symm_apply c').symm
    · apply e.injective (a₁ := χ (∏ b ∈ B, b))
      calc e (χ (∏ b ∈ B, b)) = c' := hp
        _ = e (e.symm c') := (e.apply_symm_apply c').symm

/-- Concrete non-trivial instance: the parity two-colouring with `m = 3`. -/
theorem hindman_parity_three :
    ∃ (A : Finset ℕ) (c : Fin 2), A.card = 3 ∧ (∀ a ∈ A, 0 < a) ∧
      ∀ B ⊆ A, B.Nonempty →
        parity (∑ b ∈ B, b) = c ∧ parity (∏ b ∈ B, b) = c :=
  HindmanSumsProducts.hindman_finite_sums_products 2 parity 3

/-- The `m = 3` instance is not witnessed by every set: `{1, 2, 3}` fails under parity. -/
theorem parity_three_not_any_set (c : Fin 2) :
    ¬ ∀ B ⊆ ({1, 2, 3} : Finset ℕ), B.Nonempty →
      parity (∑ b ∈ B, b) = c ∧ parity (∏ b ∈ B, b) = c := by
  intro hc
  have h1 := (hc {1} (by decide) (by decide)).1
  have h2 := (hc {2} (by decide) (by decide)).1
  have e1 : ∑ b ∈ ({1} : Finset ℕ), b = 1 := by decide
  have e2 : ∑ b ∈ ({2} : Finset ℕ), b = 2 := by decide
  have p1 : parity 1 = 1 := by decide
  have p2 : parity 2 = 0 := by decide
  rw [e1, p1] at h1
  rw [e2, p2] at h2
  rw [← h1] at h2
  exact absurd h2 (by decide)

#print axioms colourings_inhabited
#print axioms zero_colours_empty
#print axioms hypotheses_applied
#print axioms sum_computes
#print axioms prod_computes
#print axioms singleton_sum_prod
#print axioms empty_junk
#print axioms card_distinct
#print axioms positivity_checked
#print axioms monochromatic_nontrivial
#print axioms sums_essential
#print axioms products_essential
#print axioms nonempty_guard_load_bearing
#print axioms zero_colour_irrelevant
#print axioms hindman_finite_type
#print axioms coe_prod_pnat_aux
#print axioms hindman_pnat
#print axioms hindman_parity_three
#print axioms parity_three_not_any_set

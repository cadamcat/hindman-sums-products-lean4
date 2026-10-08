import Mathlib
import Challenge

/-!
Opus statement-fidelity probes for `HindmanSumsProducts.hindman_finite_sums_products`.
Every bridge takes the target's own type (`type_of%`) as a hypothesis, so it reads the
compiled `Challenge` module rather than a copy, and its axioms must not include `sorryAx`.
-/

namespace OpusProbes

open Finset

/-- The target's proposition, read from the compiled challenge module. -/
abbrev Target : Prop := type_of% @HindmanSumsProducts.hindman_finite_sums_products

-- P0. The elaborated statement, with every instance and coercion shown.
set_option pp.explicit true in
#check @HindmanSumsProducts.hindman_finite_sums_products

-- P0'. `⊆` on `Finset` elaborates to the order `≤` of `Finset.instPartialOrder`; it is the
-- subset relation by definition, and the bound variables of `∑`/`∏` range over `ℕ`.
example (A B : Finset ℕ) : B ⊆ A ↔ ∀ x, x ∈ B → x ∈ A := Iff.rfl
example (A B : Finset ℕ) : B ≤ A ↔ B ⊆ A := Iff.rfl
example (B : Finset ℕ) : ∑ b ∈ B, b = B.sum id ∧ ∏ b ∈ B, b = B.prod id := ⟨rfl, rfl⟩

/-- Independent restatement: a colouring of the
positive integers `ℕ+` into an arbitrary finite type, an `m`-element `Finset ℕ+`, and one colour
for every nonempty subset sum (taken in `ℕ`, which must be the value of a positive integer)
and every nonempty subset product (taken in `ℕ+`). -/
def IndepPNat.{u} : Prop :=
  ∀ (α : Type u) [Finite α] (χ : ℕ+ → α) (m : ℕ), ∃ (A : Finset ℕ+) (c : α), A.card = m ∧
    ∀ B ⊆ A, B.Nonempty →
      (∃ s : ℕ+, (s : ℕ) = ∑ b ∈ B, (b : ℕ) ∧ χ s = c) ∧ χ (∏ b ∈ B, b) = c

lemma coe_prod_pnat (B : Finset ℕ+) : ((∏ b ∈ B, b : ℕ+) : ℕ) = ∏ b ∈ B, (b : ℕ) :=
  map_prod PNat.coeMonoidHom (fun b => b) B

/-- P1. Target ⇒ independent ℕ⁺ statement, for colour types in every universe. -/
theorem target_imp_indep (H : Target) : IndepPNat.{u} := by
  intro α _ χ m
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  obtain ⟨A, c, hcard, hpos, hmono⟩ := H r (fun n => e (χ n.toPNat')) m
  let A' : Finset ℕ+ := (A.subtype (fun n => 0 < n))
  have hmemA' : ∀ p : ℕ+, p ∈ A' ↔ (p : ℕ) ∈ A := fun p => Finset.mem_subtype
  refine ⟨A', e.symm c, ?_, ?_⟩
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
    rw [hprod, ← coe_prod_pnat, PNat.coe_toPNat'] at hp
    have hpos' : 0 < ∑ b ∈ B, (b : ℕ) :=
      Finset.sum_pos (fun b _ => b.pos) hne
    refine ⟨⟨(∑ b ∈ B, (b : ℕ)).toPNat', PNat.toPNat'_coe hpos', ?_⟩, ?_⟩
    · exact (Equiv.eq_symm_apply e).2 hs
    · exact (Equiv.eq_symm_apply e).2 hp

/-- P2. Independent ℕ⁺ statement ⇒ target, so the target is no stronger than the source. -/
theorem indep_imp_target (H : IndepPNat.{0}) : Target := by
  intro r χ m
  obtain ⟨A', c, hcard, hmono⟩ := H (Fin r) (fun p => χ p) m
  let emb : ℕ+ ↪ ℕ := ⟨fun p : ℕ+ => (p : ℕ), PNat.coe_injective⟩
  refine ⟨A'.map emb, c, by rw [Finset.card_map, hcard], ?_, ?_⟩
  · intro a ha
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.1 ha
    exact p.pos
  · intro B hB hne
    have hBpos : ∀ b ∈ B, 0 < b := by
      intro b hb
      obtain ⟨p, _, rfl⟩ := Finset.mem_map.1 (hB hb)
      exact p.pos
    let B' : Finset ℕ+ := B.subtype (fun n => 0 < n)
    have hBmap : B'.map emb = B := by
      ext x
      constructor
      · intro hx
        obtain ⟨p, hp, rfl⟩ := Finset.mem_map.1 hx
        exact Finset.mem_subtype.1 hp
      · intro hx
        exact Finset.mem_map.2 ⟨⟨x, hBpos x hx⟩, Finset.mem_subtype.2 hx, rfl⟩
    have hB' : B' ⊆ A' := by
      intro p hp
      have : (p : ℕ) ∈ A'.map emb := hB (Finset.mem_subtype.1 hp)
      obtain ⟨q, hq, hqp⟩ := Finset.mem_map.1 this
      have : q = p := PNat.coe_injective hqp
      exact this ▸ hq
    have hne' : B'.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨⟨x, hBpos x hx⟩, Finset.mem_subtype.2 hx⟩
    obtain ⟨⟨s, hs, hχs⟩, hχp⟩ := hmono B' hB' hne'
    have hsum : ∑ b ∈ B, b = ∑ b ∈ B', (b : ℕ) := by
      rw [← hBmap, Finset.sum_map]; rfl
    have hprod : ∏ b ∈ B, b = ((∏ b ∈ B', b : ℕ+) : ℕ) := by
      rw [coe_prod_pnat, ← hBmap, Finset.prod_map]; rfl
    refine ⟨?_, ?_⟩
    · rw [hsum, ← hs]; exact hχs
    · rw [hprod]; exact hχp

/-- P3. Target ⇒ the Formal Conjectures statement of Erdős Problem 172 (right-hand side of
`Erdos172.erdos_172` at google-deepmind/formal-conjectures 9d25964, copied verbatim; Copyright 2025
The Formal Conjectures Authors, Apache-2.0, see THIRD_PARTY.md). -/
theorem target_imp_fc172 (H : Target) :
    ∀ (n : ℕ) (color : ℕ → Fin n) (m), ∃ (A : Finset ℕ), A.card ≥ m ∧ ∃ c, ∀ (S : Finset A),
    S.Nonempty → color (∑ x ∈ S, x) = c ∧ color (∏ x ∈ S, x) = c := by
  intro n color m
  obtain ⟨A, c, hcard, _, hmono⟩ := H n color m
  refine ⟨A, hcard.ge, c, fun S hS => ?_⟩
  have h := hmono (S.map (Function.Embedding.subtype _)) (by
      intro x hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_map.1 hx
      exact p.2) hS.map
  rw [Finset.sum_map, Finset.prod_map] at h
  exact h

/-- P4. Quantifier order: the colour is chosen after `m` and `A`, but a single colour then works
for every `m` (pigeonhole over `Fin r` and passage to subsets). -/
theorem target_imp_uniform_colour (H : Target) (r : ℕ) (χ : ℕ → Fin r) :
    ∃ c : Fin r, ∀ m, ∃ A : Finset ℕ, A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
      ∀ B ⊆ A, B.Nonempty → χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c := by
  choose A c hcard hpos hmono using H r χ
  obtain ⟨c₀, hc₀⟩ := Finite.exists_infinite_fiber c
  have hinf : (c ⁻¹' {c₀}).Infinite := Set.infinite_coe_iff.1 hc₀
  refine ⟨c₀, fun m => ?_⟩
  obtain ⟨m', hm'c, hmm'⟩ := hinf.exists_gt m
  have hm'c : c m' = c₀ := hm'c
  obtain ⟨T, hTA, hTcard⟩ := Finset.exists_subset_card_eq (s := A m') (n := m)
    (by rw [hcard]; omega)
  refine ⟨T, hTcard, fun a ha => hpos m' a (hTA ha), fun B hB hne => ?_⟩
  rw [← hm'c]
  exact hmono m' B (hB.trans hTA) hne

/-- The colouring by parity, used by the guard probes. -/
def parity (n : ℕ) : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by norm_num)⟩

/-- G1. The conclusion is satisfiable by a concrete object: `{2, 4}` under parity. -/
example : ∃ (A : Finset ℕ) (c : Fin 2), A.card = 2 ∧ (∀ a ∈ A, 0 < a) ∧
    ∀ B ⊆ A, B.Nonempty → parity (∑ b ∈ B, b) = c ∧ parity (∏ b ∈ B, b) = c := by
  refine ⟨{2, 4}, 0, by decide, by decide, fun B hB hne => ?_⟩
  have key : ∀ B ∈ ({2, 4} : Finset ℕ).powerset, B.Nonempty →
      parity (∑ b ∈ B, b) = 0 ∧ parity (∏ b ∈ B, b) = 0 := by decide
  exact key B (Finset.mem_powerset.2 hB) hne

/-- G2. Non-vacuity: the monochromatic clause genuinely constrains `A`; `{1, 2}` fails it. -/
example : ¬ ∃ c : Fin 2, ∀ B ⊆ ({1, 2} : Finset ℕ), B.Nonempty →
    parity (∑ b ∈ B, b) = c ∧ parity (∏ b ∈ B, b) = c := by
  rintro ⟨c, hc⟩
  have h1 := (hc {1} (by decide) (by decide)).1
  have h2 := (hc {2} (by decide) (by decide)).1
  simp [parity] at h1 h2
  rw [← h1] at h2
  exact absurd h2 (by decide)

/-- G3. The `B.Nonempty` guard is load-bearing: without it the statement is false, because the
empty sum `0` and the empty product `1` would both have to take the colour `c`. -/
example : ¬ ∀ (r : ℕ) (χ : ℕ → Fin r) (m : ℕ), ∃ (A : Finset ℕ) (c : Fin r), A.card = m ∧
    (∀ a ∈ A, 0 < a) ∧ ∀ B ⊆ A, χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c := by
  intro h
  obtain ⟨A, c, _, _, hmono⟩ := h 2 (fun n => if n = 0 then 0 else 1) 1
  have h0 := hmono ∅ (Finset.empty_subset _)
  simp at h0
  obtain ⟨h0a, h0b⟩ := h0
  rw [← h0a] at h0b
  exact absurd h0b (by decide)

/-- G4. The colour of `0` never matters: two colourings that agree on positive integers have the
same monochromatic sets. -/
example (r : ℕ) (χ χ' : ℕ → Fin r) (hχ : ∀ n, 0 < n → χ n = χ' n) (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (c : Fin r) :
    (∀ B ⊆ A, B.Nonempty → χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c) ↔
    (∀ B ⊆ A, B.Nonempty → χ' (∑ b ∈ B, b) = c ∧ χ' (∏ b ∈ B, b) = c) := by
  have key : ∀ B ⊆ A, B.Nonempty → χ (∑ b ∈ B, b) = χ' (∑ b ∈ B, b) ∧
      χ (∏ b ∈ B, b) = χ' (∏ b ∈ B, b) := fun B hB hne =>
    ⟨hχ _ (Finset.sum_pos (fun b hb => hA b (hB hb)) hne),
     hχ _ (Finset.prod_pos (fun b hb => hA b (hB hb)))⟩
  constructor
  · intro h B hB hne
    rw [← (key B hB hne).1, ← (key B hB hne).2]; exact h B hB hne
  · intro h B hB hne
    rw [(key B hB hne).1, (key B hB hne).2]; exact h B hB hne

/-- G5. `r = 0` is vacuous only because no colouring exists, of `ℕ` or of `ℕ+`. -/
example : IsEmpty (ℕ → Fin 0) ∧ IsEmpty (ℕ+ → Fin 0) :=
  ⟨⟨fun χ => (χ 0).elim0⟩, ⟨fun χ => (χ 1).elim0⟩⟩

end OpusProbes

#print axioms OpusProbes.target_imp_indep
#print axioms OpusProbes.indep_imp_target
#print axioms OpusProbes.target_imp_fc172
#print axioms OpusProbes.target_imp_uniform_colour

import HindmanSumsProducts.Prediction.Results

/-!
# Nilsequence projections and the Ramsey selection of gap energies (§5.2, 05:355–430)

The paper works in the real Hilbert space of uniformly bounded families with pairing
`lim_𝒰 ⟨·,·⟩_{L²(μ_i)}` (05:355–364) and its closed subspaces `𝒩_{i,l}` spanned by representing
families at gap `l`.  Every statement of §5 uses only norms of projections `‖P_{i,l} v‖₂` of
bounded families `v`, and for a closed span these are
`‖P_{i,l} v‖₂ = sup {⟨v, u⟩ : u ∈ span, ‖u‖₂ ≤ 1}`.
So the statements below use `projNorm`, defined by that supremum, with no completion; the
Hilbert space itself is a device of the proofs (`energy_selection`, `projection_lower_bound`).
In particular (eq:prediction-coarse-approximation) `‖S − P F‖ ≤ ε` with `S ∈ 𝒩` is equivalent to
`‖P(F − S)‖ ≤ ε`, since `P S = S`.
-/

open scoped BigOperators NNReal Topology
open Filter

namespace HindmanSumsProducts.Prediction

noncomputable section

variable {K r : ℕ}

/-- The pairing `⟨f, g⟩ = lim_𝒰 E_{μ_i} f_N g_N` of 05:356–359. -/
def familyInner (A : Parameters K) (U : Ultrafilter ℕ) (i : Fin K) (f g : ℕ → ℤ → ℝ) : ℝ :=
  ulim U (fun N => Emu A N i (fun y => f N y * g N y))

/-- The span of the representing families at gap `l` of step `≤ s` (all menus, all Lipschitz
bounds); its closure in the Hilbert space is `𝒩_{i,l}` (05:359–364). -/
def repSpan (A : Parameters K) (l : Fin K) (s : ℕ) : Submodule ℝ (ℕ → ℤ → ℝ) :=
  Submodule.span ℝ
    {v | ∃ (Fm : Menu s) (Km : ℝ≥0) (Φ : RepFamily A l Fm Km), v = Φ.eval}

/-- `‖P_{i,l} v‖₂`, the norm of the orthogonal projection onto `𝒩_{i,l}` (step `≤ s`), for a
bounded family `v`. -/
def projNorm (A : Parameters K) (U : Ultrafilter ℕ) (i l : Fin K) (s : ℕ)
    (v : ℕ → ℤ → ℝ) : ℝ :=
  sSup ((fun u => familyInner A U i v u) ''
    {u | u ∈ repSpan A l s ∧ familyInner A U i u u ≤ 1})

/-- (eq:prediction-nested-spaces), inclusion part (05:366–373): if `R_l ∣ R_{l'}` then
representing families at gap `l'` are representing families at gap `l` (pieces are re-indexed;
the global progression index is unchanged). -/
theorem repSpan_antitone (A : Parameters K) (s : ℕ) {l l' : Fin K}
    (hdiv : ∀ N, A.H N l ∣ A.H N l') : repSpan A l' s ≤ repSpan A l s := by
  sorry

/-- Raising the step bound only enlarges the span (`OAI.SourceMenuLiteral.raiseMenu`). -/
theorem repSpan_mono_step (A : Parameters K) (l : Fin K) {s s' : ℕ} (h : s ≤ s') :
    repSpan A l s ≤ repSpan A l s' := by
  sorry

/-- Projection lower bound (05:670–674): a span element `V` with `‖V‖₂ ≤ 1` and
`⟨h, V⟩ ≥ c` forces `‖P_{i,l} h‖₂ ≥ c`, for a bounded family `h`. -/
theorem le_projNorm (A : Parameters K) (U : Ultrafilter ℕ) (i l : Fin K) (s : ℕ)
    (h V : ℕ → ℤ → ℝ) (hb : ∃ C, ∀ N y, |h N y| ≤ C) (hV : V ∈ repSpan A l s)
    (hVn : familyInner A U i V V ≤ 1) :
    familyInner A U i h V ≤ projNorm A U i l s h := by
  sorry

/-- A Lipschitz map of `[0,1]` into itself, applied to a representing family, is a representing
family on the same menu (05:374–376, used for `ψ(S)` at 05:729–731). -/
theorem RepFamily.comp_exists {A : Parameters K} {l : Fin K} {s : ℕ} {Fm : Menu s}
    {Km : ℝ≥0} (Φ : RepFamily A l Fm Km) (ψ : ℝ → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ)
    (hψ01 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ψ x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ Ψ : RepFamily A l Fm (L * Km), ∀ N y, Ψ.eval N y = ψ (Φ.eval N y) := by
  sorry

/-- Closure of the model class (02:103–105, 05:374–376, 05:407–419; blueprint X.1): for finitely
many menus of step `≤ s` there is one menu (built from product nilmanifolds of the charted menus)
on which every `[0,1]`-valued Lipschitz combination of representing families on those menus, at
the same gap, is again a representing family.  This includes clipping finite real combinations
to `[0,1]` and re-expressing finitely many families on one common menu. -/
theorem rep_menu_combination (A : Parameters K) (l : Fin K) {k s : ℕ} (Fm : Fin k → Menu s) :
    ∃ F' : Menu s, ∀ (Km : Fin k → ℝ≥0) (Φ : ∀ t, RepFamily A l (Fm t) (Km t))
      (G : (Fin k → ℝ) → ℝ) (L : ℝ≥0), LipschitzWith L G →
      (∀ x : Fin k → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) → G x ∈ Set.Icc (0 : ℝ) 1) →
      ∃ (K' : ℝ≥0) (Ψ : RepFamily A l F' K'),
        ∀ N y, Ψ.eval N y = G (fun t => (Φ t).eval N y) := by
  sorry

/-- The coarse approximant (05:407–419): a `[0,1]`-valued family `F` has a `[0,1]`-valued
representing family `S` at gap `l` with `‖P_{i,l}(F − S)‖₂ ≤ ε` (approximate `P F` by a finite
combination, clip it to `[0,1]`, Pythagoras). -/
theorem coarse_approximant (A : Parameters K) (U : Ultrafilter ℕ) (i l : Fin K) (s : ℕ)
    (F : ℕ → ℤ → ℝ) (hF : ∀ N y, F N y ∈ Set.Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Fm : Menu s) (Km : ℝ≥0) (Φ : RepFamily A l Fm Km),
      projNorm A U i l s (fun N y => F N y - Φ.eval N y) ≤ ε := by
  sorry

/-- The Ramsey step of Lemma `lem:energy-selection` (05:399–405): a tuple `(T, l, i)` with
`T < l < i` is identified with the set `T ∪ {l, i}`; for `c` colours there is a master count
`K₀` such that every colouring of subsets has a set `H` of size `2n` on which the colour of a
subset of size `3, …, n+1` depends only on its size. -/
theorem energy_ramsey (n c : ℕ) :
    ∃ K₀ : ℕ, ∀ col : Finset (Fin K₀) → Fin c, ∃ H : Finset (Fin K₀), H.card = 2 * n ∧
      ∀ T T' : Finset (Fin K₀), T ⊆ H → T' ⊆ H → T.card = T'.card → 3 ≤ T.card →
        T.card ≤ n + 1 → col T = col T' := by
  sorry

/-- A master block whose pivot is the principal index `prin u` and whose tail consists of
principal indices `prin v`, `v < u₁` (`u₁ ≤ u`). -/
def PrincipalBlock {n : ℕ} (prin : Fin n → Fin K) (u₁ u : Fin n) (B : Block K) : Prop :=
  B.1 = prin u ∧ ∀ t ∈ B.2.val, ∃ v, v < u₁ ∧ t = prin v

/-- The output of Lemma `lem:energy-selection` (05:378–396) for master parameters `A`, an
ultrafilter `U`, a `[0,1]`-valued family `F`, and `ε`: interleaved indices
`k_1 < j_1 < ⋯ < k_n < j_n` (`pad`, `prin`), one menu of step `≤ s` with one Lipschitz bound, and
`[0,1]`-valued representing families `S_{B,a,c}` at the coarse gap `k_u` for the blocks with pivot
`j_u`, such that (eq:prediction-coarse-approximation) `‖P_{j_u,k_u}(F − S)‖ ≤ ε` and
(eq:prediction-fine-projection) `‖P_{j_u,k_{u₁}}(F − S)‖ ≤ 2ε` whenever the tail consists of
principal indices before `j_{u₁}`, `u₁ ≤ u` (for a chain on the principal indices, `k_{u₁}` is
the padding index immediately before its first pivot). -/
structure EnergySelection (n s : ℕ) (As : Finset ℚ) (A : Parameters K) (U : Ultrafilter ℕ)
    (F : BlockFamily K r) (ε : ℝ) where
  pad : Fin n → Fin K
  prin : Fin n → Fin K
  pad_lt_prin : ∀ u, pad u < prin u
  prin_lt_pad : ∀ u v, u < v → prin u < pad v
  menu : Menu s
  lip : ℝ≥0
  model : (u : Fin n) → Block K → ℚ → Fin r → RepFamily A (pad u) menu lip
  coarse : ∀ (u : Fin n) (B : Block K), PrincipalBlock prin u u B → ∀ a ∈ As, ∀ c : Fin r,
    projNorm A U (prin u) (pad u) s (fun N y => F N B a c y - (model u B a c).eval N y) ≤ ε
  fine : ∀ (u₁ u : Fin n) (B : Block K), u₁ ≤ u → PrincipalBlock prin u₁ u B →
    ∀ a ∈ As, ∀ c : Fin r,
      projNorm A U (prin u) (pad u₁) s (fun N y => F N B a c y - (model u B a c).eval N y) ≤
        2 * ε

/-- Lemma `lem:energy-selection` (05:378–396): for every `ε > 0` a master count `K` depending
only on `n`, `r`, `|𝒜|` and `ε` admits the selection, for every step `s`, every scale list of size
`≤ a`, every master parameters with nested gap lengths, every ultrafilter and every
`[0,1]`-valued family.  The model complexity (menu, Lipschitz bound) depends on all of these. -/
theorem energy_selection (n r a : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ (s : ℕ) (As : Finset ℚ), As.card ≤ a → ∀ (A : Parameters K),
      (∀ N (l l' : Fin K), l ≤ l' → A.H N l ∣ A.H N l') →
      ∀ (U : Ultrafilter ℕ) (F : BlockFamily K r), UnitValued F →
        Nonempty (EnergySelection n s As A U F ε) := by
  sorry

end

end HindmanSumsProducts.Prediction

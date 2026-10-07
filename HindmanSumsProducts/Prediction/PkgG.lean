import HindmanSumsProducts.Prediction.Projections
import HindmanSumsProducts.Concatenation

/-! Helper lemmas for §5 (part S5-G). -/

namespace HindmanSumsProducts

open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Prediction

private theorem expect_top_addSubgroup {G : Type*} [AddCommGroup G] [Fintype G]
    (f : (⊤ : AddSubgroup G) → ℂ) (g : G → ℂ)
    (h : ∀ x, f x = g (x : G)) : (𝔼 x : (⊤ : AddSubgroup G), f x) = 𝔼 x : G, g x := by
  exact Fintype.expect_equiv AddSubgroup.topEquiv.toEquiv f g (fun x => by simpa using h x)

/-- The subgroup box moment on repeated top directions is OpenAI's Gowers moment. -/
theorem boxMoment_replicate_top_helper (t : ℕ) {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) :
    SubgroupBox.boxMoment (List.replicate t (⊤ : AddSubgroup G)) f = OAI.Erdos3.gowersMoment t f := by
  induction t generalizing f with
  | zero => rfl
  | succ t ih =>
      rw [List.replicate_succ]
      simp only [SubgroupBox.boxMoment, OAI.Erdos3.gowersMoment]
      calc
        _ = 𝔼 h : (⊤ : AddSubgroup G),
            OAI.Erdos3.gowersMoment t (OAI.Erdos3.multiplicativeDerivative f h) := by
              change (𝔼 h ∈ (Finset.univ : Finset (⊤ : AddSubgroup G)),
                SubgroupBox.boxMoment (List.replicate t (⊤ : AddSubgroup G))
                  (SubgroupBox.mderiv f h)) =
                𝔼 h ∈ (Finset.univ : Finset (⊤ : AddSubgroup G)),
                  OAI.Erdos3.gowersMoment t
                    (OAI.Erdos3.multiplicativeDerivative f h)
              apply Finset.expect_congr rfl
              intro h hh
              rw [ih]
              rfl
        _ = 𝔼 h : G, OAI.Erdos3.gowersMoment t
            (OAI.Erdos3.multiplicativeDerivative f h) := by
              apply expect_top_addSubgroup
              intro h
              rfl
        _ = OAI.Erdos3.gowersMoment (t + 1) f := rfl

/-- The probability of two independently sampled tuples under the same good-event conditioning. -/
theorem nested_goodSlotAverage_bad_eq {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (S : FromArithmetic.MasterScales K As sl Dm)
    (l : Fin K) (N : ℕ) {q : ℕ} (good : (Fin q → ℕ) → Prop)
    (E : (Fin q → ℕ) → (Fin q → ℕ) → Prop) :
    goodSlotAverage S l N good (fun p =>
      goodSlotAverage S l N good (fun p' => if E p p' then 0 else 1)) =
    (gapSlotProbability S l N good)⁻¹ * (gapSlotProbability S l N good)⁻¹ *
      independentPrimePairProbability
        (fun _ : Fin q => (S.primeStage.pool N l).lower)
        (fun _ : Fin q => (S.primeStage.pool N l).upper)
        (fun _ : Fin q => (S.primeStage.pool N l).lower)
        (fun _ : Fin q => (S.primeStage.pool N l).upper)
        (fun p p' => good p ∧ good p' ∧ ¬ E p p') := by
  classical
  let lo : Fin q → ℕ := fun _ => (S.primeStage.pool N l).lower
  let hi : Fin q → ℕ := fun _ => (S.primeStage.pool N l).upper
  let mass : (Fin q → ℕ) → ℝ := independentPrimePoolMass lo hi
  let gp : ℝ := independentPrimePoolProbability lo hi good
  have hterm (p : Fin q → ℕ) :
      mass p * (if good p then gp⁻¹ *
        (∑' p' : Fin q → ℕ, mass p' *
          (if good p' then if E p p' then 0 else 1 else 0)) else 0) =
      gp⁻¹ * (mass p *
        (∑' p' : Fin q → ℕ, mass p' *
          if good p ∧ good p' ∧ ¬ E p p' then 1 else 0)) := by
    by_cases hp : good p
    · have hs : (∑' p' : Fin q → ℕ, mass p' *
          (if good p' then if E p p' then 0 else 1 else 0)) =
        ∑' p' : Fin q → ℕ, mass p' *
          (if good p' ∧ ¬ E p p' then 1 else 0) := by
          apply tsum_congr
          intro p'
          by_cases hg : good p'
          · by_cases he : E p p' <;> simp [hg, he]
          · simp [hg]
      have hs' : (∑' p' : Fin q → ℕ, mass p' *
          (if good p' ∧ ¬ E p p' then 1 else 0)) =
        ∑' p' : Fin q → ℕ, mass p' *
          (if good p ∧ good p' ∧ ¬ E p p' then 1 else 0) := by
          apply tsum_congr
          intro p'
          simp [hp, and_assoc]
      simp only [if_pos hp]
      rw [hs]
      rw [hs']
      ring
    · simp [hp]
  change gp⁻¹ * (∑' p : Fin q → ℕ,
      mass p * (if good p then gp⁻¹ *
        (∑' p' : Fin q → ℕ, mass p' *
          (if good p' then if E p p' then 0 else 1 else 0)) else 0)) =
    gp⁻¹ * gp⁻¹ * independentPrimePairProbability lo hi lo hi
      (fun p p' => good p ∧ good p' ∧ ¬ E p p')
  rw [show (∑' p : Fin q → ℕ,
      mass p * (if good p then gp⁻¹ *
        (∑' p' : Fin q → ℕ, mass p' *
          (if good p' then if E p p' then 0 else 1 else 0)) else 0)) =
      gp⁻¹ * independentPrimePairProbability lo hi lo hi
        (fun p p' => good p ∧ good p' ∧ ¬ E p p') by
        calc
          _ = ∑' p : Fin q → ℕ, gp⁻¹ * (mass p *
              (∑' p' : Fin q → ℕ, mass p' *
                if good p ∧ good p' ∧ ¬ E p p' then 1 else 0)) := by
                apply tsum_congr
                intro p
                exact hterm p
          _ = gp⁻¹ * ∑' p : Fin q → ℕ, mass p *
                (∑' p' : Fin q → ℕ, mass p' *
                  if good p ∧ good p' ∧ ¬ E p p' then 1 else 0) := tsum_mul_left
          _ = _ := by
                simp [independentPrimePairProbability, lo, hi, mass]]
  ring

private def poolTupleSupport {q : ℕ} (lo hi : Fin q → ℕ) : Finset (Fin q → ℕ) :=
  Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))

private lemma poolMass_zero_of_not_support {q : ℕ} (lo hi : Fin q → ℕ)
    (p : Fin q → ℕ) (hp : p ∉ poolTupleSupport lo hi) :
    independentPrimePoolMass lo hi p = 0 := by
  classical
  have hnotall : ¬ ∀ i : Fin q, p i ∈ Finset.Ico (lo i) (hi i) := by
    intro hall
    apply hp
    simpa [poolTupleSupport] using hall
  obtain ⟨i, hi⟩ := not_forall.mp hnotall
  unfold independentPrimePoolMass
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  unfold primePoolLaw
  split_ifs with h
  · exact False.elim (hi (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩))
  · rfl

private lemma poolMass_summable {q : ℕ} (lo hi : Fin q → ℕ) :
    Summable (independentPrimePoolMass lo hi) := by
  apply summable_of_ne_finset_zero (s := poolTupleSupport lo hi)
  intro p hp
  exact poolMass_zero_of_not_support lo hi p hp

private lemma poolProbability_summable {q : ℕ} (lo hi : Fin q → ℕ)
    (E : (Fin q → ℕ) → Prop) :
    Summable (fun p => independentPrimePoolMass lo hi p * if E p then 1 else 0) := by
  classical
  apply summable_of_ne_finset_zero (s := poolTupleSupport lo hi)
  intro p hp
  rw [poolMass_zero_of_not_support lo hi p hp]
  simp

private lemma pairOuter_summable {q q' : ℕ}
    (loF hiF : Fin q → ℕ) (loG hiG : Fin q' → ℕ)
    (E : (Fin q → ℕ) → (Fin q' → ℕ) → Prop) :
    Summable (fun x => independentPrimePoolMass loF hiF x *
      (∑' y : Fin q' → ℕ,
        independentPrimePoolMass loG hiG y * if E x y then 1 else 0)) := by
  classical
  apply summable_of_ne_finset_zero (s := poolTupleSupport loF hiF)
  intro x hx
  rw [poolMass_zero_of_not_support loF hiF x hx]
  simp

theorem pairProbability_product {q q' : ℕ}
    (loF hiF : Fin q → ℕ) (loG hiG : Fin q' → ℕ)
    (EF : (Fin q → ℕ) → Prop) (EG : (Fin q' → ℕ) → Prop) :
    independentPrimePairProbability loF hiF loG hiG (fun x y => EF x ∧ EG y) =
      independentPrimePoolProbability loF hiF EF *
        independentPrimePoolProbability loG hiG EG := by
  classical
  let f : (Fin q → ℕ) → ℝ := fun x =>
    independentPrimePoolMass loF hiF x * if EF x then 1 else 0
  let g : (Fin q' → ℕ) → ℝ := fun y =>
    independentPrimePoolMass loG hiG y * if EG y then 1 else 0
  have hf : Summable f := by
    apply summable_of_ne_finset_zero (s := poolTupleSupport loF hiF)
    intro x hx
    change independentPrimePoolMass loF hiF x * (if EF x then 1 else 0) = 0
    rw [poolMass_zero_of_not_support loF hiF x hx]
    simp
  have hg : Summable g := by
    apply summable_of_ne_finset_zero (s := poolTupleSupport loG hiG)
    intro y hy
    change independentPrimePoolMass loG hiG y * (if EG y then 1 else 0) = 0
    rw [poolMass_zero_of_not_support loG hiG y hy]
    simp
  calc
    independentPrimePairProbability loF hiF loG hiG (fun x y => EF x ∧ EG y) =
        ∑' x, f x * ∑' y, g y := by
          unfold independentPrimePairProbability
          apply tsum_congr
          intro x
          by_cases hEx : EF x <;> simp [f, g, hEx]
    _ = (∑' x, f x) * (∑' y, g y) := hf.tsum_mul_right _
    _ = independentPrimePoolProbability loF hiF EF *
        independentPrimePoolProbability loG hiG EG := by
          simp [f, g, independentPrimePoolProbability]

theorem pairProbability_add_disjoint {q q' : ℕ}
    (loF hiF : Fin q → ℕ) (loG hiG : Fin q' → ℕ)
    (E F : (Fin q → ℕ) → (Fin q' → ℕ) → Prop)
    [DecidableRel E] [DecidableRel F]
    [DecidableRel (fun (x : Fin q → ℕ) (y : Fin q' → ℕ) => E x y ∨ F x y)]
    (hdisj : ∀ x y, ¬ (E x y ∧ F x y)) :
    independentPrimePairProbability loF hiF loG hiG (fun x y => E x y ∨ F x y) =
      independentPrimePairProbability loF hiF loG hiG E +
      independentPrimePairProbability loF hiF loG hiG F := by
  classical
  letI : DecidableRel E := fun x y => Classical.propDecidable (E x y)
  letI : DecidableRel F := fun x y => Classical.propDecidable (F x y)
  letI : DecidableRel (fun (x : Fin q → ℕ) (y : Fin q' → ℕ) => E x y ∨ F x y) :=
    fun x y => Classical.propDecidable (E x y ∨ F x y)
  have hinner (x : Fin q → ℕ) :
      (∑' y : Fin q' → ℕ,
        independentPrimePoolMass loG hiG y * if E x y ∨ F x y then 1 else 0) =
      (∑' y : Fin q' → ℕ,
        independentPrimePoolMass loG hiG y * if E x y then 1 else 0) +
      (∑' y : Fin q' → ℕ,
        independentPrimePoolMass loG hiG y * if F x y then 1 else 0) := by
    have hE : Summable (fun y : Fin q' → ℕ =>
        independentPrimePoolMass loG hiG y * if E x y then 1 else 0) :=
      poolProbability_summable loG hiG (E x)
    have hF : Summable (fun y : Fin q' → ℕ =>
        independentPrimePoolMass loG hiG y * if F x y then 1 else 0) :=
      poolProbability_summable loG hiG (F x)
    calc
      _ = ∑' y : Fin q' → ℕ,
          ((independentPrimePoolMass loG hiG y * if E x y then 1 else 0) +
            (independentPrimePoolMass loG hiG y * if F x y then 1 else 0)) := by
          apply tsum_congr
          intro y
          by_cases hEx : E x y
          · have hFy : ¬ F x y := fun hf => hdisj x y ⟨hEx, hf⟩
            simp [hEx, hFy]
          · simp [hEx]
      _ = _ := hE.tsum_add hF
  have hOuterE := pairOuter_summable loF hiF loG hiG E
  have hOuterF := pairOuter_summable loF hiF loG hiG F
  unfold independentPrimePairProbability
  calc
    (∑' x : Fin q → ℕ,
      independentPrimePoolMass loF hiF x *
        (∑' y : Fin q' → ℕ,
          independentPrimePoolMass loG hiG y * if E x y ∨ F x y then 1 else 0)) =
      ∑' x : Fin q → ℕ,
        independentPrimePoolMass loF hiF x *
          ((∑' y : Fin q' → ℕ,
            independentPrimePoolMass loG hiG y * if E x y then 1 else 0) +
           (∑' y : Fin q' → ℕ,
            independentPrimePoolMass loG hiG y * if F x y then 1 else 0)) := by
            apply tsum_congr
            intro x
            rw [hinner x]
    _ = ∑' x : Fin q → ℕ,
        ((independentPrimePoolMass loF hiF x *
            (∑' y : Fin q' → ℕ,
              independentPrimePoolMass loG hiG y * if E x y then 1 else 0)) +
          (independentPrimePoolMass loF hiF x *
            (∑' y : Fin q' → ℕ,
              independentPrimePoolMass loG hiG y * if F x y then 1 else 0))) := by
            apply tsum_congr
            intro x
            ring
    _ = (∑' x : Fin q → ℕ,
          independentPrimePoolMass loF hiF x *
            (∑' y : Fin q' → ℕ,
              independentPrimePoolMass loG hiG y * if E x y then 1 else 0)) +
        ∑' x : Fin q → ℕ,
          independentPrimePoolMass loF hiF x *
            (∑' y : Fin q' → ℕ,
              independentPrimePoolMass loG hiG y * if F x y then 1 else 0) :=
            hOuterE.tsum_add hOuterF

theorem poolLower_tendsto {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (l : Fin K) : Tendsto (fun N => (MS.primeStage.pool N l).lower) atTop atTop := by
  have hdom := MS.primeStage.pool_lower_dominates l
  have hratio : Tendsto
      (fun N => ((MS.primeStage.pool N l).lower : ℝ) /
        (masterScaleV MS.core.parameters N l : ℝ) ^ (1 : ℝ)) atTop atTop := by
    simpa [Real.rpow_one] using hdom 1 (by norm_num)
  have hle : (fun N => ((MS.primeStage.pool N l).lower : ℝ) /
      (masterScaleV MS.core.parameters N l : ℝ)) ≤ᶠ[atTop]
      (fun N => ((MS.primeStage.pool N l).lower : ℝ)) := by
    filter_upwards with N
    have hV : 1 ≤ (masterScaleV MS.core.parameters N l : ℝ) := by
      exact_mod_cast (show 1 ≤ masterScaleV MS.core.parameters N l by
        unfold masterScaleV
        omega)
    have hVpos : 0 < (masterScaleV MS.core.parameters N l : ℝ) := by linarith
    have hlow : 0 ≤ ((MS.primeStage.pool N l).lower : ℝ) := by positivity
    apply (div_le_iff₀ hVpos).2
    have hmul := mul_nonneg hlow (sub_nonneg.mpr hV)
    nlinarith
  have hReal : Tendsto (fun N => ((MS.primeStage.pool N l).lower : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_mono' atTop (by simpa using hle) hratio
  exact tendsto_natCast_atTop_iff.mp hReal

private noncomputable def shortDiff {q a L : ℕ} [NeZero q] (u0 u1 : Fin L) :
    AddSubgroup.zmultiples (a : ZMod q) :=
  ⟨((u1.val : ℤ) - u0.val) • (a : ZMod q),
    AddSubgroup.zsmul_mem_zmultiples _ _⟩

private theorem shortDiff_injective {q a L : ℕ} [NeZero q] (ha : 0 < a)
    (hadiv : a ∣ q) (hL : L ≤ q / a) (u0 : Fin L) :
    Function.Injective (shortDiff (q := q) (a := a) (L := L) u0) := by
  classical
  intro u1 u2 h
  have heq : ((a : ℤ) * ((u1.val : ℤ) - u0.val) : ZMod q) =
      (a : ℤ) * ((u2.val : ℤ) - u0.val) := by
    simpa [shortDiff, zsmul_eq_mul, mul_comm] using congrArg Subtype.val h
  have heqCast : (((a : ℤ) * ((u1.val : ℤ) - u0.val) : ℤ) : ZMod q) =
      (((a : ℤ) * ((u2.val : ℤ) - u0.val) : ℤ) : ZMod q) := by
    exact_mod_cast heq
  have hmod : (q : ℤ) ∣ (a : ℤ) * ((u2.val : ℤ) - (u1.val : ℤ)) := by
    have h' := (ZMod.intCast_eq_intCast_iff_dvd_sub
      ((a : ℤ) * ((u1.val : ℤ) - u0.val))
      ((a : ℤ) * ((u2.val : ℤ) - u0.val)) q).mp heqCast
    simpa [mul_sub, sub_sub_sub_cancel_right] using h'
  have hq : q = a * (q / a) := by
    calc
      q = (q / a) * a := (Nat.div_mul_cancel hadiv).symm
      _ = a * (q / a) := Nat.mul_comm _ _
  rw [hq, Nat.cast_mul] at hmod
  have hdiv : ((q / a : ℕ) : ℤ) ∣ (u2.val : ℤ) - u1.val :=
    Int.dvd_of_mul_dvd_mul_left (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt ha)) hmod
  have hsmall : Int.natAbs ((u2.val : ℤ) - u1.val) < q / a :=
    (Int.natAbs_coe_sub_coe_lt_of_lt u2.isLt u1.isLt).trans_le hL
  have hsmall' : Int.natAbs ((u2.val : ℤ) - u1.val) <
      Int.natAbs ((q : ℤ) / (a : ℤ)) := by
    rw [← Int.natCast_div q a, Int.natAbs_natCast]
    exact hsmall
  have hzero : (u2.val : ℤ) - u1.val = 0 := by
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv hsmall'
  apply Fin.ext
  exact_mod_cast (sub_eq_zero.mp hzero).symm

private theorem shiftAverage_shortDiff_le {q a J0 L d : ℕ} [NeZero q]
    (ha : 0 < a) (hadiv : a ∣ q) (hL : 0 < L) (hLn : L ≤ q / a)
    (hn : q / a ≤ 2 * J0 * L)
    (F : (Fin d → AddSubgroup.zmultiples (a : ZMod q)) → ℝ)
    (hF : ∀ h, 0 ≤ F h) :
    shiftAverage (Fin d) L (fun u => F (fun j =>
      shortDiff (⟨u j 0 % L, Nat.mod_lt _ hL⟩) (⟨u j 1 % L, Nat.mod_lt _ hL⟩))) ≤
        (2 * J0 : ℝ) ^ d *
          𝔼 h : (Fin d → AddSubgroup.zmultiples (a : ZMod q)), F h := by
  classical
  let Q : AddSubgroup (ZMod q) := AddSubgroup.zmultiples (a : ZMod q)
  let B : Type := (Fin d → Fin L) × (Fin d → Fin L)
  let diff : Fin L → Fin L → Q := fun u0 u1 =>
    shortDiff (q := q) (a := a) (L := L) u0 u1
  let S : Finset (Fin d → Fin 2 → ℕ) :=
    Fintype.piFinset (fun _ : Fin d => Fintype.piFinset fun _ : Fin 2 => Finset.range L)
  let toNat : (Fin d → Fin 2 → Fin L) → (Fin d → Fin 2 → ℕ) :=
    fun u i e => (u i e).val
  have hS : S = Finset.univ.image toNat := by
    ext u
    change u ∈ Fintype.piFinset
        (fun _ : Fin d => Fintype.piFinset fun _ : Fin 2 => Finset.range L) ↔
      u ∈ Finset.univ.image toNat
    rw [Fintype.mem_piFinset]
    simp only [Fintype.mem_piFinset, Finset.mem_range, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · intro hu
      refine ⟨fun i e => ⟨u i e, hu i e⟩, ?_⟩
      funext i e
      rfl
    · rintro ⟨v, hvu⟩ i e
      have hv := congrFun (congrFun hvu i) e
      rw [← hv]
      exact (v i e).isLt
  have htoNat_inj : Function.Injective toNat := by
    intro u v huv
    funext i e
    exact Fin.ext (congrFun (congrFun huv i) e)
  let split : (Fin d → Fin 2 → Fin L) ≃ B :=
    { toFun := fun (u : Fin d → Fin 2 → Fin L) => (fun i => u i 0, fun i => u i 1)
      invFun := fun (p : B) i e => if e = 0 then p.1 i else p.2 i
      left_inv := by
        intro u
        funext i e
        fin_cases e <;> simp
      right_inv := by
        rintro ⟨u0, u1⟩
        simp }
  have hDiffInjective (u0 : Fin d → Fin L) :
      Function.Injective (fun u1 : Fin d → Fin L =>
        fun j => diff (u0 j) (u1 j)) := by
    intro u1 u2 huv
    funext j
    exact shortDiff_injective ha hadiv hLn (u0 j) (congrFun huv j)
  have hEndpointSum :
      (∑ u0 : Fin d → Fin L, ∑ u1 : Fin d → Fin L,
        F (fun j => diff (u0 j) (u1 j))) ≤
        (L : ℝ) ^ d * ∑ h : Fin d → Q, F h := by
    calc
      _ ≤ ∑ u0 : Fin d → Fin L, ∑ h : Fin d → Q, F h := by
        apply Finset.sum_le_sum
        intro u0 hu0
        calc
          _ = ∑ h ∈ (Finset.univ.image (fun u1 : Fin d → Fin L =>
              fun j => diff (u0 j) (u1 j))), F h := by
                rw [Finset.sum_image (Set.injOn_of_injective (hDiffInjective u0))]
          _ ≤ ∑ h : Fin d → Q, F h := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro h hh
                  simp
                · intro h hh hh'
                  exact hF h
      _ = (Fintype.card (Fin d → Fin L) : ℝ) * ∑ h : Fin d → Q, F h := by
        simp [Finset.sum_const]
      _ = _ := by simp [Fintype.card_fun, Fintype.card_fin]
  have hsum :
      (∑ u ∈ S, F (fun j => shortDiff
          (⟨u j 0 % L, Nat.mod_lt _ hL⟩) (⟨u j 1 % L, Nat.mod_lt _ hL⟩))) =
        ∑ p : B, F (fun j => diff (p.1 j) (p.2 j)) := by
    rw [hS, Finset.sum_image (Set.injOn_of_injective htoNat_inj)]
    exact Fintype.sum_equiv split _ _ (by
      intro u
      congr 1
      funext j
      simp [toNat, split, diff, Nat.mod_eq_of_lt (u j 0).isLt,
        Nat.mod_eq_of_lt (u j 1).isLt])
  have hRatio : ((L : ℝ) ^ d)⁻¹ ≤ (2 * J0 : ℝ) ^ d /
      (Fintype.card (Fin d → Q) : ℝ) := by
    have hnn : 0 < q / a := by omega
    have hmul : (q / a : ℝ) ≤ (2 * J0 : ℝ) * L := by exact_mod_cast hn
    have hpow : (q / a : ℝ) ^ d ≤ (2 * J0 : ℝ) ^ d * (L : ℝ) ^ d := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hmul d
    have hcardQ : Fintype.card Q = q / a := by
      rw [Fintype.card_zmultiples, ZMod.addOrderOf_coe, Nat.gcd_eq_right hadiv]
      exact NeZero.ne q
    have hcardVec : Fintype.card (Fin d → Q) = (q / a) ^ d := by
      simp [hcardQ]
    rw [hcardVec]
    have haReal : (a : ℝ) ≠ 0 := by positivity
    have hpowCast : ((q / a : ℕ) : ℝ) ^ d ≤
        (2 * J0 : ℝ) ^ d * (L : ℝ) ^ d := by
      simpa [Nat.cast_div hadiv haReal] using hpow
    have hLp : 0 < (L : ℝ) ^ d := by positivity
    have hqr : (0 : ℝ) < ((q / a : ℕ) : ℝ) := by exact_mod_cast hnn
    have hnP : 0 < ((q / a : ℕ) : ℝ) ^ d := pow_pos hqr _
    field_simp [ne_of_gt hLp, ne_of_gt hnP]
    push_cast
    nlinarith [hpowCast]
  have hsumQ : 0 ≤ ∑ h : Fin d → Q, F h := Finset.sum_nonneg fun h _ => hF h
  have hEndpointPair :
      (∑ p : B, F (fun j => diff (p.1 j) (p.2 j))) ≤
        (L : ℝ) ^ d * ∑ h : Fin d → Q, F h := by
    rw [show (Finset.univ : Finset ((Fin d → Fin L) × (Fin d → Fin L))) =
        (Finset.univ : Finset (Fin d → Fin L)) ×ˢ Finset.univ by ext p; simp,
      Finset.sum_product]
    exact hEndpointSum
  unfold shiftAverage
  rw [hsum]
  have hcardA : Fintype.card (Fin d → Fin L) = L ^ d := by simp
  change ((L : ℝ) ^ (2 * Fintype.card (Fin d)))⁻¹ *
      ∑ p : B, F (fun j => shortDiff (p.1 j) (p.2 j)) ≤ _
  calc
    _ ≤ ((L : ℝ) ^ (2 * Fintype.card (Fin d)))⁻¹ *
        ((L : ℝ) ^ d * ∑ h : Fin d → Q, F h) := by
          exact mul_le_mul_of_nonneg_left hEndpointPair (inv_nonneg.mpr (by positivity))
    _ = ((L : ℝ) ^ d)⁻¹ * ∑ h : Fin d → Q, F h := by
          rw [show 2 * Fintype.card (Fin d) = 2 * d by simp]
          rw [show (L : ℝ) ^ (2 * d) = ((L : ℝ) ^ d) ^ 2 by
            rw [← pow_mul]
            ring]
          field_simp
          <;> ring
    _ ≤ (2 * J0 : ℝ) ^ d /
          (Fintype.card (Fin d → Q) : ℝ) * ∑ h : Fin d → Q, F h :=
            mul_le_mul_of_nonneg_right hRatio hsumQ
    _ = (2 * J0 : ℝ) ^ d *
          𝔼 h : (Fin d → Q), F h := by
            rw [Fintype.expect_eq_sum_div_card]
            ring

private theorem shiftAverage_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℕ) (hL : 0 < L) (F : (ι → Fin 2 → ℕ) → ℝ) :
    (shiftAverage ι L F) ^ 2 ≤ shiftAverage ι L (fun u => F u ^ 2) := by
  classical
  let s := Fintype.piFinset (fun _ : ι => Fintype.piFinset fun _ : Fin 2 => Finset.range L)
  let Z : ℝ := (L : ℝ) ^ (2 * Fintype.card ι)
  have hinnerCard :
      (Fintype.piFinset (fun _ : Fin 2 => Finset.range L)).card = L ^ 2 := by
    simpa using Fintype.card_piFinset_const (Finset.range L) 2
  have hcardNat : s.card = L ^ (2 * Fintype.card ι) := by
    calc
      s.card = ∏ i : ι, (Fintype.piFinset (fun _ : Fin 2 => Finset.range L)).card := by
        simp [s, Fintype.card_piFinset]
      _ = (L ^ 2) ^ Fintype.card ι := by simp [hinnerCard]
      _ = L ^ (2 * Fintype.card ι) := by rw [pow_mul]
  have hcard : (s.card : ℝ) = Z := by
    change (s.card : ℝ) = (L : ℝ) ^ (2 * Fintype.card ι)
    exact_mod_cast hcardNat
  have hZ : 0 < Z := by
    dsimp [Z]
    positivity
  have hcs : (∑ u ∈ s, F u) ^ 2 ≤ Z * ∑ u ∈ s, F u ^ 2 := by
    simpa [Z, hcard, mul_comm] using
      (Finset.sum_mul_sq_le_sq_mul_sq s F (fun _ => (1 : ℝ)))
  unfold shiftAverage
  change (Z⁻¹ * ∑ u ∈ s, F u) ^ 2 ≤ Z⁻¹ * ∑ u ∈ s, F u ^ 2
  calc
    (Z⁻¹ * ∑ u ∈ s, F u) ^ 2 = (Z⁻¹) ^ 2 * (∑ u ∈ s, F u) ^ 2 := by rw [mul_pow]
    _ ≤ (Z⁻¹) ^ 2 * (Z * ∑ u ∈ s, F u ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = Z⁻¹ * ∑ u ∈ s, F u ^ 2 := by field_simp [ne_of_gt hZ]

private theorem boxMoment_eq_average_gowersMoment {G : Type*} [AddCommGroup G] [Fintype G]
    (Q : AddSubgroup G) (t : ℕ) (f : G → ℂ) :
    SubgroupBox.boxMoment (List.replicate t Q) f =
      𝔼 x : G, OAI.Erdos3.gowersMoment t (fun y : Q => f (x + y)) := by
  induction t generalizing f with
  | zero =>
      change (𝔼 x : G, f x) = 𝔼 x : G, 𝔼 y : Q, f (x + y)
      rw [Finset.expect_comm]
      have htrans (y : Q) : (𝔼 x : G, f (x + y)) = 𝔼 x : G, f x := by
        exact Fintype.expect_equiv (Equiv.addRight (y : G))
          (fun x => f (x + y)) f (fun _ => rfl)
      simp_rw [htrans]
      simp
  | succ t ih =>
      rw [List.replicate_succ]
      simp only [SubgroupBox.boxMoment, OAI.Erdos3.gowersMoment]
      calc
        (𝔼 h : Q, SubgroupBox.boxMoment (List.replicate t Q) (SubgroupBox.mderiv f h)) =
            𝔼 h : Q, 𝔼 x : G, OAI.Erdos3.gowersMoment t
              (fun y : Q => SubgroupBox.mderiv f h (x + y)) := by
                apply Finset.expect_congr rfl
                intro h hh
                exact ih (SubgroupBox.mderiv f h)
        _ = 𝔼 x : G, 𝔼 h : Q, OAI.Erdos3.gowersMoment t
              (OAI.Erdos3.multiplicativeDerivative (fun y : Q => f (x + y)) h) := by
                rw [Finset.expect_comm]
                apply Finset.expect_congr rfl
                intro x hx
                apply Finset.expect_congr rfl
                intro h hh
                congr 1
                funext y
                simp [SubgroupBox.mderiv, OAI.Erdos3.multiplicativeDerivative,
                  add_assoc, add_left_comm, add_comm]
        _ = 𝔼 x : G, OAI.Erdos3.gowersMoment (t + 1)
              (fun y : Q => f (x + y)) := by rfl

private def cubeSubsetReal {G : Type*} [AddCommGroup G] (d : ℕ) (f : G → ℝ)
    (x : G) (h : Fin d → G) : ℝ :=
  ∏ ω : Finset (Fin d), f (x + ∑ j ∈ ω, h j)

private def finsetBoolEquiv (d : ℕ) : Finset (Fin d) ≃ (Fin d → Bool) where
  toFun S := fun j => decide (j ∈ S)
  invFun b := Finset.univ.filter fun j => b j
  left_inv := by
    intro S
    ext j
    simp
  right_inv := by
    intro b
    funext j
    cases h : b j <;> simp [h]

private theorem conjugationPower_real (n : ℕ) (x : ℝ) :
    OAI.Erdos3.conjugationPower n (x : ℂ) = x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [OAI.Erdos3.conjugationPower, ih]

private theorem cubeSubset_eq_cubeProduct {G : Type*} [AddCommGroup G] (d : ℕ)
    (f : G → ℝ) (h : Fin d → G) (x : G) :
    (∏ ω : Finset (Fin d), (f (x + ∑ j ∈ ω, h j) : ℂ)) =
      OAI.Erdos3.cubeProduct (fun y => (f y : ℂ)) (List.ofFn h) x := by
  classical
  rw [OAI.Erdos3.cubeProduct_eq_boolean_product]
  apply Fintype.prod_equiv (finsetBoolEquiv d)
  intro ω
  have hshift : OAI.Erdos3.cubeShift h (finsetBoolEquiv d ω) = ∑ j ∈ ω, h j := by
    simp [OAI.Erdos3.cubeShift, finsetBoolEquiv]
  rw [hshift, conjugationPower_real]

private def finConsEquiv (d : ℕ) (α : Type*) :
    (Fin (d + 1) → α) ≃ α × (Fin d → α) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv := by
    intro f
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv := by
    rintro ⟨a, f⟩
    rfl

private theorem cubeSubset_complex_eq {G : Type*} [AddCommGroup G] (d : ℕ)
    (f : G → ℝ) (x : G) (h : Fin d → G) :
    ((cubeSubsetReal d f x h : ℝ) : ℂ) =
      OAI.Erdos3.cubeProduct (fun y => (f y : ℂ)) (List.ofFn h) x := by
  calc
    ((cubeSubsetReal d f x h : ℝ) : ℂ) =
        ∏ ω : Finset (Fin d), (f (x + ∑ j ∈ ω, h j) : ℂ) := by
          exact Complex.ofReal_prod _ _
    _ = _ := cubeSubset_eq_cubeProduct d f h x

private theorem cubeSubsetReal_cons {G : Type*} [AddCommGroup G] (d : ℕ)
    (f : G → ℝ) (x s : G) (h : Fin d → G) :
    cubeSubsetReal (d + 1) f x (Fin.cons s h) =
      cubeSubsetReal d (fun y => f y * f (y + s)) x h := by
  apply Complex.ofReal_injective
  rw [cubeSubset_complex_eq, List.ofFn_cons,
    OAI.Erdos3.cubeProduct_cons_eq_derivative]
  have hderiv : OAI.Erdos3.multiplicativeDerivative (fun y => (f y : ℂ)) s =
      fun y => ((f y * f (y + s) : ℝ) : ℂ) := by
    funext y
    simp [OAI.Erdos3.multiplicativeDerivative]
  rw [hderiv, cubeSubset_complex_eq]

private theorem probWeights_square_mean_le {ι : Type*} [Fintype ι]
    (α : SubgroupBox.ProbWeights ι) (f : ι → ℝ) :
    (∑ i, α.w i * f i) ^ 2 ≤ ∑ i, α.w i * f i ^ 2 := by
  let m : ℝ := ∑ i, α.w i * f i
  have hvar : 0 ≤ ∑ i, α.w i * (f i - m) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (α.nonneg i) (sq_nonneg _)
  have hsum : (∑ i, α.w i * (f i - m) ^ 2) =
      (∑ i, α.w i * f i ^ 2) - m ^ 2 := by
    calc
      _ = ∑ i, (α.w i * f i ^ 2 - (2 * m) * (α.w i * f i) + m ^ 2 * α.w i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i, α.w i * f i ^ 2) -
            (2 * m) * (∑ i, α.w i * f i) + m ^ 2 * (∑ i, α.w i) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = (∑ i, α.w i * f i ^ 2) - m ^ 2 := by
            simp [m, α.total]
            ring
  dsimp [m] at hvar hsum
  linarith

private theorem fintype_expect_sq_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) : (𝔼 i, f i) ^ 2 ≤ 𝔼 i, f i ^ 2 := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hcs : (∑ i, f i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, f i ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) f (fun _ => (1 : ℝ))
    simpa [mul_comm] using h
  field_simp [ne_of_gt hc]
  nlinarith [hcs]

private noncomputable def uniformProbWeights (ι : Type*) [Fintype ι] [Nonempty ι] :
    SubgroupBox.ProbWeights ι where
  w _ := (Fintype.card ι : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    simp [Finset.sum_const, Fintype.card_ne_zero]

private def productProbWeights {ι κ : Type*} [Fintype ι] [Fintype κ]
    (α : SubgroupBox.ProbWeights ι) (β : SubgroupBox.ProbWeights κ) :
    SubgroupBox.ProbWeights (ι × κ) where
  w x := α.w x.1 * β.w x.2
  nonneg x := mul_nonneg (α.nonneg x.1) (β.nonneg x.2)
  total := by
    calc
      ∑ x : ι × κ, α.w x.1 * β.w x.2 =
          ∑ i : ι, ∑ j : κ, α.w i * β.w j := by
            rw [Fintype.sum_prod_type]
      _ = ∑ i : ι, α.w i * (∑ j : κ, β.w j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = (∑ i : ι, α.w i) * (∑ j : κ, β.w j) := by
            rw [← Finset.sum_mul]
      _ = 1 := by rw [α.total, β.total]; norm_num

private theorem probWeights_rpow_mean_le {ι : Type*} [Fintype ι]
    (α : SubgroupBox.ProbWeights ι) (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i)
    (r : ℝ) (hr : 1 ≤ r) :
    (∑ i, α.w i * z i) ^ r ≤ ∑ i, α.w i * (z i ^ r) := by
  have h := (convexOn_rpow hr).map_sum_le
    (t := (Finset.univ : Finset ι)) (w := α.w) (p := z)
    (fun i hi => α.nonneg i) α.total (fun i hi => Set.mem_Ici.mpr (hz i))
  simpa [smul_eq_mul] using h

private theorem expect_translate_average {G : Type*} [AddCommGroup G] [Fintype G]
    (Q : AddSubgroup G) (f : G → ℝ) :
    (𝔼 x : G, 𝔼 y : Q, f (x + y)) = 𝔼 x : G, f x := by
  classical
  calc
    (𝔼 x : G, 𝔼 y : Q, f (x + y)) = 𝔼 y : Q, 𝔼 x : G, f (x + y) :=
      Finset.expect_comm _ _ _
    _ = 𝔼 y : Q, 𝔼 x : G, f x := by
          apply Finset.expect_congr rfl
          intro y hy
          exact Fintype.expect_equiv (Equiv.addRight (y : G))
            (fun x => f (x + y)) f (fun _ => rfl)
    _ = 𝔼 x : G, f x := by simp

private theorem gowersMoment_succ_cubeExpansion {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (f : G → ℝ) :
    (OAI.Erdos3.gowersMoment (d + 1) (fun x => (f x : ℂ))).re =
      𝔼 s : G, 𝔼 h : Fin d → G, 𝔼 y : G,
        cubeSubsetReal d f y h * cubeSubsetReal d f (y + s) h := by
  classical
  have hproduct (s : G) (h : Fin d → G) (y : G) :
      (OAI.Erdos3.cubeProduct
        (OAI.Erdos3.multiplicativeDerivative (fun x => (f x : ℂ)) s)
        (List.ofFn h) y).re = cubeSubsetReal d f y h * cubeSubsetReal d f (y + s) h := by
    have hcube (x : G) : OAI.Erdos3.cubeProduct (fun z => (f z : ℂ))
        (List.ofFn h) x = (cubeSubsetReal d f x h : ℂ) := by
      calc
        _ = ∏ ω : Finset (Fin d), (f (x + ∑ j ∈ ω, h j) : ℂ) :=
          (cubeSubset_eq_cubeProduct d f h x).symm
        _ = _ := (Complex.ofReal_prod _ _).symm
    rw [OAI.Erdos3.cubeProduct_derivative]
    rw [hcube y, hcube (y + s)]
    simp
  unfold OAI.Erdos3.gowersMoment
  rw [OAI.Erdos3.expect_re]
  apply Finset.expect_congr rfl
  intro s hs
  rw [OAI.Erdos3.gowersMoment_eq_cubeAverage]
  simp only [OAI.Erdos3.cubeAverage_eq_expect_tuple, OAI.Erdos3.expect_re]
  apply Finset.expect_congr rfl
  intro h hh
  apply Finset.expect_congr rfl
  intro y hy
  exact hproduct s h y

private theorem cubeMeanSquare_le_boxMoment {G : Type*} [AddCommGroup G] [Fintype G]
    [Nonempty G] (Q : AddSubgroup G) (d : ℕ) (f : G → ℝ) :
    𝔼 h : Fin d → Q, (𝔼 x : G, cubeSubsetReal d f x (fun j => (h j : G))) ^ 2 ≤
      (SubgroupBox.boxMoment (List.replicate (d + 1) Q) (fun x => (f x : ℂ))).re := by
  letI instQ : Fintype Q := Fintype.subtype
    (Finset.univ.filter fun x : G => x ∈ Q) (by intro x; simp)
  let cube (x : G) (h : Fin d → Q) : ℝ :=
    cubeSubsetReal d f x (fun j => (h j : G))
  have hroot (h : Fin d → Q) :
      (𝔼 x : G, cube x h) = 𝔼 x : G, 𝔼 y : Q, cube (x + y) h := by
    simpa [cube] using (expect_translate_average Q (fun x => cubeSubsetReal d f x (fun j => (h j : G)))).symm
  have hpoint (h : Fin d → Q) :
      (𝔼 x : G, cube x h) ^ 2 ≤ 𝔼 x : G, (𝔼 y : Q, cube (x + y) h) ^ 2 := by
    rw [hroot h]
    exact fintype_expect_sq_le (fun x => 𝔼 y : Q, cube (x + y) h)
  have hCS :
      (𝔼 h : Fin d → Q, (𝔼 x : G, cube x h) ^ 2) ≤
        𝔼 h : Fin d → Q, 𝔼 x : G, (𝔼 y : Q, cube (x + y) h) ^ 2 := by
    apply Finset.expect_le_expect
    intro h hh
    exact hpoint h
  have hlocalSq (x : G) (h : Fin d → Q) :
      (𝔼 y : Q, cube (x + y) h) ^ 2 =
        𝔼 y : Q, 𝔼 z : Q, cube (x + y) h * cube (x + z) h := by
    rw [pow_two, Fintype.expect_mul_expect]
  have hshift (x : G) (y : Q) (h : Fin d → Q) :
      (𝔼 z : Q, cube (x + y) h * cube (x + z) h) =
        𝔼 s : Q, cube (x + y) h * cube (x + y + s) h := by
    symm
    exact Finset.expect_equiv (s := (@Finset.univ Q instQ)) (t := (@Finset.univ Q instQ))
      (Equiv.addLeft y) (by intro s; simp) (by intro s hs; simp [add_assoc])
  have htrans (y s : Q) (h : Fin d → Q) :
      (𝔼 x : G, cube (x + y) h * cube (x + y + s) h) =
        𝔼 x : G, cube x h * cube (x + s) h := by
    exact Fintype.expect_equiv (Equiv.addRight (y : G))
      (fun x => cube (x + y) h * cube (x + y + s) h)
      (fun x => cube x h * cube (x + s) h) (fun _ => by simp [add_assoc])
  have hExpansion :
      (𝔼 h : Fin d → Q, 𝔼 x : G, (𝔼 y : Q, cube (x + y) h) ^ 2) =
        𝔼 h : Fin d → Q, 𝔼 s : Q, 𝔼 x : G, cube x h * cube (x + s) h := by
    calc
      _ = 𝔼 h : Fin d → Q, 𝔼 x : G, 𝔼 y : Q, 𝔼 z : Q,
            cube (x + y) h * cube (x + z) h := by
              apply Finset.expect_congr rfl
              intro h hh
              apply Finset.expect_congr rfl
              intro x hx
              exact hlocalSq x h
      _ = 𝔼 h : Fin d → Q, 𝔼 x : G, 𝔼 y : Q, 𝔼 s : Q,
            cube (x + y) h * cube (x + y + s) h := by
              apply Finset.expect_congr rfl
              intro h hh
              apply Finset.expect_congr rfl
              intro x hx
              apply Finset.expect_congr rfl
              intro y hy
              exact hshift x y h
      _ = 𝔼 h : Fin d → Q, 𝔼 y : Q, 𝔼 x : G, 𝔼 s : Q,
            cube (x + y) h * cube (x + y + s) h := by
              apply Finset.expect_congr rfl
              intro h hh
              exact Finset.expect_comm (Finset.univ : Finset G) (@Finset.univ Q instQ)
                (fun x y => 𝔼 s : Q, cube (x + y) h * cube (x + y + s) h)
      _ = 𝔼 h : Fin d → Q, 𝔼 y : Q, 𝔼 s : Q, 𝔼 x : G,
            cube (x + y) h * cube (x + y + s) h := by
              apply Finset.expect_congr rfl
              intro h hh
              apply Finset.expect_congr rfl
              intro y hy
              exact Finset.expect_comm (Finset.univ : Finset G) (@Finset.univ Q instQ)
                (fun x s => cube (x + y) h * cube (x + y + s) h)
      _ = 𝔼 h : Fin d → Q, 𝔼 y : Q, 𝔼 s : Q, 𝔼 x : G,
            cube x h * cube (x + s) h := by
              apply Finset.expect_congr rfl
              intro h hh
              apply Finset.expect_congr rfl
              intro y hy
              apply Finset.expect_congr rfl
              intro s hs
              exact htrans y s h
      _ = 𝔼 h : Fin d → Q, 𝔼 s : Q, 𝔼 x : G, cube x h * cube (x + s) h := by
              simp
  have hMoment :
      (SubgroupBox.boxMoment (List.replicate (d + 1) Q)
        (fun x => (f x : ℂ))).re =
        𝔼 h : Fin d → Q, 𝔼 s : Q, 𝔼 x : G, cube x h * cube (x + s) h := by
    rw [boxMoment_eq_average_gowersMoment]
    rw [OAI.Erdos3.expect_re]
    calc
      _ = 𝔼 x : G, 𝔼 s : Q, 𝔼 h : Fin d → Q, 𝔼 y : Q,
            cubeSubsetReal d (fun z : Q => f (x + z)) y h *
              cubeSubsetReal d (fun z : Q => f (x + z)) (y + s) h := by
                apply Finset.expect_congr rfl
                intro x hx
                exact gowersMoment_succ_cubeExpansion d (fun z : Q => f (x + z))
      _ = 𝔼 x : G, 𝔼 s : Q, 𝔼 h : Fin d → Q, 𝔼 y : Q,
            cube (x + y) h * cube (x + y + s) h := by
              apply Finset.expect_congr rfl
              intro x hx
              apply Finset.expect_congr rfl
              intro s hs
              apply Finset.expect_congr rfl
              intro h hh
              apply Finset.expect_congr rfl
              intro y hy
              simp [cube, cubeSubsetReal, add_assoc, add_left_comm, add_comm]
      _ = 𝔼 s : Q, 𝔼 x : G, 𝔼 h : Fin d → Q, 𝔼 y : Q,
            cube (x + y) h * cube (x + y + s) h := by
              exact Finset.expect_comm (Finset.univ : Finset G) (@Finset.univ Q instQ)
                (fun x s => 𝔼 h : Fin d → Q, 𝔼 y : Q,
                  cube (x + y) h * cube (x + y + s) h)
      _ = 𝔼 s : Q, 𝔼 h : Fin d → Q, 𝔼 x : G, 𝔼 y : Q,
            cube (x + y) h * cube (x + y + s) h := by
              apply Finset.expect_congr rfl
              intro s hs
              exact Finset.expect_comm (Finset.univ : Finset G)
                (Finset.univ : Finset (Fin d → Q))
                (fun x h => 𝔼 y : Q, cube (x + y) h * cube (x + y + s) h)
      _ = 𝔼 h : Fin d → Q, 𝔼 s : Q, 𝔼 x : G, 𝔼 y : Q,
            cube (x + y) h * cube (x + y + s) h := by
              exact Finset.expect_comm (@Finset.univ Q instQ)
                (Finset.univ : Finset (Fin d → Q))
                (fun s h => 𝔼 x : G, 𝔼 y : Q,
                  cube (x + y) h * cube (x + y + s) h)
      _ = 𝔼 h : Fin d → Q, 𝔼 s : Q, 𝔼 x : G, cube x h * cube (x + s) h := by
              apply Finset.expect_congr rfl
              intro h hh
              apply Finset.expect_congr rfl
              intro s hs
              exact expect_translate_average Q (fun x => cube x h * cube (x + s) h)
  calc
    _ ≤ 𝔼 h : Fin d → Q, 𝔼 x : G, (𝔼 y : Q, cube (x + y) h) ^ 2 := hCS
    _ = (SubgroupBox.boxMoment (List.replicate (d + 1) Q)
          (fun x => (f x : ℂ))).re := by
            simpa [cube] using hExpansion.trans hMoment.symm

private theorem gowersNorm_mono {H : Type*} [AddCommGroup H] [Fintype H]
    {n m : ℕ} (hnm : n ≤ m) (f : H → ℂ) :
    OAI.Erdos3.gowersNorm (n + 1) f ≤ OAI.Erdos3.gowersNorm (m + 1) f := by
  induction hnm with
  | refl => exact le_rfl
  | @step m h ih =>
      exact ih.trans (OAI.Erdos3.gowersNorm_le_succ m f)

private theorem boxMoment_re_eq_average_gowersNorm_pow
    {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G)
    (n : ℕ) (hn : 0 < n) (f : G → ℝ) :
    (SubgroupBox.boxMoment (List.replicate n Q) (fun x => (f x : ℂ))).re =
      𝔼 x : G, (OAI.Erdos3.gowersNorm n (fun y : Q => (f (x + y) : ℂ))) ^ (2 ^ n) := by
  rw [boxMoment_eq_average_gowersMoment, OAI.Erdos3.expect_re]
  apply Finset.expect_congr rfl
  intro x hx
  have hpow := OAI.Erdos3.gowersNorm_pow (n - 1) (fun y : Q => (f (x + y) : ℂ))
  simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0))] using hpow.symm

private theorem shortDiff_cast_eq {q a L : ℕ} [NeZero q] (u0 u1 : Fin L) :
    (shortDiff (q := q) (a := a) (L := L) u0 u1 : ZMod q) =
      (((a : ℤ) * ((u1.val : ℤ) - u0.val) : ℤ) : ZMod q) := by
  simp [shortDiff, zsmul_eq_mul, Int.cast_ofNat]
  ring

private theorem shiftAverage_eq_finset_expect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℕ) (F : (ι → Fin 2 → ℕ) → ℝ) :
    shiftAverage ι L F = 𝔼 u ∈ Fintype.piFinset
      (fun _ : ι => Fintype.piFinset fun _ : Fin 2 => Finset.range L), F u := by
  classical
  let S : Finset (ι → Fin 2 → ℕ) := Fintype.piFinset
    (fun _ : ι => Fintype.piFinset fun _ : Fin 2 => Finset.range L)
  have hinner : (Fintype.piFinset (fun _ : Fin 2 => Finset.range L)).card = L ^ 2 := by
    simpa using Fintype.card_piFinset_const (Finset.range L) 2
  have hcard : S.card = L ^ (2 * Fintype.card ι) := by
    calc
      S.card = ∏ i : ι, (Fintype.piFinset
          (fun _ : Fin 2 => Finset.range L)).card := by
            simp [S, Fintype.card_piFinset]
      _ = (L ^ 2) ^ Fintype.card ι := by simp [hinner]
      _ = L ^ (2 * Fintype.card ι) := by rw [pow_mul]
  unfold shiftAverage
  rw [Finset.expect_eq_sum_div_card]
  change ((L : ℝ) ^ (2 * Fintype.card ι))⁻¹ * ∑ u ∈ S, F u =
    (∑ u ∈ S, F u) / (S.card : ℝ)
  rw [hcard]
  simp [Nat.cast_pow, div_eq_mul_inv]
  ring

def harmonicLawIntSupport (X W : ℕ) : Finset ℤ :=
  (Finset.Ico (X : ℤ) (X ^ 2 : ℤ)).filter fun z => Nat.Coprime z.toNat W

def harmonicLawNatSupport (X W : ℕ) : Finset ℕ :=
  (Finset.Ico X (X ^ 2)).filter fun n => Nat.Coprime n W

private theorem harmonicLawIntSupport_eq_map (X W : ℕ) (hX : 0 < X) :
    harmonicLawIntSupport X W = (harmonicLawNatSupport X W).map Nat.castEmbedding := by
  classical
  ext z
  simp only [harmonicLawIntSupport, harmonicLawNatSupport, Finset.mem_filter,
    Finset.mem_Ico, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hcop⟩
    have hzpos : 0 ≤ z := le_trans (by exact_mod_cast hX.le) hlo
    have hzNat : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hzpos
    refine ⟨z.toNat, ?_, hzNat⟩
    refine ⟨⟨?_, ?_⟩, hcop⟩
    · have h' : (X : ℤ) ≤ (z.toNat : ℤ) := by simpa [hzNat] using hlo
      exact_mod_cast h'
    · have h' : (z.toNat : ℤ) < (X ^ 2 : ℤ) := by simpa [hzNat] using hhi
      exact_mod_cast h'
  · rintro ⟨n, hn, hcast⟩
    change (n : ℤ) = z at hcast
    subst z
    rcases hn with ⟨⟨hnlo, hnhigh⟩, hcop⟩
    exact ⟨⟨by exact_mod_cast hnlo, by exact_mod_cast hnhigh⟩, hcop⟩

theorem harmonicLaw_zero_of_not_mem (X W : ℕ) (z : ℤ)
    (hz : z ∉ harmonicLawIntSupport X W) : harmonicLaw X W z = 0 := by
  by_cases hz0 : 0 ≤ z
  · have hzNat : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0
    have hcond : ¬ (X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W) := by
      intro hc
      apply hz
      have hlo : (X : ℤ) ≤ z := by
        have h' : (X : ℤ) ≤ (z.toNat : ℤ) := by exact_mod_cast hc.1
        simpa [hzNat] using h'
      have hhi : z < (X ^ 2 : ℤ) := by
        have h' : (z.toNat : ℤ) < (X ^ 2 : ℤ) := by exact_mod_cast hc.2.1
        simpa [hzNat] using h'
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlo, hhi⟩, hc.2.2⟩
    have hcond' : ¬ (0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W) := by
      rintro ⟨_, hc⟩
      exact hcond ⟨hc.1, hc.2.1, hc.2.2⟩
    simp [harmonicLaw, hcond']
  · simp [harmonicLaw, hz0]

theorem harmonicLaw_expect_finset (X W : ℕ) (f : ℤ → ℝ) :
    (∑' z : ℤ, harmonicLaw X W z * f z) =
      ∑ z ∈ harmonicLawIntSupport X W, harmonicLaw X W z * f z := by
  classical
  apply tsum_eq_sum
  intro z hz
  rw [harmonicLaw_zero_of_not_mem X W z hz]
  simp

theorem harmonicLaw_tsum_eq_one (X W : ℕ) (hX : 0 < X)
    (hH : 0 < harmonicNormalizer X W) :
    (∑' z : ℤ, harmonicLaw X W z) = 1 := by
  classical
  let S := harmonicLawIntSupport X W
  have hzero (z : ℤ) (hz : z ∉ S) : harmonicLaw X W z = 0 := by
    by_cases hz0 : 0 ≤ z
    · have hzNat : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0
      have hcond : ¬ (X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W) := by
        intro hc
        apply hz
        have hlo : (X : ℤ) ≤ z := by
          have h' : (X : ℤ) ≤ (z.toNat : ℤ) := by exact_mod_cast hc.1
          simpa [hzNat] using h'
        have hhi : z < (X ^ 2 : ℤ) := by
          have h' : (z.toNat : ℤ) < (X ^ 2 : ℤ) := by exact_mod_cast hc.2.1
          simpa [hzNat] using h'
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlo, hhi⟩, hc.2.2⟩
      have hcond' : ¬ (0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W) := by
        rintro ⟨_, hc⟩
        exact hcond ⟨hc.1, hc.2.1, hc.2.2⟩
      simp [harmonicLaw, hcond']
    · simp [harmonicLaw, hz0]
  rw [tsum_eq_sum (s := S) hzero]
  rw [show S = (harmonicLawNatSupport X W).map Nat.castEmbedding by
      exact harmonicLawIntSupport_eq_map X W hX]
  rw [Finset.sum_map]
  have hsum :
      (∑ n ∈ harmonicLawNatSupport X W,
          harmonicLaw X W (n : ℤ)) = 1 := by
    calc
      _ = (∑ n ∈ harmonicLawNatSupport X W,
          1 / ((n : ℝ) * harmonicNormalizer X W)) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hnpos : (0 : ℝ) < (n : ℝ) := by
              have hnX : X ≤ n := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1
              exact_mod_cast hX.trans_le hnX
            have hnrange := Finset.mem_filter.mp hn
            have hbounds := Finset.mem_Ico.mp hnrange.1
            have hpoint :
                harmonicLaw X W (n : ℤ) =
                  1 / ((n : ℝ) * harmonicNormalizer X W) := by
              simp [harmonicLaw, hbounds.1, hbounds.2, hnrange.2]
            exact hpoint
      _ = (∑ n ∈ harmonicLawNatSupport X W, 1 / (n : ℝ)) /
          harmonicNormalizer X W := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro n hn
            field_simp [ne_of_gt hH, ne_of_gt (by
              have hnX : X ≤ n := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1
              exact_mod_cast hX.trans_le hnX)]
      _ = 1 := by
            rw [show (∑ n ∈ harmonicLawNatSupport X W, 1 / (n : ℝ)) =
                harmonicNormalizer X W by
                  simp [harmonicLawNatSupport, harmonicNormalizer, Finset.sum_filter,
                    Finset.Ico, Nat.coprime_comm]]
            exact div_self (ne_of_gt hH)
  exact hsum

theorem harmonicLaw_expect_indicator (X W : ℕ) (hX : 0 < X)
    (hH : 0 < harmonicNormalizer X W) (E : ℤ → Prop) :
    (∑' z : ℤ, harmonicLaw X W z * if E z then 1 else 0) =
      (∑ n ∈ harmonicLawNatSupport X W,
        if E (n : ℤ) then 1 / (n : ℝ) else 0) / harmonicNormalizer X W := by
  classical
  let S := harmonicLawIntSupport X W
  have hzero (z : ℤ) (hz : z ∉ S) :
      harmonicLaw X W z * (if E z then 1 else 0) = 0 := by
    rw [harmonicLaw_zero_of_not_mem]
    · simp
    · simpa [S] using hz
  rw [tsum_eq_sum (s := S) hzero]
  rw [show S = (harmonicLawNatSupport X W).map Nat.castEmbedding by
      exact harmonicLawIntSupport_eq_map X W hX]
  rw [Finset.sum_map]
  calc
    _ = ∑ n ∈ harmonicLawNatSupport X W,
        (1 / ((n : ℝ) * harmonicNormalizer X W)) *
          (if E (n : ℤ) then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hnrange := Finset.mem_filter.mp hn
            have hbounds := Finset.mem_Ico.mp hnrange.1
            have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hX.trans_le hbounds.1
            have hpoint : harmonicLaw X W (n : ℤ) =
                1 / ((n : ℝ) * harmonicNormalizer X W) := by
              simp [harmonicLaw, hbounds.1, hbounds.2, hnrange.2]
            change harmonicLaw X W (n : ℤ) * (if E (n : ℤ) then 1 else 0) = _
            rw [hpoint]
    _ = (∑ n ∈ harmonicLawNatSupport X W,
          if E (n : ℤ) then 1 / (n : ℝ) else 0) / harmonicNormalizer X W := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro n hn
            by_cases he : E (n : ℤ)
            · simp [he]
              field_simp [ne_of_gt hH, ne_of_gt (by
                have hnX : X ≤ n := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1
                exact_mod_cast hX.trans_le hnX)]
            · simp [he]

theorem boundaryStrip_imp_rawBoundary {H width R n : ℕ}
    (hH : 0 < H) (hR : width < R) (hn : R ≤ n) :
    InBoundaryStrip H width (n : ℤ) → (n - R) / H < (n + R) / H := by
  intro hs
  have hdecomp : n % H + H * (n / H) = n := Nat.mod_add_div n H
  have hrem : n % H < H := Nat.mod_lt _ hH
  rcases hs with hl | hu
  · have hlow : (n - R) / H < n / H := by
      have hlNat : n % H ≤ width := by exact_mod_cast hl
      have hrltR : n % H < R := lt_of_le_of_lt hlNat hR
      have hsubEq : n - n % H = (n - R) + (R - n % H) := by omega
      have hsub : n - R < n - n % H := by
        rw [hsubEq]
        exact Nat.lt_add_of_pos_right (Nat.sub_pos_of_lt hrltR)
      have hdivEq : n - n % H = H * (n / H) := by
        conv_lhs => rw [← hdecomp]
        simp [Nat.add_sub_cancel_left]
      have hnum : n - R < H * (n / H) := hsub.trans_eq hdivEq
      exact (Nat.div_lt_iff_lt_mul hH).2 (by simpa [Nat.mul_comm] using hnum)
    have hupp : n / H ≤ (n + R) / H := Nat.div_le_div_right (Nat.le_add_right _ _)
    exact lt_of_lt_of_le hlow hupp
  · have hupp : n / H < (n + R) / H := by
      have hRplus : H * (n / H + 1) ≤ n + R := by
        rw [Nat.mul_add]
        omega
      have hRplus' : (n / H + 1) * H ≤ n + R := by nlinarith [hRplus]
      have hdiv : n / H + 1 ≤ (n + R) / H := (Nat.le_div_iff_mul_le hH).2 hRplus'
      exact lt_of_lt_of_le (Nat.lt_succ_self _) hdiv
    have hlow : (n - R) / H ≤ n / H := Nat.div_le_div_right (Nat.sub_le _ _)
    exact lt_of_le_of_lt hlow hupp

theorem harmonicBoundary_mass_le_raw {X W H width R : ℕ}
    (hX : 0 < X) (hW : 0 < W) (hcut : 4 * W ≤ X) (hH : 0 < H)
    (hR : width < R) (hRle : R ≤ X) :
    (∑' z : ℤ, harmonicLaw X W z * boundaryIndicator H width z) ≤
      OAI.DyadicHarmonicBoundary.badMass X (X ^ 2) W 1 H R /
        harmonicNormalizer X W := by
  classical
  change (∑' z : ℤ, harmonicLaw X W z *
    (if InBoundaryStrip H width z then 1 else 0)) ≤ _
  rw [harmonicLaw_expect_indicator X W hX
    (by
      have hpos := OAI.RawHarmonicProbability.mass_pos X W hW hcut
      simpa [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
        Finset.sum_filter, one_div, Nat.coprime_comm] using hpos)
    (fun z => InBoundaryStrip H width z)]
  have hnormPos : 0 < harmonicNormalizer X W := by
    have hpos := OAI.RawHarmonicProbability.mass_pos X W hW hcut
    simpa [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
      Finset.sum_filter, one_div, Nat.coprime_comm] using hpos
  have hsum :
      (∑ n ∈ harmonicLawNatSupport X W,
        if InBoundaryStrip H width (n : ℤ) then 1 / (n : ℝ) else 0) ≤
      OAI.DyadicHarmonicBoundary.badMass X (X ^ 2) W 1 H R := by
    unfold OAI.DyadicHarmonicBoundary.badMass
    let raw : ℕ → ℝ := fun n =>
      if W.Coprime n ∧ (n - R) / H ≠ (n + R) / H then 1 / (n : ℝ) else 0
    have hpoint : ∀ n ∈ harmonicLawNatSupport X W,
        (if InBoundaryStrip H width (n : ℤ) then 1 / (n : ℝ) else 0) ≤ raw n := by
      intro n hn
      have hnX : X ≤ n := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1
      have hcop := (Finset.mem_filter.mp hn).2
      by_cases hs : InBoundaryStrip H width (n : ℤ)
      · have hraw := boundaryStrip_imp_rawBoundary hH hR (le_trans hRle hnX) hs
        have hne : (n - R) / H ≠ (n + R) / H := ne_of_lt hraw
        have hcop' : W.Coprime n := Nat.coprime_comm.mp hcop
        simp only [hs]
        change 1 / (n : ℝ) ≤ raw n
        dsimp [raw]
        split_ifs with h
        · rfl
        · exact False.elim (h ⟨hcop', hne⟩)
      · simp [raw, hs]
        split_ifs <;> positivity
    have hfirst :
        (∑ n ∈ harmonicLawNatSupport X W,
          if InBoundaryStrip H width (n : ℤ) then 1 / (n : ℝ) else 0) ≤
          ∑ n ∈ harmonicLawNatSupport X W, raw n := by
      apply Finset.sum_le_sum
      intro n hn
      exact hpoint n hn
    have hsecond :
        (∑ n ∈ harmonicLawNatSupport X W, raw n) ≤
          ∑ n ∈ Finset.Ico X (X ^ 2), raw n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact (Finset.mem_filter.mp hn).1
      · intro n hn hnot
        dsimp [raw]
        split_ifs <;> positivity
    simpa [raw] using hfirst.trans hsecond
  exact div_le_div_of_nonneg_right hsum (le_of_lt hnormPos)

private theorem shortDiff_cube_moment_bound {q a J0 L d : ℕ} [NeZero q]
    (ha : 0 < a) (hadiv : a ∣ q) (hL : 0 < L) (hLn : L ≤ q / a)
    (hn : q / a ≤ 2 * J0 * L) (f : ZMod q → ℝ) :
    |𝔼 x : ZMod q, shiftAverage (Fin d) L (fun u =>
      ∏ ω : Finset (Fin d), f (x +
        (((a : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0) : ℤ) : ZMod q)))| ≤
      Real.sqrt ((2 * J0 : ℝ) ^ d) *
        Real.sqrt ((SubgroupBox.boxMoment
          (List.replicate (d + 1) (AddSubgroup.zmultiples (a : ZMod q)))
          (fun x => (f x : ℂ))).re) := by
  classical
  let Q : AddSubgroup (ZMod q) := AddSubgroup.zmultiples (a : ZMod q)
  let cube (x : ZMod q) (h : Fin d → Q) : ℝ :=
    cubeSubsetReal d f x (fun j => (h j : ZMod q))
  let avg (h : Fin d → Q) : ℝ := 𝔼 x : ZMod q, cube x h
  let F (h : Fin d → Q) : ℝ := avg h ^ 2
  let endpoint (u : Fin d → Fin 2 → ℕ) : ℝ :=
    𝔼 x : ZMod q, ∏ ω : Finset (Fin d), f (x +
      (((a : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0) : ℤ) : ZMod q))
  have hLmem (u : Fin d → Fin 2 → ℕ)
      (hu : u ∈ Fintype.piFinset (fun _ : Fin d =>
        Fintype.piFinset fun _ : Fin 2 => Finset.range L)) :
      ∀ j e, u j e < L := by
    simpa only [Fintype.mem_piFinset, Finset.mem_range] using hu
  have hdiff (u : Fin d → Fin 2 → ℕ)
      (hu : u ∈ Fintype.piFinset (fun _ : Fin d =>
        Fintype.piFinset fun _ : Fin 2 => Finset.range L)) (ω : Finset (Fin d)) :
      (∑ j ∈ ω, shortDiff (q := q) (a := a) (L := L)
          ⟨u j 0 % L, Nat.mod_lt _ hL⟩ ⟨u j 1 % L, Nat.mod_lt _ hL⟩ : ZMod q) =
        (((a : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0) : ℤ) : ZMod q) := by
    calc
      _ = ∑ j ∈ ω, (((a : ℤ) *
          ((u j 1 : ℤ) - u j 0) : ℤ) : ZMod q) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [shortDiff_cast_eq]
            simp [Nat.mod_eq_of_lt (hLmem u hu j 1), Nat.mod_eq_of_lt (hLmem u hu j 0)]
      _ = (((a : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0) : ℤ) : ZMod q) := by
            rw [Finset.mul_sum]
            simp only [Int.cast_sum, Int.cast_mul]
  have hsq :
      (shiftAverage (Fin d) L endpoint) ^ 2 ≤
        shiftAverage (Fin d) L (fun u => endpoint u ^ 2) := by
    exact shiftAverage_sq_le L hL endpoint
  have hterm (u : Fin d → Fin 2 → ℕ)
      (hu : u ∈ Fintype.piFinset (fun _ : Fin d =>
        Fintype.piFinset fun _ : Fin 2 => Finset.range L)) :
      endpoint u = avg (fun j => shortDiff (q := q) (a := a) (L := L)
        ⟨u j 0 % L, Nat.mod_lt _ hL⟩ ⟨u j 1 % L, Nat.mod_lt _ hL⟩) := by
    unfold endpoint avg cube cubeSubsetReal
    apply Finset.expect_congr rfl
    intro x hx
    apply Finset.prod_congr rfl
    intro ω hω
    rw [hdiff u hu ω]
  have hnonneg (h : Fin d → Q) : 0 ≤ F h := sq_nonneg _
  have hdist := shiftAverage_shortDiff_le (q := q) (a := a) (J0 := J0) (L := L)
    (d := d) ha hadiv hL hLn hn F hnonneg
  have hmeanSq :
      shiftAverage (Fin d) L (fun u => endpoint u ^ 2) ≤
        (2 * J0 : ℝ) ^ d *
          𝔼 h : Fin d → Q, F h := by
    rw [show shiftAverage (Fin d) L (fun u => endpoint u ^ 2) =
      shiftAverage (Fin d) L (fun u => F
        (fun j => shortDiff (q := q) (a := a) (L := L)
          ⟨u j 0 % L, Nat.mod_lt _ hL⟩ ⟨u j 1 % L, Nat.mod_lt _ hL⟩)) by
            unfold shiftAverage
            congr 1
            apply Finset.sum_congr rfl
            intro u hu
            change endpoint u ^ 2 = F (fun j => shortDiff (q := q) (a := a) (L := L)
              ⟨u j 0 % L, Nat.mod_lt _ hL⟩ ⟨u j 1 % L, Nat.mod_lt _ hL⟩)
            simp [F, hterm u hu]]
    exact hdist
  have hcubeMean := cubeMeanSquare_le_boxMoment Q d f
  have hFmean :
      (𝔼 h : Fin d → Q, F h) ≤
        (SubgroupBox.boxMoment (List.replicate (d + 1) Q) (fun x => (f x : ℂ))).re := by
    simpa [F, avg, cube] using hcubeMean
  have hbound :
      (shiftAverage (Fin d) L endpoint) ^ 2 ≤
        (2 * J0 : ℝ) ^ d *
          (SubgroupBox.boxMoment (List.replicate (d + 1) Q)
      (fun x => (f x : ℂ))).re := by
    exact hsq.trans (hmeanSq.trans (mul_le_mul_of_nonneg_left hFmean (by positivity)))
  have hmoment_nonneg : 0 ≤
      (SubgroupBox.boxMoment (List.replicate (d + 1) Q)
        (fun x => (f x : ℂ))).re := by
    apply SubgroupBox.boxMoment_re_nonneg
    intro hnil
    have hlen := congrArg List.length hnil
    simp at hlen
  have hfactor_nonneg : 0 ≤ (2 * J0 : ℝ) ^ d := by positivity
  have habs :
      |shiftAverage (Fin d) L endpoint| ≤ Real.sqrt ((2 * J0 : ℝ) ^ d) *
        Real.sqrt ((SubgroupBox.boxMoment (List.replicate (d + 1) Q)
          (fun x => (f x : ℂ))).re) := by
    calc
      _ = Real.sqrt ((shiftAverage (Fin d) L endpoint) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((2 * J0 : ℝ) ^ d *
          (SubgroupBox.boxMoment (List.replicate (d + 1) Q)
            (fun x => (f x : ℂ))).re) := Real.sqrt_le_sqrt hbound
      _ = _ := Real.sqrt_mul hfactor_nonneg _
  have houter :
      (𝔼 x : ZMod q, shiftAverage (Fin d) L (fun u =>
        ∏ ω : Finset (Fin d), f (x +
          (((a : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0) : ℤ) : ZMod q)))) =
      shiftAverage (Fin d) L endpoint := by
    simp_rw [shiftAverage_eq_finset_expect]
    exact Finset.expect_comm (Finset.univ : Finset (ZMod q))
      (Fintype.piFinset (fun _ : Fin d =>
        Fintype.piFinset fun _ : Fin 2 => Finset.range L))
      (fun x u => ∏ ω : Finset (Fin d), f (x +
        (((a : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0) : ℤ) : ZMod q)))
  rw [houter]
  simpa [endpoint] using habs

private theorem succ_le_two_pow (d : ℕ) : d + 1 ≤ 2 ^ d := by
  induction d with
  | zero => norm_num
  | succ d ih =>
      calc
        d + 1 + 1 ≤ 2 * (d + 1) := by omega
        _ ≤ 2 * 2 ^ d := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (d + 1) := by rw [pow_succ]; ring

private theorem weighted_uniform_expect {Cl G : Type*} [Fintype Cl] [Fintype G] [Nonempty G]
    (α : SubgroupBox.ProbWeights Cl) (g : Cl → G → ℝ) :
    (∑ c, α.w c * 𝔼 x : G, g c x) =
      ∑ z : Cl × G,
        (productProbWeights α (uniformProbWeights G)).w z * g z.1 z.2 := by
  classical
  calc
    _ = ∑ c, α.w c * ((∑ x : G, g c x) / Fintype.card G) := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [Fintype.expect_eq_sum_div_card]
    _ = ∑ c, ∑ x : G, (α.w c * (Fintype.card G : ℝ)⁻¹) * g c x := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = ∑ z : Cl × G,
          (productProbWeights α (uniformProbWeights G)).w z * g z.1 z.2 := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro x hx
          simp [productProbWeights, uniformProbWeights, mul_assoc, mul_left_comm, mul_comm]

/-- Endpoint differences from short intervals control the subgroup cube norm. -/
theorem periodizedShiftCube_le_boxNorm {q a J0 L d : ℕ} [NeZero q]
    (ha : 0 < a) (hadiv : a ∣ q) (hL : 0 < L) (hLn : L ≤ q / a)
    (hn : q / a ≤ 2 * J0 * L) {Cl : Type} [Fintype Cl]
    (α : SubgroupBox.ProbWeights Cl) (f : Cl → ZMod q → ℝ)
    (hf : ∀ c x, |f c x| ≤ 1) :
    |∑ c, α.w c * 𝔼 x : ZMod q, shiftAverage (Fin d) L (fun u =>
      ∏ ω : Finset (Fin d), f c (x +
        (((a : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0) : ℤ) : ZMod q)))| ≤
      Real.sqrt ((2 * J0 : ℝ) ^ d) *
        (∑ c, α.w c * (SubgroupBox.boxMoment
          (List.replicate (2 ^ d) (AddSubgroup.zmultiples (a : ZMod q)))
          (fun x => (f c x : ℂ))).re) ^ ((1 : ℝ) / 2 ^ (2 ^ d)) := by
  classical
  let Q : AddSubgroup (ZMod q) := AddSubgroup.zmultiples (a : ZMod q)
  let small (c : Cl) : ℝ :=
    (SubgroupBox.boxMoment (List.replicate (d + 1) Q)
      (fun x => (f c x : ℂ))).re
  let large (c : Cl) : ℝ :=
    (SubgroupBox.boxMoment (List.replicate (2 ^ d) Q)
      (fun x => (f c x : ℂ))).re
  let U (c : Cl) (x : ZMod q) : ℝ :=
    OAI.Erdos3.gowersNorm (d + 1) (fun y : Q => (f c (x + y) : ℂ))
  let V (c : Cl) (x : ZMod q) : ℝ :=
    OAI.Erdos3.gowersNorm (2 ^ d) (fun y : Q => (f c (x + y) : ℂ))
  let r : ℕ := 2 ^ (d + 1)
  let p : ℕ := 2 ^ (2 ^ d)
  let R : ℝ := (p : ℝ) / r
  let β : SubgroupBox.ProbWeights (Cl × ZMod q) :=
    productProbWeights α (uniformProbWeights (ZMod q))
  let z (cx : Cl × ZMod q) : ℝ := V cx.1 cx.2 ^ r
  let A : ℝ := ∑ c, α.w c * small c
  let B : ℝ := ∑ c, α.w c * large c
  have hdegree : d + 1 ≤ 2 ^ d := succ_le_two_pow d
  have hrle : r ≤ p := by
    dsimp [r, p]
    exact Nat.pow_le_pow_right (by omega) hdegree
  have hrge : 2 ≤ r := by
    dsimp [r]
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hrpos : 0 < (r : ℝ) := by positivity
  have hRge : 1 ≤ R := by
    dsimp [R]
    apply (le_div_iff₀ hrpos).2
    norm_num
    exact_mod_cast hrle
  have hRmul : (r : ℝ) * R = (p : ℝ) := by
    dsimp [R]
    field_simp
  have hsmallEq (c : Cl) : small c = 𝔼 x : ZMod q, U c x ^ r := by
    simpa [small, U, Q, r] using
      (boxMoment_re_eq_average_gowersNorm_pow Q (d + 1) (by omega)
        (fun x => f c x))
  have hlargeEq (c : Cl) : large c = 𝔼 x : ZMod q, V c x ^ p := by
    simpa [large, V, Q, p] using
      (boxMoment_re_eq_average_gowersNorm_pow Q (2 ^ d) (by positivity)
        (fun x => f c x))
  have hU_nonneg (c : Cl) (x : ZMod q) : 0 ≤ U c x := by
    exact OAI.Erdos3.gowersNorm_nonneg d _
  have hV_nonneg (c : Cl) (x : ZMod q) : 0 ≤ V c x := by
    simpa [V, Nat.sub_add_cancel (by positivity : 0 < 2 ^ d)] using
      (OAI.Erdos3.gowersNorm_nonneg (2 ^ d - 1)
        (fun y : Q => (f c (x + y) : ℂ)))
  have hV_le_one (c : Cl) (x : ZMod q) : V c x ≤ 1 := by
    have h := OAI.Erdos3.gowersNorm_le_one (2 ^ d - 1)
      (fun y : Q => (f c (x + y) : ℂ)) (by
        intro y
        simpa [Complex.norm_real, Real.norm_eq_abs] using hf c (x + y))
    simpa [V, Nat.sub_add_cancel (by positivity : 0 < 2 ^ d)] using h
  have hU_le_V (c : Cl) (x : ZMod q) : U c x ≤ V c x := by
    simpa [U, V, Nat.sub_add_cancel (by positivity : 0 < 2 ^ d)] using
      (gowersNorm_mono (n := d) (m := 2 ^ d - 1) (by omega)
        (fun y : Q => (f c (x + y) : ℂ)))
  have hsmall_nonneg (c : Cl) : 0 ≤ small c := by
    refine SubgroupBox.boxMoment_re_nonneg
      (Qs := List.replicate (d + 1) Q) ?_ (fun x => (f c x : ℂ))
    intro he
    have hh := congrArg List.length he
    simp at hh
  have hlarge_nonneg (c : Cl) : 0 ≤ large c := by
    refine SubgroupBox.boxMoment_re_nonneg
      (Qs := List.replicate (2 ^ d) Q) ?_ (fun x => (f c x : ℂ))
    intro he
    have hh := congrArg List.length he
    simp at hh
  have hsmall_le_one (c : Cl) : small c ≤ 1 := by
    rw [hsmallEq c]
    calc
      _ ≤ 𝔼 x : ZMod q, (1 : ℝ) := by
            apply Finset.expect_le_expect
            intro x hx
            simpa using pow_le_pow_left₀ (hU_nonneg c x)
              (hU_le_V c x |>.trans (hV_le_one c x)) r
      _ = 1 := by simp
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun c hc => mul_nonneg (α.nonneg c) (hsmall_nonneg c)
  have hA_le_one : A ≤ 1 := by
    dsimp [A]
    calc
      _ ≤ ∑ c, α.w c * 1 := by
            apply Finset.sum_le_sum
            intro c hc
            exact mul_le_mul_of_nonneg_left (hsmall_le_one c) (α.nonneg c)
      _ = 1 := by simpa using α.total
  have hsmall_le_Vmoment (c : Cl) :
      small c ≤ 𝔼 x : ZMod q, V c x ^ r := by
    rw [hsmallEq c]
    apply Finset.expect_le_expect
    intro x hx
    exact pow_le_pow_left₀ (hU_nonneg c x) (hU_le_V c x) r
  have hA_le_z : A ≤ ∑ cx : Cl × ZMod q, β.w cx * z cx := by
    dsimp [A, β, z]
    rw [← weighted_uniform_expect α (fun c x => V c x ^ r)]
    apply Finset.sum_le_sum
    intro c hc
    exact mul_le_mul_of_nonneg_left (hsmall_le_Vmoment c) (α.nonneg c)
  have hB_eq : B = ∑ cx : Cl × ZMod q, β.w cx * V cx.1 cx.2 ^ p := by
    dsimp [B, β]
    rw [← weighted_uniform_expect α (fun c x => V c x ^ p)]
    apply Finset.sum_congr rfl
    intro c hc
    rw [← hlargeEq c]
  have hz_nonneg (cx : Cl × ZMod q) : 0 ≤ z cx := by
    exact pow_nonneg (hV_nonneg cx.1 cx.2) r
  have hzpow (cx : Cl × ZMod q) : z cx ^ R = V cx.1 cx.2 ^ p := by
    calc
      z cx ^ R = (V cx.1 cx.2 ^ (r : ℝ)) ^ R := by
        dsimp [z]
        rw [← Real.rpow_natCast]
      _ = V cx.1 cx.2 ^ ((r : ℝ) * R) := by
        exact (Real.rpow_mul (hV_nonneg cx.1 cx.2) _ _).symm
      _ = V cx.1 cx.2 ^ (p : ℝ) := by rw [hRmul]
      _ = V cx.1 cx.2 ^ p := Real.rpow_natCast _ _
  have hJensen :
      (∑ cx : Cl × ZMod q, β.w cx * z cx) ^ R ≤ B := by
    have hj := probWeights_rpow_mean_le β z hz_nonneg R hRge
    calc
      _ ≤ ∑ cx : Cl × ZMod q, β.w cx * z cx ^ R := hj
      _ = B := by rw [show (∑ cx : Cl × ZMod q, β.w cx * z cx ^ R) =
          ∑ cx : Cl × ZMod q, β.w cx * V cx.1 cx.2 ^ p by
            apply Finset.sum_congr rfl
            intro cx hc
            rw [hzpow], hB_eq]
  have hrootA : Real.sqrt A ≤ A ^ ((1 : ℝ) / r) := by
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_ge' hA_nonneg hA_le_one (by positivity)
    have hrR : (1 : ℝ) / r ≤ (1 : ℝ) / 2 := by
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        (by exact_mod_cast hrge)
    exact hrR
  have hAtoZ : A ^ ((1 : ℝ) / r) ≤
      (∑ cx : Cl × ZMod q, β.w cx * z cx) ^ ((1 : ℝ) / r) := by
    apply Real.rpow_le_rpow hA_nonneg hA_le_z
    positivity
  have hZ_nonneg : 0 ≤ ∑ cx : Cl × ZMod q, β.w cx * z cx :=
    Finset.sum_nonneg fun cx hcx => mul_nonneg (β.nonneg cx) (hz_nonneg cx)
  have hZrootEq :
      (∑ cx : Cl × ZMod q, β.w cx * z cx) ^ ((1 : ℝ) / r) =
        ((∑ cx : Cl × ZMod q, β.w cx * z cx) ^ R) ^ ((1 : ℝ) / p) := by
    rw [← Real.rpow_mul hZ_nonneg]
    have hexp : R * ((1 : ℝ) / p) = (1 : ℝ) / r := by
      dsimp [R]
      field_simp
      exact div_self (by positivity)
    rw [hexp]
  have hZtoB :
      ((∑ cx : Cl × ZMod q, β.w cx * z cx) ^ R) ^ ((1 : ℝ) / p) ≤
        B ^ ((1 : ℝ) / p) := by
    apply Real.rpow_le_rpow (by positivity) hJensen
    positivity
  have hMroot : Real.sqrt A ≤ B ^ ((1 : ℝ) / p) :=
    hrootA.trans (hAtoZ.trans (hZrootEq ▸ hZtoB))
  let H : Cl → ℝ := fun c => Real.sqrt (small c)
  have hH_nonneg : 0 ≤ ∑ c, α.w c * H c :=
    Finset.sum_nonneg fun c hc => mul_nonneg (α.nonneg c) (Real.sqrt_nonneg _)
  have hH_sq : (∑ c, α.w c * H c) ^ 2 ≤ A := by
    have hcs := probWeights_square_mean_le α H
    calc
      (∑ c, α.w c * H c) ^ 2 ≤ ∑ c, α.w c * H c ^ 2 := hcs
      _ = A := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [H, A, Real.sq_sqrt (hsmall_nonneg c)]
  have hH_le : (∑ c, α.w c * H c) ≤ Real.sqrt A := by
    exact (Real.le_sqrt hH_nonneg hA_nonneg).2 hH_sq
  let E (c : Cl) : ℝ :=
    𝔼 x : ZMod q, shiftAverage (Fin d) L (fun u =>
      ∏ ω : Finset (Fin d), f c (x +
        (((a : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0) : ℤ) : ZMod q)))
  have htriangle :
      |∑ c, α.w c * E c| ≤ Real.sqrt ((2 * J0 : ℝ) ^ d) *
        (∑ c, α.w c * H c) := by
    calc
      _ ≤ ∑ c, |α.w c * E c| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ c, α.w c * |E c| := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [abs_mul, abs_of_nonneg (α.nonneg c)]
      _ ≤ ∑ c, α.w c * (Real.sqrt ((2 * J0 : ℝ) ^ d) * H c) := by
            apply Finset.sum_le_sum
            intro c hc
            exact mul_le_mul_of_nonneg_left
              (shortDiff_cube_moment_bound ha hadiv hL hLn hn (f c)) (α.nonneg c)
      _ = Real.sqrt ((2 * J0 : ℝ) ^ d) * (∑ c, α.w c * H c) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c hc
            ring
  have hconst_nonneg : 0 ≤ Real.sqrt ((2 * J0 : ℝ) ^ d) := Real.sqrt_nonneg _
  have hfinal : |∑ c, α.w c * E c| ≤
      Real.sqrt ((2 * J0 : ℝ) ^ d) * B ^ ((1 : ℝ) / p) :=
    htriangle.trans (mul_le_mul_of_nonneg_left (hH_le.trans hMroot) hconst_nonneg)
  simpa [B, large, Q, p, E] using hfinal

/-- Reciprocal weights on an interval of relative width `H/X` are close in total variation
to uniform weights. -/
theorem reciprocalWeights_uniformTV {ι : Type*} [Fintype ι] [Nonempty ι]
    (base width : ℝ) (hbase : 0 < base) (hwidth : 0 ≤ width)
    (y : ι → ℝ) (hy : ∀ i, base ≤ y i ∧ y i ≤ base + width) :
    ∑ i, |(y i)⁻¹ / (∑ j, (y j)⁻¹) - (Fintype.card ι : ℝ)⁻¹| ≤ width / base := by
  classical
  let lo : ℝ := (base + width)⁻¹
  let hi : ℝ := base⁻¹
  let S : ℝ := ∑ i, (y i)⁻¹
  have hbw : 0 < base + width := by linarith
  have hlo : 0 < lo := by dsimp [lo]; positivity
  have hhi : 0 < hi := by dsimp [hi]; positivity
  have hypos (i : ι) : 0 < y i := lt_of_lt_of_le hbase (hy i).1
  have hwi_lo (i : ι) : lo ≤ (y i)⁻¹ := by
    dsimp [lo]
    simpa [one_div] using one_div_le_one_div_of_le (hypos i) (hy i).2
  have hwi_hi (i : ι) : (y i)⁻¹ ≤ hi := by
    dsimp [hi]
    simpa [one_div] using one_div_le_one_div_of_le hbase (hy i).1
  have hSpos : 0 < S := by
    dsimp [S]
    exact Finset.sum_pos (fun i _ => inv_pos.mpr (hypos i)) Finset.univ_nonempty
  have hcardpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hSlo : (Fintype.card ι : ℝ) * lo ≤ S := by
    dsimp [S]
    calc
      _ = ∑ i, lo := by simp [Finset.sum_const, Fintype.card_ne_zero]
      _ ≤ ∑ i, (y i)⁻¹ := Finset.sum_le_sum fun i _ => hwi_lo i
  have hmean_lo : lo ≤ S / Fintype.card ι := by
    rw [le_div_iff₀ hcardpos]
    simpa [mul_comm] using hSlo
  have hmean_hi : S / Fintype.card ι ≤ hi := by
    rw [div_le_iff₀ hcardpos]
    calc
      S = ∑ i, (y i)⁻¹ := rfl
      _ ≤ ∑ i, hi := Finset.sum_le_sum fun i _ => hwi_hi i
      _ = hi * (Fintype.card ι : ℝ) := by simpa [Finset.sum_const, Fintype.card_ne_zero, mul_comm]
  have hgap : 0 ≤ hi - lo := sub_nonneg.mpr (by
    dsimp [hi, lo]
    simpa [one_div] using
      one_div_le_one_div_of_le hbase (le_add_of_nonneg_right hwidth))
  have hterm (i : ι) :
      |(y i)⁻¹ / S - (Fintype.card ι : ℝ)⁻¹| ≤ (hi - lo) / S := by
    have hdiff : |(y i)⁻¹ - S / Fintype.card ι| ≤ hi - lo := by
      rw [abs_le]
      constructor <;> linarith [hwi_lo i, hwi_hi i, hmean_lo, hmean_hi]
    have hrewrite : (y i)⁻¹ / S - (Fintype.card ι : ℝ)⁻¹ =
        ((y i)⁻¹ - S / Fintype.card ι) / S := by
      field_simp [ne_of_gt hSpos, ne_of_gt hcardpos]
    rw [hrewrite, abs_div, abs_of_pos hSpos]
    exact div_le_div_of_nonneg_right hdiff hSpos.le
  have hcardRatio : (Fintype.card ι : ℝ) / S ≤ lo⁻¹ := by
    apply (div_le_iff₀ hSpos).2
    have := (le_div_iff₀ hlo).2 hSlo
    simpa [div_eq_mul_inv, mul_comm] using this
  calc
    _ ≤ ∑ _i : ι, ((hi - lo) / S) := Finset.sum_le_sum fun i _ => hterm i
    _ = (Fintype.card ι : ℝ) * ((hi - lo) / S) := by simp
    _ = (hi - lo) * ((Fintype.card ι : ℝ) / S) := by ring
    _ ≤ (hi - lo) * lo⁻¹ := mul_le_mul_of_nonneg_left hcardRatio hgap
    _ = width / base := by
      dsimp [hi, lo]
      field_simp [ne_of_gt hbase, ne_of_gt hbw]
      ring

theorem reciprocalWeights_uniform_expect_diff {ι : Type*} [Fintype ι] [Nonempty ι]
    (base width : ℝ) (hbase : 0 < base) (hwidth : 0 ≤ width)
    (y g : ι → ℝ) (hy : ∀ i, base ≤ y i ∧ y i ≤ base + width)
    (hg : ∀ i, |g i| ≤ 1) :
    |(∑ i, (y i)⁻¹ * g i) / (∑ i, (y i)⁻¹) -
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, g i| ≤ width / base := by
  classical
  have hTV := reciprocalWeights_uniformTV base width hbase hwidth y hy
  let S : ℝ := ∑ i, (y i)⁻¹
  have hSpos : 0 < S := by
    dsimp [S]
    exact Finset.sum_pos (fun i _ => inv_pos.mpr (lt_of_lt_of_le hbase (hy i).1))
      Finset.univ_nonempty
  have hsum1 :
      (∑ i, (y i)⁻¹ * g i) / S =
        ∑ i, ((y i)⁻¹ / S) * g i := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsum2 : (Fintype.card ι : ℝ)⁻¹ * ∑ i, g i =
      ∑ i, (Fintype.card ι : ℝ)⁻¹ * g i := by rw [Finset.mul_sum]
  rw [hsum1, hsum2, ← Finset.sum_sub_distrib]
  have hsum3 :
      (∑ i, ((y i)⁻¹ / S * g i - (Fintype.card ι : ℝ)⁻¹ * g i)) =
        ∑ i, ((y i)⁻¹ / S - (Fintype.card ι : ℝ)⁻¹) * g i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum3]
  calc
    |∑ i, ((y i)⁻¹ / S - (Fintype.card ι : ℝ)⁻¹) * g i| ≤
        ∑ i, |((y i)⁻¹ / S - (Fintype.card ι : ℝ)⁻¹) * g i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |(y i)⁻¹ / S - (Fintype.card ι : ℝ)⁻¹| := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul]
          simpa using mul_le_mul_of_nonneg_left (hg i) (abs_nonneg _)
    _ ≤ width / base := hTV

/-- A finite shift average preserves a uniform bound on its integrand. -/
theorem shiftAverage_abs_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℕ) (F : (ι → Fin 2 → ℕ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ u, |F u| ≤ C) : |shiftAverage ι L F| ≤ C := by
  classical
  rw [shiftAverage_eq_finset_expect]
  let S := Fintype.piFinset (fun _ : ι => Fintype.piFinset fun _ : Fin 2 => Finset.range L)
  by_cases hS : S.Nonempty
  · apply abs_le.mpr
    constructor
    · calc
        -C = 𝔼 u ∈ S, (-C : ℝ) := (Finset.expect_const hS _).symm
        _ ≤ 𝔼 u ∈ S, F u := Finset.expect_le_expect fun u hu => (abs_le.mp (hF u)).1
    · calc
        𝔼 u ∈ S, F u ≤ 𝔼 u ∈ S, (C : ℝ) :=
          Finset.expect_le_expect fun u hu => (abs_le.mp (hF u)).2
        _ = C := Finset.expect_const hS _
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [hEmpty, S, Finset.expect]
    exact hC

/-- A bounded integrand stays bounded under the good-slot conditional law. -/
theorem goodSlotAverage_abs_le {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (S : FromArithmetic.MasterScales K As sl Dm)
    (l : Fin K) (N : ℕ) {q : ℕ} (good : (Fin q → ℕ) → Prop) (F : (Fin q → ℕ) → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀ p, good p → |F p| ≤ C) :
    |goodSlotAverage S l N good F| ≤ C := by
  classical
  let lo : Fin q → ℕ := fun _ => (S.primeStage.pool N l).lower
  let hi : Fin q → ℕ := fun _ => (S.primeStage.pool N l).upper
  let mass : (Fin q → ℕ) → ℝ := independentPrimePoolMass lo hi
  let gp : ℝ := gapSlotProbability S l N good
  let num : ℝ := ∑' p : Fin q → ℕ, mass p * if good p then F p else 0
  have hnumSumm : Summable (fun p : Fin q → ℕ => mass p * if good p then F p else 0) := by
    apply summable_of_ne_finset_zero (s := poolTupleSupport lo hi)
    intro p hp
    change independentPrimePoolMass lo hi p * (if good p then F p else 0) = 0
    rw [poolMass_zero_of_not_support lo hi p hp]
    simp
  have hposSumm : Summable (fun p : Fin q → ℕ => mass p * if good p then 1 else 0) :=
    poolProbability_summable lo hi good
  have hconstantSumm : Summable (fun p : Fin q → ℕ => mass p * if good p then C else 0) := by
    apply summable_of_ne_finset_zero (s := poolTupleSupport lo hi)
    intro p hp
    change independentPrimePoolMass lo hi p * (if good p then C else 0) = 0
    rw [poolMass_zero_of_not_support lo hi p hp]
    simp
  have hgp : gp = ∑' p : Fin q → ℕ, mass p * if good p then 1 else 0 := by
    change independentPrimePoolProbability lo hi good = _
    rfl
  have hmassNonneg (p : Fin q → ℕ) : 0 ≤ mass p := by
    dsimp [mass, independentPrimePoolMass]
    apply Finset.prod_nonneg
    intro i hii
    have hpm : 0 ≤ primePoolMass (lo i) (hi i) := by
      unfold primePoolMass
      positivity
    unfold primePoolLaw
    split_ifs <;> positivity
  have hupper : num ≤ C * gp := by
    calc
      num ≤ ∑' p : Fin q → ℕ, mass p * if good p then C else 0 := by
        apply Summable.tsum_le_tsum
          (f := fun p : Fin q → ℕ => mass p * if good p then F p else 0)
          (g := fun p => mass p * if good p then C else 0)
        · intro p
          by_cases hp : good p
          · simpa [hp] using mul_le_mul_of_nonneg_left (abs_le.mp (hF p hp)).2
              (hmassNonneg p)
          · simp [hp]
        · exact hnumSumm
        · exact hconstantSumm
      _ = C * gp := by
        rw [hgp, ← tsum_mul_left]
        apply tsum_congr
        intro p
        by_cases hp : good p <;> simp [hp] <;> ring
  have hnegSumm : Summable (fun p : Fin q → ℕ => mass p * if good p then -C else 0) := by
    apply summable_of_ne_finset_zero (s := poolTupleSupport lo hi)
    intro p hp
    change independentPrimePoolMass lo hi p * (if good p then -C else 0) = 0
    rw [poolMass_zero_of_not_support lo hi p hp]
    simp
  have hnegEq : -C * gp =
      ∑' p : Fin q → ℕ, mass p * if good p then -C else 0 := by
    rw [hgp, ← tsum_mul_left]
    apply tsum_congr
    intro p
    by_cases hp : good p <;> simp [hp] <;> ring
  have hlower : -C * gp ≤ num := by
    calc
      -C * gp = ∑' p : Fin q → ℕ, mass p * if good p then -C else 0 := hnegEq
      _ ≤ num := Summable.tsum_le_tsum
        (fun p => by
          by_cases hp : good p
          · simpa [hp] using mul_le_mul_of_nonneg_left (abs_le.mp (hF p hp)).1
              (hmassNonneg p)
          · simp [hp])
        hnegSumm hnumSumm
  have hlower' : -(C * gp) ≤ num := by simpa [neg_mul] using hlower
  have habsNum : |num| ≤ C * gp := abs_le.mpr ⟨hlower', hupper⟩
  by_cases hgp0 : gp = 0
  · unfold goodSlotAverage
    rw [show gapSlotProbability S l N good = gp by rfl, hgp0]
    simp
    exact hC
  · have hgpPos : 0 < gp := by
      have hgpNonneg : 0 ≤ gp := by
        rw [hgp]
        exact tsum_nonneg fun p => mul_nonneg (hmassNonneg p) (by split_ifs <;> norm_num)
      exact lt_of_le_of_ne hgpNonneg (Ne.symm hgp0)
    change |gp⁻¹ * num| ≤ C
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hgpPos.le)]
    calc
      gp⁻¹ * |num| ≤ gp⁻¹ * (C * gp) :=
        mul_le_mul_of_nonneg_left habsNum (inv_nonneg.mpr hgpPos.le)
      _ = C := by field_simp [ne_of_gt hgpPos]

theorem goodSlotAverage_sub {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (S : FromArithmetic.MasterScales K As sl Dm)
    (l : Fin K) (N : ℕ) {q : ℕ} (good : (Fin q → ℕ) → Prop)
    (F G : (Fin q → ℕ) → ℝ) :
    goodSlotAverage S l N good (fun p => F p - G p) =
      goodSlotAverage S l N good F - goodSlotAverage S l N good G := by
  classical
  let lo : Fin q → ℕ := fun _ => (S.primeStage.pool N l).lower
  let hi : Fin q → ℕ := fun _ => (S.primeStage.pool N l).upper
  let mass : (Fin q → ℕ) → ℝ := independentPrimePoolMass lo hi
  let gp : ℝ := gapSlotProbability S l N good
  have hF : Summable (fun p : Fin q → ℕ => mass p * if good p then F p else 0) := by
    apply summable_of_ne_finset_zero (s := poolTupleSupport lo hi)
    intro p hp
    change independentPrimePoolMass lo hi p * (if good p then F p else 0) = 0
    rw [poolMass_zero_of_not_support lo hi p hp]
    simp
  have hG : Summable (fun p : Fin q → ℕ => mass p * if good p then G p else 0) := by
    apply summable_of_ne_finset_zero (s := poolTupleSupport lo hi)
    intro p hp
    change independentPrimePoolMass lo hi p * (if good p then G p else 0) = 0
    rw [poolMass_zero_of_not_support lo hi p hp]
    simp
  have hnum :
      (∑' p : Fin q → ℕ, mass p * (if good p then F p - G p else 0)) =
        (∑' p : Fin q → ℕ, mass p * if good p then F p else 0) -
          (∑' p : Fin q → ℕ, mass p * if good p then G p else 0) := by
    calc
      _ = ∑' p : Fin q → ℕ,
          ((mass p * if good p then F p else 0) -
            (mass p * if good p then G p else 0)) := by
              apply tsum_congr
              intro p
              by_cases hp : good p <;> simp [hp] <;> ring
      _ = _ := hF.tsum_sub hG
  change gp⁻¹ * (∑' p : Fin q → ℕ,
      mass p * (if good p then F p - G p else 0)) =
    gp⁻¹ * (∑' p : Fin q → ℕ, mass p * if good p then F p else 0) -
      gp⁻¹ * (∑' p : Fin q → ℕ, mass p * if good p then G p else 0)
  rw [hnum]
  ring

theorem shiftAverage_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℕ) (F G : (ι → Fin 2 → ℕ) → ℝ)
    (h : ∀ u, F u = G u) : shiftAverage ι L F = shiftAverage ι L G := by
  unfold shiftAverage
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  exact h u

theorem shiftAverage_congr_of_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℕ) (F G : (ι → Fin 2 → ℕ) → ℝ)
    (h : ∀ u, (∀ i b, u i b < L) → F u = G u) :
    shiftAverage ι L F = shiftAverage ι L G := by
  unfold shiftAverage
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  apply h u
  intro i b
  have hi := Fintype.mem_piFinset.mp hu i
  have hb := Fintype.mem_piFinset.mp hi b
  exact Finset.mem_range.mp hb

theorem abs_int_natCast_sub_le {a b L : ℕ} (ha : a < L) (hb : b < L) :
    |(a : ℤ) - b| ≤ (L : ℤ) := by
  have hnat : Int.natAbs ((a : ℤ) - b) < L :=
    Int.natAbs_coe_sub_coe_lt_of_lt ha hb
  have hcast : (Int.natAbs ((a : ℤ) - b) : ℤ) < (L : ℤ) :=
    Int.ofNat_lt.mpr hnat
  rw [Int.natCast_natAbs] at hcast
  exact le_of_lt hcast

end Prediction

end HindmanSumsProducts

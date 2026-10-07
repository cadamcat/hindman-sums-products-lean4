import Mathlib

/-!
# Concatenation of box norms along subgroups

Replaces the Tao–Ziegler concatenation theorem used in the paper at `05_prediction.tex` 450–470 and
580–595, by the subgroup form of Kravitz–Kuca–Leng (arXiv:2407.08636, Lemma 6.1) and a two-call
recursion. Blueprint and proofs: `research/blueprint/CONCATENATION.md` (§3 mathematics, §5 ledger).
-/

open scoped BigOperators
open Finset

namespace HindmanSumsProducts.SubgroupBox

section defs
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- `Δ_h f`; definitionally `OAI.Erdos3.multiplicativeDerivative`. -/
def mderiv (f : G → ℂ) (h : G) : G → ℂ := fun x ↦ f x * star (f (x + h))

/-- iterated derivative along a list; agrees with `OAI.Erdos3.cubeProduct f hs`. -/
def cubeProd (f : G → ℂ) : List G → G → ℂ
  | [] => f
  | h :: hs => cubeProd (mderiv f h) hs

/-- average over a subgroup, `P_Q f (x) = 𝔼_{h ∈ Q} f (x + h)` -/
noncomputable def avgOn (Q : AddSubgroup G) [Fintype Q] (f : G → ℂ) (x : G) : ℂ :=
  𝔼 h : Q, f (x + h)

open Classical in
/-- `‖f‖^{2^t}` along the list of subgroup directions (Fejér form, head outermost). -/
noncomputable def boxMoment : List (AddSubgroup G) → (G → ℂ) → ℂ
  | [], f => 𝔼 x, f x
  | Q :: Qs, f => 𝔼 h : Q, boxMoment Qs (mderiv f h)

open Classical in
/-- iterated uniform average over `h₁ ∈ Q₁, …, h_t ∈ Q_t`. -/
noncomputable def cubeAvg {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] :
    List (AddSubgroup G) → (List G → M) → M
  | [], F => F []
  | Q :: Qs, F => 𝔼 h : Q, cubeAvg Qs (fun hs ↦ F ((h : G) :: hs))

def crossDeriv (f g : G → ℂ) (h : G) : G → ℂ := fun x ↦ f x * star (g (x + h))

open Classical in
/-- box inner product of a `{0,1}^t`-indexed family (mixed moment), head outermost. -/
noncomputable def boxInner : (Qs : List (AddSubgroup G)) → ((Fin Qs.length → Bool) → G → ℂ) → ℂ
  | [], F => 𝔼 x, F default x
  | _ :: Qs, F => 𝔼 h : _, boxInner Qs
      (fun ω ↦ crossDeriv (F (Fin.cons false ω)) (F (Fin.cons true ω)) (h : G))

structure ProbWeights (ι : Type*) [Fintype ι] where
  w : ι → ℝ
  nonneg : ∀ i, 0 ≤ w i
  total : ∑ i, w i = 1

open Classical in
noncomputable def badPairMass {ι : Type*} [Fintype ι] (π : ProbWeights ι)
    (Q : ι → AddSubgroup G) : ℝ :=
  ∑ i, ∑ j, if Q i ⊔ Q j = ⊤ then 0 else π.w i * π.w j
end defs

section statements
variable {G : Type*} [AddCommGroup G] [Fintype G]

private theorem expect_add_translate (t : G) (f : G → ℂ) :
    (𝔼 x, f (x + t)) = 𝔼 x, f x := by
  classical
  exact Fintype.expect_equiv (Equiv.addRight t) (fun x : G => f (x + t)) f (by intro x; rfl)

private theorem avgOn_add_mem (Q : AddSubgroup G) [Fintype Q] (f : G → ℂ) (x : G)
    (a : Q) : avgOn Q f (x + a) = avgOn Q f x := by
  classical
  unfold avgOn
  calc
    (𝔼 h : Q, f ((x + (a : G)) + h)) =
        𝔼 h : Q, f (x + ((a : G) + h)) := by congr 1; funext h; simp [add_assoc]
    _ = 𝔼 h : Q, f (x + h) :=
      Fintype.expect_equiv (Equiv.addLeft a) _ _ (by intro h; rfl)

-- C1
theorem expect_add_sup (A B : AddSubgroup G) [Fintype A] [Fintype B]
    [Fintype (A ⊔ B : AddSubgroup G)] (φ : G → ℂ) :
    (𝔼 a : A, 𝔼 b : B, φ ((a : G) + b)) = 𝔼 c : (A ⊔ B : AddSubgroup G), φ c := by
  classical
  let C := (A ⊔ B : AddSubgroup G)
  let f : A × B →+ C :=
    { toFun := fun p => ⟨(p.1 : G) + p.2,
        AddSubgroup.mem_sup.mpr ⟨p.1, p.1.property, p.2, p.2.property, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp [add_assoc, add_comm, add_left_comm] }
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.mp c.property
    refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
    exact Subtype.ext hab
  have hfilter (c : C) :
      (Finset.univ.filter (fun p : A × B => f p = c)).card = Fintype.card f.ker := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using
      Fintype.card_congr (f.fiberEquivKerOfSurjective hf c)
  have hsum : (∑ p : A × B, φ (f p : G)) =
      (Fintype.card f.ker : ℂ) * ∑ c : C, φ (c : G) := by
    calc
      (∑ p : A × B, φ (f p : G)) =
          ∑ c : C, ∑ p ∈ Finset.univ with f p = c, φ (f p : G) := by
        symm
        exact Finset.sum_fiberwise_of_maps_to
          (s := Finset.univ) (t := Finset.univ) (g := fun p : A × B => f p)
          (fun _ _ => Finset.mem_univ _) (fun p => φ (f p : G))
      _ = ∑ c : C, (Fintype.card f.ker : ℂ) * φ (c : G) := by
        apply Finset.sum_congr rfl
        intro c hc
        calc
          (∑ p ∈ Finset.univ with f p = c, φ (f p : G)) =
              ∑ p ∈ Finset.univ with f p = c, φ (c : G) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hp' : f p = c := by simpa using hp
            exact congrArg φ (congrArg Subtype.val hp')
          _ = (Fintype.card f.ker : ℂ) * φ (c : G) := by
            rw [← hfilter c]
            simp [Finset.sum_const]
      _ = (Fintype.card f.ker : ℂ) * ∑ c : C, φ (c : G) := by
        rw [Finset.mul_sum]
  have hcardSource : Fintype.card (A × B) = Fintype.card C * Fintype.card f.ker := by
    calc
      Fintype.card (A × B) =
          ∑ c : C, (Finset.univ.filter (fun p : A × B => f p = c)).card := by
        simpa using (Finset.card_eq_sum_card_fiberwise
          (s := (Finset.univ : Finset (A × B))) (t := (Finset.univ : Finset C))
          (f := fun p : A × B => f p) (fun _ _ => Finset.mem_univ _))
      _ = Fintype.card C * Fintype.card f.ker := by
        simp [hfilter, Finset.sum_const]
  have hsum' : (∑ p : A × B, φ ((p.1 : G) + p.2)) =
      (Fintype.card f.ker : ℂ) * ∑ c : C, φ (c : G) := by
    simpa [f] using hsum
  calc
    (𝔼 a : A, 𝔼 b : B, φ ((a : G) + b)) =
        𝔼 p : A × B, φ ((p.1 : G) + p.2) := by
      simpa using (Finset.expect_product' (Finset.univ : Finset A)
        (Finset.univ : Finset B) (fun a b => φ ((a : G) + b))).symm
    _ = 𝔼 c : C, φ (c : G) := by
      rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, hsum']
      rw [show (Fintype.card (A × B) : ℂ) =
          (Fintype.card C : ℂ) * Fintype.card f.ker by exact_mod_cast hcardSource]
      have hC : (Fintype.card C : ℂ) ≠ 0 := by
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card C ≠ 0)
      have hK : (Fintype.card f.ker : ℂ) ≠ 0 := by
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card f.ker ≠ 0)
      field_simp

theorem expect_mul_star_avgOn (Q : AddSubgroup G) [Fintype Q] (f g : G → ℂ) :
    (𝔼 x, f x * star (avgOn Q g x)) = 𝔼 x, avgOn Q f x * star (avgOn Q g x) := by
  classical
  let F : G → ℂ := fun x => f x * star (avgOn Q g x)
  have hshift (a : Q) :
      (𝔼 x, F x) = 𝔼 x, f (x + a) * star (avgOn Q g (x + a)) := by
    change (𝔼 x, F x) = 𝔼 x, F (x + (a : G))
    exact (expect_add_translate (a : G) F).symm
  calc
    (𝔼 x, F x) = 𝔼 a : Q, 𝔼 x, F x := by simp
    _ = 𝔼 a : Q, 𝔼 x, f (x + a) * star (avgOn Q g (x + a)) := by
      apply Finset.expect_congr rfl
      intro a ha
      exact hshift a
    _ = 𝔼 x, 𝔼 a : Q, f (x + a) * star (avgOn Q g (x + a)) :=
      Finset.expect_comm (Finset.univ : Finset Q) (Finset.univ : Finset G) _
    _ = 𝔼 x, 𝔼 a : Q, f (x + a) * star (avgOn Q g x) := by
      apply Finset.expect_congr rfl
      intro x hx
      apply Finset.expect_congr rfl
      intro a ha
      rw [avgOn_add_mem]
    _ = 𝔼 x, avgOn Q f x * star (avgOn Q g x) := by
      apply Finset.expect_congr rfl
      intro x hx
      simpa only [avgOn] using
        (Finset.expect_mul Finset.univ (fun a : Q => f (x + a))
          (star (avgOn Q g x))).symm

open Classical in
theorem boxMoment_singleton (Q : AddSubgroup G) (f : G → ℂ) :
    boxMoment [Q] f = 𝔼 x, (((‖avgOn Q f x‖ ^ 2 : ℝ)) : ℂ) := by
  classical
  calc
    boxMoment [Q] f = 𝔼 x, f x * star (avgOn Q f x) := by
      simp only [boxMoment, mderiv]
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro x hx
      simp only [avgOn]
      calc
        (𝔼 h : Q, f x * star (f (x + h))) =
            f x * 𝔼 h : Q, star (f (x + h)) := by
          exact (Finset.mul_expect Finset.univ (fun h : Q => star (f (x + h))) (f x)).symm
        _ = f x * star (𝔼 h : Q, f (x + h)) := by
          have hs := map_expect (starRingEnd ℂ) (fun h : Q => f (x + h)) Finset.univ
          exact congrArg (fun z : ℂ => f x * z) hs.symm
    _ = 𝔼 x, avgOn Q f x * star (avgOn Q f x) := expect_mul_star_avgOn Q f f
    _ = 𝔼 x, (((‖avgOn Q f x‖ ^ 2 : ℝ)) : ℂ) := by
      apply Finset.expect_congr rfl
      intro x hx
      simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

-- C3
theorem boxMoment_append (Qs Rs : List (AddSubgroup G)) (f : G → ℂ) :
    boxMoment (Qs ++ Rs) f = cubeAvg Qs (fun hs ↦ boxMoment Rs (cubeProd f hs)) := by
  induction Qs generalizing f with
  | nil => rfl
  | cons Q Qs ih =>
    simp only [List.cons_append, boxMoment, cubeAvg]
    apply Finset.expect_congr rfl
    intro h hh
    simpa only [cubeProd] using ih (mderiv f h)

private theorem mderiv_comm (f : G → ℂ) (h k : G) :
    mderiv (mderiv f h) k = mderiv (mderiv f k) h := by
  funext x
  simp only [mderiv, star_mul, star_star]
  have hadd : x + k + h = x + h + k := by abel
  rw [hadd]
  ring

private theorem boxMoment_swap (Q R : AddSubgroup G) (Qs : List (AddSubgroup G))
    (f : G → ℂ) : boxMoment (Q :: R :: Qs) f = boxMoment (R :: Q :: Qs) f := by
  classical
  calc
    boxMoment (Q :: R :: Qs) f =
        𝔼 h : Q, 𝔼 k : R, boxMoment Qs (mderiv (mderiv f h) k) := by
      simp only [boxMoment]
    _ = 𝔼 k : R, 𝔼 h : Q, boxMoment Qs (mderiv (mderiv f h) k) :=
      Finset.expect_comm (Finset.univ : Finset Q) (Finset.univ : Finset R) _
    _ = 𝔼 k : R, 𝔼 h : Q, boxMoment Qs (mderiv (mderiv f k) h) := by
      apply Finset.expect_congr rfl
      intro k hk
      apply Finset.expect_congr rfl
      intro h hh
      exact congrArg (boxMoment Qs) (mderiv_comm f h k)
    _ = boxMoment (R :: Q :: Qs) f := by simp only [boxMoment]

theorem boxMoment_perm {Qs Rs : List (AddSubgroup G)} (h : Qs.Perm Rs) (f : G → ℂ) :
    boxMoment Qs f = boxMoment Rs f := by
  classical
  induction h using List.Perm.recOnSwap' generalizing f with
  | nil => rfl
  | cons _ _ ih =>
    simp only [boxMoment]
    apply Finset.expect_congr rfl
    intro q hq
    exact ih (mderiv f q)
  | swap' Q R htail ih =>
    calc
      boxMoment _ f = boxMoment _ f := boxMoment_swap R Q _ f
      _ = _ := by
        simp only [boxMoment]
        apply Finset.expect_congr rfl
        intro q hq
        apply Finset.expect_congr rfl
        intro r hr
        exact ih (mderiv (mderiv f q) r)
  | trans _ _ ih₁ ih₂ => exact (ih₁ f).trans (ih₂ f)

theorem boxMoment_im {Qs : List (AddSubgroup G)} (hQs : Qs ≠ []) (f : G → ℂ) :
    (boxMoment Qs f).im = 0 := by
  classical
  induction Qs generalizing f with
  | nil => simp at hQs
  | cons Q Rs ih =>
    cases Rs with
    | nil =>
      rw [boxMoment_singleton]
      rw [Complex.im_expect]
      apply Finset.expect_eq_zero
      intro x hx
      exact Complex.ofReal_im _
    | cons R Rs =>
      conv_lhs => rw [boxMoment.eq_def]
      rw [Complex.im_expect]
      apply Finset.expect_eq_zero
      intro h hh
      exact ih (by simp) (mderiv f h)

theorem boxMoment_re_nonneg {Qs : List (AddSubgroup G)} (hQs : Qs ≠ []) (f : G → ℂ) :
    0 ≤ (boxMoment Qs f).re := by
  classical
  induction Qs generalizing f with
  | nil => simp at hQs
  | cons Q Rs ih =>
    cases Rs with
    | nil =>
      rw [boxMoment_singleton, Complex.re_expect]
      change 0 ≤ (𝔼 x, (‖avgOn Q f x‖ ^ 2 : ℝ))
      apply Finset.expect_nonneg
      intro x hx
      exact sq_nonneg _
    | cons R Rs =>
      conv_rhs => rw [boxMoment.eq_def]
      rw [Complex.re_expect]
      apply Finset.expect_nonneg
      intro h hh
      exact ih (by simp) (mderiv f h)

private theorem expect_re_le_one (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    (𝔼 x, f x).re ≤ 1 := by
  classical
  rw [Complex.re_expect]
  apply Finset.expect_le Finset.univ_nonempty
  intro x hx
  exact (Complex.re_le_norm (f x)).trans (hf x)

theorem boxMoment_re_le_one (Qs : List (AddSubgroup G)) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    (boxMoment Qs f).re ≤ 1 := by
  classical
  induction Qs generalizing f with
  | nil => exact expect_re_le_one f hf
  | cons Q Qs ih =>
    simp only [boxMoment, Complex.re_expect]
    apply Finset.expect_le Finset.univ_nonempty
    intro h hh
    apply ih
    intro x
    calc
      ‖mderiv f h x‖ = ‖f x‖ * ‖f (x + h)‖ := by simp [mderiv]
      _ ≤ 1 := by
        have hfx := hf x
        have hfy := hf (x + h)
        have hnx := norm_nonneg (f x)
        have hny := norm_nonneg (f (x + h))
        nlinarith

private theorem expect_cross_avgOn (Q : AddSubgroup G) [Fintype Q] (f g : G → ℂ) :
    (𝔼 h : Q, 𝔼 x, crossDeriv f g h x) =
      𝔼 x, avgOn Q f x * star (avgOn Q g x) := by
  classical
  change (𝔼 h : Q, 𝔼 x, f x * star (g (x + h))) = _
  rw [Finset.expect_comm]
  calc
    (𝔼 x, 𝔼 h : Q, f x * star (g (x + h))) =
        𝔼 x, f x * star (avgOn Q g x) := by
      apply Finset.expect_congr rfl
      intro x hx
      calc
        (𝔼 h : Q, f x * star (g (x + h))) =
            f x * 𝔼 h : Q, star (g (x + h)) :=
          (Finset.mul_expect Finset.univ (fun h : Q => star (g (x + h))) (f x)).symm
        _ = f x * star (𝔼 h : Q, g (x + h)) := by
          congr 1
          exact (map_expect (starRingEnd ℂ) (fun h : Q => g (x + h)) Finset.univ).symm
        _ = f x * star (avgOn Q g x) := rfl
    _ = 𝔼 x, avgOn Q f x * star (avgOn Q g x) := expect_mul_star_avgOn Q f g

private theorem mderiv_crossDeriv (f g : G → ℂ) (h k : G) :
    mderiv (crossDeriv f g h) k = crossDeriv (mderiv f k) (mderiv g k) h := by
  funext x
  simp only [mderiv, crossDeriv, star_mul, star_star]
  have hadd : x + k + h = x + h + k := by abel
  rw [hadd]
  ring

private theorem norm_expect_mul_star_sq_le {Ω : Type*} [Fintype Ω]
    (f g : Ω → ℂ) :
    ‖𝔼 x, f x * star (g x)‖ ^ 2 ≤
      (𝔼 x, ‖f x‖ ^ 2) * (𝔼 x, ‖g x‖ ^ 2) := by
  have hnorm : ‖𝔼 x, f x * star (g x)‖ ≤ 𝔼 x, ‖f x‖ * ‖g x‖ := by
    simpa only [norm_mul, norm_star] using
      (RCLike.norm_expect_le (K := ℂ) (f := fun x => f x * star (g x)))
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (fun x => ‖f x‖) (fun x => ‖g x‖))

private theorem expect_sqrt_mul_le {ι : Type*} [Fintype ι] (A B : ι → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) :
    (𝔼 i, Real.sqrt (A i * B i)) ≤
      Real.sqrt ((𝔼 i, A i) * (𝔼 i, B i)) := by
  classical
  have hcs := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (A i)) (fun i => Real.sqrt (B i))
  have hprod : (𝔼 i, Real.sqrt (A i) * Real.sqrt (B i)) =
      𝔼 i, Real.sqrt (A i * B i) := by
    apply Finset.expect_congr rfl
    intro i hi
    rw [Real.sqrt_mul (hA i)]
  have hAsq : (𝔼 i, Real.sqrt (A i) ^ 2) = 𝔼 i, A i := by
    apply Finset.expect_congr rfl
    intro i hi
    rw [Real.sq_sqrt (hA i)]
  have hBsq : (𝔼 i, Real.sqrt (B i) ^ 2) = 𝔼 i, B i := by
    apply Finset.expect_congr rfl
    intro i hi
    rw [Real.sq_sqrt (hB i)]
  have hsq : (𝔼 i, Real.sqrt (A i * B i)) ^ 2 ≤
      (𝔼 i, A i) * (𝔼 i, B i) := by
    simpa only [hprod, hAsq, hBsq] using hcs
  apply (Real.le_sqrt (Finset.expect_nonneg (fun i hi => Real.sqrt_nonneg _))
    (mul_nonneg (Finset.expect_nonneg (fun i hi => hA i))
      (Finset.expect_nonneg (fun i hi => hB i)))).2
  exact hsq

open Classical in
private theorem boxMoment_cross_avg_le (Q : AddSubgroup G) (Qs : List (AddSubgroup G))
    (f g : G → ℂ) :
    (𝔼 h : Q, (boxMoment Qs (crossDeriv f g h)).re) ≤
      Real.sqrt ((boxMoment (Q :: Qs) f).re * (boxMoment (Q :: Qs) g).re) := by
  classical
  induction Qs generalizing f g with
  | nil =>
    have hEq : (𝔼 h : Q, boxMoment [] (crossDeriv f g h)) =
        𝔼 x, avgOn Q f x * star (avgOn Q g x) := by
      simpa only [boxMoment] using expect_cross_avgOn Q f g
    have hnorm := norm_expect_mul_star_sq_le
      (fun x => avgOn Q f x) (fun x => avgOn Q g x)
    have hA : (boxMoment [Q] f).re = 𝔼 x, ‖avgOn Q f x‖ ^ 2 := by
      rw [boxMoment_singleton, Complex.re_expect]
      apply Finset.expect_congr rfl
      intro x hx
      exact Complex.ofReal_re (‖avgOn Q f x‖ ^ 2)
    have hB : (boxMoment [Q] g).re = 𝔼 x, ‖avgOn Q g x‖ ^ 2 := by
      rw [boxMoment_singleton, Complex.re_expect]
      apply Finset.expect_congr rfl
      intro x hx
      exact Complex.ofReal_re (‖avgOn Q g x‖ ^ 2)
    have hA0 : 0 ≤ (boxMoment [Q] f).re := boxMoment_re_nonneg (by simp) f
    have hB0 : 0 ≤ (boxMoment [Q] g).re := boxMoment_re_nonneg (by simp) g
    have hbound : ‖𝔼 x, avgOn Q f x * star (avgOn Q g x)‖ ≤
        Real.sqrt ((boxMoment [Q] f).re * (boxMoment [Q] g).re) := by
      apply (Real.le_sqrt (norm_nonneg _) (mul_nonneg hA0 hB0)).2
      simpa only [hA, hB] using hnorm
    calc
      (𝔼 h : Q, (boxMoment [] (crossDeriv f g h)).re) =
          (𝔼 h : Q, boxMoment [] (crossDeriv f g h)).re := by
        symm
        rw [Complex.re_expect]
      _ = (𝔼 x, avgOn Q f x * star (avgOn Q g x)).re := congrArg Complex.re hEq
      _ ≤ ‖𝔼 x, avgOn Q f x * star (avgOn Q g x)‖ := Complex.re_le_norm _
      _ ≤ Real.sqrt ((boxMoment [Q] f).re * (boxMoment [Q] g).re) := hbound
  | cons R Rs ih =>
    have hEq : (𝔼 h : Q, (boxMoment (R :: Rs) (crossDeriv f g h)).re) =
        𝔼 r : R, (𝔼 h : Q,
          boxMoment Rs (crossDeriv (mderiv f r) (mderiv g r) h)).re := by
      simp only [boxMoment, Complex.re_expect]
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro r hr
      apply Finset.expect_congr rfl
      intro h hh
      rw [mderiv_crossDeriv]
    let A : R → ℝ := fun r => (boxMoment (Q :: Rs) (mderiv f r)).re
    let B : R → ℝ := fun r => (boxMoment (Q :: Rs) (mderiv g r)).re
    have hA0 : ∀ r, 0 ≤ A r := fun r => boxMoment_re_nonneg (by simp) _
    have hB0 : ∀ r, 0 ≤ B r := fun r => boxMoment_re_nonneg (by simp) _
    have hAavg : (𝔼 r : R, A r) = (boxMoment (Q :: R :: Rs) f).re := by
      calc
        _ = (boxMoment (R :: Q :: Rs) f).re := by
          rw [boxMoment, Complex.re_expect]
        _ = (boxMoment (Q :: R :: Rs) f).re := congrArg Complex.re (boxMoment_swap R Q Rs f)
    have hBavg : (𝔼 r : R, B r) = (boxMoment (Q :: R :: Rs) g).re := by
      calc
        _ = (boxMoment (R :: Q :: Rs) g).re := by
          rw [boxMoment, Complex.re_expect]
        _ = (boxMoment (Q :: R :: Rs) g).re := congrArg Complex.re (boxMoment_swap R Q Rs g)
    calc
      (𝔼 h : Q, (boxMoment (R :: Rs) (crossDeriv f g h)).re) =
          𝔼 r : R, (𝔼 h : Q,
            boxMoment Rs (crossDeriv (mderiv f r) (mderiv g r) h)).re := hEq
      _ ≤ 𝔼 r : R, Real.sqrt (A r * B r) := by
        apply Finset.expect_le_expect
        intro r hr
        calc
          (𝔼 h : Q, boxMoment Rs (crossDeriv (mderiv f r) (mderiv g r) h)).re =
              𝔼 h : Q, (boxMoment Rs (crossDeriv (mderiv f r) (mderiv g r) h)).re :=
            Complex.re_expect (Finset.univ : Finset Q)
              (fun h => boxMoment Rs (crossDeriv (mderiv f r) (mderiv g r) h))
          _ ≤ Real.sqrt (A r * B r) := ih (mderiv f r) (mderiv g r)
      _ ≤ Real.sqrt ((𝔼 r : R, A r) * (𝔼 r : R, B r)) :=
        expect_sqrt_mul_le A B hA0 hB0
      _ = Real.sqrt ((boxMoment (Q :: R :: Rs) f).re *
            (boxMoment (Q :: R :: Rs) g).re) := by rw [hAavg, hBavg]

private theorem prod_bool_tuple_succ {M : Type*} [CommMonoid M] {n : ℕ}
    (F : (Fin (n + 1) → Bool) → M) :
    (∏ ω, F ω) =
      (∏ ω : Fin n → Bool, F (Fin.cons false ω)) *
        (∏ ω : Fin n → Bool, F (Fin.cons true ω)) := by
  calc
    (∏ ω, F ω) = ∏ q : Bool × (Fin n → Bool), F (Fin.cons q.1 q.2) := by
      apply Fintype.prod_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).symm
      intro ω
      simp
    _ = _ := by rw [Fintype.prod_prod_type]; simp [mul_comm]

-- Adapted from OpenAI openai/math (Apache-2.0),
-- OAI/Combinatorics/Progressions/Estimates/BooleanCubeProduct.lean.
private def conjugationPower : ℕ → (ℂ →+* ℂ)
  | 0 => RingHom.id ℂ
  | n + 1 => (starRingEnd ℂ).comp (conjugationPower n)

private theorem conjugationPower_star (n : ℕ) (z : ℂ) :
    conjugationPower n (star z) = star (conjugationPower n z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change star (conjugationPower n (star z)) = star (star (conjugationPower n z))
    exact congrArg star ih

private def booleanWeight {n : ℕ} (ω : Fin n → Bool) : ℕ :=
  ∑ i, if ω i then 1 else 0

private def cubeShift {n : ℕ} (hs : Fin n → G) (ω : Fin n → Bool) : G :=
  ∑ i, if ω i then hs i else 0

@[simp] private theorem booleanWeight_cons_false {n : ℕ} (ω : Fin n → Bool) :
    booleanWeight (Fin.cons false ω) = booleanWeight ω := by
  unfold booleanWeight
  rw [Fin.sum_univ_succ]
  simp

@[simp] private theorem booleanWeight_cons_true {n : ℕ} (ω : Fin n → Bool) :
    booleanWeight (Fin.cons true ω) = booleanWeight ω + 1 := by
  unfold booleanWeight
  rw [Fin.sum_univ_succ]
  simp [Nat.add_comm]

@[simp] private theorem cubeShift_cons_false {n : ℕ} (h : G) (hs : Fin n → G)
    (ω : Fin n → Bool) :
    cubeShift (Fin.cons h hs) (Fin.cons false ω) = cubeShift hs ω := by
  simp [cubeShift, Fin.sum_univ_succ]

@[simp] private theorem cubeShift_cons_true {n : ℕ} (h : G) (hs : Fin n → G)
    (ω : Fin n → Bool) :
    cubeShift (Fin.cons h hs) (Fin.cons true ω) = h + cubeShift hs ω := by
  simp [cubeShift, Fin.sum_univ_succ]

private def mixedCubeProduct {n : ℕ} (F : (Fin n → Bool) → G → ℂ)
    (hs : Fin n → G) (x : G) : ℂ :=
  ∏ ω, conjugationPower (booleanWeight ω) (F ω (x + cubeShift hs ω))

private theorem mixedCubeProduct_cons {n : ℕ}
    (F : (Fin (n + 1) → Bool) → G → ℂ) (h : G) (hs : Fin n → G) (x : G) :
    mixedCubeProduct F (Fin.cons h hs) x =
      mixedCubeProduct (fun ω => F (Fin.cons false ω)) hs x *
        star (mixedCubeProduct (fun ω => F (Fin.cons true ω)) hs (x + h)) := by
  simp only [mixedCubeProduct]
  rw [prod_bool_tuple_succ]
  simp only [booleanWeight_cons_false, booleanWeight_cons_true,
    cubeShift_cons_false, cubeShift_cons_true, conjugationPower, RingHom.comp_apply,
    starRingEnd_apply, ← add_assoc]
  change _ = _ * (starRingEnd ℂ) _
  rw [map_prod]
  simp only [starRingEnd_apply]

private theorem mixedCubeProduct_crossDerivative {n : ℕ}
    (F H : (Fin n → Bool) → G → ℂ) (h : G) (hs : Fin n → G) (x : G) :
    mixedCubeProduct (fun ω => crossDeriv (F ω) (H ω) h) hs x =
      mixedCubeProduct F hs x * star (mixedCubeProduct H hs (x + h)) := by
  simp only [mixedCubeProduct, crossDeriv, map_mul, conjugationPower_star,
    Finset.prod_mul_distrib]
  change _ = _ * (starRingEnd ℂ) _
  rw [map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro ω hω
  congr 3
  abel

private def listToFin (hs : List G) : Fin hs.length → G := fun i => hs.get i

private def mixedCubeProductList (F : List Bool → G → ℂ) (hs : List G) (x : G) : ℂ :=
  mixedCubeProduct (fun ω => F (List.ofFn ω)) (listToFin hs) x

private theorem list_get_cons_fin (h : G) (hs : List G) :
    (fun i : Fin (hs.length + 1) => (h :: hs).get i) =
      Fin.cons h (fun i => hs.get i) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [listToFin]

private theorem listToFin_cons (h : G) (hs : List G) :
    listToFin (h :: hs) = Fin.cons h (listToFin hs) := list_get_cons_fin h hs

private theorem mixedCubeProductList_cons (F : List Bool → G → ℂ)
    (h : G) (hs : List G) (x : G) :
    mixedCubeProductList F (h :: hs) x =
    mixedCubeProductList (fun ω => F (false :: ω)) hs x *
        star (mixedCubeProductList (fun ω => F (true :: ω)) hs (x + h)) := by
  change mixedCubeProduct (fun ω => F (List.ofFn ω)) (listToFin (h :: hs)) x = _
  rw [listToFin_cons, mixedCubeProduct_cons]
  simp [mixedCubeProductList, List.ofFn_cons]

private theorem mixedCubeProductList_crossDerivative (F H : List Bool → G → ℂ)
    (h : G) (hs : List G) (x : G) :
    mixedCubeProductList
        (fun ω => crossDeriv (F ω) (H ω) h) hs x =
      mixedCubeProductList F hs x * star (mixedCubeProductList H hs (x + h)) := by
  unfold mixedCubeProductList
  exact mixedCubeProduct_crossDerivative
    (fun ω => F (List.ofFn ω)) (fun ω => H (List.ofFn ω)) h (listToFin hs) x

private theorem mixedCubeProductList_nil (F : List Bool → G → ℂ) (x : G) :
    mixedCubeProductList F [] x = F [] x := by
  simp [mixedCubeProductList, mixedCubeProduct, listToFin, booleanWeight,
    cubeShift, conjugationPower]

private theorem mixedCubeProductList_congr (F H : List Bool → G → ℂ)
    (hs : List G) (x : G) (h : ∀ ω y, F ω y = H ω y) :
    mixedCubeProductList F hs x = mixedCubeProductList H hs x := by
  unfold mixedCubeProductList mixedCubeProduct
  apply Finset.prod_congr rfl
  intro ω hω
  exact congrArg (conjugationPower (booleanWeight ω))
    (h (List.ofFn ω) (x + cubeShift (listToFin hs) ω))

private theorem mixedCubeProductList_congr_onFin (F H : List Bool → G → ℂ)
    (hs : List G) (x : G) (h : ∀ ω : Fin hs.length → Bool, ∀ y,
      F (List.ofFn ω) y = H (List.ofFn ω) y) :
    mixedCubeProductList F hs x = mixedCubeProductList H hs x := by
  unfold mixedCubeProductList mixedCubeProduct
  apply Finset.prod_congr rfl
  intro ω hω
  exact congrArg (conjugationPower (booleanWeight ω))
    (h ω (x + cubeShift (listToFin hs) ω))

private theorem mixedCubeProductList_append (F : List Bool → G → ℂ)
    (ks ls : List G) (x : G) :
    mixedCubeProductList F (ks ++ ls) x =
      mixedCubeProductList
        (fun α y => mixedCubeProductList (fun β => F (α ++ β)) ls y) ks x := by
  induction ks generalizing F x with
  | nil => simp [mixedCubeProductList_nil]
  | cons a ks ih =>
    let A : List Bool → G → ℂ :=
      fun α y => mixedCubeProductList (fun β => F (α ++ β)) ls y
    calc
      mixedCubeProductList F ((a :: ks) ++ ls) x =
          mixedCubeProductList F (a :: (ks ++ ls)) x := by simp
      _ = mixedCubeProductList (fun ω => F (false :: ω)) (ks ++ ls) x *
          star (mixedCubeProductList (fun ω => F (true :: ω)) (ks ++ ls) (x + a)) :=
        mixedCubeProductList_cons F a (ks ++ ls) x
      _ = mixedCubeProductList
            (fun α y => mixedCubeProductList (fun β => F (false :: (α ++ β))) ls y) ks x *
          star (mixedCubeProductList
            (fun α y => mixedCubeProductList (fun β => F (true :: (α ++ β))) ls y)
            ks (x + a)) := by
        rw [ih, ih]
      _ = mixedCubeProductList (fun α y => A (false :: α) y) ks x *
          star (mixedCubeProductList (fun α y => A (true :: α) y) ks (x + a)) := by
        rfl
      _ = mixedCubeProductList A (a :: ks) x :=
        (mixedCubeProductList_cons A a ks x).symm

private theorem expect_prod_boolean_pow_le {Ω : Type*} [Fintype Ω]
    (n : ℕ) (F : (Fin n → Bool) → Ω → ℝ) (hF : ∀ ω x, 0 ≤ F ω x) :
    (𝔼 x, ∏ ω, F ω x) ^ (2 ^ n) ≤ ∏ ω, 𝔼 x, F ω x ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let A (b : Bool) (x : Ω) := ∏ ω : Fin n → Bool, F (Fin.cons b ω) x
    have hprod (x : Ω) : (∏ ω, F ω x) = A false x * A true x :=
      prod_bool_tuple_succ _
    have hcs := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (A false) (A true)
    have hpart (b : Bool) : (𝔼 x, A b x ^ 2) ^ (2 ^ n) ≤
        ∏ ω : Fin n → Bool, 𝔼 x, F (Fin.cons b ω) x ^ (2 ^ (n + 1)) := by
      have h := ih (fun ω x => F (Fin.cons b ω) x ^ 2) (fun _ _ => sq_nonneg _)
      simpa only [A, ← Finset.prod_pow, ← pow_mul, ← pow_succ'] using h
    calc
      (𝔼 x, ∏ ω, F ω x) ^ (2 ^ (n + 1)) =
          ((𝔼 x, A false x * A true x) ^ 2) ^ (2 ^ n) := by
        simp_rw [hprod]
        rw [← pow_mul, pow_succ']
      _ ≤ ((𝔼 x, A false x ^ 2) * (𝔼 x, A true x ^ 2)) ^ (2 ^ n) :=
        pow_le_pow_left₀ (sq_nonneg _) hcs _
      _ = (𝔼 x, A false x ^ 2) ^ (2 ^ n) *
          (𝔼 x, A true x ^ 2) ^ (2 ^ n) := mul_pow _ _ _
      _ ≤ (∏ ω : Fin n → Bool, 𝔼 x, F (Fin.cons false ω) x ^ (2 ^ (n + 1))) *
          (∏ ω : Fin n → Bool, 𝔼 x, F (Fin.cons true ω) x ^ (2 ^ (n + 1))) := by
        apply mul_le_mul (hpart false) (hpart true)
        · exact pow_nonneg (Finset.expect_nonneg (fun _ _ => sq_nonneg _)) _
        · exact Finset.prod_nonneg (fun ω _ => Finset.expect_nonneg
            (fun x _ => pow_nonneg (hF _ x) _))
      _ = ∏ ω, 𝔼 x, F ω x ^ (2 ^ (n + 1)) :=
        (prod_bool_tuple_succ (fun ω => 𝔼 x, F ω x ^ (2 ^ (n + 1)))).symm

private noncomputable def boxNorm (Qs : List (AddSubgroup G)) (f : G → ℂ) : ℝ :=
  (boxMoment Qs f).re ^ (((2 ^ Qs.length : ℕ) : ℝ)⁻¹)

private theorem boxNorm_nonneg {Qs : List (AddSubgroup G)} (hQs : Qs ≠ []) (f : G → ℂ) :
    0 ≤ boxNorm Qs f := Real.rpow_nonneg (boxMoment_re_nonneg hQs f) _

private theorem boxNorm_pow {Qs : List (AddSubgroup G)} (hQs : Qs ≠ []) (f : G → ℂ) :
    boxNorm Qs f ^ (2 ^ Qs.length) = (boxMoment Qs f).re := by
  unfold boxNorm
  exact Real.rpow_inv_natCast_pow (n := 2 ^ Qs.length) (boxMoment_re_nonneg hQs f)
    (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))

private theorem boxNorm_pair_pow (Q : AddSubgroup G) (Qs : List (AddSubgroup G))
    (f g : G → ℂ) :
    (boxNorm (Q :: Qs) f * boxNorm (Q :: Qs) g) ^ (2 ^ Qs.length) =
      Real.sqrt ((boxMoment (Q :: Qs) f).re * (boxMoment (Q :: Qs) g).re) := by
  let a := boxNorm (Q :: Qs) f
  let b := boxNorm (Q :: Qs) g
  let u := (boxMoment (Q :: Qs) f).re
  let v := (boxMoment (Q :: Qs) g).re
  have ha : 0 ≤ a := boxNorm_nonneg (by simp) f
  have hb : 0 ≤ b := boxNorm_nonneg (by simp) g
  have hu : 0 ≤ u := boxMoment_re_nonneg (by simp) f
  have hv : 0 ≤ v := boxMoment_re_nonneg (by simp) g
  have hpa : a ^ (2 ^ Qs.length * 2) = u := by
    simpa [a, List.length_cons, pow_succ, Nat.mul_comm] using
      (boxNorm_pow (Qs := Q :: Qs) (by simp) f)
  have hpb : b ^ (2 ^ Qs.length * 2) = v := by
    simpa [b, List.length_cons, pow_succ, Nat.mul_comm] using
      (boxNorm_pow (Qs := Q :: Qs) (by simp) g)
  have hsq : ((a * b) ^ (2 ^ Qs.length)) ^ 2 = u * v := by
    calc
      ((a * b) ^ (2 ^ Qs.length)) ^ 2 =
          (a ^ (2 ^ Qs.length) * b ^ (2 ^ Qs.length)) ^ 2 := by rw [mul_pow]
      _ = (a ^ (2 ^ Qs.length)) ^ 2 * (b ^ (2 ^ Qs.length)) ^ 2 := by rw [mul_pow]
      _ = a ^ (2 ^ Qs.length * 2) * b ^ (2 ^ Qs.length * 2) := by
        rw [← pow_mul, ← pow_mul]
      _ = u * v := by rw [hpa, hpb]
  have hroot : (Real.sqrt (u * v)) ^ 2 = u * v := Real.sq_sqrt (mul_nonneg hu hv)
  change (a * b) ^ (2 ^ Qs.length) = Real.sqrt (u * v)
  apply le_antisymm
  · exact (Real.le_sqrt (pow_nonneg (mul_nonneg ha hb) _) (mul_nonneg hu hv)).2 hsq.le
  · exact (Real.sqrt_le_iff).2 ⟨pow_nonneg (mul_nonneg ha hb) _, hsq.ge⟩

open Classical in
noncomputable def boxInnerSubgroups :
    (Qs : List (AddSubgroup G)) → ((Fin Qs.length → Bool) → G → ℂ) → ℂ
  | [], F => 𝔼 x, F default x
  | Q :: Qs, F => 𝔼 h : Q, boxInnerSubgroups Qs
      (fun ω => crossDeriv (F (Fin.cons false ω)) (F (Fin.cons true ω)) (h : G))

private theorem norm_boxInner_le_boxNorm (Qs : List (AddSubgroup G)) (hQs : Qs ≠ [])
    (F : (Fin Qs.length → Bool) → G → ℂ) :
    ‖boxInnerSubgroups Qs F‖ ≤ ∏ ω, boxNorm Qs (F ω) := by
  classical
  induction Qs with
  | nil => simp at hQs
  | cons Q Qs ih =>
    cases Qs with
    | nil =>
      let f₀ : G → ℂ := F (Fin.cons false default)
      let f₁ : G → ℂ := F (Fin.cons true default)
      have hbox : boxInnerSubgroups [Q] F =
          𝔼 x, avgOn Q f₀ x * star (avgOn Q f₁ x) := by
        simpa only [boxInnerSubgroups] using expect_cross_avgOn Q f₀ f₁
      have hnorm := norm_expect_mul_star_sq_le
        (fun x => avgOn Q f₀ x) (fun x => avgOn Q f₁ x)
      have hmoment₀ : (boxMoment [Q] f₀).re = 𝔼 x, ‖avgOn Q f₀ x‖ ^ 2 := by
        rw [boxMoment_singleton, Complex.re_expect]
        apply Finset.expect_congr rfl
        intro x hx
        exact Complex.ofReal_re (‖avgOn Q f₀ x‖ ^ 2)
      have hmoment₁ : (boxMoment [Q] f₁).re = 𝔼 x, ‖avgOn Q f₁ x‖ ^ 2 := by
        rw [boxMoment_singleton, Complex.re_expect]
        apply Finset.expect_congr rfl
        intro x hx
        exact Complex.ofReal_re (‖avgOn Q f₁ x‖ ^ 2)
      have hn₀ : 0 ≤ boxNorm [Q] f₀ := boxNorm_nonneg (by simp) f₀
      have hn₁ : 0 ≤ boxNorm [Q] f₁ := boxNorm_nonneg (by simp) f₁
      have hp₀ : boxNorm [Q] f₀ ^ 2 = (boxMoment [Q] f₀).re := by
        simpa using boxNorm_pow (Qs := [Q]) (by simp) f₀
      have hp₁ : boxNorm [Q] f₁ ^ 2 = (boxMoment [Q] f₁).re := by
        simpa using boxNorm_pow (Qs := [Q]) (by simp) f₁
      have hp : (boxNorm [Q] f₀ * boxNorm [Q] f₁) ^ 2 =
          (boxMoment [Q] f₀).re * (boxMoment [Q] f₁).re := by
        rw [mul_pow, hp₀, hp₁]
      have hnorm' : ‖boxInnerSubgroups [Q] F‖ ^ 2 ≤
          (boxNorm [Q] f₀ * boxNorm [Q] f₁) ^ 2 := by
        rw [hbox, hp]
        simpa only [hmoment₀, hmoment₁] using hnorm
      have hle := le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0)
        (mul_nonneg hn₀ hn₁) hnorm'
      calc
        ‖boxInnerSubgroups [Q] F‖ ≤ boxNorm [Q] f₀ * boxNorm [Q] f₁ := hle
        _ = ∏ ω : Fin [Q].length → Bool, boxNorm [Q] (F ω) := by
          change boxNorm [Q] (F (Fin.cons false default)) *
            boxNorm [Q] (F (Fin.cons true default)) =
              ∏ ω : Fin 1 → Bool, boxNorm [Q] (F ω)
          have hprod := (prod_bool_tuple_succ (n := 0)
            (fun ω => boxNorm [Q] (F ω))).symm
          rw [Fintype.prod_subsingleton _ (default : Fin 0 → Bool),
            Fintype.prod_subsingleton _ (default : Fin 0 → Bool)] at hprod
          exact hprod
    | cons R Rs =>
      let D (ω : Fin (R :: Rs).length → Bool) (h : Q) : G → ℂ :=
        crossDeriv (F (Fin.cons false ω)) (F (Fin.cons true ω)) h
      have hnorm : ‖boxInnerSubgroups (Q :: R :: Rs) F‖ ≤
          𝔼 h : Q, ∏ ω, boxNorm (R :: Rs) (D ω h) := by
        change ‖𝔼 h : Q, boxInnerSubgroups (R :: Rs) (fun ω => D ω h)‖ ≤ _
        calc
          ‖𝔼 h : Q, boxInnerSubgroups (R :: Rs) (fun ω => D ω h)‖ ≤
              𝔼 h : Q, ‖boxInnerSubgroups (R :: Rs) (fun ω => D ω h)‖ :=
            RCLike.norm_expect_le (K := ℂ)
          _ ≤ 𝔼 h : Q, ∏ ω, boxNorm (R :: Rs) (D ω h) := by
            apply Finset.expect_le_expect
            intro h hh
            exact ih (by simp) (fun ω => D ω h)
      have hholder := expect_prod_boolean_pow_le (R :: Rs).length
        (fun ω h => boxNorm (R :: Rs) (D ω h))
        (fun ω h => boxNorm_nonneg (by simp) (D ω h))
      have hcross :
          (∏ ω : Fin (R :: Rs).length → Bool,
            𝔼 h : Q, boxNorm (R :: Rs) (D ω h) ^ (2 ^ (R :: Rs).length)) ≤
          ∏ ω : Fin (R :: Rs).length → Bool,
            (boxNorm (Q :: R :: Rs) (F (Fin.cons false ω)) *
              boxNorm (Q :: R :: Rs) (F (Fin.cons true ω))) ^ (2 ^ (R :: Rs).length) := by
        apply Finset.prod_le_prod₀
        · intro ω hω
          apply Finset.expect_nonneg
          intro h hh
          exact pow_nonneg (boxNorm_nonneg (by simp) (D ω h)) _
        · intro ω hω
          let f₀ : G → ℂ := F (Fin.cons false ω)
          let f₁ : G → ℂ := F (Fin.cons true ω)
          calc
            (𝔼 h : Q, boxNorm (R :: Rs) (D ω h) ^ (2 ^ (R :: Rs).length)) =
                𝔼 h : Q, (boxMoment (R :: Rs) (D ω h)).re := by
              apply Finset.expect_congr rfl
              intro h hh
              rw [boxNorm_pow (Qs := R :: Rs) (by simp) (D ω h)]
            _ ≤ Real.sqrt ((boxMoment (Q :: R :: Rs) f₀).re *
                (boxMoment (Q :: R :: Rs) f₁).re) := boxMoment_cross_avg_le Q (R :: Rs) f₀ f₁
            _ = (boxNorm (Q :: R :: Rs) f₀ * boxNorm (Q :: R :: Rs) f₁) ^
                (2 ^ (R :: Rs).length) := (boxNorm_pair_pow Q (R :: Rs) f₀ f₁).symm
      have hfactor :
          (∏ ω : Fin (R :: Rs).length → Bool,
            (boxNorm (Q :: R :: Rs) (F (Fin.cons false ω)) *
              boxNorm (Q :: R :: Rs) (F (Fin.cons true ω))) ^ (2 ^ (R :: Rs).length)) =
            (∏ ω : Fin (Q :: R :: Rs).length → Bool, boxNorm (Q :: R :: Rs) (F ω)) ^
              (2 ^ (R :: Rs).length) := by
        rw [Finset.prod_pow, Finset.prod_mul_distrib,
          ← prod_bool_tuple_succ (fun ω => boxNorm (Q :: R :: Rs) (F ω))]
        rfl
      have hnon : 0 ≤ ∏ ω : Fin (Q :: R :: Rs).length → Bool,
          boxNorm (Q :: R :: Rs) (F ω) :=
        Finset.prod_nonneg (fun ω hω => boxNorm_nonneg (by simp) (F ω))
      apply le_of_pow_le_pow_left₀
        (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hnon
      exact (pow_le_pow_left₀ (norm_nonneg _) hnorm _).trans (hholder.trans (hcross.trans_eq hfactor))

-- C4 (Gowers–Cauchy–Schwarz along subgroup directions)
theorem norm_boxInner_pow_le (Qs : List (AddSubgroup G)) (hQs : Qs ≠ [])
    (F : (Fin Qs.length → Bool) → G → ℂ) :
    ‖boxInnerSubgroups Qs F‖ ^ (2 ^ Qs.length) ≤
      ∏ ω, (boxMoment Qs (F ω)).re := by
  classical
  have hroot := norm_boxInner_le_boxNorm Qs hQs F
  calc
    ‖boxInnerSubgroups Qs F‖ ^ (2 ^ Qs.length) ≤
        (∏ ω, boxNorm Qs (F ω)) ^ (2 ^ Qs.length) := pow_le_pow_left₀ (norm_nonneg _) hroot _
    _ = ∏ ω, boxNorm Qs (F ω) ^ (2 ^ Qs.length) := by
      rw [← Finset.prod_pow]
    _ = ∏ ω, (boxMoment Qs (F ω)).re := by
      apply Finset.prod_congr rfl
      intro ω hω
      exact boxNorm_pow hQs (F ω)

open Classical in
private noncomputable def boxInnerList :
    List (AddSubgroup G) → (List Bool → G → ℂ) → ℂ
  | [], F => 𝔼 x, F [] x
  | Q :: Qs, F => 𝔼 h : Q, boxInnerList Qs
      (fun ω => crossDeriv (F (false :: ω)) (F (true :: ω)) (h : G))

private theorem boxInnerList_eq (Qs : List (AddSubgroup G))
    (F : List Bool → G → ℂ) :
    boxInnerList Qs F = boxInnerSubgroups Qs (fun ω => F (List.ofFn ω)) := by
  induction Qs generalizing F with
  | nil => rfl
  | cons Q Qs ih =>
    simp only [boxInnerList, boxInnerSubgroups]
    apply Finset.expect_congr rfl
    intro h hh
    simpa only [List.ofFn_cons] using
      (ih (fun ω => crossDeriv (F (false :: ω)) (F (true :: ω)) (h : G)))

private theorem norm_boxInnerList_pow_le (Qs : List (AddSubgroup G)) (hQs : Qs ≠ [])
    (F : List Bool → G → ℂ) :
    ‖boxInnerList Qs F‖ ^ (2 ^ Qs.length) ≤
      ∏ ω : Fin Qs.length → Bool, (boxMoment Qs (F (List.ofFn ω))).re := by
  simpa [boxInnerList_eq] using
    (norm_boxInner_pow_le Qs hQs (fun ω => F (List.ofFn ω)))

open Classical in
private theorem boxMoment_singleton_corr (Q : AddSubgroup G) (f : G → ℂ) :
    boxMoment [Q] f = 𝔼 x, f x * star (avgOn Q f x) := by
  classical
  calc
    boxMoment [Q] f = 𝔼 x, (((‖avgOn Q f x‖ ^ 2 : ℝ)) : ℂ) := boxMoment_singleton Q f
    _ = 𝔼 x, avgOn Q f x * star (avgOn Q f x) := by
      apply Finset.expect_congr rfl
      intro x hx
      simpa [Complex.normSq_eq_norm_sq] using (Complex.mul_conj (avgOn Q f x)).symm
    _ = 𝔼 x, f x * star (avgOn Q f x) := (expect_mul_star_avgOn Q f f).symm

private theorem cubeProd_crossDerivative_aux (f g : G → ℂ) (h : G)
    (hs : List G) (x : G) :
    cubeProd (crossDeriv f g h) hs x =
      cubeProd f hs x * star (cubeProd g hs (x + h)) := by
  induction hs generalizing f g x with
  | nil => simp [cubeProd, crossDeriv]
  | cons k hs ih =>
    calc
      cubeProd (crossDeriv f g h) (k :: hs) x =
          cubeProd (mderiv (crossDeriv f g h) k) hs x := rfl
      _ = cubeProd (crossDeriv (mderiv f k) (mderiv g k) h) hs x := by
        rw [mderiv_crossDeriv]
      _ = cubeProd (mderiv f k) hs x *
          star (cubeProd (mderiv g k) hs (x + h)) := ih (mderiv f k) (mderiv g k) x
      _ = cubeProd f (k :: hs) x * star (cubeProd g (k :: hs) (x + h)) := rfl

private def cubeRest (f : G → ℂ) : List G → G → ℂ
  | [], _ => 1
  | h :: hs, x => cubeRest f hs x * star (cubeProd f hs (x + h))

private theorem cubeProd_factor (f : G → ℂ) (hs : List G) (x : G) :
    cubeProd f hs x = f x * cubeRest f hs x := by
  induction hs generalizing f with
  | nil => simp [cubeProd, cubeRest]
  | cons h hs ih =>
    calc
      cubeProd f (h :: hs) x = cubeProd (mderiv f h) hs x := rfl
      _ = cubeProd f hs x * star (cubeProd f hs (x + h)) := by
        change cubeProd (crossDeriv f f h) hs x = _
        exact cubeProd_crossDerivative_aux f f h hs x
      _ = f x * cubeRest f (h :: hs) x := by
        rw [ih f]
        simp [cubeRest]
        ring

private theorem cubeProd_star_aux (f : G → ℂ) (hs : List G) (x : G) :
    cubeProd (fun y => star (f y)) hs x = star (cubeProd f hs x) := by
  induction hs generalizing f with
  | nil => rfl
  | cons h hs ih =>
    have hder : mderiv (fun y => star (f y)) h =
        (fun y => star (mderiv f h y)) := by
      funext y
      simp [mderiv, star_mul]
      ring
    calc
      cubeProd (fun y => star (f y)) (h :: hs) x =
          cubeProd (mderiv (fun y => star (f y)) h) hs x := rfl
      _ = cubeProd (fun y => star (mderiv f h y)) hs x := by rw [hder]
      _ = star (cubeProd (mderiv f h) hs x) := ih (mderiv f h)
      _ = star (cubeProd f (h :: hs) x) := rfl

private theorem cubeProd_starCross_aux (f : G → ℂ) (h : G) (hs : List G) (x : G) :
    cubeProd (fun y => star (crossDeriv f f h y)) hs x =
      star (cubeProd f hs x) * cubeProd f hs (x + h) := by
  have hcross :
      crossDeriv (fun y => star (f y)) (fun y => star (f y)) h =
        (fun y => star (crossDeriv f f h y)) := by
    funext y
    simp [crossDeriv, star_mul]
    ring
  calc
    cubeProd (fun y => star (crossDeriv f f h y)) hs x =
        cubeProd (crossDeriv (fun y => star (f y)) (fun y => star (f y)) h) hs x := by
      rw [hcross]
    _ = cubeProd (fun y => star (f y)) hs x *
        star (cubeProd (fun y => star (f y)) hs (x + h)) :=
      cubeProd_crossDerivative_aux _ _ h hs x
    _ = star (cubeProd f hs x) * cubeProd f hs (x + h) := by
      rw [cubeProd_star_aux, cubeProd_star_aux]
      simp

private def psiIntegrand (f : G → ℂ) (hs : List G) (h : G) (x : G) : ℂ :=
  star (cubeRest f hs x) * cubeProd f hs (x + h)

private theorem psiIntegrand_insert (f : G → ℂ) (a : G) (hs : List G)
    (h : G) (x : G) :
    psiIntegrand f (a :: hs) h x =
      psiIntegrand f hs h x *
        star (cubeProd (fun y => star (crossDeriv f f h y)) hs (x + a)) := by
  unfold psiIntegrand
  calc
    star (cubeRest f (a :: hs) x) * cubeProd f (a :: hs) (x + h) =
        star (cubeRest f hs x * star (cubeProd f hs (x + a))) *
          cubeProd (mderiv f a) hs (x + h) := rfl
    _ = star (cubeRest f hs x) * cubeProd f hs (x + a) *
          (cubeProd f hs (x + h) * star (cubeProd f hs (x + h + a))) := by
      have hder : mderiv f a = crossDeriv f f a := rfl
      rw [hder, cubeProd_crossDerivative_aux]
      simp only [star_mul, star_star]
      ring
    _ = (star (cubeRest f hs x) * cubeProd f hs (x + h)) *
          star (cubeProd (fun y => star (crossDeriv f f h y)) hs (x + a)) := by
      rw [cubeProd_starCross_aux]
      simp only [star_mul, star_star]
      have hshift : x + h + a = x + a + h := by abel
      rw [hshift]
      ring
    _ = _ := by ring

private def maskAllFalse (ω : List Bool) : Prop := ∀ b ∈ ω, b = false

@[simp] private theorem maskAllFalse_nil : maskAllFalse [] := by simp [maskAllFalse]

@[simp] private theorem maskAllFalse_cons_false (ω : List Bool) :
    maskAllFalse (false :: ω) ↔ maskAllFalse ω := by simp [maskAllFalse]

@[simp] private theorem not_maskAllFalse_cons_true (ω : List Bool) :
    ¬ maskAllFalse (true :: ω) := by simp [maskAllFalse]

private theorem maskAllFalse_ofFn_iff_default {n : ℕ} (ω : Fin n → Bool) :
    maskAllFalse (List.ofFn ω) ↔ ω = default := by
  constructor
  · intro h
    funext i
    apply h
    simp
  · rintro rfl
    simp [maskAllFalse]

open Classical in
private theorem mixedCubeProductList_root_mul (F : List Bool → G → ℂ)
    (c : G → ℂ) (hs : List G) (x : G) :
    mixedCubeProductList
        (fun ω y => if maskAllFalse ω then c y * F ω y else F ω y) hs x =
      c x * mixedCubeProductList F hs x := by
  classical
  unfold mixedCubeProductList mixedCubeProduct
  let φ (ω : Fin hs.length → Bool) :=
    conjugationPower (booleanWeight ω) (F (List.ofFn ω) (x + cubeShift (listToFin hs) ω))
  let ψ (ω : Fin hs.length → Bool) :=
    if ω = default then c x * φ ω else φ ω
  have hfactor (ω : Fin hs.length → Bool) :
      conjugationPower (booleanWeight ω)
          (if maskAllFalse (List.ofFn ω) then
            c (x + cubeShift (listToFin hs) ω) *
              F (List.ofFn ω) (x + cubeShift (listToFin hs) ω)
          else F (List.ofFn ω) (x + cubeShift (listToFin hs) ω)) = ψ ω := by
    by_cases hω : ω = default
    · subst ω
      simp [ψ, φ, maskAllFalse, booleanWeight, cubeShift, conjugationPower]
    · have hnot : ¬ maskAllFalse (List.ofFn ω) := by
        simpa [maskAllFalse_ofFn_iff_default] using hω
      simp only [hnot, if_false, ψ, φ]
      rw [if_neg hω]
  have hsplit : (∏ ω, ψ ω) = c x * (∏ ω, φ ω) := by
    calc
      (∏ ω, ψ ω) = ψ default *
          ∏ ω ∈ (Finset.univ.erase (default : Fin hs.length → Bool)), ψ ω :=
        (Finset.mul_prod_erase Finset.univ ψ (Finset.mem_univ _)).symm
      _ = (c x * φ default) *
          ∏ ω ∈ (Finset.univ.erase (default : Fin hs.length → Bool)), φ ω := by
        congr 1
        · simp [ψ]
        · apply Finset.prod_congr rfl
          intro ω hmem
          have hne := (Finset.mem_erase.mp hmem).1
          change (if ω = default then c x * φ ω else φ ω) = φ ω
          split_ifs with heq
          · exact (hne heq).elim
          · rfl
      _ = c x * (φ default *
          ∏ ω ∈ (Finset.univ.erase (default : Fin hs.length → Bool)), φ ω) := by ring
      _ = c x * (∏ ω, φ ω) := by
        rw [Finset.mul_prod_erase Finset.univ φ (Finset.mem_univ _)]
  calc
    (∏ ω,
        conjugationPower (booleanWeight ω)
          (if maskAllFalse (List.ofFn ω) then
            c (x + cubeShift (listToFin hs) ω) *
              F (List.ofFn ω) (x + cubeShift (listToFin hs) ω)
          else F (List.ofFn ω) (x + cubeShift (listToFin hs) ω))) =
        ∏ ω, ψ ω := by
          apply Finset.prod_congr rfl
          intro ω hω
          exact hfactor ω
    _ = c x * ∏ ω, φ ω := hsplit

private theorem mixedCubeProductList_one (hs : List G) (x : G) :
    mixedCubeProductList (fun _ _ => (1 : ℂ)) hs x = 1 := by
  unfold mixedCubeProductList mixedCubeProduct
  simp [conjugationPower]

open Classical in
private theorem mixedCubeProductList_root_only (f : G → ℂ) (hs : List G) (x : G) :
    mixedCubeProductList (fun ω y => if maskAllFalse ω then f y else 1) hs x = f x := by
  classical
  simpa [mixedCubeProductList_one] using
    (mixedCubeProductList_root_mul (fun _ _ => (1 : ℂ)) f hs x)

private theorem mixedCubeProductList_star (F : List Bool → G → ℂ)
    (hs : List G) (x : G) :
    star (mixedCubeProductList F hs x) =
      mixedCubeProductList (fun ω y => star (F ω y)) hs x := by
  unfold mixedCubeProductList mixedCubeProduct
  change (starRingEnd ℂ) (∏ ω,
      conjugationPower (booleanWeight ω) (F (List.ofFn ω) (x + cubeShift (listToFin hs) ω))) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro ω hω
  change star (conjugationPower (booleanWeight ω)
      (F (List.ofFn ω) (x + cubeShift (listToFin hs) ω))) = _
  rw [← conjugationPower_star]

open Classical in
private noncomputable def psiFamily (f : G → ℂ) (h : G) : List Bool → G → ℂ :=
  fun ω x => if maskAllFalse ω then f (x + h) else star (crossDeriv f f h x)

open Classical in
private noncomputable def psiConjFamily (f : G → ℂ) (h : G) : List Bool → G → ℂ :=
  fun ω x => if maskAllFalse ω then star (f (x + h)) else crossDeriv f f h x

open Classical in
private noncomputable def pairFamily (s : ℕ) (f : G → ℂ) (h₀ h₁ : G) :
    List Bool → G → ℂ := fun ω x =>
  if maskAllFalse ω then f (x + h₀) * star (f (x + h₁))
  else if maskAllFalse (ω.drop s) then star (crossDeriv f f h₀ x)
  else if maskAllFalse (ω.take s) then crossDeriv f f h₁ x
  else 1

private theorem maskAllFalse_append (α β : List Bool) :
    maskAllFalse (α ++ β) ↔ maskAllFalse α ∧ maskAllFalse β := by
  simp [maskAllFalse, List.mem_append]

open Classical in
private theorem pairFamily_append_split (s : ℕ) (f : G → ℂ) (h₀ h₁ : G)
    (α β : List Bool) (hα : α.length = s) (x : G) :
    pairFamily s f h₀ h₁ (α ++ β) x =
      if maskAllFalse α then
        if maskAllFalse β then f (x + h₀) * star (f (x + h₁))
        else crossDeriv f f h₁ x
      else if maskAllFalse β then star (crossDeriv f f h₀ x) else 1 := by
  classical
  have htake : (α ++ β).take s = α := by
    have hle : s ≤ α.length := by omega
    rw [List.take_append_of_le_length hle]
    simp [hα]
  have hdrop : (α ++ β).drop s = β := by
    have hle : s ≤ α.length := by omega
    rw [List.drop_append_of_le_length hle]
    simp [hα]
  by_cases hA : maskAllFalse α <;> by_cases hB : maskAllFalse β <;>
    simp [pairFamily, maskAllFalse_append, htake, hdrop, hA, hB]

private theorem cubeProd_mixedCubeProductList (f : G → ℂ) (hs : List G) (x : G) :
    cubeProd f hs x = mixedCubeProductList (fun _ => f) hs x := by
  induction hs generalizing f with
  | nil =>
    simp [cubeProd, mixedCubeProductList, mixedCubeProduct, listToFin,
      booleanWeight, cubeShift, conjugationPower]
  | cons a hs ih =>
    calc
      cubeProd f (a :: hs) x = cubeProd (mderiv f a) hs x := rfl
      _ = mixedCubeProductList (fun _ => mderiv f a) hs x := ih (mderiv f a)
      _ = mixedCubeProductList (fun _ => crossDeriv f f a) hs x := by
        rfl
      _ = mixedCubeProductList (fun _ => f) hs x *
          star (mixedCubeProductList (fun _ => f) hs (x + a)) := by
        exact mixedCubeProductList_crossDerivative (fun _ => f) (fun _ => f) a hs x
      _ = mixedCubeProductList (fun _ => f) (a :: hs) x :=
        (mixedCubeProductList_cons (fun _ => f) a hs x).symm

private theorem psiIntegrand_eq_mixedCubeProductList (f : G → ℂ) (hs : List G)
    (h : G) (x : G) :
    psiIntegrand f hs h x = mixedCubeProductList (psiFamily f h) hs x := by
  induction hs generalizing f with
  | nil => simp [psiIntegrand, cubeRest, cubeProd, mixedCubeProductList,
      mixedCubeProduct, listToFin, psiFamily, maskAllFalse, booleanWeight,
      cubeShift, conjugationPower]
  | cons a hs ih =>
    calc
      psiIntegrand f (a :: hs) h x =
          psiIntegrand f hs h x *
            star (cubeProd (fun y => star (crossDeriv f f h y)) hs (x + a)) :=
        psiIntegrand_insert f a hs h x
      _ = mixedCubeProductList (psiFamily f h) hs x *
          star (mixedCubeProductList (fun _ y => star (crossDeriv f f h y)) hs (x + a)) := by
        rw [ih]
        have hcube := cubeProd_mixedCubeProductList
          (fun y => star (crossDeriv f f h y)) hs (x + a)
        change cubeProd (fun y => star (crossDeriv f f h y)) hs (x + a) =
          mixedCubeProductList (fun _ y => star (crossDeriv f f h y)) hs (x + a) at hcube
        rw [hcube]
      _ = mixedCubeProductList (psiFamily f h) (a :: hs) x := by
        symm
        rw [mixedCubeProductList_cons]
        have hfalse : (fun ω => psiFamily f h (false :: ω)) = psiFamily f h := by
          funext ω y
          simp [psiFamily, maskAllFalse]
        have htrue :
            (fun ω => psiFamily f h (true :: ω)) =
              (fun _ y => star (crossDeriv f f h y)) := by
          funext ω y
          simp [psiFamily, maskAllFalse]
        rw [hfalse, htrue]

private theorem psiConjFamily_eq_mixedCubeProductList (f : G → ℂ) (hs : List G)
    (h : G) (x : G) :
    mixedCubeProductList (psiConjFamily f h) hs x =
      star (psiIntegrand f hs h x) := by
  have hfamily : psiConjFamily f h = fun ω y => star (psiFamily f h ω y) := by
    funext ω y
    by_cases hw : maskAllFalse ω <;> simp [psiConjFamily, psiFamily, hw]
  calc
    mixedCubeProductList (psiConjFamily f h) hs x =
        mixedCubeProductList (fun ω y => star (psiFamily f h ω y)) hs x := by rw [hfamily]
    _ = star (mixedCubeProductList (psiFamily f h) hs x) :=
      (mixedCubeProductList_star (psiFamily f h) hs x).symm
    _ = star (psiIntegrand f hs h x) := by rw [psiIntegrand_eq_mixedCubeProductList]

private theorem pairMixedCubeProductList (s : ℕ) (f : G → ℂ) (h₀ h₁ : G)
    (ks ls : List G) (hks : ks.length = s) (hls : ls.length = s) (x : G) :
    mixedCubeProductList (pairFamily s f h₀ h₁) (ks ++ ls) x =
      psiIntegrand f ks h₀ x * star (psiIntegrand f ls h₁ x) := by
  classical
  let c : G → ℂ := fun y => mixedCubeProductList (psiConjFamily f h₁) ls y
  let A : List Bool → G → ℂ := fun α y =>
    if maskAllFalse α then c y * psiFamily f h₀ α y else psiFamily f h₀ α y
  have hinner (α : List Bool) (hα : α.length = s) (y : G) :
      mixedCubeProductList (fun β => pairFamily s f h₀ h₁ (α ++ β)) ls y = A α y := by
    by_cases hA : maskAllFalse α
    · have hF : (fun β z => pairFamily s f h₀ h₁ (α ++ β) z) =
      (fun β z => if maskAllFalse β then
            f (z + h₀) * psiConjFamily f h₁ β z else psiConjFamily f h₁ β z) := by
        funext β z
        rw [pairFamily_append_split s f h₀ h₁ α β hα z]
        by_cases hB : maskAllFalse β <;>
          simp [hA, hB, psiConjFamily]
      calc
        _ = mixedCubeProductList
            (fun β z => if maskAllFalse β then
              f (z + h₀) * psiConjFamily f h₁ β z else psiConjFamily f h₁ β z) ls y := by
          rw [hF]
        _ = f (y + h₀) * mixedCubeProductList (psiConjFamily f h₁) ls y :=
          mixedCubeProductList_root_mul (psiConjFamily f h₁) (fun z => f (z + h₀)) ls y
        _ = A α y := by
          change f (y + h₀) * c y =
            (if maskAllFalse α then c y * psiFamily f h₀ α y else psiFamily f h₀ α y)
          have hpsi : psiFamily f h₀ α y = f (y + h₀) := by
            simp [psiFamily, hA]
          rw [if_pos hA, hpsi]
          ring
    · have hF : (fun β z => pairFamily s f h₀ h₁ (α ++ β) z) =
          (fun β z => if maskAllFalse β then star (crossDeriv f f h₀ z) else 1) := by
        funext β z
        rw [pairFamily_append_split s f h₀ h₁ α β hα z]
        by_cases hB : maskAllFalse β <;> simp [hA, hB]
      calc
        _ = mixedCubeProductList
            (fun β z => if maskAllFalse β then star (crossDeriv f f h₀ z) else 1) ls y := by
          rw [hF]
        _ = star (crossDeriv f f h₀ y) := mixedCubeProductList_root_only _ _ _
        _ = A α y := by
          change star (crossDeriv f f h₀ y) =
            (if maskAllFalse α then c y * psiFamily f h₀ α y else psiFamily f h₀ α y)
          simp [hA, psiFamily]
  have hAroot : A = fun α y =>
      if maskAllFalse α then c y * psiFamily f h₀ α y else psiFamily f h₀ α y := rfl
  have houter : mixedCubeProductList (pairFamily s f h₀ h₁) (ks ++ ls) x =
      mixedCubeProductList A ks x := by
    rw [mixedCubeProductList_append]
    apply mixedCubeProductList_congr_onFin
    intro ω y
    exact hinner (List.ofFn ω) (by simp [hks]) y
  calc
    mixedCubeProductList (pairFamily s f h₀ h₁) (ks ++ ls) x =
        mixedCubeProductList A ks x := houter
    _ = c x * mixedCubeProductList (psiFamily f h₀) ks x := by
      rw [hAroot, mixedCubeProductList_root_mul]
    _ = psiIntegrand f ks h₀ x * star (psiIntegrand f ls h₁ x) := by
      rw [psiIntegrand_eq_mixedCubeProductList,
        ← psiConjFamily_eq_mixedCubeProductList]
      simp [c, mul_comm]

private def rootCorrelation (f : G → ℂ) (h₀ h₁ : G) : G → ℂ :=
  fun x => f (x + h₀) * star (f (x + h₁))

private theorem crossDeriv_norm_le_one (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (h x : G) : ‖crossDeriv f f h x‖ ≤ 1 := by
  rw [crossDeriv, norm_mul, norm_star]
  have h₁ := hf x
  have h₂ := hf (x + h)
  nlinarith [norm_nonneg (f x), norm_nonneg (f (x + h))]

open Classical in
private theorem pairFamily_norm_le_one (s : ℕ) (f : G → ℂ) (h₀ h₁ : G)
    (hf : ∀ x, ‖f x‖ ≤ 1) (ω : List Bool) (x : G) :
    ‖pairFamily s f h₀ h₁ ω x‖ ≤ 1 := by
  by_cases hroot : maskAllFalse ω
  · simp [pairFamily, hroot, norm_mul, norm_star]
    have h₀' := hf (x + h₀)
    have h₁' := hf (x + h₁)
    nlinarith [norm_nonneg (f (x + h₀)), norm_nonneg (f (x + h₁))]
  · by_cases hright : maskAllFalse (ω.drop s)
    · simpa [pairFamily, hroot, hright, norm_star] using
        (crossDeriv_norm_le_one f hf h₀ x)
    · by_cases hleft : maskAllFalse (ω.take s)
      · simpa [pairFamily, hroot, hright, hleft] using
          (crossDeriv_norm_le_one f hf h₁ x)
      · simp [pairFamily, hroot, hright, hleft]

open Classical in
private theorem pairFamily_GCS_root_bound (K L : List (AddSubgroup G))
    (s : ℕ) (hK : K.length = s) (hL : L.length = s) (hs : 0 < s)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (h₀ h₁ : G) :
    ‖boxInnerList (K ++ L) (pairFamily s f h₀ h₁)‖ ≤
      boxNorm (K ++ L) (rootCorrelation f h₀ h₁) := by
  classical
  let Qs := K ++ L
  have hlen : Qs.length = 2 * s := by
    simp [Qs, List.length_append, hK, hL, two_mul]
  have hQs : Qs ≠ [] := by
    intro hz
    have hzero := congrArg List.length hz
    simp [Qs, List.length_append, hK, hL] at hzero
    omega
  let F := pairFamily s f h₀ h₁
  let root := rootCorrelation f h₀ h₁
  let M (ω : Fin Qs.length → Bool) := (boxMoment Qs (F (List.ofFn ω))).re
  have hM0 (ω : Fin Qs.length → Bool) : 0 ≤ M ω :=
    boxMoment_re_nonneg hQs (F (List.ofFn ω))
  have hM1 (ω : Fin Qs.length → Bool) : M ω ≤ 1 := by
    exact boxMoment_re_le_one Qs (F (List.ofFn ω))
      (pairFamily_norm_le_one s f h₀ h₁ hf (List.ofFn ω))
  have hrootF : F (List.ofFn (default : Fin Qs.length → Bool)) = root := by
    funext x
    simp [F, root, pairFamily, rootCorrelation, maskAllFalse]
  have hroot0 : 0 ≤ M (default : Fin Qs.length → Bool) := hM0 _
  have hothers :
      (∏ ω ∈ (Finset.univ.erase (default : Fin Qs.length → Bool)), M ω) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro ω hω
      exact hM0 ω
    · intro ω hω
      exact hM1 ω
  have hprodEq : (∏ ω : Fin Qs.length → Bool, M ω) =
      M default * ∏ ω ∈ (Finset.univ.erase (default : Fin Qs.length → Bool)), M ω :=
    (Finset.mul_prod_erase Finset.univ M (Finset.mem_univ _)).symm
  have hprod : (∏ ω : Fin Qs.length → Bool, M ω) ≤ M default := by
    rw [hprodEq]
    calc
      M default * ∏ ω ∈ (Finset.univ.erase (default : Fin Qs.length → Bool)), M ω ≤
          M default * 1 := mul_le_mul_of_nonneg_left hothers hroot0
      _ = M default := by ring
  have hgcs := norm_boxInnerList_pow_le Qs hQs F
  have hrootMoment : M (default : Fin Qs.length → Bool) = (boxMoment Qs root).re := by
    change (boxMoment Qs (F (List.ofFn (default : Fin Qs.length → Bool)))).re = _
    rw [hrootF]
  have hpow : ‖boxInnerList Qs F‖ ^ (2 ^ Qs.length) ≤
      boxNorm Qs root ^ (2 ^ Qs.length) := by
    calc
      ‖boxInnerList Qs F‖ ^ (2 ^ Qs.length) ≤ ∏ ω, M ω := hgcs
      _ ≤ M default := hprod
      _ = (boxMoment Qs root).re := hrootMoment
      _ = boxNorm Qs root ^ (2 ^ Qs.length) := (boxNorm_pow hQs root).symm
  exact le_of_pow_le_pow_left₀ (by positivity : (2 ^ Qs.length : ℕ) ≠ 0)
    (boxNorm_nonneg hQs root) hpow

private theorem mderiv_norm_le_one (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (h : G) (x : G) :
    ‖mderiv f h x‖ ≤ 1 := by
  rw [mderiv, norm_mul, norm_star]
  have h₁ := hf x
  have h₂ := hf (x + h)
  have hn₁ := norm_nonneg (f x)
  have hn₂ := norm_nonneg (f (x + h))
  nlinarith

private theorem cubeProd_norm_le_one (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hs : List G) (x : G) : ‖cubeProd f hs x‖ ≤ 1 := by
  induction hs generalizing f with
  | nil => simpa [cubeProd] using hf x
  | cons h hs ih =>
    change ‖cubeProd (mderiv f h) hs x‖ ≤ 1
    exact ih (mderiv f h) (fun y => mderiv_norm_le_one f hf h y)

private theorem cubeRest_norm_le_one (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hs : List G) (x : G) : ‖cubeRest f hs x‖ ≤ 1 := by
  induction hs generalizing f with
  | nil => simp [cubeRest]
  | cons h hs ih =>
    rw [cubeRest, norm_mul, norm_star]
    have h₁ := ih f hf
    have h₂ := cubeProd_norm_le_one f hf hs (x + h)
    have hn₁ := norm_nonneg (cubeRest f hs x)
    have hn₂ := norm_nonneg (cubeProd f hs (x + h))
    nlinarith

open Classical in
private theorem cubeAvg_expect_comm (Qs : List (AddSubgroup G))
    (F : List G → G → ℂ) :
    cubeAvg Qs (fun hs => 𝔼 x, F hs x) = 𝔼 x, cubeAvg Qs (fun hs => F hs x) := by
  classical
  induction Qs generalizing F with
  | nil => rfl
  | cons Q Qs ih =>
    simp only [cubeAvg]
    calc
      (𝔼 h : Q, cubeAvg Qs (fun hs => 𝔼 x, F (h :: hs) x)) =
          𝔼 h : Q, 𝔼 x, cubeAvg Qs (fun hs => F (h :: hs) x) := by
        apply Finset.expect_congr rfl
        intro h hh
        exact ih (fun hs x => F (h :: hs) x)
      _ = 𝔼 x, 𝔼 h : Q, cubeAvg Qs (fun hs => F (h :: hs) x) :=
        Finset.expect_comm Finset.univ Finset.univ _
      _ = 𝔼 x, cubeAvg (Q :: Qs) (fun hs => F hs x) := by
        simp only [cubeAvg]

open Classical in
private theorem cubeAvg_expect_comm_general {Ω : Type*} [Fintype Ω]
    (Qs : List (AddSubgroup G)) (F : List G → Ω → ℂ) :
    cubeAvg Qs (fun hs => 𝔼 x : Ω, F hs x) =
      𝔼 x : Ω, cubeAvg Qs (fun hs => F hs x) := by
  induction Qs generalizing F with
  | nil => rfl
  | cons Q Qs ih =>
    simp only [cubeAvg]
    calc
      (𝔼 q : Q, cubeAvg Qs (fun hs => 𝔼 x : Ω, F (q :: hs) x)) =
          𝔼 q : Q, 𝔼 x : Ω, cubeAvg Qs (fun hs => F (q :: hs) x) := by
        apply Finset.expect_congr rfl
        intro q hq
        exact ih (fun hs x => F (q :: hs) x)
      _ = 𝔼 x : Ω, 𝔼 q : Q, cubeAvg Qs (fun hs => F (q :: hs) x) :=
        Finset.expect_comm (Finset.univ : Finset Q) (Finset.univ : Finset Ω) _
      _ = 𝔼 x : Ω, cubeAvg (Q :: Qs) (fun hs => F hs x) := by simp only [cubeAvg]

private theorem cubeAvg_re (Qs : List (AddSubgroup G)) (F : List G → ℂ) :
    (cubeAvg Qs F).re = cubeAvg Qs (fun hs => (F hs).re) := by
  induction Qs generalizing F with
  | nil => rfl
  | cons Q Qs ih =>
    simp only [cubeAvg, Complex.re_expect]
    apply Finset.expect_congr rfl
    intro q hq
    exact ih (fun hs => F ((q : G) :: hs))

private theorem boxMoment_re_append (Qs Rs : List (AddSubgroup G)) (f : G → ℂ) :
    (boxMoment (Qs ++ Rs) f).re =
      cubeAvg Qs (fun hs => (boxMoment Rs (cubeProd f hs)).re) := by
  rw [boxMoment_append, cubeAvg_re]

private theorem replicate_append_singleton (n : ℕ) (Q : AddSubgroup G) :
    List.replicate n Q ++ [Q] = List.replicate (n + 1) Q := by
  calc
    List.replicate n Q ++ [Q] = List.replicate n Q ++ List.replicate 1 Q := by simp
    _ = List.replicate (n + 1) Q := (List.replicate_add n 1 Q).symm

open Classical in
private theorem cubeAvg_mul_left (Qs : List (AddSubgroup G)) (c : ℂ)
    (F : List G → ℂ) : cubeAvg Qs (fun hs => c * F hs) = c * cubeAvg Qs F := by
  classical
  induction Qs generalizing F with
  | nil => simp [cubeAvg]
  | cons Q Qs ih =>
    simp only [cubeAvg]
    calc
      (𝔼 h : Q, cubeAvg Qs (fun hs => c * F (h :: hs))) =
          𝔼 h : Q, c * cubeAvg Qs (fun hs => F (h :: hs)) := by
        apply Finset.expect_congr rfl
        intro h hh
        exact ih (fun hs => F (h :: hs))
      _ = c * 𝔼 h : Q, cubeAvg Qs (fun hs => F (h :: hs)) :=
        (Finset.mul_expect Finset.univ _ c).symm

open Classical in
private theorem cubeAvg_star (Qs : List (AddSubgroup G)) (F : List G → ℂ) :
    star (cubeAvg Qs F) = cubeAvg Qs (fun hs => star (F hs)) := by
  classical
  induction Qs generalizing F with
  | nil => simp [cubeAvg]
  | cons Q Qs ih =>
    simp only [cubeAvg]
    calc
      star (𝔼 h : Q, cubeAvg Qs (fun hs => F (h :: hs))) =
          𝔼 h : Q, star (cubeAvg Qs (fun hs => F (h :: hs))) := by
        exact map_expect (starRingEnd ℂ)
          (fun h : Q => cubeAvg Qs (fun hs => F (h :: hs))) Finset.univ
      _ = 𝔼 h : Q, cubeAvg Qs (fun hs => star (F (h :: hs))) := by
        apply Finset.expect_congr rfl
        intro h hh
        exact ih (fun hs => F (h :: hs))

open Classical in
private theorem cubeAvg_congr (Qs : List (AddSubgroup G)) (F H : List G → ℂ)
    (h : ∀ hs, F hs = H hs) : cubeAvg Qs F = cubeAvg Qs H := by
  classical
  induction Qs generalizing F H with
  | nil => exact h []
  | cons Q Qs ih =>
    simp only [cubeAvg]
    apply Finset.expect_congr rfl
    intro q hq
    apply ih
    intro hs
    exact h (q :: hs)

private theorem cubeAvg_congr_valid (Qs : List (AddSubgroup G))
    (F H : List G → ℂ)
    (h : ∀ hs, hs.length = Qs.length → F hs = H hs) :
    cubeAvg Qs F = cubeAvg Qs H := by
  induction Qs generalizing F H with
  | nil => exact h [] rfl
  | cons Q Qs ih =>
    simp only [cubeAvg]
    apply Finset.expect_congr rfl
    intro q hq
    apply ih
    intro hs hlen
    exact h ((q : G) :: hs) (by simp [hlen])

private theorem boxInnerList_cube (Qs : List (AddSubgroup G))
    (F : List Bool → G → ℂ) :
    boxInnerList Qs F = cubeAvg Qs (fun hs => 𝔼 x, mixedCubeProductList F hs x) := by
  induction Qs generalizing F with
  | nil =>
    simp [boxInnerList, cubeAvg, mixedCubeProductList, mixedCubeProduct,
      listToFin, booleanWeight, cubeShift, conjugationPower]
  | cons Q Qs ih =>
    simp only [boxInnerList, cubeAvg]
    apply Finset.expect_congr rfl
    intro h hh
    rw [ih]
    apply cubeAvg_congr
    intro hs
    apply Finset.expect_congr rfl
    intro x hx
    rw [mixedCubeProductList_crossDerivative]
    rw [mixedCubeProductList_cons]

open Classical in
private theorem cubeAvg_append (Qs Rs : List (AddSubgroup G))
    (F : List G → List G → ℂ) :
    cubeAvg (Qs ++ Rs) (fun hs => F (hs.take Qs.length) (hs.drop Qs.length)) =
      cubeAvg Qs (fun qs => cubeAvg Rs (fun rs => F qs rs)) := by
  induction Qs generalizing F with
  | nil => simp [cubeAvg]
  | cons Q Qs ih =>
    simp only [List.cons_append, List.length_cons, cubeAvg]
    apply Finset.expect_congr rfl
    intro q hq
    have htake (hs : List G) :
        ((q : G) :: hs).take (Qs.length + 1) =
          (q : G) :: hs.take Qs.length := by
      simp
    have hdrop (hs : List G) :
        ((q : G) :: hs).drop (Qs.length + 1) = hs.drop Qs.length := by
      simp
    have hsplit :
        (fun hs : List G =>
          F (((q : G) :: hs).take (Qs.length + 1))
            (((q : G) :: hs).drop (Qs.length + 1))) =
        (fun hs => F ((q : G) :: hs.take Qs.length) (hs.drop Qs.length)) := by
      funext hs
      rw [htake, hdrop]
    rw [hsplit, ih (fun qs rs => F ((q : G) :: qs) rs)]

open Classical in
private theorem cubeAvg_concat (Qs Rs : List (AddSubgroup G)) (F : List G → ℂ) :
    cubeAvg (Qs ++ Rs) F =
      cubeAvg Qs (fun qs => cubeAvg Rs (fun rs => F (qs ++ rs))) := by
  induction Qs generalizing F with
  | nil => simp [cubeAvg]
  | cons Q Qs ih =>
    simp only [List.cons_append, cubeAvg]
    apply Finset.expect_congr rfl
    intro q hq
    simpa [List.append_assoc] using ih (fun hs => F ((q : G) :: hs))

open Classical in
private theorem cubeAvg_mul_star_append (Qs Rs : List (AddSubgroup G))
    (F H : List G → ℂ) :
    cubeAvg Qs F * star (cubeAvg Rs H) =
      cubeAvg (Qs ++ Rs)
        (fun hs => F (hs.take Qs.length) * star (H (hs.drop Qs.length))) := by
  rw [cubeAvg_append (Qs := Qs) (Rs := Rs)
    (F := fun qs rs => F qs * star (H rs))]
  let c := star (cubeAvg Rs H)
  calc
    cubeAvg Qs F * star (cubeAvg Rs H) = c * cubeAvg Qs F := by ring
    _ = cubeAvg Qs (fun qs => c * F qs) := (cubeAvg_mul_left Qs c F).symm
    _ = cubeAvg Qs (fun qs => F qs * cubeAvg Rs (fun rs => star (H rs))) := by
      apply cubeAvg_congr
      intro qs
      calc
        c * F qs = star (cubeAvg Rs H) * F qs := by rfl
        _ = F qs * star (cubeAvg Rs H) := by ring
        _ = F qs * cubeAvg Rs (fun rs => star (H rs)) := by
          dsimp [c]
          change F qs * star (cubeAvg Rs H) = _
          rw [cubeAvg_star]
          rfl
    _ = cubeAvg Qs (fun qs => cubeAvg Rs (fun rs => F qs * star (H rs))) := by
      apply cubeAvg_congr
      intro qs
      exact (cubeAvg_mul_left Rs (F qs) (fun rs => star (H rs))).symm

private theorem cubeAvg_mul_star_nested (Qs Rs : List (AddSubgroup G))
    (F H : List G → ℂ) :
    cubeAvg Qs F * star (cubeAvg Rs H) =
      cubeAvg Qs (fun qs => cubeAvg Rs (fun rs => F qs * star (H rs))) := by
  calc
    cubeAvg Qs F * star (cubeAvg Rs H) =
        cubeAvg (Qs ++ Rs)
          (fun hs => F (hs.take Qs.length) * star (H (hs.drop Qs.length))) :=
      cubeAvg_mul_star_append Qs Rs F H
    _ = cubeAvg Qs (fun qs => cubeAvg Rs (fun rs => F qs * star (H rs))) :=
      cubeAvg_append Qs Rs (fun qs rs => F qs * star (H rs))

open Classical in
private theorem cubeAvg_nested_expect {Ω : Type*} [Fintype Ω]
    (Qs Rs : List (AddSubgroup G)) (F : List G → List G → Ω → ℂ) :
    cubeAvg Qs (fun qs => cubeAvg Rs (fun rs => 𝔼 t : Ω, F qs rs t)) =
      𝔼 t : Ω, cubeAvg Qs (fun qs => cubeAvg Rs (fun rs => F qs rs t)) := by
  calc
    cubeAvg Qs (fun qs => cubeAvg Rs (fun rs => 𝔼 t : Ω, F qs rs t)) =
        cubeAvg (Qs ++ Rs) (fun hs => 𝔼 t : Ω,
          F (hs.take Qs.length) (hs.drop Qs.length) t) :=
      (cubeAvg_append Qs Rs (fun qs rs => 𝔼 t : Ω, F qs rs t)).symm
    _ = 𝔼 t : Ω, cubeAvg (Qs ++ Rs)
        (fun hs => F (hs.take Qs.length) (hs.drop Qs.length) t) :=
      cubeAvg_expect_comm_general (Qs ++ Rs)
        (fun hs t => F (hs.take Qs.length) (hs.drop Qs.length) t)
    _ = 𝔼 t : Ω, cubeAvg Qs (fun qs => cubeAvg Rs (fun rs => F qs rs t)) := by
      apply Finset.expect_congr rfl
      intro t ht
      exact cubeAvg_append Qs Rs (fun qs rs => F qs rs t)

private theorem probWeights_pow_jensen {ι : Type*} [Fintype ι]
    (π : ProbWeights ι) (F : ι → ℝ) (hF : ∀ i, 0 ≤ F i) (N : ℕ) :
    (∑ i, π.w i * F i) ^ N ≤ ∑ i, π.w i * F i ^ N := by
  have h := (convexOn_pow N).map_sum_le
    (t := (Finset.univ : Finset ι)) (w := π.w)
    (fun i hi => π.nonneg i) π.total
    (fun i hi => Set.mem_Ici.mpr (hF i))
  simpa [smul_eq_mul] using h

private theorem expect_pow_jensen {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (F : Ω → ℝ) (hF : ∀ i, 0 ≤ F i) (N : ℕ) :
    (𝔼 i, F i) ^ N ≤ 𝔼 i, F i ^ N := by
  classical
  let w : Ω → ℝ := fun _ => (Fintype.card Ω : ℝ)⁻¹
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω ≠ 0)
  have htotal : ∑ i, w i = 1 := by
    simp [w, Finset.sum_const, nsmul_eq_mul]
  have hmean (f : Ω → ℝ) : (∑ i, w i * f i) = 𝔼 i, f i := by
    calc
      (∑ i, w i * f i) = (Fintype.card Ω : ℝ)⁻¹ * ∑ i, f i := by
        dsimp [w]
        rw [← Finset.mul_sum]
      _ = (∑ i, f i) / Fintype.card Ω := by
        simp [div_eq_mul_inv, mul_comm]
      _ = 𝔼 i, f i := (Fintype.expect_eq_sum_div_card f).symm
  have h := (convexOn_pow N).map_sum_le
    (t := (Finset.univ : Finset Ω)) (w := w)
    (fun i hi => inv_nonneg.mpr (Nat.cast_nonneg _)) htotal
    (fun i hi => Set.mem_Ici.mpr (hF i))
  calc
    (𝔼 i, F i) ^ N = (∑ i, w i * F i) ^ N := by rw [hmean]
    _ ≤ ∑ i, w i * F i ^ N := by simpa [smul_eq_mul] using h
    _ = 𝔼 i, F i ^ N := hmean (fun i => F i ^ N)

private theorem cubeAvg_real_add (Qs : List (AddSubgroup G))
    (F H : List G → ℝ) :
    cubeAvg Qs (fun hs => F hs + H hs) = cubeAvg Qs F + cubeAvg Qs H := by
  classical
  induction Qs generalizing F H with
  | nil => rfl
  | cons Q Qs ih =>
    simp only [cubeAvg]
    calc
      (𝔼 q : Q, cubeAvg Qs (fun hs => F ((q : G) :: hs) + H ((q : G) :: hs))) =
          𝔼 q : Q, (cubeAvg Qs (fun hs => F ((q : G) :: hs)) +
            cubeAvg Qs (fun hs => H ((q : G) :: hs))) := by
        apply Finset.expect_congr rfl
        intro q hq
        exact ih (fun hs => F ((q : G) :: hs)) (fun hs => H ((q : G) :: hs))
      _ = _ := Finset.expect_add_distrib _ _ _

private theorem cubeAvg_real_sub (Qs : List (AddSubgroup G))
    (F H : List G → ℝ) :
    cubeAvg Qs (fun hs => F hs - H hs) = cubeAvg Qs F - cubeAvg Qs H := by
  classical
  induction Qs generalizing F H with
  | nil => rfl
  | cons Q Qs ih =>
    simp only [cubeAvg]
    calc
      (𝔼 q : Q, cubeAvg Qs (fun hs => F ((q : G) :: hs) - H ((q : G) :: hs))) =
          𝔼 q : Q, (cubeAvg Qs (fun hs => F ((q : G) :: hs)) -
            cubeAvg Qs (fun hs => H ((q : G) :: hs))) := by
        apply Finset.expect_congr rfl
        intro q hq
        exact ih (fun hs => F ((q : G) :: hs)) (fun hs => H ((q : G) :: hs))
      _ = _ := Finset.expect_sub_distrib _ _ _

private theorem cubeAvg_real_const (Qs : List (AddSubgroup G)) (c : ℝ) :
    cubeAvg Qs (fun _ => c) = c := by
  classical
  induction Qs with
  | nil => rfl
  | cons Q Qs ih => simp [cubeAvg, ih]

private theorem cubeAvg_real_nonneg (Qs : List (AddSubgroup G))
    (F : List G → ℝ) (hF : ∀ hs, 0 ≤ F hs) : 0 ≤ cubeAvg Qs F := by
  classical
  induction Qs generalizing F with
  | nil => exact hF []
  | cons Q Qs ih =>
    simp only [cubeAvg]
    exact Finset.expect_nonneg (fun q hq => ih
      (fun hs => F ((q : G) :: hs)) (fun hs => hF ((q : G) :: hs)))

private theorem cubeAvg_real_mono (Qs : List (AddSubgroup G))
    (F H : List G → ℝ) (h : ∀ hs, F hs ≤ H hs) : cubeAvg Qs F ≤ cubeAvg Qs H := by
  classical
  induction Qs generalizing F H with
  | nil => exact h []
  | cons Q Qs ih =>
    simp only [cubeAvg]
    exact Finset.expect_le_expect (fun q hq => ih
      (fun hs => F ((q : G) :: hs)) (fun hs => H ((q : G) :: hs))
      (fun hs => h ((q : G) :: hs)))

private theorem cubeAvg_real_pow_jensen (Qs : List (AddSubgroup G))
    (F : List G → ℝ) (hF : ∀ hs, 0 ≤ F hs) (N : ℕ) :
    (cubeAvg Qs F) ^ N ≤ cubeAvg Qs (fun hs => F hs ^ N) := by
  classical
  induction Qs generalizing F with
  | nil => rfl
  | cons Q Qs ih =>
    let A (q : Q) := cubeAvg Qs (fun hs => F ((q : G) :: hs))
    have hA0 (q : Q) : 0 ≤ A q :=
      cubeAvg_real_nonneg Qs (fun hs => F ((q : G) :: hs)) (fun hs => hF ((q : G) :: hs))
    calc
      (cubeAvg (Q :: Qs) F) ^ N = (𝔼 q : Q, A q) ^ N := by rfl
      _ ≤ 𝔼 q : Q, A q ^ N := expect_pow_jensen A hA0 N
      _ ≤ 𝔼 q : Q, cubeAvg Qs (fun hs => F ((q : G) :: hs) ^ N) := by
        apply Finset.expect_le_expect
        intro q hq
        exact ih (fun hs => F ((q : G) :: hs)) (fun hs => hF ((q : G) :: hs))
      _ = cubeAvg (Q :: Qs) (fun hs => F hs ^ N) := by rfl

private theorem cubeAvg_probWeighted_sum {ι : Type*} [Fintype ι]
    (π : ProbWeights ι) (Qs : List (AddSubgroup G)) (F : ι → List G → ℝ) :
    cubeAvg Qs (fun hs => ∑ i, π.w i * F i hs) =
      ∑ i, π.w i * cubeAvg Qs (F i) := by
  classical
  induction Qs generalizing F with
  | nil => simp [cubeAvg]
  | cons Q Qs ih =>
    simp only [cubeAvg]
    calc
      (𝔼 q : Q, cubeAvg Qs (fun hs => ∑ i, π.w i * F i ((q : G) :: hs))) =
          𝔼 q : Q, ∑ i, π.w i * cubeAvg Qs (fun hs => F i ((q : G) :: hs)) := by
        apply Finset.expect_congr rfl
        intro q hq
        exact ih (fun i hs => F i ((q : G) :: hs))
      _ = ∑ i, π.w i * 𝔼 q : Q, cubeAvg Qs (fun hs => F i ((q : G) :: hs)) := by
        rw [Finset.expect_sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.mul_expect Finset.univ
          (fun q : Q => cubeAvg Qs (fun hs => F i ((q : G) :: hs))) (π.w i)).symm
      _ = ∑ i, π.w i * cubeAvg (Q :: Qs) (F i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [cubeAvg]

private theorem cubeAvg_probWeighted_pow_jensen {ι : Type*} [Fintype ι]
    (π : ProbWeights ι) (Qs : ι → List (AddSubgroup G)) (F : ι → List G → ℝ)
    (hF : ∀ i hs, 0 ≤ F i hs) (N : ℕ) :
    (∑ i, π.w i * cubeAvg (Qs i) (F i)) ^ N ≤
      ∑ i, π.w i * cubeAvg (Qs i) (fun hs => F i hs ^ N) := by
  classical
  have hA0 (i : ι) : 0 ≤ cubeAvg (Qs i) (F i) :=
    cubeAvg_real_nonneg (Qs i) (F i) (hF i)
  calc
    (∑ i, π.w i * cubeAvg (Qs i) (F i)) ^ N ≤
        ∑ i, π.w i * (cubeAvg (Qs i) (F i)) ^ N :=
      probWeights_pow_jensen π (fun i => cubeAvg (Qs i) (F i)) hA0 N
    _ ≤ ∑ i, π.w i * cubeAvg (Qs i) (fun hs => F i hs ^ N) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (cubeAvg_real_pow_jensen (Qs i) (F i) (hF i) N) (π.nonneg i)

private theorem pow_sub_pow_le_mul (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hba : b ≤ a) (n : ℕ) :
    a ^ n - (a - b) ^ n ≤ (n : ℝ) * b := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc0 : 0 ≤ a - b := sub_nonneg.mpr hba
    have hc1 : a - b ≤ 1 := (sub_le_self a hb0).trans ha1
    have hpowA : a ^ n ≤ 1 := pow_le_one₀ ha0 ha1
    have hstep : a ^ (n + 1) - (a - b) ^ (n + 1) =
        a ^ n * b + (a - b) * (a ^ n - (a - b) ^ n) := by
      rw [pow_succ, pow_succ]
      ring
    calc
      a ^ (n + 1) - (a - b) ^ (n + 1) =
          a ^ n * b + (a - b) * (a ^ n - (a - b) ^ n) := hstep
      _ ≤ b + (a - b) * ((n : ℝ) * b) := by
        calc
          a ^ n * b + (a - b) * (a ^ n - (a - b) ^ n) ≤
              1 * b + (a - b) * ((n : ℝ) * b) := by
            exact add_le_add (mul_le_mul_of_nonneg_right hpowA hb0)
              (mul_le_mul_of_nonneg_left ih hc0)
          _ = _ := by ring
      _ ≤ b + 1 * ((n : ℝ) * b) := by
        calc
          b + (a - b) * ((n : ℝ) * b) =
              (a - b) * ((n : ℝ) * b) + b := by ring
          _ ≤ 1 * ((n : ℝ) * b) + b := add_le_add_left
            (mul_le_mul_of_nonneg_right hc1 (mul_nonneg (Nat.cast_nonneg n) hb0)) b
          _ = b + 1 * ((n : ℝ) * b) := by ring
      _ = ((n + 1 : ℕ) : ℝ) * b := by push_cast; ring

private theorem max_sub_pow_lower (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (n : ℕ) (hn : 1 ≤ n) :
    (max (a - b) 0) ^ n ≥ a ^ n - (n : ℝ) * b := by
  by_cases hba : b ≤ a
  · rw [max_eq_left (sub_nonneg.mpr hba)]
    have h := pow_sub_pow_le_mul a b ha0 ha1 hb0 hba n
    linarith
  · have hab : a ≤ b := le_of_not_ge hba
    rw [max_eq_right (sub_nonpos.mpr hab)]
    cases n with
    | zero => omega
    | succ n =>
      have hpowA : a ^ (n + 1) ≤ a := by
        rw [pow_succ]
        calc
          a ^ n * a ≤ 1 * a := mul_le_mul_of_nonneg_right (pow_le_one₀ ha0 ha1) ha0
          _ = a := by ring
      have hbn : b ≤ ((n + 1 : ℕ) : ℝ) * b := by
        rw [Nat.cast_succ]
        nlinarith [mul_nonneg (Nat.cast_nonneg n) hb0]
      have hle : a ^ (n + 1) ≤ ((n + 1 : ℕ) : ℝ) * b :=
        le_trans hpowA (le_trans hab hbn)
      have hsub : a ^ (n + 1) - ((n + 1 : ℕ) : ℝ) * b ≤ 0 := sub_nonpos.mpr hle
      simpa using hsub

open Classical in
private theorem cubeAvg_norm_le_one (Qs : List (AddSubgroup G)) (F : List G → ℂ)
    (hF : ∀ hs, ‖F hs‖ ≤ 1) : ‖cubeAvg Qs F‖ ≤ 1 := by
  classical
  induction Qs generalizing F with
  | nil => simpa [cubeAvg] using hF []
  | cons Q Qs ih =>
    change ‖𝔼 h : Q, cubeAvg Qs (fun hs => F (h :: hs))‖ ≤ 1
    calc
      ‖𝔼 h : Q, cubeAvg Qs (fun hs => F (h :: hs))‖ ≤
          𝔼 h : Q, ‖cubeAvg Qs (fun hs => F (h :: hs))‖ := RCLike.norm_expect_le (K := ℂ)
      _ ≤ 1 := Finset.expect_le Finset.univ_nonempty (fun h hh => ih _ (fun hs => hF (h :: hs)))

open Classical in
private noncomputable def concatPsi (K : List (AddSubgroup G)) (H : AddSubgroup G)
    (g : G → ℂ) (x : G) : ℂ :=
  cubeAvg K (fun ks => 𝔼 h : H,
    star (cubeRest g ks x) * cubeProd g ks (x + h))

private theorem expect_mul_star_expect {A B : Type*} [Fintype A] [Fintype B]
    (F : A → ℂ) (H : B → ℂ) :
    (𝔼 a : A, F a) * star (𝔼 b : B, H b) =
      𝔼 a : A, 𝔼 b : B, F a * star (H b) := by
  classical
  have hstar : star (𝔼 b : B, H b) = 𝔼 b : B, star (H b) := by
    simpa only [starRingEnd_apply] using
      (map_expect (starRingEnd ℂ) (fun b : B => H b) Finset.univ)
  rw [hstar]
  exact Finset.expect_mul_expect Finset.univ Finset.univ F (fun b => star (H b))

open Classical in
private theorem concatPsi_pair_correlation (K L : List (AddSubgroup G))
    (s : ℕ) (hK : K.length = s) (hL : L.length = s)
    (H J : AddSubgroup G) (g : G → ℂ) :
    (𝔼 x, concatPsi K H g x * star (concatPsi L J g x)) =
      𝔼 a : H, 𝔼 b : J,
        boxInnerList (K ++ L) (pairFamily s g (a : G) (b : G)) := by
  classical
  let Pair (ks ls : List G) (a : H) (b : J) (x : G) : ℂ :=
    psiIntegrand g ks (a : G) x * star (psiIntegrand g ls (b : G) x)
  have hbase (x : G) : concatPsi K H g x * star (concatPsi L J g x) =
      cubeAvg K (fun ks => cubeAvg L (fun ls =>
        𝔼 a : H, 𝔼 b : J, Pair ks ls a b x)) := by
    unfold concatPsi
    change cubeAvg K (fun ks => 𝔼 a : H, psiIntegrand g ks (a : G) x) *
        star (cubeAvg L (fun ls => 𝔼 b : J, psiIntegrand g ls (b : G) x)) = _
    rw [cubeAvg_mul_star_nested]
    apply cubeAvg_congr
    intro ks
    apply cubeAvg_congr
    intro ls
    exact expect_mul_star_expect
      (fun a : H => psiIntegrand g ks (a : G) x)
      (fun b : J => psiIntegrand g ls (b : G) x)
  have hcomm (ks ls : List G) :
      (𝔼 x, 𝔼 a : H, 𝔼 b : J, Pair ks ls a b x) =
        𝔼 a : H, 𝔼 b : J, 𝔼 x, Pair ks ls a b x := by
    calc
      _ = 𝔼 a : H, 𝔼 x, 𝔼 b : J, Pair ks ls a b x := by
        rw [Finset.expect_comm (Finset.univ : Finset G) (Finset.univ : Finset H)]
      _ = _ := by
        apply Finset.expect_congr rfl
        intro a ha
        exact Finset.expect_comm (Finset.univ : Finset G) (Finset.univ : Finset J) _
  have hbox (a : H) (b : J) :
      boxInnerList (K ++ L) (pairFamily s g (a : G) (b : G)) =
        cubeAvg K (fun ks => cubeAvg L (fun ls => 𝔼 x, Pair ks ls a b x)) := by
    calc
      boxInnerList (K ++ L) (pairFamily s g (a : G) (b : G)) =
          cubeAvg (K ++ L) (fun hs =>
            𝔼 x, mixedCubeProductList (pairFamily s g (a : G) (b : G)) hs x) :=
        boxInnerList_cube _ _
      _ = cubeAvg K (fun ks => cubeAvg L (fun ls =>
            𝔼 x, mixedCubeProductList (pairFamily s g (a : G) (b : G)) (ks ++ ls) x)) :=
        cubeAvg_concat K L _
      _ = cubeAvg K (fun ks => cubeAvg L (fun ls => 𝔼 x, Pair ks ls a b x)) := by
        apply cubeAvg_congr_valid
        intro ks hkslen
        apply cubeAvg_congr_valid
        intro ls hlslen
        apply Finset.expect_congr rfl
        intro x hx
        have hks : ks.length = s := hkslen.trans hK
        have hls : ls.length = s := hlslen.trans hL
        exact pairMixedCubeProductList s g (a : G) (b : G) ks ls hks hls x
  calc
    (𝔼 x, concatPsi K H g x * star (concatPsi L J g x)) =
        𝔼 x, cubeAvg K (fun ks => cubeAvg L (fun ls =>
          𝔼 a : H, 𝔼 b : J, Pair ks ls a b x)) := by
      apply Finset.expect_congr rfl
      intro x hx
      exact hbase x
    _ = cubeAvg K (fun ks => cubeAvg L (fun ls =>
          𝔼 x, 𝔼 a : H, 𝔼 b : J, Pair ks ls a b x)) := by
      exact (cubeAvg_nested_expect K L
        (fun ks ls x => 𝔼 a : H, 𝔼 b : J, Pair ks ls a b x)).symm
    _ = cubeAvg K (fun ks => cubeAvg L (fun ls =>
          𝔼 a : H, 𝔼 b : J, 𝔼 x, Pair ks ls a b x)) := by
      apply cubeAvg_congr
      intro ks
      apply cubeAvg_congr
      intro ls
      exact hcomm ks ls
    _ = 𝔼 a : H, 𝔼 b : J, cubeAvg K (fun ks => cubeAvg L (fun ls =>
          𝔼 x, Pair ks ls a b x)) := by
      calc
        _ = 𝔼 a : H, cubeAvg K (fun ks => cubeAvg L (fun ls =>
              𝔼 b : J, 𝔼 x, Pair ks ls a b x)) :=
          cubeAvg_nested_expect K L
            (fun ks ls a => 𝔼 b : J, 𝔼 x, Pair ks ls a b x)
        _ = _ := by
          apply Finset.expect_congr rfl
          intro a ha
          exact cubeAvg_nested_expect K L
            (fun ks ls b => 𝔼 x, Pair ks ls a b x)
    _ = 𝔼 a : H, 𝔼 b : J, boxInnerList (K ++ L)
          (pairFamily s g (a : G) (b : G)) := by
      apply Finset.expect_congr rfl
      intro a ha
      apply Finset.expect_congr rfl
      intro b hb
      exact (hbox a b).symm

private theorem concatPsi_norm_le_one (K : List (AddSubgroup G)) (H : AddSubgroup G)
    (g : G → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1) (x : G) : ‖concatPsi K H g x‖ ≤ 1 := by
  classical
  apply cubeAvg_norm_le_one
  intro ks
  calc
    ‖𝔼 h : H, star (cubeRest g ks x) * cubeProd g ks (x + h)‖ ≤
        𝔼 h : H, ‖star (cubeRest g ks x) * cubeProd g ks (x + h)‖ :=
      RCLike.norm_expect_le (K := ℂ)
    _ ≤ 1 := by
      apply Finset.expect_le Finset.univ_nonempty
      intro h hh
      rw [norm_mul, norm_star]
      have hr := cubeRest_norm_le_one g hg ks x
      have hp := cubeProd_norm_le_one g hg ks (x + h)
      have hn₁ := norm_nonneg (cubeRest g ks x)
      have hn₂ := norm_nonneg (cubeProd g ks (x + h))
      nlinarith

private theorem boxMoment_root_split (K : List (AddSubgroup G)) (H : AddSubgroup G)
    (g : G → ℂ) :
    boxMoment (K ++ [H]) g = 𝔼 x, g x * star (concatPsi K H g x) := by
  classical
  calc
    boxMoment (K ++ [H]) g =
        cubeAvg K (fun ks => boxMoment [H] (cubeProd g ks)) := boxMoment_append K [H] g
    _ = cubeAvg K (fun ks => 𝔼 x, cubeProd g ks x *
        star (avgOn H (cubeProd g ks) x)) := by
      simp_rw [boxMoment_singleton_corr]
    _ = 𝔼 x, cubeAvg K (fun ks => cubeProd g ks x *
        star (avgOn H (cubeProd g ks) x)) :=
      cubeAvg_expect_comm K (fun ks x => cubeProd g ks x *
        star (avgOn H (cubeProd g ks) x))
    _ = 𝔼 x, g x * star (concatPsi K H g x) := by
      apply Finset.expect_congr rfl
      intro x hx
      unfold concatPsi
      calc
        cubeAvg K (fun ks => cubeProd g ks x *
            star (avgOn H (cubeProd g ks) x)) =
          cubeAvg K (fun ks => g x * star (𝔼 h : H,
            star (cubeRest g ks x) * cubeProd g ks (x + h))) := by
          apply cubeAvg_congr
          intro ks
          have hrest := cubeProd_factor g ks x
          have hstar : star (avgOn H (cubeProd g ks) x) =
              𝔼 h : H, star (cubeProd g ks (x + h)) := by
            simpa only [avgOn, starRingEnd_apply] using
              (map_expect (starRingEnd ℂ) (fun h : H => cubeProd g ks (x + h)) Finset.univ)
          rw [hrest, hstar]
          let R := cubeRest g ks x
          calc
            (g x * R) * 𝔼 h : H, star (cubeProd g ks (x + h)) =
                g x * 𝔼 h : H, R * star (cubeProd g ks (x + h)) := by
              rw [← Finset.mul_expect]
              ring
            _ = g x * star (𝔼 h : H, star R * cubeProd g ks (x + h)) := by
              congr 1
              calc
                (𝔼 h : H, R * star (cubeProd g ks (x + h))) =
                    𝔼 h : H, star (star R * cubeProd g ks (x + h)) := by
                  apply Finset.expect_congr rfl
                  intro h hh
                  simp [R, star_mul, star_star, mul_comm]
                _ = star (𝔼 h : H, star R * cubeProd g ks (x + h)) := by
                  symm
                  exact map_expect (starRingEnd ℂ)
                    (fun h : H => star R * cubeProd g ks (x + h)) Finset.univ
        _ = g x * cubeAvg K (fun ks =>
            star (𝔼 h : H, star (cubeRest g ks x) * cubeProd g ks (x + h))) := by
          exact cubeAvg_mul_left K (g x) _
        _ = g x * star (cubeAvg K (fun ks =>
            𝔼 h : H, star (cubeRest g ks x) * cubeProd g ks (x + h))) := by
          congr 1
          exact (cubeAvg_star K (fun ks =>
            𝔼 h : H, star (cubeRest g ks x) * cubeProd g ks (x + h))).symm

private noncomputable def concatPsiMix {ι : Type*} [Fintype ι]
    (π : ProbWeights ι) (H : ι → AddSubgroup G) (K : ι → List (AddSubgroup G))
    (g : G → ℂ) (x : G) : ℂ :=
  ∑ i, (π.w i : ℂ) * concatPsi (K i) (H i) g x

private theorem concat_root_cs {ι : Type*} [Fintype ι] (π : ProbWeights ι)
    (H : ι → AddSubgroup G) (K : ι → List (AddSubgroup G)) (g : G → ℂ)
    (hg : ∀ x, ‖g x‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hyp : δ ≤ ∑ i, π.w i * (boxMoment (K i ++ [H i]) g).re) :
    δ ^ 2 ≤ 𝔼 x, ‖concatPsiMix π H K g x‖ ^ 2 := by
  classical
  have hcomplex :
      (𝔼 x, g x * star (concatPsiMix π H K g x)) =
        ∑ i, (π.w i : ℂ) * boxMoment (K i ++ [H i]) g := by
    calc
      (𝔼 x, g x * star (concatPsiMix π H K g x)) =
          𝔼 x, ∑ i, (π.w i : ℂ) * (g x * star (concatPsi (K i) (H i) g x)) := by
        apply Finset.expect_congr rfl
        intro x hx
        simp [concatPsiMix, map_sum, star_sum, star_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, (π.w i : ℂ) *
          (𝔼 x, g x * star (concatPsi (K i) (H i) g x)) := by
        rw [Finset.expect_sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.mul_expect Finset.univ
          (fun x => g x * star (concatPsi (K i) (H i) g x)) (π.w i : ℂ)).symm
      _ = ∑ i, (π.w i : ℂ) * boxMoment (K i ++ [H i]) g := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← boxMoment_root_split]
  have hroot :
      (∑ i, π.w i * (boxMoment (K i ++ [H i]) g).re) =
        (𝔼 x, g x * star (concatPsiMix π H K g x)).re := by
    calc
      _ = (∑ i, (π.w i : ℂ) * boxMoment (K i ++ [H i]) g).re := by
        simp [Complex.re_sum]
      _ = _ := congrArg Complex.re hcomplex.symm
  have hδroot : δ ≤ (𝔼 x, g x * star (concatPsiMix π H K g x)).re := by
    rw [← hroot]
    exact hyp
  have hcorr : δ ≤ ‖𝔼 x, g x * star (concatPsiMix π H K g x)‖ :=
    hδroot.trans (Complex.re_le_norm _)
  have hpow : δ ^ 2 ≤ ‖𝔼 x, g x * star (concatPsiMix π H K g x)‖ ^ 2 :=
    pow_le_pow_left₀ hδ hcorr 2
  have hcs := norm_expect_mul_star_sq_le
    (fun x => g x) (fun x => concatPsiMix π H K g x)
  have hg2 : (𝔼 x, ‖g x‖ ^ 2) ≤ 1 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro x hx
    have hn := norm_nonneg (g x)
    have hb := hg x
    nlinarith
  have hpsi2 : 0 ≤ (𝔼 x, ‖concatPsiMix π H K g x‖ ^ 2) :=
    Finset.expect_nonneg (fun x hx => sq_nonneg _)
  nlinarith [mul_nonneg (sub_nonneg.mpr hg2) hpsi2]

open Classical in
private theorem expect_sub_sup (A B : AddSubgroup G) (φ : G → ℂ) :
    (𝔼 a : A, 𝔼 b : B, φ ((b : G) - a)) =
      𝔼 c : (A ⊔ B : AddSubgroup G), φ c := by
  classical
  calc
    (𝔼 a : A, 𝔼 b : B, φ ((b : G) - a)) =
        𝔼 a : A, 𝔼 b : B, φ (-(a : G) + b) := by
      apply Finset.expect_congr rfl
      intro a ha
      apply Finset.expect_congr rfl
      intro b hb
      congr 1
      abel
    _ = 𝔼 a : A, 𝔼 b : B, φ ((a : G) + b) := by
      apply Fintype.expect_equiv (Equiv.neg A)
      intro a
      apply Finset.expect_congr rfl
      intro b hb
      congr 1
    _ = 𝔼 c : (A ⊔ B : AddSubgroup G), φ c := expect_add_sup A B φ

open Classical in
private theorem avgOn_pair_sup_boxMoment (A B : AddSubgroup G) (g : G → ℂ) :
    (𝔼 x, avgOn A g x * star (avgOn B g x)) = boxMoment [A ⊔ B] g := by
  classical
  have hprod (x : G) : avgOn A g x * star (avgOn B g x) =
      𝔼 a : A, 𝔼 b : B, g (x + a) * star (g (x + b)) := by
    rw [avgOn]
    change (𝔼 a : A, g (x + a)) *
      star (𝔼 b : B, g (x + b)) = _
    have hstar : star (𝔼 b : B, g (x + b)) =
        𝔼 b : B, star (g (x + b)) := by
      simpa only [starRingEnd_apply] using
        (map_expect (starRingEnd ℂ) (fun b : B => g (x + b)) Finset.univ)
    rw [hstar]
    exact Finset.expect_mul_expect Finset.univ Finset.univ
      (fun a : A => g (x + a)) (fun b : B => star (g (x + b)))
  have hshift (a : A) (b : B) :
      (𝔼 x, g (x + a) * star (g (x + b))) =
        𝔼 x, g x * star (g (x + ((b : G) - a))) := by
    let φ : G → ℂ := fun y => g y * star (g (y + ((b : G) - a)))
    calc
      (𝔼 x, g (x + a) * star (g (x + b))) = 𝔼 x, φ (x + a) := by
        apply Finset.expect_congr rfl
        intro x hx
        dsimp [φ]
        congr 2
        abel
      _ = 𝔼 x, φ x := expect_add_translate (a : G) φ
  calc
    (𝔼 x, avgOn A g x * star (avgOn B g x)) =
        𝔼 x, 𝔼 a : A, 𝔼 b : B, g (x + a) * star (g (x + b)) := by
      apply Finset.expect_congr rfl
      intro x hx
      exact hprod x
    _ = 𝔼 a : A, 𝔼 b : B, 𝔼 x, g (x + a) * star (g (x + b)) := by
      rw [Finset.expect_comm (Finset.univ : Finset G) (Finset.univ : Finset A)]
      apply Finset.expect_congr rfl
      intro a ha
      exact Finset.expect_comm (Finset.univ : Finset G) (Finset.univ : Finset B) _
    _ = 𝔼 a : A, 𝔼 b : B,
        𝔼 x, g x * star (g (x + ((b : G) - a))) := by
      apply Finset.expect_congr rfl
      intro a ha
      apply Finset.expect_congr rfl
      intro b hb
      exact hshift a b
    _ = 𝔼 c : (A ⊔ B : AddSubgroup G),
        𝔼 x, g x * star (g (x + c)) := by
      simpa using (expect_sub_sup A B (fun c => 𝔼 x, g x * star (g (x + c))))
    _ = 𝔼 x, g x * star (avgOn (A ⊔ B : AddSubgroup G) g x) := by
      rw [Finset.expect_comm (Finset.univ : Finset (A ⊔ B : AddSubgroup G))
        (Finset.univ : Finset G)]
      apply Finset.expect_congr rfl
      intro x hx
      change 𝔼 c : (A ⊔ B : AddSubgroup G), g x * star (g (x + c)) = _
      simp only [avgOn]
      calc
        (𝔼 c : (A ⊔ B : AddSubgroup G), g x * star (g (x + c))) =
            g x * 𝔼 c : (A ⊔ B : AddSubgroup G), star (g (x + c)) :=
        (Finset.mul_expect Finset.univ
          (fun c : (A ⊔ B : AddSubgroup G) => star (g (x + c))) (g x)).symm
        _ = g x * star (𝔼 c : (A ⊔ B : AddSubgroup G), g (x + c)) := by
          congr 1
          simpa only [starRingEnd_apply] using
            (map_expect (starRingEnd ℂ)
              (fun c : (A ⊔ B : AddSubgroup G) => g (x + c)) Finset.univ).symm
    _ = boxMoment [A ⊔ B] g := (boxMoment_singleton_corr (A ⊔ B) g).symm

private theorem cubeProd_crossDerivative (f g : G → ℂ) (h : G) (hs : List G) (x : G) :
    cubeProd (crossDeriv f g h) hs x =
      cubeProd f hs x * star (cubeProd g hs (x + h)) := by
  induction hs generalizing f g x with
  | nil => simp [cubeProd, crossDeriv]
  | cons k hs ih =>
    calc
      cubeProd (crossDeriv f g h) (k :: hs) x =
          cubeProd (mderiv (crossDeriv f g h) k) hs x := rfl
      _ = cubeProd (crossDeriv (mderiv f k) (mderiv g k) h) hs x := by
        rw [mderiv_crossDeriv]
      _ = cubeProd (mderiv f k) hs x *
          star (cubeProd (mderiv g k) hs (x + h)) := ih (mderiv f k) (mderiv g k) x
      _ = cubeProd f (k :: hs) x * star (cubeProd g (k :: hs) (x + h)) := rfl

private theorem boxMoment_translate (Qs : List (AddSubgroup G)) (f : G → ℂ) (t : G) :
    boxMoment Qs (fun x => f (x + t)) = boxMoment Qs f := by
  induction Qs generalizing f with
  | nil => exact expect_add_translate t f
  | cons Q Qs ih =>
    simp only [boxMoment]
    apply Finset.expect_congr rfl
    intro h hh
    have hder : mderiv (fun x => f (x + t)) h = fun x => mderiv f h (x + t) := by
      funext x
      simp [mderiv, add_assoc, add_comm, add_left_comm]
    calc
      boxMoment Qs (mderiv (fun x => f (x + t)) h) =
          boxMoment Qs (fun x => mderiv f h (x + t)) := congrArg (boxMoment Qs) hder
      _ = boxMoment Qs (mderiv f h) := ih (mderiv f h)

private theorem singleton_append_perm (Q : AddSubgroup G) :
    ∀ Ks : List (AddSubgroup G), ([Q] ++ Ks).Perm (Ks ++ [Q])
  | [] => by simp
  | R :: Rs => by
      simpa only [List.singleton_append, List.cons_append, List.nil_append] using
        (List.Perm.swap R Q Rs).trans (List.Perm.cons R (singleton_append_perm Q Rs))

open Classical in
private theorem boxMoment_avg_root (K : List (AddSubgroup G))
    (A B : AddSubgroup G) (g : G → ℂ) :
    (𝔼 a : A, 𝔼 b : B, boxMoment K
      (fun x => g (x + a) * star (g (x + b)))) =
        boxMoment (K ++ [A ⊔ B]) g := by
  classical
  calc
    (𝔼 a : A, 𝔼 b : B, boxMoment K
        (fun x => g (x + a) * star (g (x + b)))) =
      𝔼 a : A, 𝔼 b : B, boxMoment K
        (fun x => crossDeriv g g ((b : G) - a) (x + a)) := by
      apply Finset.expect_congr rfl
      intro a ha
      apply Finset.expect_congr rfl
      intro b hb
      apply congrArg (boxMoment K)
      funext x
      dsimp [crossDeriv]
      congr 2
      abel
    _ = 𝔼 a : A, 𝔼 b : B, boxMoment K (crossDeriv g g ((b : G) - a)) := by
      apply Finset.expect_congr rfl
      intro a ha
      apply Finset.expect_congr rfl
      intro b hb
      exact boxMoment_translate K (crossDeriv g g ((b : G) - a)) a
    _ = 𝔼 c : (A ⊔ B : AddSubgroup G), boxMoment K (crossDeriv g g c) := by
      exact expect_sub_sup A B (fun c => boxMoment K (crossDeriv g g c))
    _ = boxMoment ([A ⊔ B] ++ K) g := by
      symm
      rw [boxMoment_append]
      simp only [cubeAvg, cubeProd, mderiv, crossDeriv]
      apply Finset.expect_congr rfl
      intro c hc
      rfl
    _ = boxMoment (K ++ [A ⊔ B]) g :=
      boxMoment_perm (singleton_append_perm (A ⊔ B) K) g

private theorem weighted_complex_square {ι : Type*} [Fintype ι] (π : ProbWeights ι)
    (F : ι → G → ℂ) :
    (𝔼 x, ‖∑ i, (π.w i : ℂ) * F i x‖ ^ 2) =
      ∑ i, ∑ j, π.w i * π.w j * (𝔼 x, F i x * star (F j x)).re := by
  classical
  let ψ (x : G) := ∑ i, (π.w i : ℂ) * F i x
  have hstar (x : G) : star (ψ x) = ∑ j, (π.w j : ℂ) * star (F j x) := by
    dsimp [ψ]
    calc
      star (∑ i, (π.w i : ℂ) * F i x) =
          ∑ i, star ((π.w i : ℂ) * F i x) := map_sum (starRingEnd ℂ) _ _
      _ = ∑ i, (π.w i : ℂ) * star (F i x) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp
  have hprod (x : G) : ψ x * star (ψ x) =
      ∑ i, ∑ j, (π.w i : ℂ) * (π.w j : ℂ) * (F i x * star (F j x)) := by
    calc
      ψ x * star (ψ x) =
          (∑ i, (π.w i : ℂ) * F i x) *
            (∑ j, (π.w j : ℂ) * star (F j x)) := by
        rw [hstar]
      _ = ∑ i, ((π.w i : ℂ) * F i x) *
            ∑ j, (π.w j : ℂ) * star (F j x) := Finset.sum_mul ..
      _ = ∑ i, ∑ j, (π.w i : ℂ) * (π.w j : ℂ) *
            (F i x * star (F j x)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hmean : (𝔼 x, ψ x * star (ψ x)) =
      ∑ i, ∑ j, (π.w i : ℂ) * (π.w j : ℂ) * (𝔼 x, F i x * star (F j x)) := by
    calc
      (𝔼 x, ψ x * star (ψ x)) =
          𝔼 x, ∑ i, ∑ j, (π.w i : ℂ) * (π.w j : ℂ) * (F i x * star (F j x)) := by
        apply Finset.expect_congr rfl
        intro x hx
        exact hprod x
      _ = ∑ i, ∑ j, (π.w i : ℂ) * (π.w j : ℂ) *
            (𝔼 x, F i x * star (F j x)) := by
        rw [Finset.expect_sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.expect_sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        exact (Finset.mul_expect Finset.univ
          (fun x => F i x * star (F j x)) ((π.w i : ℂ) * (π.w j : ℂ))).symm
  calc
    (𝔼 x, ‖ψ x‖ ^ 2) = (𝔼 x, (ψ x * star (ψ x)).re) := by
      apply Finset.expect_congr rfl
      intro x hx
      have hz : (ψ x * star (ψ x)).re = ‖ψ x‖ ^ 2 := by
        change (ψ x * (starRingEnd ℂ) (ψ x)).re = _
        rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      exact hz.symm
    _ = (𝔼 x, ψ x * star (ψ x)).re := by rw [Complex.re_expect]
    _ = _ := by
      rw [hmean]
      simp [Complex.re_sum, Complex.mul_re]

private theorem concat_step_zero {ι : Type*} [Fintype ι] (π : ProbWeights ι)
    (H : ι → AddSubgroup G) (g : G → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hyp : δ ≤ ∑ i, π.w i * (boxMoment [H i] g).re) :
    δ ^ 2 ≤ ∑ i, ∑ j, π.w i * π.w j *
      (boxMoment [H i ⊔ H j] g).re := by
  classical
  have hrootHyp : δ ≤ ∑ i, π.w i * (boxMoment (([] : List (AddSubgroup G)) ++ [H i]) g).re := by
    simpa using hyp
  have hcs := concat_root_cs π H (fun _ => []) g hg hδ hrootHyp
  have hpsi (x : G) : concatPsiMix π H (fun _ => []) g x =
      ∑ i, (π.w i : ℂ) * avgOn (H i) g x := by
    simp [concatPsiMix, concatPsi, cubeAvg, cubeRest, cubeProd, avgOn]
  have hsum : (𝔼 x, ‖concatPsiMix π H (fun _ => []) g x‖ ^ 2) =
      ∑ i, ∑ j, π.w i * π.w j * (boxMoment [H i ⊔ H j] g).re := by
    calc
      (𝔼 x, ‖concatPsiMix π H (fun _ => []) g x‖ ^ 2) =
          𝔼 x, ‖∑ i, (π.w i : ℂ) * avgOn (H i) g x‖ ^ 2 := by
        apply Finset.expect_congr rfl
        intro x hx
        rw [hpsi]
      _ = ∑ i, ∑ j, π.w i * π.w j *
          (𝔼 x, avgOn (H i) g x * star (avgOn (H j) g x)).re :=
        weighted_complex_square π (fun i => avgOn (H i) g)
      _ = ∑ i, ∑ j, π.w i * π.w j * (boxMoment [H i ⊔ H j] g).re := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [avgOn_pair_sup_boxMoment]
  calc
    δ ^ 2 ≤ 𝔼 x, ‖concatPsiMix π H (fun _ => []) g x‖ ^ 2 := hcs
    _ = ∑ i, ∑ j, π.w i * π.w j * (boxMoment [H i ⊔ H j] g).re := hsum

-- C5 (KKL Lemma 6.1, subgroup form, weighted index law, B = G)
theorem concat_step {ι : Type*} [Fintype ι] (π : ProbWeights ι) (s : ℕ)
    (H : ι → AddSubgroup G) (K : ι → List (AddSubgroup G)) (hK : ∀ i, (K i).length = s)
    (g : G → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hyp : δ ≤ ∑ i, π.w i * (boxMoment (K i ++ [H i]) g).re) :
    δ ^ (2 ^ (2 * s + 1)) ≤
      ∑ i, ∑ j, π.w i * π.w j * (boxMoment (K i ++ K j ++ [H i ⊔ H j]) g).re := by
  classical
  by_cases hs0 : s = 0
  · have hK0 : ∀ i, K i = [] := by
      intro i
      exact List.eq_nil_of_length_eq_zero (by simpa [hs0] using hK i)
    have hyp0 : δ ≤ ∑ i, π.w i * (boxMoment [H i] g).re := by
      simpa [hK0] using hyp
    have hzero := concat_step_zero π H g hg hδ hyp0
    simpa [hs0, hK0] using hzero
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs0
    let P : ℕ := 2 ^ (2 * s)
    let S (i j : ι) : ℝ :=
      𝔼 a : H i, 𝔼 b : H j,
        boxNorm (K i ++ K j) (rootCorrelation g (a : G) (b : G))
    have hpairLen (i j : ι) : (K i ++ K j).length = 2 * s := by
      simp [List.length_append, hK i, hK j, two_mul]
    have hpairNe (i j : ι) : K i ++ K j ≠ [] := by
      intro hz
      have hlen0 := congrArg List.length hz
      simp [hpairLen i j] at hlen0
      omega
    have hS0 (i j : ι) : 0 ≤ S i j := by
      dsimp [S]
      apply Finset.expect_nonneg
      intro a ha
      apply Finset.expect_nonneg
      intro b hb
      exact boxNorm_nonneg (hpairNe i j) _
    have hcorr (i j : ι) :
        (𝔼 x, concatPsi (K i) (H i) g x *
          star (concatPsi (K j) (H j) g x)).re ≤ S i j := by
      rw [concatPsi_pair_correlation (K i) (K j) s (hK i) (hK j)
        (H i) (H j) g]
      simp_rw [Complex.re_expect]
      dsimp [S]
      apply Finset.expect_le_expect
      intro a ha
      apply Finset.expect_le_expect
      intro b hb
      calc
        (boxInnerList (K i ++ K j) (pairFamily s g (a : G) (b : G))).re ≤
            ‖boxInnerList (K i ++ K j) (pairFamily s g (a : G) (b : G))‖ :=
          Complex.re_le_norm _
        _ ≤ boxNorm (K i ++ K j) (rootCorrelation g (a : G) (b : G)) :=
          pairFamily_GCS_root_bound (K i) (K j) s (hK i) (hK j) hspos
            g hg (a : G) (b : G)
    have hrootAvg (i j : ι) :
        𝔼 a : H i, 𝔼 b : H j,
          (boxMoment (K i ++ K j)
            (rootCorrelation g (a : G) (b : G))).re =
          (boxMoment (K i ++ K j ++ [H i ⊔ H j]) g).re := by
      have hcomplex :
          𝔼 a : H i, 𝔼 b : H j,
            boxMoment (K i ++ K j) (rootCorrelation g (a : G) (b : G)) =
          boxMoment (K i ++ K j ++ [H i ⊔ H j]) g := by
        change 𝔼 a : H i, 𝔼 b : H j,
            boxMoment (K i ++ K j)
              (fun x => g (x + (a : G)) * star (g (x + (b : G)))) = _
        exact boxMoment_avg_root (K i ++ K j) (H i) (H j) g
      calc
        𝔼 a : H i, 𝔼 b : H j,
            (boxMoment (K i ++ K j) (rootCorrelation g (a : G) (b : G))).re =
          𝔼 a : H i,
            (𝔼 b : H j, boxMoment (K i ++ K j)
              (rootCorrelation g (a : G) (b : G))).re := by
          apply Finset.expect_congr rfl
          intro a ha
          exact (Complex.re_expect (Finset.univ : Finset (H j))
            (fun b => boxMoment (K i ++ K j)
              (rootCorrelation g (a : G) (b : G)))).symm
        _ = (𝔼 a : H i, 𝔼 b : H j,
            boxMoment (K i ++ K j) (rootCorrelation g (a : G) (b : G))).re :=
          (Complex.re_expect (Finset.univ : Finset (H i))
            (fun a => 𝔼 b : H j, boxMoment (K i ++ K j)
              (rootCorrelation g (a : G) (b : G)))).symm
        _ = _ := congrArg Complex.re hcomplex
    have hSijPow (i j : ι) : S i j ^ P ≤
        (boxMoment (K i ++ K j ++ [H i ⊔ H j]) g).re := by
      let B (a : H i) (b : H j) : ℝ :=
        boxNorm (K i ++ K j) (rootCorrelation g (a : G) (b : G))
      have hB0 (a : H i) (b : H j) : 0 ≤ B a b :=
        boxNorm_nonneg (hpairNe i j) _
      have hBavg0 (a : H i) : 0 ≤ 𝔼 b : H j, B a b :=
        Finset.expect_nonneg (fun b hb => hB0 a b)
      have hJb (a : H i) :
          (𝔼 b : H j, B a b) ^ P ≤ 𝔼 b : H j, B a b ^ P :=
        expect_pow_jensen (fun b : H j => B a b) (fun b => hB0 a b) P
      have hJa :
          (𝔼 a : H i, 𝔼 b : H j, B a b) ^ P ≤
            𝔼 a : H i, (𝔼 b : H j, B a b) ^ P :=
        expect_pow_jensen (fun a : H i => 𝔼 b : H j, B a b)
          (fun a => hBavg0 a) P
      calc
        S i j ^ P = (𝔼 a : H i, 𝔼 b : H j, B a b) ^ P := by rfl
        _ ≤ 𝔼 a : H i, (𝔼 b : H j, B a b) ^ P := hJa
        _ ≤ 𝔼 a : H i, 𝔼 b : H j, B a b ^ P := by
          apply Finset.expect_le_expect
          intro a ha
          exact hJb a
        _ = 𝔼 a : H i, 𝔼 b : H j,
              (boxMoment (K i ++ K j) (rootCorrelation g (a : G) (b : G))).re := by
          apply Finset.expect_congr rfl
          intro a ha
          apply Finset.expect_congr rfl
          intro b hb
          dsimp [B]
          rw [show P = 2 ^ (K i ++ K j).length by
            dsimp [P]
            rw [hpairLen i j], boxNorm_pow (hpairNe i j) _]
        _ = (boxMoment (K i ++ K j ++ [H i ⊔ H j]) g).re := hrootAvg i j
    let T (i : ι) : ℝ := ∑ j, π.w j * S i j
    let W : ℝ := ∑ i, π.w i * T i
    have hT0 (i : ι) : 0 ≤ T i := by
      dsimp [T]
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (π.nonneg j) (hS0 i j)
    have hmeanS : (∑ i, π.w i * ∑ j, π.w j * S i j) = W := by rfl
    have hWpow : W ^ P ≤ ∑ i, ∑ j, π.w i * π.w j * S i j ^ P := by
      calc
        W ^ P = (∑ i, π.w i * T i) ^ P := by rfl
        _ ≤ ∑ i, π.w i * T i ^ P := probWeights_pow_jensen π T hT0 P
        _ ≤ ∑ i, π.w i * (∑ j, π.w j * S i j ^ P) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left
            (probWeights_pow_jensen π (fun j => S i j) (fun j => hS0 i j) P)
            (π.nonneg i)
        _ = ∑ i, ∑ j, π.w i * π.w j * S i j ^ P := by
          simp_rw [Finset.mul_sum, mul_assoc]
    have htarget :
        (∑ i, ∑ j, π.w i * π.w j * S i j ^ P) ≤
          ∑ i, ∑ j, π.w i * π.w j *
            (boxMoment (K i ++ K j ++ [H i ⊔ H j]) g).re := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hSijPow i j)
        (mul_nonneg (π.nonneg i) (π.nonneg j))
    have hdelta : δ ^ 2 ≤ W := by
      have hroot := concat_root_cs π H K g hg hδ hyp
      have hmix : (𝔼 x, ‖concatPsiMix π H K g x‖ ^ 2) =
          ∑ i, ∑ j, π.w i * π.w j *
            (𝔼 x, concatPsi (K i) (H i) g x *
              star (concatPsi (K j) (H j) g x)).re := by
        simpa [concatPsiMix] using weighted_complex_square π
          (fun i => concatPsi (K i) (H i) g)
      calc
        δ ^ 2 ≤ 𝔼 x, ‖concatPsiMix π H K g x‖ ^ 2 := hroot
        _ = ∑ i, ∑ j, π.w i * π.w j *
            (𝔼 x, concatPsi (K i) (H i) g x *
              star (concatPsi (K j) (H j) g x)).re := hmix
        _ ≤ ∑ i, ∑ j, π.w i * π.w j * S i j := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (hcorr i j)
            (mul_nonneg (π.nonneg i) (π.nonneg j))
        _ = W := by
          calc
            (∑ i, ∑ j, π.w i * π.w j * S i j) =
                ∑ i, π.w i * ∑ j, π.w j * S i j := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = W := hmeanS
    have hpow : (δ ^ 2) ^ P ≤
        ∑ i, ∑ j, π.w i * π.w j *
          (boxMoment (K i ++ K j ++ [H i ⊔ H j]) g).re := by
      calc
        (δ ^ 2) ^ P ≤ W ^ P := pow_le_pow_left₀ (sq_nonneg δ) hdelta P
        _ ≤ ∑ i, ∑ j, π.w i * π.w j * S i j ^ P := hWpow
        _ ≤ _ := htarget
    have hExp : 2 * P = 2 ^ (2 * s + 1) := by
      dsimp [P]
      calc
        2 * 2 ^ (2 * s) = 2 ^ (2 * s) * 2 := Nat.mul_comm _ _
        _ = 2 ^ (2 * s + 1) := by rw [pow_succ]
    calc
      δ ^ (2 ^ (2 * s + 1)) = (δ ^ 2) ^ P := by
        rw [← hExp, pow_mul]
      _ ≤ ∑ i, ∑ j, π.w i * π.w j *
          (boxMoment (K i ++ K j ++ [H i ⊔ H j]) g).re := hpow

-- C6 (generic pairs)
theorem replace_generic {ι : Type*} [Fintype ι] (π : ProbWeights ι)
    (H : ι → AddSubgroup G) (L : ι → ι → List (AddSubgroup G)) (g : G → ℂ)
    (hg : ∀ x, ‖g x‖ ≤ 1) :
    (∑ i, ∑ j, π.w i * π.w j * (boxMoment (L i j ++ [H i ⊔ H j]) g).re) - badPairMass π H ≤
      ∑ i, ∑ j, π.w i * π.w j * (boxMoment (L i j ++ [⊤]) g).re := by
  classical
  have hpoint (i j : ι) :
      π.w i * π.w j * (boxMoment (L i j ++ [H i ⊔ H j]) g).re ≤
        π.w i * π.w j * (boxMoment (L i j ++ [⊤]) g).re +
          (if H i ⊔ H j = ⊤ then 0 else π.w i * π.w j) := by
    have hloc0 : 0 ≤ (boxMoment (L i j ++ [H i ⊔ H j]) g).re :=
      boxMoment_re_nonneg (by simp) g
    have hloc1 : (boxMoment (L i j ++ [H i ⊔ H j]) g).re ≤ 1 :=
      boxMoment_re_le_one _ g hg
    have hfull0 : 0 ≤ (boxMoment (L i j ++ [⊤]) g).re :=
      boxMoment_re_nonneg (by simp) g
    by_cases hsup : H i ⊔ H j = ⊤
    · simp [hsup]
    · have hw : 0 ≤ π.w i * π.w j := mul_nonneg (π.nonneg i) (π.nonneg j)
      simp [hsup]
      nlinarith [mul_nonneg hw (sub_nonneg.mpr hloc1), mul_nonneg hw hfull0]
  have hsum :
      (∑ i, ∑ j, π.w i * π.w j * (boxMoment (L i j ++ [H i ⊔ H j]) g).re) ≤
        (∑ i, ∑ j, π.w i * π.w j * (boxMoment (L i j ++ [⊤]) g).re) +
          badPairMass π H := by
    unfold badPairMass
    calc
      _ ≤ ∑ i, ∑ j, (π.w i * π.w j * (boxMoment (L i j ++ [⊤]) g).re +
          (if H i ⊔ H j = ⊤ then 0 else π.w i * π.w j)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hpoint i j
      _ = _ := by simp_rw [Finset.sum_add_distrib]
  linarith

-- C7 (subgroup concatenation, degree 2^k - 1)
theorem subgroup_concatenation (k : ℕ) (hk : 1 ≤ k) :
    ∃ N C : ℕ, 1 ≤ N ∧ ∀ {G : Type} [AddCommGroup G] [Fintype G]
      {ι : Type} [Fintype ι] (π : ProbWeights ι) (Q : ι → AddSubgroup G)
      (g : G → ℂ), (∀ x, ‖g x‖ ≤ 1) →
      (∑ i, π.w i * (boxMoment (List.replicate k (Q i)) g).re) ^ N
          - C * badPairMass π Q
        ≤ (boxMoment (List.replicate (2 ^ k - 1) (⊤ : AddSubgroup G)) g).re := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk0 : k = 0
    · subst k
      omega
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      by_cases hk1 : k = 1
      · subst k
        refine ⟨2, 1, by norm_num, ?_⟩
        intro G _ _ ι _ π Q g hg
        let A : ℝ := ∑ i, π.w i * (boxMoment [Q i] g).re
        have hA0 : 0 ≤ A := by
          dsimp [A]
          apply Finset.sum_nonneg
          intro i hi
          exact mul_nonneg (π.nonneg i) (boxMoment_re_nonneg (by simp) g)
        have hstep := concat_step_zero π Q g hg hA0 le_rfl
        have hgeneric := replace_generic π Q (fun _ _ => []) g hg
        have hweight : ∑ i, ∑ j, π.w i * π.w j = 1 := by
          calc
            ∑ i, ∑ j, π.w i * π.w j =
                ∑ i, π.w i * ∑ j, π.w j := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [← Finset.mul_sum]
            _ = 1 := by
              rw [π.total]
              simpa using π.total
        have htop :
            (∑ i, ∑ j, π.w i * π.w j * (boxMoment [⊤] g).re) =
              (boxMoment [⊤] g).re := by
          calc
            ∑ i, ∑ j, π.w i * π.w j * (boxMoment [⊤] g).re =
                (∑ i, ∑ j, π.w i * π.w j) * (boxMoment [⊤] g).re := by
              calc
                ∑ i, ∑ j, π.w i * π.w j * (boxMoment [⊤] g).re =
                    ∑ i, (∑ j, π.w i * π.w j) * (boxMoment [⊤] g).re := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  exact (Finset.sum_mul _ _ _).symm
                _ = (∑ i, ∑ j, π.w i * π.w j) * (boxMoment [⊤] g).re :=
                  (Finset.sum_mul _ _ _).symm
            _ = (boxMoment [⊤] g).re := by rw [hweight]; ring
        calc
          (∑ i, π.w i * (boxMoment (List.replicate 1 (Q i)) g).re) ^ 2 -
              (1 : ℕ) * badPairMass π Q = A ^ 2 - badPairMass π Q := by
            simp [A, List.replicate_one]
          _ ≤
              (∑ i, ∑ j, π.w i * π.w j * (boxMoment [Q i ⊔ Q j] g).re) -
                badPairMass π Q := sub_le_sub_right hstep _
          _ ≤ ∑ i, ∑ j, π.w i * π.w j *
              (boxMoment [⊤] g).re := by simpa [List.replicate_one] using hgeneric
          _ = (boxMoment (List.replicate (2 ^ 1 - 1) (⊤ : AddSubgroup G)) g).re := by
            simpa using htop
      · have hk2 : 2 ≤ k := by omega
        let d : ℕ := k - 1
        have hdpos : 1 ≤ d := by dsimp [d]; omega
        have hdk : d + 1 = k := by dsimp [d]; omega
        have hdlt : d < k := by dsimp [d]; omega
        obtain ⟨N', C', hN', hprev⟩ := ih d hdlt hdpos
        let D : ℕ := 2 ^ d - 1
        let P : ℕ := 2 ^ (2 * d + 1)
        let N : ℕ := P * N' ^ 2
        let C : ℕ := N' * (N' + C') + C'
        refine ⟨N, C, ?_, ?_⟩
        · have hPpos : 0 < P := by dsimp [P]; positivity
          have hN'pos : 0 < N' := lt_of_lt_of_le Nat.zero_lt_one hN'
          have hNpos : 0 < N := by
            dsimp [N]
            exact Nat.mul_pos hPpos (pow_pos hN'pos 2)
          exact Nat.succ_le_of_lt hNpos
        · intro G _ _ ι _ π Q g hg
          let K₀ (i : ι) := List.replicate d (Q i)
          let A : ℝ := ∑ i, π.w i * (boxMoment (List.replicate k (Q i)) g).re
          let η : ℝ := badPairMass π Q
          have hA0 : 0 ≤ A := by
            dsimp [A]
            apply Finset.sum_nonneg
            intro i hi
            exact mul_nonneg (π.nonneg i)
              (boxMoment_re_nonneg (by simp [Nat.ne_of_gt hkpos]) g)
          have hA1 : A ≤ 1 := by
            dsimp [A]
            calc
              ∑ i, π.w i * (boxMoment (List.replicate k (Q i)) g).re ≤
                  ∑ i, π.w i * 1 := by
                apply Finset.sum_le_sum
                intro i hi
                exact mul_le_mul_of_nonneg_left
                  (boxMoment_re_le_one _ g hg) (π.nonneg i)
              _ = 1 := by simp [π.total]
          have hRep (i : ι) : K₀ i ++ [Q i] = List.replicate k (Q i) := by
            dsimp [K₀]
            calc
              List.replicate d (Q i) ++ [Q i] = List.replicate (d + 1) (Q i) :=
                replicate_append_singleton d (Q i)
              _ = List.replicate k (Q i) := by rw [hdk]
          have hinput : A ≤ ∑ i, π.w i * (boxMoment (K₀ i ++ [Q i]) g).re := by
            have heq : A = ∑ i, π.w i * (boxMoment (K₀ i ++ [Q i]) g).re := by
              dsimp [A]
              apply Finset.sum_congr rfl
              intro i hi
              rw [hRep i]
            exact heq.le
          have hstep := concat_step π d Q K₀
            (by intro i; simp [K₀]) g hg hA0 hinput
          have hgeneric := replace_generic π Q (fun i j => K₀ i ++ K₀ j) g hg
          let U : ℝ :=
            ∑ i, ∑ j, π.w i * π.w j *
              (boxMoment (K₀ i ++ K₀ j ++ [⊤]) g).re
          have hUlower : A ^ P - η ≤ U := by
            calc
              A ^ P - η ≤
                  (∑ i, ∑ j, π.w i * π.w j *
                    (boxMoment (K₀ i ++ K₀ j ++ [Q i ⊔ Q j]) g).re) - η :=
                sub_le_sub_right hstep _
              _ ≤ U := by
                simpa [U, K₀, List.append_assoc, η] using hgeneric
          let X (u : List G) : ℝ :=
            ∑ i, π.w i * (boxMoment (K₀ i) (cubeProd g u)).re
          have hX0 (u : List G) : 0 ≤ X u := by
            dsimp [X, K₀]
            apply Finset.sum_nonneg
            intro i hi
            exact mul_nonneg (π.nonneg i)
              (boxMoment_re_nonneg (by simp [Nat.ne_of_gt hdpos]) (cubeProd g u))
          have hX1 (u : List G) : X u ≤ 1 := by
            dsimp [X, K₀]
            calc
              ∑ i, π.w i * (boxMoment (List.replicate d (Q i)) (cubeProd g u)).re ≤
                  ∑ i, π.w i * 1 := by
                apply Finset.sum_le_sum
                intro i hi
                exact mul_le_mul_of_nonneg_left
                  (boxMoment_re_le_one _ (cubeProd g u)
                    (cubeProd_norm_le_one g hg u)) (π.nonneg i)
              _ = 1 := by simp [π.total]
          have hpairLen (i j : ι) : (K₀ i ++ K₀ j).length = 2 * d := by
            simp [K₀, List.length_append, two_mul]
          have hperm (i j : ι) :
              (K₀ i ++ K₀ j ++ [⊤]).Perm ((K₀ j ++ [⊤]) ++ K₀ i) := by
            have hrot :
                (K₀ i ++ (K₀ j ++ [⊤])).Perm ((K₀ j ++ [⊤]) ++ K₀ i) :=
              List.perm_append_comm
            simpa [List.append_assoc] using hrot
          have hUpoint (i j : ι) :
              (boxMoment (K₀ i ++ K₀ j ++ [⊤]) g).re =
                cubeAvg (K₀ j ++ [⊤])
                  (fun u => (boxMoment (K₀ i) (cubeProd g u)).re) := by
            calc
              (boxMoment (K₀ i ++ K₀ j ++ [⊤]) g).re =
                  (boxMoment ((K₀ j ++ [⊤]) ++ K₀ i) g).re :=
                congrArg Complex.re (boxMoment_perm (hperm i j) g)
              _ = cubeAvg (K₀ j ++ [⊤])
                  (fun u => (boxMoment (K₀ i) (cubeProd g u)).re) :=
                boxMoment_re_append (K₀ j ++ [⊤]) (K₀ i) g
          have hUexpr : U = ∑ j, π.w j *
              cubeAvg (K₀ j ++ [⊤]) X := by
            dsimp [U]
            calc
              ∑ i, ∑ j, π.w i * π.w j *
                  (boxMoment (K₀ i ++ K₀ j ++ [⊤]) g).re =
                  ∑ j, ∑ i, π.w j * π.w i *
                    cubeAvg (K₀ j ++ [⊤])
                      (fun u => (boxMoment (K₀ i) (cubeProd g u)).re) := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro j hj
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [hUpoint i j]
                  ring
              _ = ∑ j, π.w j * ∑ i, π.w i *
                  cubeAvg (K₀ j ++ [⊤])
                    (fun u => (boxMoment (K₀ i) (cubeProd g u)).re) := by
                apply Finset.sum_congr rfl
                intro j hj
                calc
                  ∑ i, π.w j * π.w i *
                      cubeAvg (K₀ j ++ [⊤])
                        (fun u => (boxMoment (K₀ i) (cubeProd g u)).re) =
                      ∑ i, π.w j * (π.w i *
                        cubeAvg (K₀ j ++ [⊤])
                          (fun u => (boxMoment (K₀ i) (cubeProd g u)).re)) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
                  _ = π.w j * ∑ i, π.w i *
                      cubeAvg (K₀ j ++ [⊤])
                        (fun u => (boxMoment (K₀ i) (cubeProd g u)).re) := by
                    rw [Finset.mul_sum]
              _ = ∑ j, π.w j * cubeAvg (K₀ j ++ [⊤]) X := by
                apply Finset.sum_congr rfl
                intro j hj
                congr 1
                exact (cubeAvg_probWeighted_sum π (K₀ j ++ [⊤])
                  (fun i u => (boxMoment (K₀ i) (cubeProd g u)).re)).symm
          have hη0 : 0 ≤ η := by
            dsimp [η, badPairMass]
            apply Finset.sum_nonneg
            intro i hi
            apply Finset.sum_nonneg
            intro j hj
            by_cases htop : Q i ⊔ Q j = ⊤
            · simp [htop]
            · simp only [if_neg htop]
              exact mul_nonneg (π.nonneg i) (π.nonneg j)
          have hweight : ∑ i, ∑ j, π.w i * π.w j = 1 := by
            calc
              ∑ i, ∑ j, π.w i * π.w j =
                  ∑ i, π.w i * (∑ j, π.w j) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [← Finset.mul_sum]
              _ = (∑ i, π.w i) * (∑ j, π.w j) := by rw [Finset.sum_mul]
              _ = 1 := by rw [π.total]; norm_num
          have hU0 : 0 ≤ U := by
            dsimp [U]
            apply Finset.sum_nonneg
            intro i hi
            apply Finset.sum_nonneg
            intro j hj
            exact mul_nonneg (mul_nonneg (π.nonneg i) (π.nonneg j))
              (boxMoment_re_nonneg (by simp) g)
          have hU1 : U ≤ 1 := by
            dsimp [U]
            calc
              ∑ i, ∑ j, π.w i * π.w j *
                  (boxMoment (K₀ i ++ K₀ j ++ [⊤]) g).re ≤
                ∑ i, ∑ j, π.w i * π.w j := by
                apply Finset.sum_le_sum
                intro i hi
                apply Finset.sum_le_sum
                intro j hj
                calc
                  π.w i * π.w j * (boxMoment (K₀ i ++ K₀ j ++ [⊤]) g).re ≤
                      π.w i * π.w j * 1 :=
                    mul_le_mul_of_nonneg_left (boxMoment_re_le_one _ g hg)
                      (mul_nonneg (π.nonneg i) (π.nonneg j))
                  _ = π.w i * π.w j := by ring
              _ = 1 := hweight
          have hInd (u : List G) :
              X u ^ N' - (C' : ℝ) * η ≤
                (boxMoment (List.replicate D (⊤ : AddSubgroup G)) (cubeProd g u)).re := by
            have h := hprev π Q (cubeProd g u) (cubeProd_norm_le_one g hg u)
            simpa [X, K₀, D] using h
          let V : ℝ := ∑ j, π.w j * cubeAvg (K₀ j ++ [⊤])
            (fun u => (boxMoment (List.replicate D (⊤ : AddSubgroup G))
              (cubeProd g u)).re)
          have hDpos : 0 < D := by
            dsimp [D]
            have hp : 1 < 2 ^ d := Nat.one_lt_pow (by omega) (by norm_num)
            omega
          have hV0 : 0 ≤ V := by
            dsimp [V]
            apply Finset.sum_nonneg
            intro j hj
            apply mul_nonneg (π.nonneg j)
            apply cubeAvg_real_nonneg
            intro u
            exact boxMoment_re_nonneg (by simp [Nat.ne_of_gt hDpos])
              (cubeProd g u)
          have hVlower : U ^ N' - (C' : ℝ) * η ≤ V := by
            have hJ : U ^ N' ≤ ∑ j, π.w j *
                cubeAvg (K₀ j ++ [⊤]) (fun u => X u ^ N') := by
              rw [hUexpr]
              exact cubeAvg_probWeighted_pow_jensen π
                (fun j => K₀ j ++ [⊤]) (fun _ u => X u) (fun j u => hX0 u) N'
            have hpoint (j : ι) :
                cubeAvg (K₀ j ++ [⊤]) (fun u => X u ^ N' - (C' : ℝ) * η) ≤
                  cubeAvg (K₀ j ++ [⊤]) (fun u =>
                    (boxMoment (List.replicate D (⊤ : AddSubgroup G)) (cubeProd g u)).re) :=
              cubeAvg_real_mono _ _ _ (fun u => hInd u)
            have hsumPoint :
                ∑ j, π.w j *
                  cubeAvg (K₀ j ++ [⊤]) (fun u => X u ^ N' - (C' : ℝ) * η) ≤ V := by
              apply Finset.sum_le_sum
              intro j hj
              exact mul_le_mul_of_nonneg_left (hpoint j) (π.nonneg j)
            have hlin :
                ∑ j, π.w j *
                    cubeAvg (K₀ j ++ [⊤]) (fun u => X u ^ N' - (C' : ℝ) * η) =
                  (∑ j, π.w j * cubeAvg (K₀ j ++ [⊤]) (fun u => X u ^ N')) -
                    (C' : ℝ) * η := by
              calc
                _ = ∑ j, (π.w j * cubeAvg (K₀ j ++ [⊤]) (fun u => X u ^ N') -
                    π.w j * ((C' : ℝ) * η)) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [cubeAvg_real_sub, cubeAvg_real_const]
                  ring
                _ = (∑ j, π.w j * cubeAvg (K₀ j ++ [⊤]) (fun u => X u ^ N')) -
                    (∑ j, π.w j) * ((C' : ℝ) * η) := by
                  rw [Finset.sum_sub_distrib, Finset.sum_mul]
                _ = _ := by rw [π.total]; ring
            calc
              U ^ N' - (C' : ℝ) * η ≤
                  (∑ j, π.w j * cubeAvg (K₀ j ++ [⊤]) (fun u => X u ^ N')) -
                    (C' : ℝ) * η := sub_le_sub_right hJ _
              _ ≤ V := by rw [← hlin]; exact hsumPoint
          let TopPrefix : List (AddSubgroup G) := List.replicate (D + 1) ⊤
          have hTopRep : [⊤] ++ List.replicate D (⊤ : AddSubgroup G) = TopPrefix := by
            dsimp [TopPrefix, D]
            simp [List.replicate_succ]
          have hpermTop (j : ι) :
              ((K₀ j ++ [⊤]) ++ List.replicate D (⊤ : AddSubgroup G)).Perm
                (TopPrefix ++ K₀ j) := by
            have hrot :
                (K₀ j ++ TopPrefix).Perm (TopPrefix ++ K₀ j) := List.perm_append_comm
            simpa [TopPrefix, List.append_assoc, hTopRep] using hrot
          have hVpoint (j : ι) :
              cubeAvg (K₀ j ++ [⊤])
                  (fun u => (boxMoment (List.replicate D (⊤ : AddSubgroup G))
                    (cubeProd g u)).re) =
                cubeAvg TopPrefix (fun v => (boxMoment (K₀ j) (cubeProd g v)).re) := by
            calc
              _ = (boxMoment ((K₀ j ++ [⊤]) ++
                  List.replicate D (⊤ : AddSubgroup G)) g).re :=
                (boxMoment_re_append (K₀ j ++ [⊤])
                  (List.replicate D (⊤ : AddSubgroup G)) g).symm
              _ = (boxMoment (TopPrefix ++ K₀ j) g).re :=
                congrArg Complex.re (boxMoment_perm (hpermTop j) g)
              _ = cubeAvg TopPrefix (fun v => (boxMoment (K₀ j) (cubeProd g v)).re) :=
                boxMoment_re_append TopPrefix (K₀ j) g
          have hVexpr : V = cubeAvg TopPrefix X := by
            dsimp [V]
            calc
              ∑ j, π.w j * cubeAvg (K₀ j ++ [⊤])
                  (fun u => (boxMoment (List.replicate D (⊤ : AddSubgroup G))
                    (cubeProd g u)).re) =
                ∑ j, π.w j * cubeAvg TopPrefix
                  (fun v => (boxMoment (K₀ j) (cubeProd g v)).re) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [hVpoint j]
              _ = cubeAvg TopPrefix X := by
                exact (cubeAvg_probWeighted_sum π TopPrefix
                  (fun j v => (boxMoment (K₀ j) (cubeProd g v)).re)).symm
          have htopLower : (cubeAvg TopPrefix X) ^ N' - (C' : ℝ) * η ≤
              (boxMoment (TopPrefix ++ List.replicate D (⊤ : AddSubgroup G)) g).re := by
            have hmono := cubeAvg_real_mono TopPrefix
              (fun v => X v ^ N' - (C' : ℝ) * η)
              (fun v => (boxMoment (List.replicate D (⊤ : AddSubgroup G))
                (cubeProd g v)).re) hInd
            have hlinTop :
                cubeAvg TopPrefix (fun v => X v ^ N' - (C' : ℝ) * η) =
                  cubeAvg TopPrefix (fun v => X v ^ N') - (C' : ℝ) * η := by
              rw [cubeAvg_real_sub, cubeAvg_real_const]
            have hJtop := cubeAvg_real_pow_jensen TopPrefix X hX0 N'
            calc
              (cubeAvg TopPrefix X) ^ N' - (C' : ℝ) * η ≤
                  cubeAvg TopPrefix (fun v => X v ^ N') - (C' : ℝ) * η :=
                sub_le_sub_right hJtop _
              _ = cubeAvg TopPrefix (fun v => X v ^ N' - (C' : ℝ) * η) := hlinTop.symm
              _ ≤ cubeAvg TopPrefix (fun v =>
                  (boxMoment (List.replicate D (⊤ : AddSubgroup G))
                    (cubeProd g v)).re) := hmono
              _ = (boxMoment (TopPrefix ++ List.replicate D (⊤ : AddSubgroup G)) g).re :=
                boxMoment_re_append TopPrefix (List.replicate D (⊤ : AddSubgroup G)) g |>.symm
          have hfinalTop : V ^ N' - (C' : ℝ) * η ≤
              (boxMoment (TopPrefix ++ List.replicate D (⊤ : AddSubgroup G)) g).re := by
            simpa [hVexpr] using htopLower
          have hMpos : 0 < N' ^ 2 := pow_pos (lt_of_lt_of_le Nat.zero_lt_one hN') 2
          have hM1 : 1 ≤ N' ^ 2 := by omega
          have hApow0 : 0 ≤ A ^ P := pow_nonneg hA0 _
          have hApow1 : A ^ P ≤ 1 := pow_le_one₀ hA0 hA1
          have hUmax : max (A ^ P - η) 0 ≤ U := max_le_iff.mpr ⟨hUlower, hU0⟩
          have hUpow : A ^ (P * N' ^ 2) - (N' ^ 2 : ℝ) * η ≤ U ^ (N' ^ 2) := by
            calc
              A ^ (P * N' ^ 2) - (N' ^ 2 : ℝ) * η =
                  (A ^ P) ^ (N' ^ 2) - (N' ^ 2 : ℝ) * η := by rw [← pow_mul]
              _ ≤ (max (A ^ P - η) 0) ^ (N' ^ 2) := by
                exact_mod_cast ge_iff_le.mp
                  (max_sub_pow_lower (A ^ P) η hApow0 hApow1 hη0 (N' ^ 2) hM1)
              _ ≤ U ^ (N' ^ 2) :=
                pow_le_pow_left₀ (le_max_right _ _) hUmax _
          have hUexp0 : 0 ≤ U ^ N' := pow_nonneg hU0 _
          have hUexp1 : U ^ N' ≤ 1 := pow_le_one₀ hU0 hU1
          have hVmax : max (U ^ N' - (C' : ℝ) * η) 0 ≤ V :=
            max_le_iff.mpr ⟨hVlower, hV0⟩
          have hVpow : U ^ (N' ^ 2) - (N' : ℝ) * ((C' : ℝ) * η) ≤ V ^ N' := by
            calc
              U ^ (N' ^ 2) - (N' : ℝ) * ((C' : ℝ) * η) =
                  (U ^ N') ^ N' - (N' : ℝ) * ((C' : ℝ) * η) := by
                    rw [pow_two, ← pow_mul]
              _ ≤ (max (U ^ N' - (C' : ℝ) * η) 0) ^ N' :=
                ge_iff_le.mp (max_sub_pow_lower (U ^ N') ((C' : ℝ) * η)
                  hUexp0 hUexp1 (mul_nonneg (Nat.cast_nonneg C') hη0) N'
                  (Nat.succ_le_of_lt (lt_of_lt_of_le Nat.zero_lt_one hN')))
              _ ≤ V ^ N' := pow_le_pow_left₀ (le_max_right _ _) hVmax _
          have hTopLen : (D + 1) + D = 2 ^ k - 1 := by
            dsimp [D]
            rw [← hdk, pow_succ]
            omega
          have hTopAll : TopPrefix ++ List.replicate D (⊤ : AddSubgroup G) =
              List.replicate (2 ^ k - 1) ⊤ := by
            dsimp [TopPrefix]
            calc
              List.replicate (D + 1) ⊤ ++ List.replicate D ⊤ =
                  List.replicate ((D + 1) + D) ⊤ := by rw [← List.replicate_add]
              _ = List.replicate (2 ^ k - 1) ⊤ := by rw [hTopLen]
          have hcombined : A ^ (P * N' ^ 2) -
              ((N' ^ 2 : ℝ) + (N' : ℝ) * (C' : ℝ) + (C' : ℝ)) * η ≤
                (boxMoment (TopPrefix ++ List.replicate D (⊤ : AddSubgroup G)) g).re := by
            nlinarith [hUpow, hVpow, hfinalTop]
          rw [hTopAll] at hcombined
          have hcoeff : (N' ^ 2 : ℝ) + (N' : ℝ) * (C' : ℝ) + (C' : ℝ) = (C : ℝ) := by
            simp [C, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, pow_two]
            ring
          change A ^ N - (C : ℝ) * η ≤
            (boxMoment (List.replicate (2 ^ k - 1) (⊤ : AddSubgroup G)) g).re
          simpa [N, P, pow_mul, hcoeff] using hcombined

-- C8 (cells and the form §5 consumes)
theorem cells_concatenation (k : ℕ) (hk : 1 ≤ k) :
    ∃ N C : ℕ, 1 ≤ N ∧ ∀ {G : Type} [AddCommGroup G] [Fintype G]
      {ι : Type} [Fintype ι] (π : ProbWeights ι) (Q : ι → AddSubgroup G)
      {Cl : Type} [Fintype Cl] (α : ProbWeights Cl) (h : Cl → G → ℂ),
      (∀ c x, ‖h c x‖ ≤ 1) →
      (∑ i, π.w i * ∑ c, α.w c * (boxMoment (List.replicate k (Q i)) (h c)).re) ^ N
          - C * badPairMass π Q
        ≤ ∑ c, α.w c * (boxMoment (List.replicate (2 ^ k - 1) (⊤ : AddSubgroup G)) (h c)).re := by
  classical
  obtain ⟨N, C, hN, hconcat⟩ := subgroup_concatenation k hk
  refine ⟨N, C, hN, ?_⟩
  intro G _ _ ι _ π Q Cl _ α h hh
  let A (c : Cl) : ℝ :=
    ∑ i, π.w i * (boxMoment (List.replicate k (Q i)) (h c)).re
  let B (c : Cl) : ℝ :=
    (boxMoment (List.replicate (2 ^ k - 1) (⊤ : AddSubgroup G)) (h c)).re
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hA0 : ∀ c, 0 ≤ A c := by
    intro c
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (π.nonneg i)
      (boxMoment_re_nonneg (by simp [hkpos.ne']) (h c))
  have hmean :
      (∑ i, π.w i * ∑ c, α.w c * (boxMoment (List.replicate k (Q i)) (h c)).re) =
        ∑ c, α.w c * A c := by
    dsimp [A]
    calc
      _ = ∑ i, ∑ c, α.w c *
          (π.w i * (boxMoment (List.replicate k (Q i)) (h c)).re) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c hc
        ring
      _ = ∑ c, ∑ i, α.w c *
          (π.w i * (boxMoment (List.replicate k (Q i)) (h c)).re) := Finset.sum_comm
      _ = ∑ c, α.w c *
          (∑ i, π.w i * (boxMoment (List.replicate k (Q i)) (h c)).re) := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.mul_sum]
  have hJensen :
      (∑ c, α.w c * A c) ^ N ≤ ∑ c, α.w c * A c ^ N := by
    have h := (convexOn_pow N).map_sum_le
      (t := (Finset.univ : Finset Cl)) (w := α.w)
      (fun c hc => α.nonneg c) α.total
      (fun c hc => Set.mem_Ici.mpr (hA0 c))
    simpa [smul_eq_mul] using h
  have hpoint (c : Cl) : A c ^ N - (C : ℝ) * badPairMass π Q ≤ B c := by
    simpa [A, B] using hconcat π Q (h c) (hh c)
  have hweighted :
      (∑ c, α.w c * A c ^ N) - (C : ℝ) * badPairMass π Q ≤
        ∑ c, α.w c * B c := by
    have hsum :
        ∑ c, α.w c * (A c ^ N - (C : ℝ) * badPairMass π Q) ≤
          ∑ c, α.w c * B c := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hpoint c) (α.nonneg c)
    have hrewrite :
        (∑ c, α.w c * (A c ^ N - (C : ℝ) * badPairMass π Q)) =
          (∑ c, α.w c * A c ^ N) - (C : ℝ) * badPairMass π Q := by
      calc
        _ = (∑ c, α.w c * A c ^ N) -
            (∑ c, α.w c) * ((C : ℝ) * badPairMass π Q) := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, Finset.sum_mul]
        _ = _ := by rw [α.total]; ring
    rw [hrewrite] at hsum
    exact hsum
  calc
    (∑ i, π.w i * ∑ c, α.w c *
        (boxMoment (List.replicate k (Q i)) (h c)).re) ^ N -
        (C : ℝ) * badPairMass π Q =
      (∑ c, α.w c * A c) ^ N - (C : ℝ) * badPairMass π Q := by rw [hmean]
    _ ≤ (∑ c, α.w c * A c ^ N) - (C : ℝ) * badPairMass π Q :=
      sub_le_sub_right hJensen _
    _ ≤ ∑ c, α.w c * B c := hweighted

theorem combine_subgroups (k : ℕ) (hk : 1 ≤ k) (β : ℝ) (hβ : 0 < β) :
    ∃ δ₁ > 0, ∃ η₁ > 0, ∀ {G : Type} [AddCommGroup G] [Fintype G]
      {ι : Type} [Fintype ι] (π : ProbWeights ι) (Q : ι → AddSubgroup G)
      {Cl : Type} [Fintype Cl] (α : ProbWeights Cl) (h : Cl → G → ℂ),
      (∀ c x, ‖h c x‖ ≤ 1) → badPairMass π Q ≤ η₁ →
      ∑ c, α.w c * (boxMoment (List.replicate (2 ^ k - 1) (⊤ : AddSubgroup G)) (h c)).re ≤ δ₁ →
      ∑ i, π.w i * ∑ c, α.w c * (boxMoment (List.replicate k (Q i)) (h c)).re ≤ β := by
  classical
  obtain ⟨N, C, hN, hcells⟩ := cells_concatenation k hk
  let δ₁ : ℝ := β ^ N / 3
  let η₁ : ℝ := β ^ N / (3 * ((C : ℝ) + 1))
  have hδ : 0 < δ₁ := by positivity [hβ]
  have hη : 0 < η₁ := by positivity [hβ]
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  refine ⟨δ₁, hδ, η₁, hη, ?_⟩
  intro G _ _ ι _ π Q Cl _ α h hh hbad hfull
  let x : ℝ :=
    ∑ i, π.w i * ∑ c, α.w c * (boxMoment (List.replicate k (Q i)) (h c)).re
  have hx0 : 0 ≤ x := by
    dsimp [x]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg (π.nonneg i)
    apply Finset.sum_nonneg
    intro c hc
    exact mul_nonneg (α.nonneg c)
      (boxMoment_re_nonneg (by simp [hkpos.ne']) (h c))
  have hbox := hcells π Q α h hh
  have hbox' : x ^ N - (C : ℝ) * badPairMass π Q ≤
      ∑ c, α.w c * (boxMoment (List.replicate (2 ^ k - 1) (⊤ : AddSubgroup G)) (h c)).re := by
    simpa [x] using hbox
  have hpow : x ^ N ≤ δ₁ + (C : ℝ) * η₁ := by
    have hle := hbox'.trans hfull
    have hbad' : (C : ℝ) * badPairMass π Q ≤ (C : ℝ) * η₁ :=
      mul_le_mul_of_nonneg_left hbad (by positivity)
    dsimp [δ₁] at hle ⊢
    linarith
  have hCη : (C : ℝ) * η₁ ≤ β ^ N / 3 := by
    dsimp [η₁]
    have hC : (C : ℝ) ≤ (C : ℝ) + 1 := by linarith
    have hden : 0 < 3 * ((C : ℝ) + 1) := by positivity
    calc
      (C : ℝ) * (β ^ N / (3 * ((C : ℝ) + 1))) ≤
          ((C : ℝ) + 1) * (β ^ N / (3 * ((C : ℝ) + 1))) := by
        exact mul_le_mul_of_nonneg_right hC (div_nonneg (pow_nonneg hβ.le _) (le_of_lt hden))
      _ = β ^ N / 3 := by field_simp
  have hpow' : x ^ N ≤ (2 / 3) * β ^ N := by
    dsimp [δ₁] at hpow
    nlinarith [hpow, hCη]
  by_contra hx
  have hβx : β < x := lt_of_not_ge hx
  have hstrict : β ^ N < x ^ N := pow_lt_pow_left₀ hβx hβ.le (Nat.ne_of_gt (Nat.lt_of_lt_of_le
    Nat.zero_lt_one hN))
  nlinarith [hstrict, hpow']

theorem zmultiples_sup_eq_top (n a b : ℕ) (hab : Nat.Coprime a b) :
    AddSubgroup.zmultiples (a : ZMod n) ⊔ AddSubgroup.zmultiples (b : ZMod n) = ⊤ := by
  classical
  have hbez : (1 : ℤ) = (a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b := by
    have hgcd : ((Nat.gcd a b : ℕ) : ℤ) = 1 := by exact_mod_cast hab.gcd_eq_one
    rw [← hgcd]
    exact Nat.gcd_eq_gcd_ab a b
  have hbezZ : (1 : ZMod n) =
      (Nat.gcdA a b : ℤ) • (a : ZMod n) + (Nat.gcdB a b : ℤ) • (b : ZMod n) := by
    have h := congrArg (fun z : ℤ => (z : ZMod n)) hbez
    simpa [zsmul_eq_mul, mul_comm] using h
  have h1 : (1 : ZMod n) ∈
      AddSubgroup.zmultiples (a : ZMod n) ⊔ AddSubgroup.zmultiples (b : ZMod n) := by
    apply AddSubgroup.mem_sup.mpr
    refine ⟨(Nat.gcdA a b : ℤ) • (a : ZMod n),
      AddSubgroup.zsmul_mem_zmultiples _ _,
      (Nat.gcdB a b : ℤ) • (b : ZMod n),
      AddSubgroup.zsmul_mem_zmultiples _ _, ?_⟩
    exact hbezZ.symm
  have hone : AddSubgroup.zmultiples (1 : ZMod n) = ⊤ := by
    rw [← Int.range_castAddHom]
    exact AddMonoidHom.range_eq_top.mpr ZMod.intCast_surjective
  apply le_antisymm le_top
  rw [← hone]
  exact AddSubgroup.zmultiples_le.mpr h1

end statements
end HindmanSumsProducts.SubgroupBox

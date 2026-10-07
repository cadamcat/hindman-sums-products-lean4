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

private def cubeRest (f : G → ℂ) : List G → G → ℂ
  | [], _ => 1
  | h :: hs, x => star (f (x + h)) * cubeRest (mderiv f h) hs x

private theorem cubeProd_factor (f : G → ℂ) (hs : List G) (x : G) :
    cubeProd f hs x = f x * cubeRest f hs x := by
  induction hs generalizing f with
  | nil => simp [cubeProd, cubeRest]
  | cons h hs ih =>
    calc
      cubeProd f (h :: hs) x = cubeProd (mderiv f h) hs x := rfl
      _ = mderiv f h x * cubeRest (mderiv f h) hs x := ih (mderiv f h)
      _ = f x * cubeRest f (h :: hs) x := by simp [mderiv, cubeRest]; ring

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
    have h₁ := hf (x + h)
    have h₂ := ih (mderiv f h) (fun y => mderiv_norm_le_one f hf h y)
    have hn₁ := norm_nonneg (f (x + h))
    have hn₂ := norm_nonneg (cubeRest (mderiv f h) hs x)
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
      ∑ i, ∑ j, π.w i * π.w j * (boxMoment (K i ++ K j ++ [H i ⊔ H j]) g).re := by sorry

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
        ≤ (boxMoment (List.replicate (2 ^ k - 1) (⊤ : AddSubgroup G)) g).re := by sorry

-- C8 (cells and the form §5 consumes)
theorem cells_concatenation (k : ℕ) (hk : 1 ≤ k) :
    ∃ N C : ℕ, 1 ≤ N ∧ ∀ {G : Type} [AddCommGroup G] [Fintype G]
      {ι : Type} [Fintype ι] (π : ProbWeights ι) (Q : ι → AddSubgroup G)
      {Cl : Type} [Fintype Cl] (α : ProbWeights Cl) (h : Cl → G → ℂ),
      (∀ c x, ‖h c x‖ ≤ 1) →
      (∑ i, π.w i * ∑ c, α.w c * (boxMoment (List.replicate k (Q i)) (h c)).re) ^ N
          - C * badPairMass π Q
        ≤ ∑ c, α.w c * (boxMoment (List.replicate (2 ^ k - 1) (⊤ : AddSubgroup G)) (h c)).re := by
  sorry

theorem combine_subgroups (k : ℕ) (hk : 1 ≤ k) (β : ℝ) (hβ : 0 < β) :
    ∃ δ₁ > 0, ∃ η₁ > 0, ∀ {G : Type} [AddCommGroup G] [Fintype G]
      {ι : Type} [Fintype ι] (π : ProbWeights ι) (Q : ι → AddSubgroup G)
      {Cl : Type} [Fintype Cl] (α : ProbWeights Cl) (h : Cl → G → ℂ),
      (∀ c x, ‖h c x‖ ≤ 1) → badPairMass π Q ≤ η₁ →
      ∑ c, α.w c * (boxMoment (List.replicate (2 ^ k - 1) (⊤ : AddSubgroup G)) (h c)).re ≤ δ₁ →
      ∑ i, π.w i * ∑ c, α.w c * (boxMoment (List.replicate k (Q i)) (h c)).re ≤ β := by sorry

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

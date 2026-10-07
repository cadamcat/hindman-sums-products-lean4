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

-- C1
theorem expect_add_sup (A B : AddSubgroup G) [Fintype A] [Fintype B]
    [Fintype (A ⊔ B : AddSubgroup G)] (φ : G → ℂ) :
    (𝔼 a : A, 𝔼 b : B, φ ((a : G) + b)) = 𝔼 c : (A ⊔ B : AddSubgroup G), φ c := by sorry

theorem expect_mul_star_avgOn (Q : AddSubgroup G) [Fintype Q] (f g : G → ℂ) :
    (𝔼 x, f x * star (avgOn Q g x)) = 𝔼 x, avgOn Q f x * star (avgOn Q g x) := by sorry

open Classical in
theorem boxMoment_singleton (Q : AddSubgroup G) (f : G → ℂ) :
    boxMoment [Q] f = 𝔼 x, (((‖avgOn Q f x‖ ^ 2 : ℝ)) : ℂ) := by sorry

-- C3
theorem boxMoment_append (Qs Rs : List (AddSubgroup G)) (f : G → ℂ) :
    boxMoment (Qs ++ Rs) f = cubeAvg Qs (fun hs ↦ boxMoment Rs (cubeProd f hs)) := by sorry

theorem boxMoment_perm {Qs Rs : List (AddSubgroup G)} (h : Qs.Perm Rs) (f : G → ℂ) :
    boxMoment Qs f = boxMoment Rs f := by sorry

theorem boxMoment_im {Qs : List (AddSubgroup G)} (hQs : Qs ≠ []) (f : G → ℂ) :
    (boxMoment Qs f).im = 0 := by sorry

theorem boxMoment_re_nonneg {Qs : List (AddSubgroup G)} (hQs : Qs ≠ []) (f : G → ℂ) :
    0 ≤ (boxMoment Qs f).re := by sorry

theorem boxMoment_re_le_one (Qs : List (AddSubgroup G)) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    (boxMoment Qs f).re ≤ 1 := by sorry

-- C4 (Gowers–Cauchy–Schwarz along subgroup directions)
theorem norm_boxInner_pow_le (Qs : List (AddSubgroup G)) (hQs : Qs ≠ [])
    (F : (Fin Qs.length → Bool) → G → ℂ) :
    ‖boxInner Qs F‖ ^ (2 ^ Qs.length) ≤ ∏ ω, (boxMoment Qs (F ω)).re := by sorry

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
      ∑ i, ∑ j, π.w i * π.w j * (boxMoment (L i j ++ [⊤]) g).re := by sorry

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
    AddSubgroup.zmultiples (a : ZMod n) ⊔ AddSubgroup.zmultiples (b : ZMod n) = ⊤ := by sorry

end statements
end HindmanSumsProducts.SubgroupBox

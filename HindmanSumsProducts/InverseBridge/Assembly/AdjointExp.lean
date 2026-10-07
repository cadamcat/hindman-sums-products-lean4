import OAI.Combinatorics.Progressions.Estimates.AxisCompression
import Mathlib.Algebra.Module.LinearMap.Basic

open Finset IsNilpotent Module.End OAI.Erdos3

namespace HindmanSumsProducts.InverseBridge.AssemblyAdjoint

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem exp_mulLeft {A : Type*} [Ring A] [Algebra ℚ A] (a : A)
    (ha : IsNilpotent a) :
    IsNilpotent.exp (LinearMap.mulLeft ℚ a) = LinearMap.mulLeft ℚ (IsNilpotent.exp a) := by
  have h := IsNilpotent.map_exp ha (Algebra.lmul ℚ A)
  have hL : Algebra.lmul ℚ A a = LinearMap.mulLeft ℚ a := by ext z; rfl
  have hL' : Algebra.lmul ℚ A (IsNilpotent.exp a) =
      LinearMap.mulLeft ℚ (IsNilpotent.exp a) := by ext z; rfl
  rw [← hL, ← hL']
  exact h.symm

private theorem exp_mulRight {A : Type*} [Ring A] [Algebra ℚ A] (a : A)
    (ha : IsNilpotent a) :
    IsNilpotent.exp (LinearMap.mulRight ℚ a) = LinearMap.mulRight ℚ (IsNilpotent.exp a) := by
  obtain ⟨k, hk⟩ := ha
  have hR : IsNilpotent (LinearMap.mulRight ℚ a) := by
    refine ⟨k, ?_⟩
    simp [LinearMap.pow_mulRight, hk]
  ext z
  have hact : ((LinearMap.mulRight ℚ a) ^ k) z = 0 := by
    rw [LinearMap.pow_mulRight, LinearMap.mulRight_apply, hk, mul_zero]
  calc
    IsNilpotent.exp (LinearMap.mulRight ℚ a) z =
        ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • ((LinearMap.mulRight ℚ a) ^ i) z := by
          simpa using (IsNilpotent.exp_smul_eq_sum (a := LinearMap.mulRight ℚ a)
            (m := z) hact hR)
    _ = ∑ i ∈ range k, z * ((i.factorial : ℚ)⁻¹ • a ^ i) := by
      apply sum_congr rfl
      intro i hi
      simp only [LinearMap.pow_mulRight, LinearMap.mulRight_apply]
      rw [← mul_smul_comm]
    _ = z * (∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • a ^ i) := by rw [mul_sum]
    _ = z * IsNilpotent.exp a := by rw [IsNilpotent.exp_eq_sum hk]


def commutatorMap {A : Type*} [Ring A] [Algebra ℚ A] (a : A) :
    Module.End ℚ A := LinearMap.mulLeft ℚ a - LinearMap.mulRight ℚ a

private theorem commutator_exp_action {A : Type*} [Ring A] [Algebra ℚ A] {s : ℕ}
    (F : NilpotentAlgebraFiltration A s) {a b : A} (ha : a ∈ F.layer 1) :
    ∑ j ∈ range (s + 1), (j.factorial : ℚ)⁻¹ •
      ((commutatorMap a) ^ j) b =
        IsNilpotent.exp a * b * IsNilpotent.exp (-a) := by
  let D := commutatorMap a
  let L := LinearMap.mulLeft ℚ a
  let R := LinearMap.mulRight ℚ a
  have hna : IsNilpotent a := F.positive_nilpotent a ha
  have hraise {n : ℕ} {z : A} (hz : z ∈ F.layer n) :
      D z ∈ F.layer (n + 1) := by
    change a * z - z * a ∈ F.layer (n + 1)
    refine Submodule.sub_mem _ ?_ ?_
    · have h := F.mul_mem ha hz
      simpa [Nat.add_comm] using h
    · exact F.mul_mem hz ha
  have hiter : ∀ n (z : A), z ∈ F.layer 0 → (D ^ n) z ∈ F.layer n := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih =>
      intro z hz
      rw [pow_succ']
      exact hraise (ih z hz)
  have hDpow : D ^ (s + 1) = 0 := by
    ext z
    have hz := hiter (s + 1) z (by rw [F.zero_eq_top]; exact Submodule.mem_top)
    rw [F.terminal, Submodule.mem_bot] at hz
    exact hz
  have hDnil : IsNilpotent D := ⟨s + 1, hDpow⟩
  have hcomm : Commute L R := by
    change L * R = R * L
    ext z
    simp [L, R, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, mul_assoc]
  have hLnil : IsNilpotent L := by
    have hL : Algebra.lmul ℚ A a = L := by ext z; rfl
    rw [← hL]
    exact hna.map (Algebra.lmul ℚ A)
  have hRnil : IsNilpotent R := by
    rcases hna with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simp [R, LinearMap.pow_mulRight, hk]
  have hExpD : IsNilpotent.exp D = IsNilpotent.exp L * IsNilpotent.exp (-R) := by
    have hcomm' : Commute L (-R) := hcomm.neg_right
    have h := IsNilpotent.exp_add_of_commute hcomm' hLnil hRnil.neg
    simpa only [D, commutatorMap, sub_eq_add_neg, L, R] using h
  have hDact : (D ^ (s + 1)) • b = 0 := by simp [hDpow]
  have hseries := IsNilpotent.exp_smul_eq_sum (a := D) (m := b) hDact hDnil
  have hnegR : -R = LinearMap.mulRight ℚ (-a) := by
    ext z
    simp [R, LinearMap.mulRight_apply]
  calc
    ∑ j ∈ range (s + 1), (j.factorial : ℚ)⁻¹ • ((commutatorMap a) ^ j) b =
        IsNilpotent.exp D b := by
          simpa [D] using hseries.symm
    _ = (IsNilpotent.exp L * IsNilpotent.exp (-R)) b := by
          exact congrArg (fun f : Module.End ℚ A => f b) hExpD
    _ = IsNilpotent.exp a * b * IsNilpotent.exp (-a) := by
          rw [Module.End.mul_apply, hnegR, exp_mulLeft a hna,
            exp_mulRight (-a) hna.neg]
          simp [LinearMap.mulLeft_apply, LinearMap.mulRight_apply, mul_assoc]


private theorem commutator_pow_mem {A : Type*} [Ring A] [Algebra ℚ A] {s : ℕ}
    (F : NilpotentAlgebraFiltration A s) {a b : A} (ha : a ∈ F.layer 1)
    {j : ℕ} (hb : b ∈ F.layer 1) :
    (commutatorMap a ^ j) b ∈ F.layer (j + 1) := by
  have hraise {n : ℕ} {z : A} (hz : z ∈ F.layer n) :
      commutatorMap a z ∈ F.layer (n + 1) := by
    change a * z - z * a ∈ F.layer (n + 1)
    refine Submodule.sub_mem _ ?_ ?_
    · have h := F.mul_mem ha hz
      simpa [Nat.add_comm] using h
    · exact F.mul_mem hz ha
  induction j with
  | zero => simpa using hb
  | succ j ih =>
    rw [pow_succ']
    exact hraise ih

private theorem exp_conj_unit {A : Type*} [Ring A] [Algebra ℚ A]
    (u : Aˣ) (x : A) (hx : IsNilpotent x) :
    IsNilpotent.exp ((u : A) * x * ((u⁻¹ : Aˣ) : A)) =
      (u : A) * IsNilpotent.exp x * ((u⁻¹ : Aˣ) : A) := by
  obtain ⟨k, hk⟩ := hx
  have hpow (i : ℕ) :
      ((u : A) * x * ((u⁻¹ : Aˣ) : A)) ^ i = (u : A) * x ^ i * ((u⁻¹ : Aˣ) : A) :=
    u.conj_pow x i
  have hconjPow : ((u : A) * x * ((u⁻¹ : Aˣ) : A)) ^ k = 0 := by
    rw [hpow, hk]
    simp
  calc
    IsNilpotent.exp ((u : A) * x * ((u⁻¹ : Aˣ) : A)) =
        ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ •
          (((u : A) * x * ((u⁻¹ : Aˣ) : A)) ^ i) :=
      IsNilpotent.exp_eq_sum hconjPow
    _ = ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ •
          ((u : A) * x ^ i * ((u⁻¹ : Aˣ) : A)) := by
      apply sum_congr rfl
      intro i hi
      rw [hpow]
    _ = ∑ i ∈ range k, (u : A) * ((i.factorial : ℚ)⁻¹ • x ^ i) *
          ((u⁻¹ : Aˣ) : A) := by
      apply sum_congr rfl
      intro i hi
      calc
        (i.factorial : ℚ)⁻¹ • ((u : A) * x ^ i * ((u⁻¹ : Aˣ) : A)) =
            (i.factorial : ℚ)⁻¹ • ((u : A) * (x ^ i * ((u⁻¹ : Aˣ) : A))) := by rw [mul_assoc]
        _ = (u : A) * ((i.factorial : ℚ)⁻¹ • (x ^ i * ((u⁻¹ : Aˣ) : A))) := by
            rw [← mul_smul_comm]
        _ = (u : A) * (((i.factorial : ℚ)⁻¹ • x ^ i) * ((u⁻¹ : Aˣ) : A)) := by
            rw [smul_mul_assoc]
        _ = (u : A) * ((i.factorial : ℚ)⁻¹ • x ^ i) * ((u⁻¹ : Aˣ) : A) := by rw [mul_assoc]
    _ = (u : A) * (∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • x ^ i) *
          ((u⁻¹ : Aˣ) : A) := by
      calc
        _ = ∑ i ∈ range k, (u : A) *
              ((i.factorial : ℚ)⁻¹ • x ^ i) * ((u⁻¹ : Aˣ) : A) := rfl
        _ = (u : A) * (∑ i ∈ range k,
              ((i.factorial : ℚ)⁻¹ • x ^ i) * ((u⁻¹ : Aˣ) : A)) := by
                simp_rw [mul_assoc]
                rw [Finset.mul_sum]
        _ = (u : A) * ((∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • x ^ i) *
              ((u⁻¹ : Aˣ) : A)) := by rw [Finset.sum_mul]
        _ = (u : A) * (∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • x ^ i) *
              ((u⁻¹ : Aˣ) : A) := by rw [mul_assoc]
    _ = (u : A) * IsNilpotent.exp x * ((u⁻¹ : Aˣ) : A) := by
      exact congrArg (fun z : A => (u : A) * z * ((u⁻¹ : Aˣ) : A))
        (IsNilpotent.exp_eq_sum hk).symm

theorem lieBCH_conj_eq_commutator_exp {A : Type*} [Ring A] [Algebra ℚ A]
    {s : ℕ} (F : NilpotentAlgebraFiltration A s)
    {a b : A} (ha : a ∈ F.layer 1) (hb : b ∈ F.layer 1)
    (had : LieAlgebra.ad ℚ A a = commutatorMap a) :
    lieBCH s (lieBCH s a b) (-a) =
      ∑ j ∈ range (s + 1), (j.factorial : ℚ)⁻¹ • ((LieAlgebra.ad ℚ A a) ^ j) b := by
  let ab := nilpotentBCH a b
  let c := nilpotentBCH ab (-a)
  let r := ∑ j ∈ range (s + 1), (j.factorial : ℚ)⁻¹ •
      ((commutatorMap a) ^ j) b
  have hab : ab ∈ F.layer 1 := F.bch_mem le_rfl ha hb
  have hna : IsNilpotent a := F.positive_nilpotent a ha
  have hnb : IsNilpotent b := F.positive_nilpotent b hb
  have hneg : -a ∈ F.layer 1 := (F.layer 1).neg_mem ha
  have hcMem : c ∈ F.layer 1 := F.bch_mem le_rfl hab hneg
  have hcNil : IsNilpotent c := F.positive_nilpotent c hcMem
  have hrMem : r ∈ F.layer 1 := by
    apply Submodule.sum_mem
    intro j hj
    apply (F.layer 1).smul_mem
    have hpow := commutator_pow_mem F ha (j := j) hb
    have hjle : 1 ≤ j + 1 := by omega
    exact F.antitone hjle hpow
  have hrNil : IsNilpotent r := F.positive_nilpotent r hrMem
  let I := F.layerAlgebra 1
  have hI : ∀ z ∈ I, IsNilpotent z := fun z hz => F.positive_nilpotent z hz
  have hExpC : IsNilpotent.exp c =
      IsNilpotent.exp a * IsNilpotent.exp b * IsNilpotent.exp (-a) := by
    calc
      IsNilpotent.exp c = IsNilpotent.exp ab * IsNilpotent.exp (-a) :=
        exp_nilpotentBCH I hI hab hneg
      _ = (IsNilpotent.exp a * IsNilpotent.exp b) * IsNilpotent.exp (-a) := by
        rw [exp_nilpotentBCH I hI ha hb]
      _ = IsNilpotent.exp a * IsNilpotent.exp b * IsNilpotent.exp (-a) := by rw [mul_assoc]
  let u : Aˣ :=
    { val := IsNilpotent.exp a
      inv := IsNilpotent.exp (-a)
      val_inv := IsNilpotent.exp_mul_exp_neg_self hna
      inv_val := IsNilpotent.exp_neg_mul_exp_self hna }
  have hadj : r = IsNilpotent.exp a * b * IsNilpotent.exp (-a) :=
    commutator_exp_action F ha
  have hExpR : IsNilpotent.exp r =
      IsNilpotent.exp a * IsNilpotent.exp b * IsNilpotent.exp (-a) := by
    calc
      IsNilpotent.exp r = IsNilpotent.exp ((u : A) * b * ((u⁻¹ : Aˣ) : A)) := by rw [hadj]; rfl
      _ = (u : A) * IsNilpotent.exp b * ((u⁻¹ : Aˣ) : A) := exp_conj_unit u b hnb
      _ = IsNilpotent.exp a * IsNilpotent.exp b * IsNilpotent.exp (-a) := by rfl
  have hcr : c = r := exp_injective_on_nilpotents hcNil hrNil (hExpC.trans hExpR.symm)
  calc
    lieBCH s (lieBCH s a b) (-a) = c := by
      simp only [c, ab]
      rw [F.lieBCH_eq ha hb, F.lieBCH_eq hab hneg]
    _ = r := hcr
    _ = ∑ j ∈ range (s + 1), (j.factorial : ℚ)⁻¹ •
        ((LieAlgebra.ad ℚ A a) ^ j) b := by
      simp only [r, ← had]

/-- Local transfer helper for assembly; see the cycle note in `NOTES.md`. -/
theorem lieBCH_conj_eq_exp_ad_aux {M : Type*} [LieRing M] [LieAlgebra ℚ M] {S : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ M M S = ⊥) (a b : M) :
    lieBCH S (lieBCH S a b) (-a) =
      ∑ j ∈ Finset.range (S + 1), ((j.factorial : ℚ)⁻¹) • ((LieAlgebra.ad ℚ M a) ^ j) b := by
  let x : Fin 2 → FreeLieAlgebra ℚ (Fin 2) := FreeLieAlgebra.of ℚ
  let A := TruncatedSeries (FreeAlgebra ℚ (Fin 2)) S
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 2)) S
  let X := scaledFreeGenerator S (0 : Fin 2)
  let Y := scaledFreeGenerator S (1 : Fin 2)
  let ev := scaledFreeLieEval (X := Fin 2) S
  letI : LieRing A := LieRing.ofAssociativeRing
  have hgen (i : Fin 2) : scaledFreeGenerator S i ∈ F.layer 1 :=
    scaledFreeGenerator_mem_layer S i
  have hX : X ∈ F.layer 1 := hgen 0
  have hY : Y ∈ F.layer 1 := hgen 1
  have had : LieAlgebra.ad ℚ A X = commutatorMap X := by
    ext z
    simpa [commutatorMap, LieAlgebra.ad_apply, LinearMap.sub_apply,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply] using
      (LieRing.of_associative_ring_bracket X z)
  have hpow (j : ℕ) :
      ev (((LieAlgebra.ad ℚ (FreeLieAlgebra ℚ (Fin 2)) (x 0)) ^ j) (x 1)) =
        ((LieAlgebra.ad ℚ A X) ^ j) Y := by
    induction j with
    | zero => simp [ev, x, X, Y]
    | succ j ih =>
      simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
      calc
        ev ⁅x 0, ((LieAlgebra.ad ℚ (FreeLieAlgebra ℚ (Fin 2)) (x 0)) ^ j) (x 1)⁆ =
            ⁅ev (x 0), ev (((LieAlgebra.ad ℚ (FreeLieAlgebra ℚ (Fin 2)) (x 0)) ^ j) (x 1))⁆ :=
              ev.map_lie _ _
        _ = ⁅X, ((LieAlgebra.ad ℚ A X) ^ j) Y⁆ := by simp [ev, x, X, Y, ih]
  let p : FreeLieAlgebra ℚ (Fin 2) :=
    ∑ j ∈ Finset.range (S + 1), ((j.factorial : ℚ)⁻¹) •
      ((LieAlgebra.ad ℚ (FreeLieAlgebra ℚ (Fin 2)) (x 0)) ^ j) (x 1)
  have hp : ev p = ∑ j ∈ Finset.range (S + 1), ((j.factorial : ℚ)⁻¹) •
      (((LieAlgebra.ad ℚ A X) ^ j) Y) := by
    simp only [p, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun z => ((j.factorial : ℚ)⁻¹) • z) (hpow j)
  have hleft : ev (lieBCH S (lieBCH S (x 0) (x 1)) (-(x 0))) =
      lieBCH S (lieBCH S X Y) (-X) := by
    simp only [map_lieBCH, ev, x, X, Y, scaledFreeLieEval_of, map_neg]
  have hEval :
      ev (lieBCH S (lieBCH S (x 0) (x 1)) (-(x 0))) = ev p := by
    calc
      ev (lieBCH S (lieBCH S (x 0) (x 1)) (-(x 0))) =
          lieBCH S (lieBCH S X Y) (-X) := hleft
      _ = ∑ j ∈ Finset.range (S + 1), ((j.factorial : ℚ)⁻¹) •
            ((LieAlgebra.ad ℚ A X) ^ j) Y :=
          lieBCH_conj_eq_commutator_exp F hX hY had
      _ = ev p := hp.symm
  let φ := FreeLieAlgebra.lift ℚ ![a, b]
  have h := lie_lift_eq_of_scaledFreeLieEval_eq ![a, b] hnil hEval
  have hliftpow (j : ℕ) :
      φ (((LieAlgebra.ad ℚ (FreeLieAlgebra ℚ (Fin 2)) (x 0)) ^ j) (x 1)) =
        ((LieAlgebra.ad ℚ M a) ^ j) b := by
    induction j with
    | zero => simp [φ, x, Matrix.cons_val_zero, Matrix.cons_val_one]
    | succ j ih =>
      simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
      calc
        φ ⁅x 0, ((LieAlgebra.ad ℚ (FreeLieAlgebra ℚ (Fin 2)) (x 0)) ^ j) (x 1)⁆ =
            ⁅φ (x 0), φ (((LieAlgebra.ad ℚ (FreeLieAlgebra ℚ (Fin 2)) (x 0)) ^ j) (x 1))⁆ :=
              φ.map_lie _ _
        _ = ⁅a, ((LieAlgebra.ad ℚ M a) ^ j) b⁆ := by
              simp [φ, x, Matrix.cons_val_zero, Matrix.cons_val_one, ih]
  have hlhs : φ (lieBCH S (lieBCH S (x 0) (x 1)) (-(x 0))) =
      lieBCH S (lieBCH S a b) (-a) := by
    simp only [φ, map_lieBCH, x, map_neg, FreeLieAlgebra.lift_of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have hrhs : φ p = ∑ j ∈ Finset.range (S + 1), ((j.factorial : ℚ)⁻¹) •
      ((LieAlgebra.ad ℚ M a) ^ j) b := by
    simp only [p, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun z => ((j.factorial : ℚ)⁻¹) • z) (hliftpow j)
  exact hlhs.symm.trans (h.trans hrhs)

end HindmanSumsProducts.InverseBridge.AssemblyAdjoint

import HindmanSumsProducts.Arithmetic.Defs
import OAI.Combinatorics.SumProduct.Alignment.HarmonicTranslation01

open scoped BigOperators Topology
open Filter MeasureTheory

namespace HindmanSumsProducts
noncomputable section

/-- Error term `E_X(k)` in the harmonic residue estimate (§3, `lem:sampling`). -/
def harmonicResidueError (X W k : ℕ) : ℝ :=
  (W : ℝ) * (k + 1 : ℕ) / ((X : ℝ) * (Real.log X - (W : ℝ) / X))

/-- The pointwise clauses of the harmonic sampling lemma. -/
structure SamplingPointwiseBounds (X W : ℕ) : Prop where
  periodic_harmonic : ∀ (k a : ℕ) (A B : ℝ), Nat.Coprime k W → a < k → 0 < A → A < B →
    |(∑' n : ℕ, if A ≤ n ∧ (n : ℝ) < B ∧ Nat.Coprime n W ∧ n % k = a
        then 1 / (n : ℝ) else 0) -
      ((Nat.totient W : ℝ) / W / k * Real.log (B / A))| ≤ (Nat.totient W : ℝ) / A
  normalizer : ∀ hX : 2 ≤ X, Real.log X > (W : ℝ) / X →
    |harmonicNormalizer X W - (Nat.totient W : ℝ) / W * Real.log X| ≤ (Nat.totient W : ℝ) / X
  residue_pointwise : ∀ hX : 2 ≤ X, Real.log X > (W : ℝ) / X → ∀ k a : ℕ,
    Nat.Coprime k W → 0 < k → (ha : a < k) →
      |(k : ℝ) * harmonicResidueLaw (harmonicLaw X W) k ⟨a, ha⟩ - 1| ≤
        harmonicResidueError X W k
  residue_total_mass : ∀ hX : 2 ≤ X, Real.log X > (W : ℝ) / X → ∀ k : ℕ,
    Nat.Coprime k W → 0 < k →
      finiteL1 (harmonicResidueLaw (harmonicLaw X W) k) (uniformResidueLaw k) ≤
        harmonicResidueError X W k
  translation : ∀ hX : 2 ≤ X, Real.log X > (W : ℝ) / X → ∀ h : ℤ,
    (∃ m : ℤ, h = (W : ℤ) * m) →
      arithmeticL1 (translatedLaw (harmonicLaw X W) h) (harmonicLaw X W) ≤
        min 2 (2 * |(h : ℝ)| / ((X : ℝ) * (Real.log X - (W : ℝ) / X)))
  dilation : ∀ hX : 2 ≤ X, Real.log X > (W : ℝ) / X → ∀ k : ℕ,
    1 ≤ k → k ≤ X → Nat.Coprime k W →
      arithmeticL1 (dilatedLaw (harmonicLaw X W) k) (dilationReference (harmonicLaw X W) k) ≤
        (2 * Real.log k + (W : ℝ) * k / X * (1 + 1 / X)) /
          (Real.log X - (W : ℝ) / X) ∧
      |(∑' z : ℤ, dilationReference (harmonicLaw X W) k z) - 1| ≤
        harmonicResidueError X W k

/-- Why `sampling_pointwise_claim` assumes `0 < W` (in the paper `W` is a primorial): without it
the statement fails at `W = 0`.
For that value, `Nat.Coprime 1 0` leaves the single term `n = 1`, while its
claimed error bound is zero. -/
theorem sampling_pointwise_bounds_zero_false : ¬ SamplingPointwiseBounds 2 0 := by
  intro h
  have hh := h.periodic_harmonic 1 0 (1 / 2) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hs : (∑' n : ℕ, if (1 / 2 : ℝ) ≤ n ∧ (n : ℝ) < 2 ∧
      Nat.Coprime n 0 ∧ n % 1 = 0 then 1 / (n : ℝ) else 0) = 1 := by
    rw [tsum_eq_single 1]
    · norm_num [Nat.Coprime]
    · intro n hn
      simp [Nat.Coprime, hn]
  rw [hs] at hh
  norm_num at hh

private theorem active_unit_residue_card (W k a : ℕ) (hW : 0 < W) (hk : 0 < k)
    (hcop : Nat.Coprime k W) (ha : a < k) :
    (Finset.univ.filter (fun r : Fin (W * k) =>
      Nat.Coprime r.val W ∧ r.val % k = a)).card = Nat.totient W := by
  classical
  let R : Finset (Fin (W * k)) := Finset.univ.filter (fun r : Fin (W * k) =>
    Nat.Coprime r.val W ∧ r.val % k = a)
  let S : Finset (Fin W) := Finset.univ.filter (fun s : Fin W => Nat.Coprime s.val W)
  let crt (s : Fin W) := Nat.chineseRemainder hcop a s.val
  let e : {r : Fin (W * k) // r ∈ R} ≃ {s : Fin W // s ∈ S} := {
    toFun := fun (r : {r : Fin (W * k) // r ∈ R}) =>
      ⟨⟨r.val.val % W, Nat.mod_lt _ hW⟩, by
      rcases Finset.mem_filter.mp r.property with ⟨_, hR⟩
      have hcopr := hR.1
      have hcopmod : Nat.Coprime (r.val.val % W) W := by
        have hcopr' := hcopr
        rw [← Nat.mod_add_div r.val.val W] at hcopr'
        exact (Nat.coprime_add_mul_left_left _ W (r.val.val / W)).mp hcopr'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcopmod⟩⟩
    invFun := fun (s : {s : Fin W // s ∈ S}) => by
      let c := crt s.val
      have hlt : c.val < W * k := by
        have hlt' := Nat.chineseRemainder_lt_mul hcop a s.val.val (by omega) hW.ne'
        simpa [crt, Nat.mul_comm] using hlt'
      have hcopc : Nat.Coprime c.val W := by
        have hmod : c.val % W = s.val.val := by
          have hmodEq := (c.property.2 : c.val ≡ s.val.val [MOD W])
          simpa [Nat.ModEq, Nat.mod_eq_of_lt s.val.isLt] using hmodEq
        rw [← Nat.mod_add_div c.val W, hmod]
        exact (Nat.coprime_add_mul_left_left _ W (c.val / W)).2
          (Finset.mem_filter.mp s.property).2
      have hmodK : c.val % k = a := by
        have hmodEq := (c.property.1 : c.val ≡ a [MOD k])
        simpa [Nat.ModEq, Nat.mod_eq_of_lt ha] using hmodEq
      refine ⟨⟨c.val, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      exact ⟨hcopc, hmodK⟩
    left_inv := by
      intro r
      apply Subtype.ext
      apply Fin.ext
      rcases Finset.mem_filter.mp r.property with ⟨_, hrcond⟩
      rcases hrcond with ⟨hcopr, hrmodK⟩
      have hmodK : Nat.ModEq k r.val.val a := by
        change r.val.val % k = a % k
        simpa [Nat.mod_eq_of_lt ha] using hrmodK
      have hmodW : Nat.ModEq W r.val.val (r.val.val % W) := by
        change r.val.val % W = (r.val.val % W) % W
        rw [Nat.mod_eq_of_lt (Nat.mod_lt _ hW)]
      have hcrt := Nat.chineseRemainder_modEq_unique hcop hmodK hmodW
      have hlt' : crt (⟨r.val.val % W, Nat.mod_lt _ hW⟩ : Fin W) < k * W :=
        Nat.chineseRemainder_lt_mul hcop a (r.val.val % W) (by omega) hW.ne'
      have hltR : r.val.val < k * W := by simpa [Nat.mul_comm] using r.val.isLt
      have hmodEq := hcrt.eq_of_lt_of_lt hltR hlt'
      exact hmodEq.symm
    right_inv := by
      intro s
      apply Subtype.ext
      apply Fin.ext
      change (crt s.val).val % W = s.val.val
      have hmodEq : (crt s.val).val % W = s.val.val % W :=
        (crt s.val).property.2
      rw [Nat.mod_eq_of_lt s.val.isLt] at hmodEq
      exact hmodEq
  }
  have hcard : Fintype.card {r : Fin (W * k) // r ∈ R} =
      Fintype.card {s : Fin W // s ∈ S} := Fintype.card_congr e
  have hs : Fintype.card {s : Fin W // s ∈ S} = Nat.totient W := by
    let eNat : {s : Fin W // s ∈ S} ≃ {m : ℕ // m < W ∧ Nat.Coprime W m} := {
      toFun := fun (s : {s : Fin W // s ∈ S}) =>
        ⟨s.val.val, ⟨s.val.isLt, (Finset.mem_filter.mp s.property).2.symm⟩⟩
      invFun := fun (m : {m : ℕ // m < W ∧ Nat.Coprime W m}) =>
        ⟨⟨m.val, m.property.1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, m.property.2.symm⟩⟩
      left_inv := by
        intro s
        apply Subtype.ext
        apply Fin.ext
        rfl
      right_inv := by
        intro m
        apply Subtype.ext
        rfl
    }
    calc
      _ = Nat.card {s : Fin W // s ∈ S} := Nat.card_eq_fintype_card.symm
      _ = Nat.card {m : ℕ // m < W ∧ Nat.Coprime W m} := Nat.card_congr eNat
      _ = Nat.totient W := (Nat.totient_eq_card_lt_and_coprime W).symm
  calc
    R.card = Fintype.card {r : Fin (W * k) // r ∈ R} := (Fintype.card_coe R).symm
    _ = Fintype.card {s : Fin W // s ∈ S} := hcard
    _ = Nat.totient W := hs

-- Adapted from OpenAI openai/math (Apache-2.0),
-- OAI/NumberTheory/JointDickman/Arithmetic/HarmonicSummation.lean.
private noncomputable def samplingFiniteCountingFunction (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, w n

private theorem interval_residue_card_error (a T k r : ℕ) (hk : 0 < k)
    (hr : r < k) :
    |(({n ∈ Finset.Ico a (a + T) | n % k = r}.card : ℝ) - (T : ℝ) / k)| ≤ 1 := by
  let A : ℚ := ((a : ℚ) - r) / k
  let B : ℚ := ((a + T : ℕ) - r) / k
  have hrel : B = A + (T : ℚ) / k := by
    dsimp [A, B]
    push_cast
    field_simp
    ring
  have hset : {n ∈ Finset.Ico a (a + T) | n % k = r} =
      {n ∈ Finset.Ico a (a + T) | n ≡ r [MOD k]} := by
    ext n
    simp [Nat.ModEq, Nat.mod_eq_of_lt hr]
  have hceil : ⌈A⌉ ≤ ⌈B⌉ := Int.ceil_mono (by
    rw [hrel]
    exact le_add_of_nonneg_right (div_nonneg (by positivity) (by positivity)))
  have hcardZ :
      (({n ∈ Finset.Ico a (a + T) | n % k = r}.card : ℕ) : ℤ) = ⌈B⌉ - ⌈A⌉ := by
    rw [hset]
    have hc := Nat.Ico_filter_modEq_card a (a + T) hk r
    rw [show (↑(a + T : ℕ) - ↑r : ℚ) / ↑k = B by rfl,
      show (↑(a : ℕ) - ↑r : ℚ) / ↑k = A by rfl] at hc
    rw [max_eq_left (sub_nonneg.mpr hceil)] at hc
    exact hc
  have hcardR :
      (({n ∈ Finset.Ico a (a + T) | n % k = r}.card : ℕ) : ℝ) =
        (⌈B⌉ : ℤ) - ⌈A⌉ := by exact_mod_cast hcardZ
  have hAlo : (A : ℝ) ≤ (⌈A⌉ : ℝ) := by exact_mod_cast (Int.le_ceil A)
  have hAhi : (⌈A⌉ : ℝ) < (A : ℝ) + 1 := by exact_mod_cast (Int.ceil_lt_add_one A)
  have hBlo : (B : ℝ) ≤ (⌈B⌉ : ℝ) := by exact_mod_cast (Int.le_ceil B)
  have hBhi : (⌈B⌉ : ℝ) < (B : ℝ) + 1 := by exact_mod_cast (Int.ceil_lt_add_one B)
  have hrelR : (B : ℝ) = (A : ℝ) + (T : ℝ) / k := by
    calc
      (B : ℝ) = ((A + (T : ℚ) / k : ℚ) : ℝ) := congrArg (fun x : ℚ => (x : ℝ)) hrel
      _ = (A : ℝ) + (T : ℝ) / k := by simp only [Rat.cast_add, Rat.cast_div, Rat.cast_natCast]
  rw [hcardR, abs_le]
  constructor <;> nlinarith [hrelR]

private theorem interval_residue_card_strict_error (a T k r : ℕ) (hk : 0 < k)
    (hr : r < k) :
    |(({n ∈ Finset.Ico a (a + T) | n % k = r}.card : ℝ) - (T : ℝ) / k)| < 1 := by
  let A : ℚ := ((a : ℚ) - r) / k
  let B : ℚ := ((a + T : ℕ) - r) / k
  have hrel : B = A + (T : ℚ) / k := by
    dsimp [A, B]
    push_cast
    field_simp
    ring
  have hset : {n ∈ Finset.Ico a (a + T) | n % k = r} =
      {n ∈ Finset.Ico a (a + T) | n ≡ r [MOD k]} := by
    ext n
    simp [Nat.ModEq, Nat.mod_eq_of_lt hr]
  have hceil : ⌈A⌉ ≤ ⌈B⌉ := Int.ceil_mono (by
    rw [hrel]
    exact le_add_of_nonneg_right (div_nonneg (by positivity) (by positivity)))
  have hcardZ :
      (({n ∈ Finset.Ico a (a + T) | n % k = r}.card : ℕ) : ℤ) = ⌈B⌉ - ⌈A⌉ := by
    rw [hset]
    have hc := Nat.Ico_filter_modEq_card a (a + T) hk r
    rw [show (↑(a + T : ℕ) - ↑r : ℚ) / ↑k = B by rfl,
      show (↑(a : ℕ) - ↑r : ℚ) / ↑k = A by rfl] at hc
    rw [max_eq_left (sub_nonneg.mpr hceil)] at hc
    exact hc
  have hcardR :
      (({n ∈ Finset.Ico a (a + T) | n % k = r}.card : ℕ) : ℝ) =
        (⌈B⌉ : ℤ) - ⌈A⌉ := by exact_mod_cast hcardZ
  have hAlo : (A : ℝ) ≤ (⌈A⌉ : ℝ) := by exact_mod_cast (Int.le_ceil A)
  have hAhi : (⌈A⌉ : ℝ) < (A : ℝ) + 1 := by exact_mod_cast (Int.ceil_lt_add_one A)
  have hBlo : (B : ℝ) ≤ (⌈B⌉ : ℝ) := by exact_mod_cast (Int.le_ceil B)
  have hBhi : (⌈B⌉ : ℝ) < (B : ℝ) + 1 := by exact_mod_cast (Int.ceil_lt_add_one B)
  have hrelR : (B : ℝ) = (A : ℝ) + (T : ℝ) / k := by
    calc
      (B : ℝ) = ((A + (T : ℚ) / k : ℚ) : ℝ) := congrArg (fun x : ℚ => (x : ℝ)) hrel
      _ = (A : ℝ) + (T : ℝ) / k := by simp only [Rat.cast_add, Rat.cast_div, Rat.cast_natCast]
  rw [hcardR]
  rw [abs_lt]
  constructor <;> nlinarith [hrelR]

private theorem periodic_count_integer_deviation (L C : ℕ) (R : Finset (Fin L))
    (hcard : R.card = C) (hL : 0 < L) (a T : ℕ) :
      |(({n ∈ Finset.Ico a (a + T) |
        (⟨n % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R}.card : ℕ) : ℝ) -
      (C : ℝ) / L * T| ≤ (C : ℝ) * (1 - (C : ℝ) / L) := by
  classical
  let s : Finset ℕ := Finset.Ico a (a + T)
  let c (r : Fin L) : ℕ := {n ∈ s | n % L = r.val}.card
  let q := T / L
  let v := T % L
  have hT : T = q * L + v := by
    calc
      T = T % L + L * (T / L) := (Nat.mod_add_div T L).symm
      _ = (T / L) * L + T % L := by ac_rfl
      _ = q * L + v := rfl
  have hv : v < L := by dsimp [v]; exact Nat.mod_lt _ hL
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hratio : (T : ℝ) / L = (q : ℝ) + (v : ℝ) / L := by
    rw [hT]
    push_cast
    field_simp
    <;> ring
  have hchoice (r : Fin L) : c r = q ∨ c r = q + 1 := by
    have hs := interval_residue_card_strict_error a T L r.val hL r.isLt
    have hstrict := abs_lt.mp hs
    have hlow : (q : ℝ) ≤ (c r : ℝ) := by
      by_contra hn
      have hnatlt : c r < q := by
        by_contra h
        apply hn
        exact_mod_cast (le_of_not_gt h)
      have hnat : c r + 1 ≤ q := Nat.succ_le_of_lt hnatlt
      have hc : (c r : ℝ) + 1 ≤ q := by exact_mod_cast hnat
      have hvnonneg : 0 ≤ (v : ℝ) / L := by positivity
      nlinarith [hstrict.1, hratio, hvnonneg, hc]
    have hhigh : (c r : ℝ) ≤ (q : ℝ) + 1 := by
      by_contra hn
      have hc : (q : ℝ) + 2 ≤ (c r : ℝ) := by
        have hnat : q + 1 < c r := by
          by_contra h
          apply hn
          exact_mod_cast (le_of_not_gt h)
        have : q + 2 ≤ c r := Nat.succ_le_of_lt hnat
        exact_mod_cast this
      have hvlt : (v : ℝ) / L < 1 := by
        apply (div_lt_one hLreal).2
        exact_mod_cast hv
      nlinarith [hstrict.2, hratio, hvlt]
    have hloNat : q ≤ c r := by exact_mod_cast hlow
    have hhiNat : c r ≤ q + 1 := by exact_mod_cast hhigh
    omega
  have hclassSum : (∑ r : Fin L, c r) = T := by
    have h := Finset.sum_fiberwise s
      (fun n : ℕ => (⟨n % L, Nat.mod_lt _ hL⟩ : Fin L)) (fun _ => (1 : ℕ))
    have h' : (∑ r : Fin L, c r) = s.card := by
      simpa [c, s, Fin.ext_iff] using h
    simpa [s] using h'
  let extra (r : Fin L) : ℕ := if c r = q + 1 then 1 else 0
  have hextra (r : Fin L) : c r = q + extra r := by
    rcases hchoice r with h | h
    · simp [extra, h]
    · simp [extra, h]
  have hextraAll : (∑ r : Fin L, extra r) = v := by
    have hsum := hclassSum
    have hsum' : (∑ r : Fin L, c r) = L * q + ∑ r : Fin L, extra r := by
      calc
        _ = ∑ r : Fin L, (q + extra r) := by
          apply Finset.sum_congr rfl
          intro r _
          exact hextra r
        _ = _ := by simp [Finset.sum_add_distrib, Fintype.card_fin, add_comm]
    rw [hT, Nat.mul_comm q L] at hsum
    rw [hsum'] at hsum
    omega
  let activeExtra : ℕ := ∑ r ∈ R, extra r
  have hactiveExtra_le_C : activeExtra ≤ C := by
    calc
      activeExtra ≤ ∑ r ∈ R, 1 := by
        apply Finset.sum_le_sum
        intro r hr
        by_cases h : c r = q + 1 <;> simp [extra, h]
      _ = R.card := by simp
      _ = C := hcard
  have hactiveExtra_le_v : activeExtra ≤ v := by
    have hnonneg : ∀ r, 0 ≤ (extra r : ℝ) := fun _ => by positivity
    have hnat : activeExtra ≤ ∑ r : Fin L, extra r := by
      classical
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R)
      · intro r hr hnot
        exact Nat.zero_le _
    rw [hextraAll] at hnat
    exact hnat
  have hinactive : v - activeExtra ≤ L - C := by
    have hsumRest : (∑ r ∈ Rᶜ, extra r) = v - activeExtra := by
      have hdisj : Disjoint R Rᶜ := by
        apply Finset.disjoint_left.mpr
        intro r hr hrc
        exact (Finset.mem_compl.mp hrc) hr
      have hunion : R ∪ Rᶜ = (Finset.univ : Finset (Fin L)) := by ext r; simp
      have htotal : activeExtra + (∑ r ∈ Rᶜ, extra r) = v := by
        calc
          _ = ∑ r ∈ R ∪ Rᶜ, extra r := by
            dsimp [activeExtra]
            rw [← Finset.sum_union hdisj]
          _ = ∑ r : Fin L, extra r := by rw [hunion]
          _ = v := hextraAll
      dsimp [activeExtra] at htotal
      rw [← htotal]
      omega
    calc
      _ = ∑ r ∈ Rᶜ, extra r := hsumRest.symm
      _ ≤ ∑ r ∈ Rᶜ, 1 := by
        apply Finset.sum_le_sum
        intro r hr
        by_cases h : c r = q + 1 <;> simp [extra, h]
      _ = Rᶜ.card := by simp
      _ = L - C := by rw [Finset.card_compl, Fintype.card_fin, hcard]
  have hcount :
      ({n ∈ s | (⟨n % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R}.card : ℕ) =
        q * C + activeExtra := by
    have hactive :
        {n ∈ s | (⟨n % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R}.card =
          ∑ r ∈ R, c r := by
      let g (n : ℕ) := (⟨n % L, Nat.mod_lt _ hL⟩ : Fin L)
      let A := s.filter (fun n => g n ∈ R)
      let fiber (r : Fin L) := (A.filter (fun n => g n = r)).card
      have hsumFiber : (∑ r : Fin L, fiber r) = A.card := by
        have h := Finset.sum_fiberwise A g (fun _ => (1 : ℕ))
        simpa [fiber, Finset.sum_filter] using h
      have hzero (r : Fin L) (hr : r ∉ R) : fiber r = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro n hnA hgr
        rcases Finset.mem_filter.mp hnA with ⟨_, hmemg⟩
        exact hr (hgr ▸ hmemg)
      have hmem (r : Fin L) (hr : r ∈ R) : fiber r = c r := by
        apply congrArg Finset.card
        ext n
        simp only [fiber, A, c, g, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hnS, _⟩, hgr⟩
          exact ⟨hnS, congrArg Fin.val hgr⟩
        · rintro ⟨hnS, hgr⟩
          have hgrFin : g n = r := by
            apply Fin.ext
            simpa [g] using hgr
          have hmemR : g n ∈ R := by simpa [hgrFin] using hr
          exact ⟨⟨hnS, hmemR⟩, hgrFin⟩
      have hsumRestrict : (∑ r : Fin L, fiber r) = ∑ r ∈ R, c r := by
        calc
          _ = ∑ r ∈ R, fiber r := by
            symm
            apply Finset.sum_subset (Finset.subset_univ R)
            intro r hr hnot
            exact hzero r hnot
          _ = _ := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hmem r hr
      simpa [A, s] using hsumFiber.symm.trans hsumRestrict
    rw [hactive]
    simp_rw [hextra]
    simp [Finset.sum_add_distrib, activeExtra, hcard, Nat.mul_comm]
  have hC_le_L : C ≤ L := by
    rw [← hcard]
    simpa [Fintype.card_fin] using Finset.card_le_univ R
  have hθ : 0 ≤ (C : ℝ) / L ∧ (C : ℝ) / L ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one hLreal).2 (by exact_mod_cast hC_le_L)
  let xR : ℝ := activeExtra
  let cR : ℝ := C
  let vR : ℝ := v
  let lR : ℝ := L
  have hcR : 0 ≤ cR := by dsimp [cR]; positivity
  have hlR : 0 < lR := by dsimp [lR]; exact_mod_cast hL
  have hrestR : 0 ≤ lR - cR := by
    dsimp [lR, cR]
    exact_mod_cast (Nat.zero_le (L - C))
  have hnum : |lR * xR - cR * vR| ≤ cR * (lR - cR) := by
    have hx0 : 0 ≤ xR := by dsimp [xR]; positivity
    have hxc : xR ≤ cR := by dsimp [xR, cR]; exact_mod_cast hactiveExtra_le_C
    have hxv : xR ≤ vR := by dsimp [xR, vR]; exact_mod_cast hactiveExtra_le_v
    have hvrest : vR - xR ≤ lR - cR := by
      dsimp [vR, xR, lR, cR]
      exact_mod_cast hinactive
    have hvL : vR ≤ lR := by
      dsimp [vR, lR]
      exact_mod_cast (Nat.le_of_lt hv)
    rw [abs_le]
    constructor
    · by_cases hsmall : vR ≤ lR - cR
      · have hprod := mul_le_mul_of_nonneg_left hsmall hcR
        have hprod' := mul_nonneg hrestR hcR
        nlinarith [hprod, hprod', hx0, hrestR]
      · have hxlower : vR - (lR - cR) ≤ xR := by linarith [hvrest]
        have hprod := mul_le_mul_of_nonneg_left hxlower hlR.le
        have hrem : lR - vR ≤ cR := by linarith [hvL, hsmall]
        have hprod' := mul_le_mul_of_nonneg_left hrem hrestR
        nlinarith [hprod, hprod', hrestR]
    · by_cases hsmall : vR ≤ cR
      · have hprod := mul_le_mul_of_nonneg_left hxv hlR.le
        have hcross : 0 ≤ (lR - cR) * (cR - vR) :=
          mul_nonneg hrestR (by linarith)
        nlinarith [hprod, hcross, hrestR]
      · have hcv : cR ≤ vR := le_of_lt (lt_of_not_ge hsmall)
        have hprod := mul_le_mul_of_nonneg_left hxc hlR.le
        have hprod' := mul_le_mul_of_nonneg_left hcv hcR
        nlinarith [hprod, hprod', hcR]
  have htheta : cR / lR * lR = cR := by
    dsimp [cR, lR]
    field_simp [ne_of_gt hlR]
  have hdev :
      |xR - cR / lR * vR| ≤ cR * (1 - cR / lR) := by
    calc
      |xR - cR / lR * vR| = |(lR * xR - cR * vR) / lR| := by
        congr 1
        field_simp [ne_of_gt hlR]
        <;> ring
      _ = |lR * xR - cR * vR| / lR := by
        rw [abs_div, abs_of_pos hlR]
      _ ≤ (cR * (lR - cR)) / lR :=
        div_le_div_of_nonneg_right hnum hlR.le
      _ = cR * (1 - cR / lR) := by
        field_simp [ne_of_gt hlR]
        <;> ring
  have hmain :
      |((({n ∈ s | (⟨n % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R}.card : ℕ) : ℝ) -
        (C : ℝ) / L * T)| ≤ (C : ℝ) * (1 - (C : ℝ) / L) := by
    rw [hcount, hT]
    push_cast
    calc
      |((q : ℝ) * C + activeExtra) - (C : ℝ) / L *
          ((q : ℝ) * L + v)| = |(activeExtra : ℝ) - (C : ℝ) / L * v| := by
            congr 1
            field_simp [ne_of_gt hLreal]
            <;> ring
      _ ≤ (C : ℝ) * (1 - (C : ℝ) / L) := hdev
  exact hmain

private theorem periodic_count_real_deviation (L C : ℕ) (R : Finset (Fin L))
    (hcard : R.card = C) (hC : 1 ≤ C) (hL : 0 < L)
    (A t : ℝ) (hA : 0 ≤ A) (hAt : A ≤ t) :
      |({n ∈ Finset.Ico ⌈A⌉₊ (⌊t⌋₊ + 1) |
          (⟨n % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R}.card : ℝ) -
      (C : ℝ) / L * (t - A)| ≤ C := by
  let m := ⌈A⌉₊
  let n := ⌊t⌋₊ + 1
  have htn : t < (n : ℝ) := by
    dsimp [n]
    simpa [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one t
  have hm_lt : (m : ℝ) < t + 1 := by
    have hmA : (m : ℝ) < A + 1 := by dsimp [m]; exact Nat.ceil_lt_add_one hA
    linarith
  have hm_succ : m < n + 1 := by
    have : (m : ℝ) < (n : ℝ) + 1 := by linarith
    exact_mod_cast this
  have hmn : m ≤ n := by omega
  have hT : m + (n - m) = n := Nat.add_sub_of_le hmn
  have hAlo : A ≤ (m : ℝ) := by dsimp [m]; exact Nat.le_ceil A
  have hAhi : (m : ℝ) < A + 1 := by
    dsimp [m]
    exact Nat.ceil_lt_add_one hA
  have hTcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    exact Nat.cast_sub hmn
  have hround : |((n - m : ℕ) : ℝ) - (t - A)| ≤ 1 := by
    rw [hTcast]
    have hmerr0 : 0 ≤ (m : ℝ) - A := sub_nonneg.mpr hAlo
    have hmerr1 : (m : ℝ) - A < 1 := by nlinarith [hAhi]
    have hnerr0 : 0 ≤ (n : ℝ) - t := sub_nonneg.mpr (le_of_lt htn)
    have hnFloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (le_trans hA hAt)
    have hnerr1 : (n : ℝ) - t ≤ 1 := by dsimp [n]; push_cast; linarith
    rw [abs_le]
    constructor <;> nlinarith
  have htheta0 : 0 ≤ (C : ℝ) / L := by positivity
  have htheta1 : (C : ℝ) / L ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hL)).2
    have hCR : (C : ℝ) ≤ L := by
      rw [← hcard]
      exact_mod_cast (by simpa [Fintype.card_fin] using Finset.card_le_univ R)
    exact hCR
  have hInt :
      |(({x ∈ Finset.Ico m n |
          (⟨x % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R}.card : ℕ) : ℝ) -
        (C : ℝ) / L * (n - m : ℕ)| ≤
          (C : ℝ) * (1 - (C : ℝ) / L) := by
    simpa [hT] using periodic_count_integer_deviation L C R hcard hL m (n - m)
  have hδ : (C : ℝ) * (1 - (C : ℝ) / L) + (C : ℝ) / L ≤ C := by
    have hCR : 1 ≤ (C : ℝ) := by exact_mod_cast hC
    have hmul : 0 ≤ (C : ℝ) / L * ((C : ℝ) - 1) :=
      mul_nonneg htheta0 (sub_nonneg.mpr hCR)
    nlinarith [hmul]
  have hsplit :
      (({x ∈ Finset.Ico m n |
        (⟨x % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R}.card : ℕ) : ℝ) -
        (C : ℝ) / L * (t - A) =
      ((({x ∈ Finset.Ico m n |
        (⟨x % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R}.card : ℕ) : ℝ) -
        (C : ℝ) / L * (n - m : ℕ)) +
        (C : ℝ) / L * (((n - m : ℕ) : ℝ) - (t - A)) := by
    rw [hTcast]
    ring
  calc
    _ = |((({x ∈ Finset.Ico m n |
          (⟨x % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R}.card : ℕ) : ℝ) -
        (C : ℝ) / L * (n - m : ℕ)) +
          (C : ℝ) / L * (((n - m : ℕ) : ℝ) - (t - A))| := by rw [hsplit]
    _ ≤ |((({x ∈ Finset.Ico m n |
          (⟨x % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R}.card : ℕ) : ℝ) -
        (C : ℝ) / L * (n - m : ℕ))| +
          |(C : ℝ) / L * (((n - m : ℕ) : ℝ) - (t - A))| := abs_add_le _ _
    _ ≤ (C : ℝ) * (1 - (C : ℝ) / L) + (C : ℝ) / L := by
          apply add_le_add hInt ?_
          rw [abs_mul, abs_of_nonneg htheta0]
          simpa using mul_le_mul_of_nonneg_left hround htheta0
    _ ≤ C := hδ

private theorem periodic_count_real_deviation_halfopen (L C : ℕ) (R : Finset (Fin L))
    (hcard : R.card = C) (hC : 1 ≤ C) (hL : 0 < L)
    (A t : ℝ) (hA : 0 ≤ A) (hAt : A ≤ t) :
      |({n ∈ Finset.Ico ⌈A⌉₊ ⌈t⌉₊ |
          (⟨n % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R}.card : ℝ) -
      (C : ℝ) / L * (t - A)| ≤ C := by
  let m := ⌈A⌉₊
  let n := ⌈t⌉₊
  have hmn : m ≤ n := Nat.ceil_mono hAt
  have hT : m + (n - m) = n := Nat.add_sub_of_le hmn
  have hTcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    exact Nat.cast_sub hmn
  have hAlo : A ≤ (m : ℝ) := by dsimp [m]; exact Nat.le_ceil A
  have hAhi : (m : ℝ) < A + 1 := by dsimp [m]; exact Nat.ceil_lt_add_one hA
  have hTlo : t ≤ (n : ℝ) := by dsimp [n]; exact Nat.le_ceil t
  have hThi : (n : ℝ) < t + 1 := by
    dsimp [n]
    exact Nat.ceil_lt_add_one (le_trans hA hAt)
  have hround : |((n - m : ℕ) : ℝ) - (t - A)| < 1 := by
    rw [hTcast, abs_lt]
    constructor <;> nlinarith [hAlo, hAhi, hTlo, hThi]
  have htheta0 : 0 ≤ (C : ℝ) / L := by positivity
  have htheta1 : (C : ℝ) / L ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hL)).2
    have hCR : (C : ℝ) ≤ L := by
      rw [← hcard]
      exact_mod_cast (by simpa [Fintype.card_fin] using Finset.card_le_univ R)
    exact hCR
  have hInt :
      |(({x ∈ Finset.Ico m n |
          (⟨x % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R}.card : ℕ) : ℝ) -
        (C : ℝ) / L * (n - m : ℕ)| ≤
          (C : ℝ) * (1 - (C : ℝ) / L) := by
    simpa [hT] using periodic_count_integer_deviation L C R hcard hL m (n - m)
  have hδ : (C : ℝ) * (1 - (C : ℝ) / L) + (C : ℝ) / L ≤ C := by
    have hCR : 1 ≤ (C : ℝ) := by exact_mod_cast hC
    have hmul : 0 ≤ (C : ℝ) / L * ((C : ℝ) - 1) :=
      mul_nonneg htheta0 (sub_nonneg.mpr hCR)
    nlinarith [hmul]
  have hsplit :
      (({x ∈ Finset.Ico m n |
        (⟨x % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R}.card : ℕ) : ℝ) -
        (C : ℝ) / L * (t - A) =
      ((({x ∈ Finset.Ico m n |
        (⟨x % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R}.card : ℕ) : ℝ) -
        (C : ℝ) / L * (n - m : ℕ)) +
        (C : ℝ) / L * (((n - m : ℕ) : ℝ) - (t - A)) := by
    rw [hTcast]
    ring
  rw [show (Finset.Ico ⌈A⌉₊ ⌈t⌉₊) = Finset.Ico m n by rfl]
  rw [hsplit]
  calc
    _ ≤ |(({x ∈ Finset.Ico m n |
          (⟨x % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R}.card : ℕ) : ℝ) -
          (C : ℝ) / L * (n - m : ℕ)| +
          |(C : ℝ) / L * (((n - m : ℕ) : ℝ) - (t - A))| := abs_add_le _ _
    _ ≤ (C : ℝ) * (1 - (C : ℝ) / L) + (C : ℝ) / L := by
      apply add_le_add hInt
      rw [abs_mul, abs_of_nonneg htheta0]
      calc
        (C : ℝ) / L * |((n - m : ℕ) : ℝ) - (t - A)| ≤
            (C : ℝ) / L * 1 :=
          mul_le_mul_of_nonneg_left hround.le htheta0
        _ = (C : ℝ) / L := by ring
    _ ≤ C := hδ

private theorem samplingFiniteCountingFunction_periodic_bound
    (L C : ℕ) (R : Finset (Fin L)) (hcard : R.card = C) (hC : 1 ≤ C)
    (hL : 0 < L) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∀ t ∈ Set.Icc A B,
      |samplingFiniteCountingFunction
          (fun (n : ℕ) => if A ≤ (n : ℝ) ∧ (n : ℝ) < B ∧
              (⟨(n % L : ℕ), Nat.mod_lt n hL⟩ : Fin L) ∈ R then 1 else 0) t -
          (C : ℝ) / L * (t - A)| ≤ C := by
  classical
  intro t ht
  let w : ℕ → ℝ := fun (n : ℕ) =>
    if A ≤ (n : ℝ) ∧ (n : ℝ) < B ∧
      (⟨(n % L : ℕ), Nat.mod_lt n hL⟩ : Fin L) ∈ R then 1 else 0
  by_cases htb : t < B
  · have hset :
      (Finset.Icc 0 ⌊t⌋₊).filter (fun (n : ℕ) =>
          A ≤ (n : ℝ) ∧ (n : ℝ) < B ∧
            (⟨(n % L : ℕ), Nat.mod_lt n hL⟩ : Fin L) ∈ R) =
        (Finset.Ico ⌈A⌉₊ (⌊t⌋₊ + 1)).filter (fun (n : ℕ) =>
            (⟨(n % L : ℕ), Nat.mod_lt n hL⟩ : Fin L) ∈ R) := by
      ext (n : ℕ)
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨hn0, hnt⟩, ⟨hA_n, hnB, hres⟩⟩
        exact ⟨⟨(Nat.ceil_le).2 hA_n, by omega⟩, hres⟩
      · rintro ⟨⟨hceil, hupper⟩, hres⟩
        have hA_n : A ≤ (n : ℝ) := (Nat.ceil_le.mp hceil)
        have hnt : n ≤ ⌊t⌋₊ := Nat.le_of_lt_succ hupper
        have hnpos : 0 < n := by exact_mod_cast (lt_of_lt_of_le hA hA_n)
        have hfloorpos : 0 < ⌊t⌋₊ := lt_of_lt_of_le hnpos hnt
        have htpos : 0 ≤ t := by linarith [(Nat.floor_pos.mp hfloorpos)]
        have hncast : (n : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hnt
        have hfloorle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le htpos
        have hntR : (n : ℝ) ≤ t := hncast.trans hfloorle
        exact ⟨⟨Nat.zero_le _, hnt⟩, ⟨hA_n, hntR.trans_lt htb, hres⟩⟩
    have hF : samplingFiniteCountingFunction w t =
        (((Finset.Ico ⌈A⌉₊ (⌊t⌋₊ + 1)).filter (fun (n : ℕ) =>
          (⟨(n % L : ℕ), Nat.mod_lt n hL⟩ : Fin L) ∈ R)).card : ℝ) := by
      unfold samplingFiniteCountingFunction w
      rw [← Finset.sum_filter, hset]
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hF]
    exact periodic_count_real_deviation L C R hcard hC hL A t hA.le ht.1
  · have htbEq : t = B := le_antisymm ht.2 (le_of_not_gt htb)
    subst t
    have hset :
      (Finset.Icc 0 ⌊B⌋₊).filter (fun (n : ℕ) =>
          A ≤ (n : ℝ) ∧ (n : ℝ) < B ∧
            (⟨(n % L : ℕ), Nat.mod_lt n hL⟩ : Fin L) ∈ R) =
        (Finset.Ico ⌈A⌉₊ ⌈B⌉₊).filter (fun (n : ℕ) =>
            (⟨(n % L : ℕ), Nat.mod_lt n hL⟩ : Fin L) ∈ R) := by
      ext (n : ℕ)
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨hn0, hnB⟩, ⟨hA_n, hnB', hres⟩⟩
        exact ⟨⟨(Nat.ceil_le).2 hA_n, (Nat.lt_ceil).2 hnB'⟩, hres⟩
      · rintro ⟨⟨hceilA, hceilB⟩, hres⟩
        have hA_n : A ≤ (n : ℝ) := Nat.ceil_le.mp hceilA
        have hnB' : (n : ℝ) < B := (Nat.lt_ceil.mp hceilB)
        have hnB : n ≤ ⌊B⌋₊ := Nat.le_floor hnB'.le
        exact ⟨⟨Nat.zero_le _, hnB⟩, ⟨hA_n, hnB', hres⟩⟩
    have hF : samplingFiniteCountingFunction w B =
        (((Finset.Ico ⌈A⌉₊ ⌈B⌉₊).filter (fun (n : ℕ) =>
          (⟨(n % L : ℕ), Nat.mod_lt n hL⟩ : Fin L) ∈ R)).card : ℝ) := by
      unfold samplingFiniteCountingFunction w
      rw [← Finset.sum_filter, hset]
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hF]
    exact periodic_count_real_deviation_halfopen L C R hcard hC hL A B hA.le hAB.le

private theorem nat_ceil_eq_floor_or_succ (x : ℝ) (hx : 0 ≤ x) :
    ⌈x⌉₊ = ⌊x⌋₊ ∨ ⌈x⌉₊ = ⌊x⌋₊ + 1 := by
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hfu : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hcl : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hcu : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  have hle : ⌊x⌋₊ ≤ ⌈x⌉₊ := by exact_mod_cast hfl.trans hcl
  have hlt : ⌈x⌉₊ < ⌊x⌋₊ + 2 := by
    have hreal : (⌈x⌉₊ : ℝ) < (⌊x⌋₊ : ℝ) + 2 := by linarith
    exact_mod_cast hreal
  omega

private theorem sampling_sum_Ico_eq_Ioc_add_count (w : ℕ → ℝ) {A B : ℝ}
    (hA : 0 < A) (hAB : A < B)
    (hbelow : ∀ n : ℕ, (n : ℝ) < A → w n = 0)
    (habove : ∀ n : ℕ, B ≤ (n : ℝ) → w n = 0) :
    (∑ n ∈ Finset.Ico ⌈A⌉₊ ⌈B⌉₊, w n / (n : ℝ)) =
      (∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, w n / (n : ℝ)) +
        samplingFiniteCountingFunction w A / A := by
  classical
  let m := ⌊A⌋₊
  let n := ⌊B⌋₊
  let cA := ⌈A⌉₊
  let cB := ⌈B⌉₊
  have hcaseA := nat_ceil_eq_floor_or_succ A (le_of_lt hA)
  have hcaseB := nat_ceil_eq_floor_or_succ B (le_trans hA.le hAB.le)
  have hfloorA : (m : ℝ) ≤ A := by dsimp [m]; exact Nat.floor_le (le_of_lt hA)
  have hfloorB : (n : ℝ) ≤ B := by dsimp [n]; exact Nat.floor_le (le_of_lt (hA.trans hAB))
  have hFA : samplingFiniteCountingFunction w A = w m := by
    unfold samplingFiniteCountingFunction
    have hs : (∑ k ∈ Finset.Icc 0 m, w k) = ∑ k ∈ ({m} : Finset ℕ), w k := by
      symm
      apply Finset.sum_subset (by simp)
      intro k hk hnot
      have hklt : (k : ℝ) < A := by
        have hklt' : k < m := by
          have hkIcc := Finset.mem_Icc.mp hk
          have hkne : k ≠ m := by simpa using hnot
          exact lt_of_le_of_ne hkIcc.2 hkne
        exact lt_of_lt_of_le (by exact_mod_cast hklt') hfloorA
      exact hbelow k hklt
    simpa using hs
  have hAcast (hEq : cA = m) : (m : ℝ) = A := by
    have hAceil : A ≤ (cA : ℝ) := by dsimp [cA]; exact Nat.le_ceil A
    have hle : A ≤ (m : ℝ) := by rw [← hEq]; exact hAceil
    exact le_antisymm hfloorA hle
  have hAmLt (hSucc : cA = m + 1) : (m : ℝ) < A := by
    by_contra hnot
    have hle : A ≤ (m : ℝ) := le_of_not_gt hnot
    have hceille : cA ≤ m := (Nat.ceil_le).2 (by exact_mod_cast hle)
    omega
  have hBcast (hEq : cB = n) : (n : ℝ) = B := by
    have hBceil : B ≤ (cB : ℝ) := by dsimp [cB]; exact Nat.le_ceil B
    have hle : B ≤ (n : ℝ) := by rw [← hEq]; exact hBceil
    exact le_antisymm hfloorB hle
  have hBzero (hEq : cB = n) : w n = 0 :=
    habove n (by rw [hBcast hEq])
  have hIoc : (∑ k ∈ Finset.Ioc m n, w k / (k : ℝ)) =
      ∑ k ∈ Finset.Ico (m + 1) (n + 1), w k / (k : ℝ) := by
    congr 1
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hstart (b : ℕ) (hb : m < b) :
      (∑ k ∈ Finset.Ico m b, w k / (k : ℝ)) =
        w m / m + ∑ k ∈ Finset.Ico (m + 1) b, w k / (k : ℝ) := by
    rw [← Finset.insert_Ico_add_one_left_eq_Ico hb, Finset.sum_insert (by simp)]
  have hupper (l : ℕ) (hl : l ≤ n) :
      (∑ k ∈ Finset.Ico l (n + 1), w k / (k : ℝ)) =
        ∑ k ∈ Finset.Ico l n, w k / (k : ℝ) + w n / n := by
    exact Finset.sum_Ico_succ_top hl _
  have hmB : m < cB := by
    have hAceil : A ≤ (cA : ℝ) := by dsimp [cA]; exact Nat.le_ceil A
    have hAB' : (m : ℝ) < B := lt_of_le_of_lt hfloorA hAB
    have hBCeil : B ≤ (cB : ℝ) := by dsimp [cB]; exact Nat.le_ceil B
    have : (m : ℝ) < (cB : ℝ) := hAB'.trans_le hBCeil
    exact_mod_cast this
  have hinterval :
      (∑ k ∈ Finset.Ico cA cB, w k / (k : ℝ)) =
        (∑ k ∈ Finset.Ico (m + 1) (n + 1), w k / (k : ℝ)) + w m / m := by
    rcases hcaseA with hAeq | hAsucc <;> rcases hcaseB with hBeq | hBsucc
    · -- both endpoints are integers
      have hmnlt : m < n := by
        have hreal : (m : ℝ) < (n : ℝ) := by
          rw [hAcast hAeq, hBcast hBeq]
          exact hAB
        exact_mod_cast hreal
      have hAeq' : cA = m := hAeq
      have hBeq' : cB = n := hBeq
      rw [hAeq', hBeq']
      rw [hstart n hmnlt]
      rw [hupper (m + 1) (by omega), hBzero hBeq]
      ring
    · -- lower endpoint is an integer, upper endpoint is not
      have hAeq' : cA = m := hAeq
      have hBsucc' : cB = n + 1 := hBsucc
      rw [hAeq']
      rw [hstart cB hmB]
      rw [hBsucc']
      ring
    · -- lower endpoint is not an integer, upper endpoint is an integer
      have hAsucc' : cA = m + 1 := hAsucc
      have hBeq' : cB = n := hBeq
      rw [hAsucc', hBeq']
      rw [hupper (m + 1) (by omega)]
      rw [hBzero hBeq]
      have hmzero : w m = 0 := hbelow m (hAmLt hAsucc)
      simp [hmzero]
    · -- neither endpoint is an integer
      have hAsucc' : cA = m + 1 := hAsucc
      have hBsucc' : cB = n + 1 := hBsucc
      rw [hAsucc', hBsucc']
      have hmzero : w m = 0 := hbelow m (hAmLt hAsucc)
      simp [hmzero]
  rw [← hIoc] at hinterval
  have hcorr : w m / m = samplingFiniteCountingFunction w A / A := by
    rw [hFA]
    rcases hcaseA with hEq | hSucc
    · rw [hAcast hEq]
    · have hmzero : w m = 0 := hbelow m (hAmLt hSucc)
      simp [hmzero]
  rw [hcorr] at hinterval
  exact hinterval

-- Adapted from OpenAI openai/math (Apache-2.0),
-- OAI/NumberTheory/JointDickman/Arithmetic/HarmonicSummation.lean.
private theorem sampling_sum_div_eq_boundary_add_integral (w : ℕ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, w n / (n : ℝ)) =
      samplingFiniteCountingFunction w b / b - samplingFiniteCountingFunction w a / a +
        ∫ t in a..b, samplingFiniteCountingFunction w t / t ^ 2 := by
  have hd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro t ht
    exact differentiableAt_inv (ne_of_gt (ha.trans_le ht.1))
  have hi : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    simp only [deriv_inv']
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).neg.continuousWithinAt
  have h := sum_mul_eq_sub_sub_integral_mul (c := w) ha.le hab hd hi
  rw [← intervalIntegral.integral_of_le hab] at h
  simp only [deriv_inv] at h
  have heq :
      (fun t : ℝ => -(t ^ 2)⁻¹ * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, w n) =
        (fun t => -(samplingFiniteCountingFunction w t / t ^ 2)) := by
    funext t
    unfold samplingFiniteCountingFunction
    ring
  rw [heq, intervalIntegral.integral_neg] at h
  simpa only [div_eq_mul_inv, mul_comm, samplingFiniteCountingFunction,
    sub_neg_eq_add] using h

-- Adapted from OpenAI openai/math (Apache-2.0),
-- OAI/NumberTheory/JointDickman/Arithmetic/HarmonicSummation.lean.
private theorem sampling_harmonic_model_integral (M F : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hF : ∀ t ∈ Set.Icc a b, HasDerivAt F (M t) t)
    (hM : ContinuousOn M (Set.Icc a b)) :
    (∫ t in a..b, M t / t) =
      F b / b - F a / a + ∫ t in a..b, F t / t ^ 2 := by
  have hFc : ContinuousOn F (Set.Icc a b) :=
    fun t ht => (hF t ht).continuousAt.continuousWithinAt
  have hMi : IntervalIntegrable (fun t => M t / t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hM.div continuousOn_id (fun t ht => ne_of_gt (ha.trans_le ht.1))
  have hFi : IntervalIntegrable (fun t => F t / t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hFc.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1)))
  have hd : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x => F x / x) (M t / t - F t / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
    convert (hF t ht).div (hasDerivAt_id t) ht0 using 1
    · rfl
    · dsimp only [id_eq]
      field_simp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hMi.sub hFi)
  rw [intervalIntegral.integral_sub hMi hFi] at h
  linarith

private theorem samplingFiniteCountingFunction_div_sq_integrable (w : ℕ → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => samplingFiniteCountingFunction w t / t ^ 2) volume a b := by
  have hcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).continuousWithinAt
  have hi := integrableOn_mul_sum_Icc (m := 0) w ha.le hcont.integrableOn_Icc
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  simpa only [samplingFiniteCountingFunction, div_eq_mul_inv, mul_comm] using hi

private theorem integral_inv_sq_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (t ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun x : ℝ => -x⁻¹) ((t ^ 2)⁻¹) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le (Set.uIcc_of_le hab ▸ ht).1)
    have h := (hasDerivAt_inv ht0).neg
    convert h using 1 <;> field_simp <;> ring
  have hcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).continuousWithinAt
  have hi : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hcont
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [h]
  ring

private theorem periodic_harmonic_interval_bound (W k a : ℕ) (hW : 0 < W)
    (hk : 0 < k) (hcop : Nat.Coprime k W) (ha : a < k)
    {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    |(∑ n ∈ Finset.Ico ⌈A⌉₊ ⌈B⌉₊,
        (if A ≤ (n : ℝ) ∧ (n : ℝ) < B ∧ Nat.Coprime n W ∧ n % k = a then 1 else 0) /
          (n : ℝ)) -
      (Nat.totient W : ℝ) / W / k * Real.log (B / A)| ≤ (Nat.totient W : ℝ) / A := by
  classical
  let L := W * k
  let C := Nat.totient W
  let R : Finset (Fin L) := Finset.univ.filter (fun r : Fin L =>
    Nat.Coprime r.val W ∧ r.val % k = a)
  let w : ℕ → ℝ := fun n =>
    if A ≤ (n : ℝ) ∧ (n : ℝ) < B ∧ Nat.Coprime n W ∧ n % k = a then 1 else 0
  have hL : 0 < L := by dsimp [L]; exact Nat.mul_pos hW hk
  have hcopMod (n : ℕ) : Nat.Coprime (n % L) W ↔ Nat.Coprime n W := by
    have hdecomp : n = n % L + W * (k * (n / L)) := by
      calc
        n = n % L + L * (n / L) := (Nat.mod_add_div n L).symm
        _ = n % L + W * (k * (n / L)) := by simp [L, Nat.mul_assoc]
    calc
      _ ↔ Nat.Coprime (n % L + W * (k * (n / L))) W :=
        (Nat.coprime_add_mul_left_left _ _ _).symm
      _ ↔ Nat.Coprime n W := by rw [← hdecomp]
  have hmodMod (n : ℕ) : (n % L) % k = n % k :=
    Nat.mod_mod_of_dvd n ⟨W, by dsimp [L]; ac_rfl⟩
  have hRpred (n : ℕ) :
      (⟨n % L, Nat.mod_lt _ hL⟩ : Fin L) ∈ R ↔
        Nat.Coprime n W ∧ n % k = a := by
    dsimp [R]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcopMod n, hmodMod n]
  have hcard : R.card = C := by
    simpa [L, C, R] using active_unit_residue_card W k a hW hk hcop ha
  have hC : 1 ≤ C := by
    dsimp [C]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.mpr hW).ne'
  have hcount : ∀ t ∈ Set.Icc A B,
      |samplingFiniteCountingFunction w t - (C : ℝ) / L * (t - A)| ≤ C := by
    intro t ht
    rcases Set.mem_Icc.mp ht with ⟨hAt, htB⟩
    simpa [w, hRpred] using
      (samplingFiniteCountingFunction_periodic_bound L C R hcard hC hL hA hAB t ⟨hAt, htB⟩)
  have hbelow : ∀ n : ℕ, (n : ℝ) < A → w n = 0 := by
    intro n hn
    simp [w, not_le_of_gt hn]
  have habove : ∀ n : ℕ, B ≤ (n : ℝ) → w n = 0 := by
    intro n hn
    simp [w, not_lt.mpr hn]
  have hsumEndpoint := sampling_sum_Ico_eq_Ioc_add_count w hA hAB hbelow habove
  have habel := sampling_sum_div_eq_boundary_add_integral w hA hAB.le
  have hsum :
      (∑ n ∈ Finset.Ico ⌈A⌉₊ ⌈B⌉₊, w n / (n : ℝ)) =
        samplingFiniteCountingFunction w B / B +
          ∫ t in A..B, samplingFiniteCountingFunction w t / t ^ 2 := by
    rw [hsumEndpoint, habel]
    ring
  let model : ℝ → ℝ := fun t => (C : ℝ) / L * (t - A)
  have hmodelDeriv (t : ℝ) : HasDerivAt model ((C : ℝ) / L) t := by
    simpa [model] using ((hasDerivAt_id t).sub_const A).const_mul ((C : ℝ) / L)
  have hmodelCont : ContinuousOn (fun _ : ℝ => (C : ℝ) / L) (Set.Icc A B) :=
    continuousOn_const
  have hmodelInt := sampling_harmonic_model_integral
    (fun _ : ℝ => (C : ℝ) / L) model hA hAB.le
    (fun t _ => hmodelDeriv t) hmodelCont
  have hmodelLog :
      (C : ℝ) / L * Real.log (B / A) =
        model B / B - model A / A + ∫ t in A..B, model t / t ^ 2 := by
    have hlog : (∫ t in A..B, ((C : ℝ) / L) / t) =
        (C : ℝ) / L * Real.log (B / A) := by
      have hfun : (fun t : ℝ => ((C : ℝ) / L) / t) =
          fun t => ((C : ℝ) / L) * t⁻¹ := by
        funext t
        ring
      rw [hfun, intervalIntegral.integral_const_mul,
        integral_inv_of_pos hA (hA.trans hAB)]
    rw [← hmodelInt, hlog]
  have hFint : IntervalIntegrable
      (fun t => samplingFiniteCountingFunction w t / t ^ 2) volume A B :=
    samplingFiniteCountingFunction_div_sq_integrable w hA hAB.le
  have hModelInt : IntervalIntegrable (fun t => model t / t ^ 2) volume A B := by
    apply ContinuousOn.intervalIntegrable
    have hcont : ContinuousOn model (Set.Icc A B) := by
      fun_prop
    rw [Set.uIcc_of_le hAB.le]
    exact hcont.div (continuousOn_id.pow 2) (fun t ht =>
      pow_ne_zero 2 (ne_of_gt (hA.trans_le ht.1)))
  have hDint :
      (∫ t in A..B, samplingFiniteCountingFunction w t / t ^ 2) -
        (∫ t in A..B, model t / t ^ 2) =
      ∫ t in A..B, (samplingFiniteCountingFunction w t - model t) / t ^ 2 := by
    rw [← intervalIntegral.integral_sub hFint hModelInt]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hDnorm :
      |∫ t in A..B, (samplingFiniteCountingFunction w t - model t) / t ^ 2| ≤
        (C : ℝ) * (A⁻¹ - B⁻¹) := by
    have hmajor : IntervalIntegrable (fun t => (C : ℝ) / t ^ 2) volume A B := by
      apply ContinuousOn.intervalIntegrable
      have hcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc A B) := by
        intro t ht
        have ht0 : t ≠ 0 := ne_of_gt (hA.trans_le ht.1)
        exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).continuousWithinAt
      rw [Set.uIcc_of_le hAB.le]
      have hcont' : ContinuousOn (fun t : ℝ => (C : ℝ) * (t ^ 2)⁻¹)
          (Set.Icc A B) := by
        intro t ht
        have ht0 : t ≠ 0 := ne_of_gt (hA.trans_le ht.1)
        have hconst : ContinuousAt (fun _ : ℝ => (C : ℝ)) t := continuousAt_const
        have hinv : ContinuousAt (fun x : ℝ => (x ^ 2)⁻¹) t :=
          (continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)
        exact (hconst.mul hinv).continuousWithinAt
      simpa [div_eq_mul_inv] using hcont'
    have hpoint : ∀ t ∈ Set.Icc A B,
        |(samplingFiniteCountingFunction w t - model t) / t ^ 2| ≤ (C : ℝ) / t ^ 2 := by
      intro t ht
      have ht0 : 0 < t := hA.trans_le ht.1
      rw [abs_div, abs_of_pos (sq_pos_of_pos ht0)]
      exact div_le_div_of_nonneg_right (hcount t ht) (sq_nonneg t)
    have h := intervalIntegral.norm_integral_le_of_norm_le hAB.le
      (f := fun t => (samplingFiniteCountingFunction w t - model t) / t ^ 2)
      (g := fun t => (C : ℝ) / t ^ 2)
      (Filter.Eventually.of_forall (fun t ht => by
        rw [Real.norm_eq_abs]
        exact hpoint t ⟨ht.1.le, ht.2⟩)) hmajor
    rw [Real.norm_eq_abs] at h
    calc
      _ ≤ ∫ t in A..B, (C : ℝ) / t ^ 2 := h
      _ = (C : ℝ) * (A⁻¹ - B⁻¹) := by
        have hfun : (fun t : ℝ => (C : ℝ) / t ^ 2) =
            fun t => (C : ℝ) * (t ^ 2)⁻¹ := by
          funext t
          ring
        rw [hfun]
        calc
          _ = (C : ℝ) * ∫ t in A..B, (t ^ 2)⁻¹ :=
            intervalIntegral.integral_const_mul _ _
          _ = (C : ℝ) * (A⁻¹ - B⁻¹) := by rw [integral_inv_sq_pos hA hAB.le]
  have hBoundary :
      |(samplingFiniteCountingFunction w B - model B) / B| ≤ C / B := by
    have h := hcount B ⟨hAB.le, le_rfl⟩
    have hBpos : 0 < B := hA.trans hAB
    rw [abs_div, abs_of_pos hBpos]
    exact div_le_div_of_nonneg_right h (by positivity)
  have hdiff :
      (∑ n ∈ Finset.Ico ⌈A⌉₊ ⌈B⌉₊, w n / (n : ℝ)) -
        (C : ℝ) / L * Real.log (B / A) =
      (samplingFiniteCountingFunction w B - model B) / B +
        ∫ t in A..B, (samplingFiniteCountingFunction w t - model t) / t ^ 2 := by
    calc
      _ = (samplingFiniteCountingFunction w B / B - model B / B) +
            ((∫ t in A..B, samplingFiniteCountingFunction w t / t ^ 2) -
              ∫ t in A..B, model t / t ^ 2) := by
          rw [hsum, hmodelLog]
          have hmodelA : model A / A = 0 := by dsimp [model]; ring
          rw [hmodelA]
          ring
      _ = (samplingFiniteCountingFunction w B / B - model B / B) +
            ∫ t in A..B, (samplingFiniteCountingFunction w t - model t) / t ^ 2 := by
          rw [hDint]
      _ = _ := by dsimp [model]; ring
  have hsumw :
      (∑ n ∈ Finset.Ico ⌈A⌉₊ ⌈B⌉₊,
        (if A ≤ (n : ℝ) ∧ (n : ℝ) < B ∧ Nat.Coprime n W ∧ n % k = a then 1 else 0) /
          (n : ℝ)) =
      ∑ n ∈ Finset.Ico ⌈A⌉₊ ⌈B⌉₊, w n / (n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    rfl
  have hWposR : (0 : ℝ) < W := by exact_mod_cast hW
  have hkposR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcoeff : (Nat.totient W : ℝ) / W / k = (C : ℝ) / L := by
    dsimp [C, L]
    field_simp [ne_of_gt hWposR, ne_of_gt hkposR]
    <;> norm_cast
    <;> ring
  rw [hsumw]
  rw [hcoeff]
  rw [hdiff]
  calc
    _ ≤ |(samplingFiniteCountingFunction w B - model B) / B| +
          |∫ t in A..B, (samplingFiniteCountingFunction w t - model t) / t ^ 2| :=
        abs_add_le _ _
    _ ≤ C / B + (C : ℝ) * (A⁻¹ - B⁻¹) := add_le_add hBoundary hDnorm
    _ = C / A := by field_simp; ring

private theorem harmonicResidueLaw_eq_interval_sum (X W k a : ℕ) (ha : a < k) :
    harmonicResidueLaw (harmonicLaw X W) k ⟨a, ha⟩ =
      ∑ n ∈ Finset.Ico X (X ^ 2),
        if Nat.Coprime n W ∧ n % k = a then
          1 / ((n : ℝ) * harmonicNormalizer X W) else 0 := by
  classical
  let S : Finset ℤ := (Finset.Ico X (X ^ 2)).image (fun n : ℕ => (n : ℤ))
  have hzero (z : ℤ) (hz : z ∉ S) :
      (if 0 ≤ z ∧ z.toNat % k = a then harmonicLaw X W z else 0) = 0 := by
    by_cases hr : 0 ≤ z ∧ z.toNat % k = a
    · have hLaw :
          harmonicLaw X W z =
            if 0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W then
              1 / ((z.toNat : ℝ) * harmonicNormalizer X W) else 0 := by rfl
      by_cases hs : 0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W
      · have hzcast : (z.toNat : ℤ) = z := Int.natCast_toNat_eq_self.mpr hr.1
        have hmem : z ∈ S := by
          dsimp [S]
          apply Finset.mem_image.mpr
          exact ⟨z.toNat, Finset.mem_Ico.mpr ⟨hs.2.1, hs.2.2.1⟩, hzcast⟩
        exact (hz hmem).elim
      · rw [if_pos hr, hLaw, if_neg hs]
    · simp [hr]
  unfold harmonicResidueLaw
  rw [tsum_eq_sum (s := S) hzero]
  rw [Finset.sum_image (s := Finset.Ico X (X ^ 2))
    (f := fun z : ℤ => if 0 ≤ z ∧ z.toNat % k = a then harmonicLaw X W z else 0)
    (g := fun n : ℕ => (n : ℤ)) (by
      intro m hm n hn hmn
      exact Int.ofNat.inj hmn)]
  apply Finset.sum_congr rfl
  intro n hn
  have hnIco := Finset.mem_Ico.mp hn
  by_cases hmod : n % k = a
  · by_cases hcopr : Nat.Coprime n W
    · simp [harmonicLaw, hmod, hcopr, hnIco]
    · simp [harmonicLaw, hmod, hcopr]
  · simp [harmonicLaw, hmod]

private theorem harmonicNormalizer_bound (X W : ℕ) (hW : 0 < W) (hX : 2 ≤ X) :
    |harmonicNormalizer X W - (Nat.totient W : ℝ) / W * Real.log X| ≤
      (Nat.totient W : ℝ) / X := by
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hXtwo : 2 ≤ (X : ℝ) := by exact_mod_cast hX
  have hXsq : (X : ℝ) < (X : ℝ) ^ 2 := by nlinarith [hXtwo]
  have hBcast : ((X ^ 2 : ℕ) : ℝ) = (X : ℝ) ^ 2 := by norm_cast
  have hceilB : ⌈(X : ℝ) ^ 2⌉₊ = X ^ 2 := by
    rw [← hBcast]
    exact Nat.ceil_natCast _
  have hratio : (X : ℝ) ^ 2 / X = (X : ℝ) := by
    field_simp [ne_of_gt hXpos]
  have hp := periodic_harmonic_interval_bound W 1 0 hW (by simp) (by norm_num)
    (by norm_num) (A := (X : ℝ)) (B := (X : ℝ) ^ 2) hXpos hXsq
  have hp' := hp
  rw [Nat.ceil_natCast, hceilB] at hp'
  have hsumNorm :
      (∑ n ∈ Finset.Ico X (X ^ 2),
        (if (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < (X : ℝ) ^ 2 ∧
            Nat.Coprime n W ∧ n % 1 = 0 then 1 else 0) / (n : ℝ)) =
        harmonicNormalizer X W := by
    calc
      _ = ∑ n ∈ Finset.Ico X (X ^ 2),
          if Nat.Coprime n W then 1 / (n : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro n hn
            have hnIco := Finset.mem_Ico.mp hn
            have hlo : (X : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnIco.1
            have hhiCast : (n : ℝ) < ((X ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnIco.2
            have hhi : (n : ℝ) < (X : ℝ) ^ 2 := by simpa [hBcast] using hhiCast
            have hmod : n % 1 = 0 := Nat.mod_one _
            by_cases hc : Nat.Coprime n W
            · have hcond : (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < (X : ℝ) ^ 2 ∧
                  Nat.Coprime n W ∧ n % 1 = 0 := ⟨hlo, hhi, hc, hmod⟩
              rw [if_pos hcond, if_pos hc, one_div]
            · have hcond : ¬((X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < (X : ℝ) ^ 2 ∧
                  Nat.Coprime n W ∧ n % 1 = 0) := by
                rintro ⟨_, _, hcopr, _⟩
                exact hc hcopr
              rw [if_neg hcond, if_neg hc]
              simp
      _ = harmonicNormalizer X W := by
            rw [harmonicNormalizer, Finset.sum_filter]
  rw [hsumNorm] at hp'
  simpa [hratio] using hp'

private theorem harmonicNormalizer_pos (X W : ℕ) (hW : 0 < W) (hX : 2 ≤ X)
    (hden : Real.log X > (W : ℝ) / X) : 0 < harmonicNormalizer X W := by
  have hθpos : 0 < (Nat.totient W : ℝ) / W := by
    exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hW) (by exact_mod_cast hW)
  have hnorm := harmonicNormalizer_bound X W hW hX
  have hXposR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlower : (Nat.totient W : ℝ) / W *
      (Real.log X - (W : ℝ) / X) ≤ harmonicNormalizer X W := by
    have hphi : (Nat.totient W : ℝ) / X =
      (Nat.totient W : ℝ) / W * ((W : ℝ) / X) := by
      have hWposR : (0 : ℝ) < W := by exact_mod_cast hW
      field_simp [ne_of_gt hWposR, ne_of_gt hXposR]
      <;> ring
    have hnormlo := (abs_le.mp hnorm).1
    rw [hphi] at hnormlo
    nlinarith [hnormlo]
  exact lt_of_lt_of_le (mul_pos hθpos (sub_pos.mpr hden)) hlower

private theorem harmonicLaw_mass_one (X W : ℕ) (hW : 0 < W) (hX : 2 ≤ X)
    (hden : Real.log X > (W : ℝ) / X) :
    ∑' z : ℤ, harmonicLaw X W z = 1 := by
  have hZpos := harmonicNormalizer_pos X W hW hX hden
  have hsum :
      (∑ n ∈ Finset.Ico X (X ^ 2),
        if Nat.Coprime n W then 1 / ((n : ℝ) * harmonicNormalizer X W) else 0) = 1 := by
    calc
      _ = (∑ n ∈ Finset.Ico X (X ^ 2),
          if Nat.Coprime n W then 1 / (n : ℝ) else 0) / harmonicNormalizer X W := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro n hn
            by_cases hc : Nat.Coprime n W
            · simp only [if_pos hc]
              have hnNat : 0 < n := lt_of_lt_of_le (by omega)
                (Finset.mem_Ico.mp hn).1
              have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hnNat)
              field_simp [hZpos.ne', hnR]
              <;> ring
            · simp [hc]
      _ = harmonicNormalizer X W / harmonicNormalizer X W := by
            rw [harmonicNormalizer]
            simp [Finset.sum_filter]
      _ = 1 := div_self hZpos.ne'
  have hres : harmonicResidueLaw (harmonicLaw X W) 1 ⟨0, by omega⟩ = 1 := by
    rw [harmonicResidueLaw_eq_interval_sum X W 1 0 (by omega)]
    simpa [Nat.mod_one, and_assoc, and_left_comm, and_comm] using hsum
  have heq : harmonicResidueLaw (harmonicLaw X W) 1 ⟨0, by omega⟩ =
      ∑' z : ℤ, harmonicLaw X W z := by
    unfold harmonicResidueLaw
    apply tsum_congr
    intro z
    by_cases hz : 0 ≤ z
    · have hmod : z.toNat % 1 = 0 := Nat.mod_one _
      simp [hz, hmod]
    · have hμ : harmonicLaw X W z = 0 := by simp [harmonicLaw, hz]
      simp [hz, hμ]
  exact heq.symm.trans hres

private theorem harmonicNormalizer_lower (X W : ℕ) (hW : 0 < W) (hX : 2 ≤ X)
    (hden : Real.log X > (W : ℝ) / X) :
    (Nat.totient W : ℝ) / W * (Real.log X - (W : ℝ) / X) ≤
      harmonicNormalizer X W := by
  have hθpos : 0 < (Nat.totient W : ℝ) / W := by
    exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hW) (by exact_mod_cast hW)
  have hnorm := harmonicNormalizer_bound X W hW hX
  have hXposR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hphi : (Nat.totient W : ℝ) / X =
      (Nat.totient W : ℝ) / W * ((W : ℝ) / X) := by
    have hWposR : (0 : ℝ) < W := by exact_mod_cast hW
    field_simp [ne_of_gt hWposR, ne_of_gt hXposR]
    <;> ring
  have hnormlo := (abs_le.mp hnorm).1
  rw [hphi] at hnormlo
  nlinarith [hnormlo]

private theorem harmonicLaw_nonneg (X W : ℕ) (hW : 0 < W) (hX : 2 ≤ X)
    (hden : Real.log X > (W : ℝ) / X) (z : ℤ) :
    0 ≤ harmonicLaw X W z := by
  have hZ : 0 < harmonicNormalizer X W := harmonicNormalizer_pos X W hW hX hden
  unfold harmonicLaw
  split_ifs <;> positivity

private theorem harmonicLaw_support (X W : ℕ) {z : ℤ}
    (hz : z ∈ Finset.Icc (X : ℤ) ((X ^ 2 : ℕ) : ℤ)) :
    harmonicLaw X W z =
      if 0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W then
        1 / ((z.toNat : ℝ) * harmonicNormalizer X W) else 0 := by
  rfl

private theorem harmonicLaw_eq_zero_of_not_support (X W : ℕ) {z : ℤ}
    (hz : z ∉ Finset.Icc (X : ℤ) ((X ^ 2 : ℕ) : ℤ)) :
    harmonicLaw X W z = 0 := by
  by_cases hc : 0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W
  · have hcast : (z.toNat : ℤ) = z := Int.natCast_toNat_eq_self.mpr hc.1
    have hlow : (X : ℤ) ≤ z := by rw [← hcast]; exact_mod_cast hc.2.1
    have hhigh : z ≤ ((X ^ 2 : ℕ) : ℤ) := by
      rw [← hcast]
      exact_mod_cast hc.2.2.1.le
    exact (hz (Finset.mem_Icc.mpr ⟨hlow, hhigh⟩)).elim
  · simp [harmonicLaw, hc]

private theorem harmonicLaw_shift_ge (X W : ℕ) (hW : 0 < W) (hX : 2 ≤ X)
    (hden : Real.log X > (W : ℝ) / X) {h z : ℤ} (hh : 0 ≤ h)
    (hdiv : (W : ℤ) ∣ h) (hz : (X : ℤ) + h ≤ z) :
    harmonicLaw X W z ≤ harmonicLaw X W (z - h) := by
  have hZ : 0 < harmonicNormalizer X W := harmonicNormalizer_pos X W hW hX hden
  have hX0 : (0 : ℤ) ≤ X := by omega
  have hYpos : 0 ≤ z - h := by omega
  have hnCast : (z.toNat : ℤ) = z := by
    apply Int.natCast_toNat_eq_self.mpr
    omega
  have hyCast : ((z - h).toNat : ℤ) = z - h := by
    apply Int.natCast_toNat_eq_self.mpr
    omega
  have hNatEq : z.toNat = (z - h).toNat + h.toNat := by
    have hcast : (z.toNat : ℤ) = ((z - h).toNat : ℤ) + (h.toNat : ℤ) := by
      rw [hnCast, hyCast, Int.natCast_toNat_eq_self.mpr hh]
      ring
    exact Int.ofNat.inj hcast
  have hdivNat : W ∣ h.toNat := by
    have hcastDiv : (W : ℤ) ∣ (h.toNat : ℤ) := by simpa [Int.natCast_toNat_eq_self.mpr hh] using hdiv
    exact Int.natCast_dvd_natCast.mp hcastDiv
  have hmul : W * (h.toNat / W) = h.toNat := Nat.mul_div_cancel' hdivNat
  have hcop : Nat.Coprime z.toNat W ↔ Nat.Coprime (z - h).toNat W := by
    have hNatEqMul : z.toNat = (z - h).toNat + W * (h.toNat / W) := by
      rw [hmul]
      exact hNatEq
    rw [hNatEqMul]
    exact Nat.coprime_add_mul_left_left _ _ _
  by_cases hc : 0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W
  · have hycond : 0 ≤ z - h ∧ X ≤ (z - h).toNat ∧
        (z - h).toNat < X ^ 2 ∧ Nat.Coprime (z - h).toNat W := by
      refine ⟨hYpos, ?_, ?_, (hcop.mp hc.2.2.2)⟩
      · have : (X : ℤ) ≤ z - h := by omega
        have hcast : (X : ℤ) ≤ ((z - h).toNat : ℤ) := by rw [hyCast]; exact this
        exact_mod_cast hcast
      · have : (z - h).toNat < X ^ 2 := by omega
        exact this
    unfold harmonicLaw
    rw [if_pos hc, if_pos hycond]
    have hleNat : (z - h).toNat ≤ z.toNat := by
      have hleInt : ((z - h).toNat : ℤ) ≤ (z.toNat : ℤ) := by
        rw [hyCast, hnCast]
        omega
      exact_mod_cast hleInt
    have hposY : 0 < ((z - h).toNat : ℝ) := by
      have hXY : 0 < X := by omega
      exact_mod_cast (lt_of_lt_of_le hXY hycond.2.1)
    have hposZ : 0 < (z.toNat : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (show 0 < X by omega) hc.2.1)
    rw [div_le_div_iff₀ (mul_pos hposZ hZ) (mul_pos hposY hZ)]
    nlinarith [show ((z - h).toNat : ℝ) ≤ z.toNat by exact_mod_cast hleNat]
  · have hz0 : harmonicLaw X W z = 0 := by simp [harmonicLaw, hc]
    rw [hz0]
    exact harmonicLaw_nonneg X W hW hX hden (z - h)

private theorem arithmeticL1_eq_twice_negative_part (μ ν : ℤ → ℝ)
    (S : Finset ℤ) (hsupp : ∀ z ∉ S, μ z = 0 ∧ ν z = 0)
    (hmass : (∑' z : ℤ, μ z) = ∑' z : ℤ, ν z) :
    arithmeticL1 μ ν = 2 * ∑ z ∈ S, max (ν z - μ z) 0 := by
  classical
  have hL1 : arithmeticL1 μ ν = ∑ z ∈ S, |μ z - ν z| := by
    unfold arithmeticL1
    rw [tsum_eq_sum (s := S) (fun z hz => by
      rcases hsupp z hz with ⟨hμ, hν⟩
      simp [hμ, hν])]
  have hμsum : (∑ z ∈ S, μ z) = ∑' z : ℤ, μ z := by
    symm
    rw [tsum_eq_sum (s := S) (fun z hz => (hsupp z hz).1)]
  have hνsum : (∑ z ∈ S, ν z) = ∑' z : ℤ, ν z := by
    symm
    rw [tsum_eq_sum (s := S) (fun z hz => (hsupp z hz).2)]
  have hdiff : ∑ z ∈ S, (μ z - ν z) = 0 := by
    rw [Finset.sum_sub_distrib, hμsum, hνsum, hmass, sub_self]
  rw [hL1]
  calc
    _ = ∑ z ∈ S, ((μ z - ν z) + 2 * max (ν z - μ z) 0) := by
          apply Finset.sum_congr rfl
          intro z hz
          by_cases h : 0 ≤ μ z - ν z
          · rw [abs_of_nonneg h, max_eq_right (by linarith)]
            ring
          · have h' : μ z - ν z < 0 := lt_of_not_ge h
            rw [abs_of_neg h', max_eq_left (by linarith)]
            linarith
    _ = 0 + 2 * ∑ z ∈ S, max (ν z - μ z) 0 := by
          rw [Finset.sum_add_distrib, hdiff, zero_add, ← Finset.mul_sum]
          ring
    _ = 2 * ∑ z ∈ S, max (ν z - μ z) 0 := by ring

private theorem harmonic_residue_pointwise_bound (X W : ℕ) (hW : 0 < W)
    (hX : 2 ≤ X) (hden : Real.log X > (W : ℝ) / X)
    (k a : ℕ) (hcop : Nat.Coprime k W) (hk : 0 < k) (ha : a < k) :
    |(k : ℝ) * harmonicResidueLaw (harmonicLaw X W) k ⟨a, ha⟩ - 1| ≤
      harmonicResidueError X W k := by
  let Z := harmonicNormalizer X W
  let θ := (Nat.totient W : ℝ) / W
  let P : ℝ := ∑ n ∈ Finset.Ico X (X ^ 2),
    if Nat.Coprime n W ∧ n % k = a then 1 / (n : ℝ) else 0
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hXtwo : 2 ≤ (X : ℝ) := by exact_mod_cast hX
  have hXsq : (X : ℝ) < (X : ℝ) ^ 2 := by nlinarith [hXtwo]
  have hBcast : ((X ^ 2 : ℕ) : ℝ) = (X : ℝ) ^ 2 := by norm_cast
  have hceilB : ⌈(X : ℝ) ^ 2⌉₊ = X ^ 2 := by
    rw [← hBcast]
    exact Nat.ceil_natCast _
  have hratio : (X : ℝ) ^ 2 / X = (X : ℝ) := by
    field_simp [ne_of_gt hXpos]
  have hP : |P - θ / k * Real.log X| ≤ (Nat.totient W : ℝ) / X := by
    have hh := periodic_harmonic_interval_bound W k a hW hk hcop ha
      (A := (X : ℝ)) (B := (X : ℝ) ^ 2) hXpos hXsq
    have hh' := hh
    rw [Nat.ceil_natCast, hceilB] at hh'
    have hsumP :
        (∑ n ∈ Finset.Ico X (X ^ 2),
          (if (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < (X : ℝ) ^ 2 ∧
              Nat.Coprime n W ∧ n % k = a then 1 else 0) / (n : ℝ)) = P := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnIco := Finset.mem_Ico.mp hn
      have hlo : (X : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnIco.1
      have hhiCast : (n : ℝ) < ((X ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnIco.2
      have hhi : (n : ℝ) < (X : ℝ) ^ 2 := by simpa [hBcast] using hhiCast
      by_cases hc : Nat.Coprime n W
      · by_cases hm : n % k = a
        · have hcond : (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < (X : ℝ) ^ 2 ∧
              Nat.Coprime n W ∧ n % k = a := ⟨hlo, hhi, hc, hm⟩
          rw [if_pos hcond, if_pos (And.intro hc hm)]
        · have hcond : ¬((X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < (X : ℝ) ^ 2 ∧
              Nat.Coprime n W ∧ n % k = a) := by
            rintro ⟨_, _, _, hm'⟩
            exact hm hm'
          have hpair : ¬ (Nat.Coprime n W ∧ n % k = a) := by
            rintro ⟨_, hm'⟩
            exact hm hm'
          rw [if_neg hcond, if_neg hpair]
          simp
      · have hcond : ¬((X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < (X : ℝ) ^ 2 ∧
            Nat.Coprime n W ∧ n % k = a) := by
          rintro ⟨_, _, hc', _⟩
          exact hc hc'
        have hpair : ¬ (Nat.Coprime n W ∧ n % k = a) := by
          rintro ⟨hc', _⟩
          exact hc hc'
        rw [if_neg hcond, if_neg hpair]
        simp
    rw [hsumP] at hh'
    simpa [θ, hratio] using hh'
  have hnorm := harmonicNormalizer_bound X W hW hX
  have hθpos : 0 < θ := by
    dsimp [θ]
    exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hW) (by exact_mod_cast hW)
  have hZlower : θ * (Real.log X - (W : ℝ) / X) ≤ Z := by
    have hφX : (Nat.totient W : ℝ) / X = θ * ((W : ℝ) / X) := by
      dsimp [θ]
      have hWposR : (0 : ℝ) < W := by exact_mod_cast hW
      field_simp [ne_of_gt hWposR, ne_of_gt hXpos]
      <;> ring
    have hnormlo := (abs_le.mp hnorm).1
    dsimp [Z]
    nlinarith [hnormlo, hφX]
  have hdenpos : 0 < Real.log X - (W : ℝ) / X := by linarith
  have hZpos : 0 < Z := lt_of_lt_of_le (mul_pos hθpos hdenpos) hZlower
  have hreslaw : harmonicResidueLaw (harmonicLaw X W) k ⟨a, ha⟩ = P / Z := by
    rw [harmonicResidueLaw_eq_interval_sum X W k a ha]
    dsimp [P, Z]
    rw [show (∑ n ∈ Finset.Ico X (X ^ 2),
        if Nat.Coprime n W ∧ n % k = a then 1 / ((n : ℝ) * harmonicNormalizer X W) else 0) =
      ∑ n ∈ Finset.Ico X (X ^ 2),
        (if Nat.Coprime n W ∧ n % k = a then 1 / (n : ℝ) else 0) /
          harmonicNormalizer X W by
            apply Finset.sum_congr rfl
            intro n hn
            by_cases hcond : Nat.Coprime n W ∧ n % k = a
            · simp only [if_pos hcond]
              have hnpos : (n : ℝ) ≠ 0 := by
                apply ne_of_gt
                exact_mod_cast (lt_of_lt_of_le (by omega : 0 < X)
                  (Finset.mem_Ico.mp hn).1)
              field_simp [ne_of_gt hZpos, hnpos]
              <;> ring
            · simp [hcond]]
    rw [Finset.sum_div]
  have hnum : |(k : ℝ) * P - Z| ≤
      (Nat.totient W : ℝ) * ((k : ℝ) + 1) / X := by
    have hmain : (k : ℝ) * (θ / k * Real.log X) = θ * Real.log X := by
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
      dsimp [θ]
      field_simp [hkR]
      <;> ring
    have hsplit : (k : ℝ) * P - Z =
        (k : ℝ) * (P - θ / k * Real.log X) + (θ * Real.log X - Z) := by
      field_simp [show (k : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hk)]
      <;> ring
    have hnormflip : |θ * Real.log X - Z| ≤ (Nat.totient W : ℝ) / X := by
      have hsymm : |θ * Real.log X - Z| = |Z - θ * Real.log X| :=
        abs_sub_comm _ _
      have hnorm' : |Z - θ * Real.log X| ≤ (Nat.totient W : ℝ) / X := by
        simpa [Z, θ] using hnorm
      exact hsymm ▸ hnorm'
    have htriangle : |(k : ℝ) * P - Z| ≤
        (k : ℝ) * |P - θ / k * Real.log X| +
          |θ * Real.log X - Z| := by
      rw [hsplit]
      calc
        _ ≤ |(k : ℝ) * (P - θ / k * Real.log X)| +
              |θ * Real.log X - Z| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (k : ℝ) * ((Nat.totient W : ℝ) / X) +
            (Nat.totient W : ℝ) / X := by
              exact htriangle.trans (add_le_add
                (mul_le_mul_of_nonneg_left hP (by positivity)) hnormflip)
      _ = (Nat.totient W : ℝ) * ((k : ℝ) + 1) / X := by ring
  have hscale : (k : ℝ) * (P / Z) - 1 = ((k : ℝ) * P - Z) / Z := by
    field_simp [ne_of_gt hZpos]
    <;> ring
  have hnumNonneg : 0 ≤ (Nat.totient W : ℝ) * ((k : ℝ) + 1) / X := by positivity
  calc
    |(k : ℝ) * harmonicResidueLaw (harmonicLaw X W) k ⟨a, ha⟩ - 1|
        = |((k : ℝ) * P - Z) / Z| := by rw [hreslaw, hscale]
    _ ≤ ((Nat.totient W : ℝ) * ((k : ℝ) + 1) / X) / Z := by
          rw [abs_div, abs_of_pos hZpos]
          exact div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ ((Nat.totient W : ℝ) * ((k : ℝ) + 1) / X) /
          (θ * (Real.log X - (W : ℝ) / X)) :=
          div_le_div_of_nonneg_left hnumNonneg (mul_pos hθpos hdenpos) hZlower
    _ = harmonicResidueError X W k := by
          unfold harmonicResidueError
          dsimp [θ]
          field_simp [hXpos.ne', ne_of_gt hθpos, ne_of_gt hdenpos]
          <;> norm_cast
          <;> ring

private theorem coprime_mod_self_nat (n W : ℕ) :
    Nat.Coprime (n % W) W ↔ Nat.Coprime n W := by
  have hdecomp : n = n % W + W * (n / W) := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div n W).symm
  calc
    Nat.Coprime (n % W) W ↔ Nat.Coprime (n % W + W * (n / W)) W :=
      (Nat.coprime_add_mul_left_left _ _ _).symm
    _ ↔ Nat.Coprime n W := by rw [← hdecomp]

private theorem coprime_interval_card_multiple (a q W : ℕ) (hW : 0 < W) :
    ({n ∈ Finset.Ico a (a + q * W) | Nat.Coprime n W}.card) =
      q * Nat.totient W := by
  classical
  let I : Finset ℕ := Finset.Ico a (a + q * W)
  let U : Finset (Fin W) := Finset.univ.filter (fun r : Fin W => Nat.Coprime r.val W)
  let g (n : ℕ) : Fin W := ⟨n % W, Nat.mod_lt _ hW⟩
  let S : Finset ℕ := I.filter (fun n => Nat.Coprime n W)
  let fiber (r : Fin W) : Finset ℕ := S.filter (fun n => g n = r)
  have hdiv : (q : ℝ) * W / W = q := by
    have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
    field_simp
  have hres (r : Fin W) : ({n ∈ I | n % W = r.val}.card) = q := by
    have hs := interval_residue_card_strict_error a (q * W) W r.val hW r.isLt
    have hs' : |(({n ∈ I | n % W = r.val}.card : ℕ) : ℝ) - q| < 1 := by
      simpa [I, hdiv] using hs
    have hl : (q : ℝ) < ({n ∈ I | n % W = r.val}.card : ℝ) + 1 := by
      have h := (abs_lt.mp hs').1
      linarith
    have hu : (({n ∈ I | n % W = r.val}.card : ℕ) : ℝ) < q + 1 := by
      have h := (abs_lt.mp hs').2
      linarith
    have hlN : q < {n ∈ I | n % W = r.val}.card + 1 := by exact_mod_cast hl
    have huN : {n ∈ I | n % W = r.val}.card < q + 1 := by exact_mod_cast hu
    omega
  have hUcard : U.card = Nat.totient W := by
    let eNat : {r : Fin W // r ∈ U} ≃ {m : ℕ // m < W ∧ Nat.Coprime W m} := {
      toFun := fun r => ⟨r.val.val, ⟨r.val.isLt, (Finset.mem_filter.mp r.property).2.symm⟩⟩
      invFun := fun m =>
        ⟨⟨m.val, m.property.1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, m.property.2.symm⟩⟩
      left_inv := by intro r; apply Subtype.ext; apply Fin.ext; rfl
      right_inv := by intro m; apply Subtype.ext; rfl
    }
    calc
      U.card = Fintype.card {r : Fin W // r ∈ U} := (Fintype.card_coe U).symm
      _ = Nat.card {r : Fin W // r ∈ U} := Nat.card_eq_fintype_card.symm
      _ = Nat.card {m : ℕ // m < W ∧ Nat.Coprime W m} := Nat.card_congr eNat
      _ = Nat.totient W := (Nat.totient_eq_card_lt_and_coprime W).symm
  have htotal : (∑ r : Fin W, (fiber r).card) = S.card := by
    have h := Finset.sum_fiberwise S g (fun _ => (1 : ℕ))
    simpa [fiber] using h
  have hfiber_zero (r : Fin W) (hr : r ∉ U) : (fiber r).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro n hn hgn
    have hnC := (Finset.mem_filter.mp hn).2
    have hresC : Nat.Coprime (n % W) W := (coprime_mod_self_nat n W).mpr hnC
    have hrC : Nat.Coprime r.val W := by
      have hval : n % W = r.val := congrArg Fin.val hgn
      simpa [hval] using hresC
    exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrC⟩)
  have hsumU : (∑ r : Fin W, (fiber r).card) = ∑ r ∈ U, (fiber r).card := by
    symm
    apply Finset.sum_subset (Finset.subset_univ U)
    intro r hr hnot
    exact hfiber_zero r hnot
  have hfiber (r : Fin W) (hr : r ∈ U) :
      (fiber r).card = {n ∈ I | n % W = r.val}.card := by
    apply congrArg Finset.card
    ext n
    simp only [fiber, S, g, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hnI, hnC⟩, hgn⟩
      exact ⟨hnI, congrArg Fin.val hgn⟩
    · rintro ⟨hnI, hmod⟩
      have hnC : Nat.Coprime n W := (coprime_mod_self_nat n W).mp (by
        have hC := (Finset.mem_filter.mp hr).2
        simpa [hmod] using hC)
      have hgn : g n = r := by apply Fin.ext; exact hmod
      exact ⟨⟨hnI, hnC⟩, hgn⟩
  have hcardS : S.card = q * Nat.totient W := by
    calc
      S.card = ∑ r : Fin W, (fiber r).card := htotal.symm
      _ = ∑ r ∈ U, (fiber r).card := hsumU
      _ = ∑ r ∈ U, q := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [hfiber r hr, hres r]
      _ = q * Nat.totient W := by rw [Finset.sum_const, hUcard]; simp [Nat.mul_comm]
  simpa [I, S] using hcardS

private theorem harmonic_translation_bound_nonneg (X W : ℕ) (hW : 0 < W)
    (hX : 2 ≤ X) (hden : Real.log X > (W : ℝ) / X)
    {h : ℤ} (hh : 0 ≤ h) (hdiv : (W : ℤ) ∣ h) :
    arithmeticL1 (translatedLaw (harmonicLaw X W) h) (harmonicLaw X W) ≤
      2 * (h : ℝ) / ((X : ℝ) * (Real.log X - (W : ℝ) / X) ) ∧
    arithmeticL1 (translatedLaw (harmonicLaw X W) h) (harmonicLaw X W) ≤ 2 := by
  classical
  let μ : ℤ → ℝ := harmonicLaw X W
  let S : Finset ℤ := Finset.Icc (X : ℤ) (((X ^ 2 : ℕ) : ℤ) + h)
  let E : Finset ℤ := Finset.Ico (X : ℤ) ((X : ℤ) + h)
  have hZpos : 0 < harmonicNormalizer X W := harmonicNormalizer_pos X W hW hX hden
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hDpos : 0 < Real.log X - (W : ℝ) / X := sub_pos.mpr hden
  have hθpos : 0 < (Nat.totient W : ℝ) / W := by
    exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hW) (by exact_mod_cast hW)
  have hnormLower :
      (Nat.totient W : ℝ) / W * (Real.log X - (W : ℝ) / X) ≤ harmonicNormalizer X W :=
    harmonicNormalizer_lower X W hW hX hden
  have htransMass : (∑' z : ℤ, translatedLaw μ h z) = ∑' z : ℤ, μ z := by
    change (∑' z : ℤ, μ (z - h)) = ∑' z : ℤ, μ z
    exact (Equiv.subRight h).tsum_eq μ
  have hsupp : ∀ z ∉ S, translatedLaw μ h z = 0 ∧ μ z = 0 := by
    intro z hz
    constructor
    · change μ (z - h) = 0
      apply harmonicLaw_eq_zero_of_not_support X W
      intro hy
      rcases Finset.mem_Icc.mp hy with ⟨hylo, hyhi⟩
      apply hz
      apply Finset.mem_Icc.mpr
      constructor <;> omega
    · apply harmonicLaw_eq_zero_of_not_support X W
      intro hzbase
      rcases Finset.mem_Icc.mp hzbase with ⟨hzlo, hzhi⟩
      apply hz
      apply Finset.mem_Icc.mpr
      constructor
      · exact hzlo
      · have hhle : (0 : ℤ) ≤ h := hh
        omega
  have hL1 := arithmeticL1_eq_twice_negative_part
    (translatedLaw μ h) μ S hsupp htransMass
  have hneg (z : ℤ) :
      max (μ z - translatedLaw μ h z) 0 ≤ if z ∈ E then μ z else 0 := by
    by_cases hzE : z ∈ E
    · simp only [hzE, if_pos]
      have hμ := harmonicLaw_nonneg X W hW hX hden z
      have htr := harmonicLaw_nonneg X W hW hX hden (z - h)
      have hsub : μ z - translatedLaw μ h z ≤ μ z := by
        dsimp [μ, translatedLaw]
        linarith
      exact max_le hsub hμ
    · simp only [hzE, if_false]
      by_cases hμ0 : μ z = 0
      · have htr := harmonicLaw_nonneg X W hW hX hden (z - h)
        have htr' : 0 ≤ translatedLaw μ h z := by simpa [translatedLaw, μ] using htr
        have hsub : 0 - translatedLaw μ h z ≤ 0 := by linarith
        simp only [hμ0]
        rw [max_eq_right hsub]
      · have hbase : z ∈ Finset.Icc (X : ℤ) ((X ^ 2 : ℕ) : ℤ) := by
          by_contra hzbase
          exact hμ0 (harmonicLaw_eq_zero_of_not_support X W hzbase)
        have hafter : (X : ℤ) + h ≤ z := by
          have hzlo := (Finset.mem_Icc.mp hbase).1
          by_contra hn
          have hhi : z < (X : ℤ) + h := lt_of_not_ge hn
          exact hzE (Finset.mem_Ico.mpr ⟨hzlo, hhi⟩)
        have hmono := harmonicLaw_shift_ge X W hW hX hden hh hdiv hafter
        have hsub : μ z - translatedLaw μ h z ≤ 0 := by
          dsimp [μ, translatedLaw]
          exact sub_nonpos.mpr hmono
        simp [max_eq_right hsub]
  have hsumNeg : (∑ z ∈ S, max (μ z - translatedLaw μ h z) 0) ≤
      ∑ z ∈ E, μ z := by
    calc
      _ ≤ ∑ z ∈ S, if z ∈ E then μ z else 0 := by
            apply Finset.sum_le_sum
            intro z hz
            exact hneg z
      _ = ∑ z ∈ S.filter (fun z => z ∈ E), μ z := by
            rw [← Finset.sum_filter]
      _ ≤ ∑ z ∈ E, μ z := by
            have hsubset : S.filter (fun z => z ∈ E) ⊆ E := by
              intro z hz
              exact (Finset.mem_filter.mp hz).2
            apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
            intro z hz hnot
            exact harmonicLaw_nonneg X W hW hX hden z
  let t : ℕ := h.toNat
  let q : ℕ := t / W
  have hcast : (t : ℤ) = h := Int.natCast_toNat_eq_self.mpr hh
  have hdivNat : W ∣ t := by
    have hdivCast : (W : ℤ) ∣ (t : ℤ) := by simpa [hcast] using hdiv
    exact Int.natCast_dvd_natCast.mp hdivCast
  have hmul : t = q * W := by
    dsimp [q, t]
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hdivNat).symm
  have hEimage : E = (Finset.Ico X (X + t)).image (fun n : ℕ => (n : ℤ)) := by
    ext z
    constructor
    · intro hzE
      rcases Finset.mem_Ico.mp hzE with ⟨hzlo, hzhi⟩
      have hzpos : 0 ≤ z := by omega
      have hzn : (z.toNat : ℤ) = z := Int.natCast_toNat_eq_self.mpr hzpos
      apply Finset.mem_image.mpr
      refine ⟨z.toNat, Finset.mem_Ico.mpr ?_, hzn⟩
      constructor
      · have hlow : (X : ℤ) ≤ (z.toNat : ℤ) := by simpa [hzn] using hzlo
        exact_mod_cast hlow
      · have hhi : (z.toNat : ℤ) < (X : ℤ) + (t : ℤ) := by
          rw [hzn, hcast]
          exact hzhi
        exact_mod_cast hhi
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨n, hn, hzn⟩
      rcases Finset.mem_Ico.mp hn with ⟨hnlo, hnhi⟩
      have hzn' : z = (n : ℤ) := hzn.symm
      subst z
      apply Finset.mem_Ico.mpr
      constructor
      · exact_mod_cast hnlo
      · have hupper : (X : ℤ) + (t : ℤ) = (X : ℤ) + h := by rw [hcast]
        rw [← hupper]
        exact_mod_cast hnhi
  have hterm (n : ℕ) (hn : n ∈ Finset.Ico X (X + t)) :
      μ (n : ℤ) ≤ if Nat.Coprime n W then
        1 / ((X : ℝ) * harmonicNormalizer X W) else 0 := by
    have hnI := Finset.mem_Ico.mp hn
    by_cases hcop : Nat.Coprime n W
    · have hnCast : ((n : ℤ).toNat) = n := by simp
      by_cases hupper : n < X ^ 2
      · have hcond : 0 ≤ (n : ℤ) ∧ X ≤ (n : ℤ).toNat ∧
            (n : ℤ).toNat < X ^ 2 ∧ Nat.Coprime (n : ℤ).toNat W := by
          refine ⟨by omega, ?_, ?_, ?_⟩
          · simpa [hnCast] using hnI.1
          · simpa [hnCast] using hupper
          · simpa [hnCast] using hcop
        change harmonicLaw X W (n : ℤ) ≤ _
        unfold harmonicLaw
        rw [if_pos hcond]
        rw [if_pos hcop]
        have hnCastR : ((n : ℤ).toNat : ℝ) = (n : ℝ) := by exact_mod_cast hnCast
        rw [hnCastR]
        have hnR : (X : ℝ) ≤ n := by exact_mod_cast hnI.1
        have hnposR : 0 < (n : ℝ) := lt_of_lt_of_le hXpos hnR
        rw [div_le_div_iff₀ (mul_pos hnposR hZpos) (mul_pos hXpos hZpos)]
        nlinarith
      · have hcond : ¬(0 ≤ (n : ℤ) ∧ X ≤ (n : ℤ).toNat ∧
            (n : ℤ).toNat < X ^ 2 ∧ Nat.Coprime (n : ℤ).toNat W) := by
          simp [hnCast, hnI.1, hupper, hcop]
        unfold μ harmonicLaw
        rw [if_neg hcond]
        rw [if_pos hcop]
        positivity
    · simp [μ, harmonicLaw, hcop]
  have hEdge : (∑ z ∈ E, μ z) ≤
      ((q * Nat.totient W : ℕ) : ℝ) / ((X : ℝ) * harmonicNormalizer X W) := by
    rw [hEimage]
    rw [Finset.sum_image (s := Finset.Ico X (X + t))
      (f := fun z : ℤ => μ z) (g := fun n : ℕ => (n : ℤ))
      (by intro m hm n hn hmn; exact Int.ofNat.inj hmn)]
    calc
      _ ≤ ∑ n ∈ Finset.Ico X (X + t),
            if Nat.Coprime n W then
              1 / ((X : ℝ) * harmonicNormalizer X W) else 0 := by
                apply Finset.sum_le_sum
                intro n hn
                exact hterm n hn
      _ = (({n ∈ Finset.Ico X (X + t) | Nat.Coprime n W}.card : ℝ)) /
            ((X : ℝ) * harmonicNormalizer X W) := by
              rw [← Finset.sum_filter]
              simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, mul_inv]
      _ = _ := by
            have hcard : ({n ∈ Finset.Ico X (X + t) | Nat.Coprime n W}.card) =
                q * Nat.totient W := by simpa [hmul] using coprime_interval_card_multiple X q W hW
            rw [hcard]
  have hEdgeNorm :
      ((q * Nat.totient W : ℕ) : ℝ) / ((X : ℝ) * harmonicNormalizer X W) ≤
        (h : ℝ) / ((X : ℝ) * (Real.log X - (W : ℝ) / X)) := by
    have hqW : (q : ℝ) * W = h := by
      have hqWInt : ((q * W : ℕ) : ℤ) = h := by
        calc
          ((q * W : ℕ) : ℤ) = (t : ℤ) := by exact_mod_cast hmul.symm
          _ = h := hcast
      have hqWReal : ((q * W : ℕ) : ℝ) = h := by exact_mod_cast hqWInt
      simpa [Nat.cast_mul] using hqWReal
    have htheta : (Nat.totient W : ℝ) / W * (h : ℝ) =
        ((q * Nat.totient W : ℕ) : ℝ) := by
      rw [← hqW]
      field_simp [ne_of_gt (show (0 : ℝ) < W by exact_mod_cast hW)]
      push_cast
      <;> ring
    have htarget : 0 < (X : ℝ) * (Real.log X - (W : ℝ) / X) :=
      mul_pos hXpos hDpos
    have hsource : 0 < (X : ℝ) * harmonicNormalizer X W := mul_pos hXpos hZpos
    have hcross :
        ((q * Nat.totient W : ℕ) : ℝ) *
            ((X : ℝ) * (Real.log X - (W : ℝ) / X)) ≤
          (h : ℝ) * ((X : ℝ) * harmonicNormalizer X W) := by
      rw [← htheta]
      have hhR : 0 ≤ (h : ℝ) := by exact_mod_cast hh
      have hn := mul_le_mul_of_nonneg_right hnormLower hhR
      have hnX := mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ X)
      nlinarith [hnX]
    exact (div_le_div_iff₀ hsource htarget).2 hcross
  have hL1bound : arithmeticL1 (translatedLaw μ h) μ ≤
      2 * (h : ℝ) / ((X : ℝ) * (Real.log X - (W : ℝ) / X)) := by
    rw [hL1]
    calc
      2 * ∑ z ∈ S, max (μ z - translatedLaw μ h z) 0 ≤ 2 * ∑ z ∈ E, μ z :=
        mul_le_mul_of_nonneg_left hsumNeg (by norm_num)
      _ ≤ 2 * ((h : ℝ) / ((X : ℝ) * (Real.log X - (W : ℝ) / X))) :=
        mul_le_mul_of_nonneg_left (hEdge.trans hEdgeNorm) (by norm_num)
      _ = _ := by ring
  have hμsum : (∑ z ∈ S, μ z) = 1 := by
    have htsum : (∑' z : ℤ, μ z) = ∑ z ∈ S, μ z :=
      tsum_eq_sum (f := μ) (s := S) (fun z hz => (hsupp z hz).2)
    rw [← htsum]
    exact harmonicLaw_mass_one X W hW hX hden
  have htrivial : arithmeticL1 (translatedLaw μ h) μ ≤ 2 := by
    rw [hL1]
    have hpoint (z : ℤ) : max (μ z - translatedLaw μ h z) 0 ≤ μ z := by
      have hμ := harmonicLaw_nonneg X W hW hX hden z
      have htr := harmonicLaw_nonneg X W hW hX hden (z - h)
      have htr' : 0 ≤ translatedLaw μ h z := by simpa [translatedLaw, μ] using htr
      exact max_le (by linarith) hμ
    calc
      2 * ∑ z ∈ S, max (μ z - translatedLaw μ h z) 0 ≤ 2 * ∑ z ∈ S, μ z :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z hz => hpoint z) (by norm_num)
      _ = 2 := by rw [hμsum]; ring
  exact ⟨hL1bound, htrivial⟩

private theorem dilatedLaw_at_nat_multiple (X W k m : ℕ) (hk : 0 < k) :
    dilatedLaw (harmonicLaw X W) k ((k * m : ℕ) : ℤ) = harmonicLaw X W (m : ℤ) := by
  unfold dilatedLaw
  have hdiv : (k : ℤ) ∣ ((k * m : ℕ) : ℤ) := by
    refine ⟨m, ?_⟩
    push_cast
    ring
  rw [if_pos (Int.emod_eq_zero_of_dvd hdiv)]
  have hquot : ((k * m : ℕ) : ℤ) / (k : ℤ) = (m : ℤ) := by
    rw [← Int.natCast_ediv]
    simp [Nat.mul_div_left, hk]
  rw [hquot]

private theorem dilation_pair_zero_outside (X W k : ℕ) (hk : 0 < k) {z : ℤ}
    (hz : z ∉ Finset.Icc (0 : ℤ) ((k * X ^ 2 : ℕ) : ℤ)) :
    dilatedLaw (harmonicLaw X W) k z = 0 ∧
      dilationReference (harmonicLaw X W) k z = 0 := by
  constructor
  · unfold dilatedLaw
    by_cases hmod : z % (k : ℤ) = 0
    · have hdiv : (k : ℤ) ∣ z := Int.dvd_iff_emod_eq_zero.mpr hmod
      have hquotZero : harmonicLaw X W (z / (k : ℤ)) = 0 := by
        apply harmonicLaw_eq_zero_of_not_support X W
        intro hbase
        rcases Finset.mem_Icc.mp hbase with ⟨hlo, hhi⟩
        have hdecomp := Int.emod_add_mul_ediv z (k : ℤ)
        rw [hmod] at hdecomp
        have hmul : z = (k : ℤ) * (z / (k : ℤ)) := by simpa using hdecomp.symm
        have hkR : 0 < (k : ℤ) := by exact_mod_cast hk
        have hzlo : 0 ≤ z := by nlinarith
        have hXsq : (z / (k : ℤ)) ≤ (X ^ 2 : ℕ) := hhi
        have hzupper : z ≤ ((k * X ^ 2 : ℕ) : ℤ) := by
          have hmulUpper := Int.mul_le_mul_of_nonneg_left hXsq hkR.le
          rw [hmul]
          simpa [Int.natCast_mul] using hmulUpper
        exact (hz (Finset.mem_Icc.mpr ⟨hzlo, hzupper⟩)).elim
      simp [hmod, hquotZero]
    · simp [hmod]
  · unfold dilationReference
    by_cases hdiv : (k : ℤ) ∣ z
    · have hμzero : harmonicLaw X W z = 0 := by
        apply harmonicLaw_eq_zero_of_not_support X W
        intro hbase
        rcases Finset.mem_Icc.mp hbase with ⟨hlo, hhi⟩
        have hkR : 1 ≤ (k : ℤ) := by exact_mod_cast hk
        have hzupper : z ≤ ((k * X ^ 2 : ℕ) : ℤ) := by
          have hmulUpper := Int.mul_le_mul_of_nonneg_left hhi (by omega : (0 : ℤ) ≤ k)
          calc
            z ≤ (k : ℤ) * z := by nlinarith
            _ ≤ (k : ℤ) * (X ^ 2 : ℕ) := hmulUpper
            _ = ((k * X ^ 2 : ℕ) : ℤ) := by norm_cast
        exact (hz (Finset.mem_Icc.mpr ⟨le_trans (by norm_num) hlo, hzupper⟩)).elim
      simp [hdiv, hμzero]
    · simp [hdiv]

private theorem harmonic_dilation_l1_scaled_sum (X W k : ℕ) (hW : 0 < W)
    (hX : 2 ≤ X) (hden : Real.log X > (W : ℝ) / X) (hk : 1 ≤ k) :
    arithmeticL1 (dilatedLaw (harmonicLaw X W) k)
      (dilationReference (harmonicLaw X W) k) =
      ∑ m ∈ Finset.Icc 0 (X ^ 2),
        |harmonicLaw X W (m : ℤ) - (k : ℝ) * harmonicLaw X W ((k * m : ℕ) : ℤ)| := by
  classical
  let S : Finset ℤ := Finset.Icc (0 : ℤ) ((k * X ^ 2 : ℕ) : ℤ)
  let A : ℤ → ℝ := dilatedLaw (harmonicLaw X W) k
  let B : ℤ → ℝ := dilationReference (harmonicLaw X W) k
  have hzero (z : ℤ) (hz : z ∉ S) : A z = 0 ∧ B z = 0 := by
    simpa [A, B, S] using dilation_pair_zero_outside X W k (by omega) hz
  have hzeroDvd (z : ℤ) (hd : ¬(k : ℤ) ∣ z) : A z = 0 ∧ B z = 0 := by
    have hmod : z % (k : ℤ) ≠ 0 := by
      intro hmod
      exact hd (Int.dvd_iff_emod_eq_zero.mpr hmod)
    constructor
    · dsimp [A, dilatedLaw]
      simp [hmod]
    · dsimp [B, dilationReference]
      simp [hd]
  have hfinite : arithmeticL1 A B = ∑ z ∈ S, |A z - B z| := by
    unfold arithmeticL1
    exact tsum_eq_sum (f := fun z => |A z - B z|) (s := S) (fun z hz => by
      rcases hzero z hz with ⟨hA, hB⟩
      simp [hA, hB])
  have hfilter : (∑ z ∈ S, |A z - B z|) =
      ∑ z ∈ S.filter (fun z => (k : ℤ) ∣ z), |A z - B z| := by
    calc
      _ = ∑ z ∈ S, if (k : ℤ) ∣ z then |A z - B z| else 0 := by
            apply Finset.sum_congr rfl
            intro z hz
            by_cases hd : (k : ℤ) ∣ z
            · simp [hd]
            · rcases hzeroDvd z hd with ⟨hA, hB⟩
              simp [hd, hA, hB]
      _ = _ := by rw [← Finset.sum_filter]
  rw [hfinite, hfilter]
  refine Finset.sum_bij (fun z hz => z.toNat / k) ?_ ?_ ?_ ?_
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzS, hdiv⟩
    have hzI := Finset.mem_Icc.mp hzS
    have hzcast : (z.toNat : ℤ) = z := Int.natCast_toNat_eq_self.mpr hzI.1
    have hdivCast : (k : ℤ) ∣ (z.toNat : ℤ) := by simpa [hzcast] using hdiv
    have hdivNat : k ∣ z.toNat := Int.natCast_dvd_natCast.mp hdivCast
    have hmul : k * (z.toNat / k) = z.toNat := Nat.mul_div_cancel' hdivNat
    have hquot : z.toNat / k ≤ X ^ 2 := by
      have hzupper : z.toNat ≤ k * X ^ 2 := by
        have hzupperInt : (z.toNat : ℤ) ≤ ((k * X ^ 2 : ℕ) : ℤ) := by
          simpa [hzcast] using hzI.2
        exact_mod_cast hzupperInt
      have hmulUpper : k * (z.toNat / k) ≤ k * X ^ 2 := by simpa [hmul] using hzupper
      exact Nat.le_of_mul_le_mul_left hmulUpper (by omega)
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hquot⟩
  · intro z hz1 z' hz2 heq
    have hzI1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hz1).1
    have hzI2 := Finset.mem_Icc.mp (Finset.mem_filter.mp hz2).1
    have hzcast1 : (z.toNat : ℤ) = z := Int.natCast_toNat_eq_self.mpr hzI1.1
    have hzcast2 : (z'.toNat : ℤ) = z' := Int.natCast_toNat_eq_self.mpr hzI2.1
    have hd1 : k ∣ z.toNat := Int.natCast_dvd_natCast.mp (by
      simpa [hzcast1] using (Finset.mem_filter.mp hz1).2)
    have hd2 : k ∣ z'.toNat := Int.natCast_dvd_natCast.mp (by
      simpa [hzcast2] using (Finset.mem_filter.mp hz2).2)
    have hm1 : k * (z.toNat / k) = z.toNat := Nat.mul_div_cancel' hd1
    have hm2 : k * (z'.toNat / k) = z'.toNat := Nat.mul_div_cancel' hd2
    have hnat : z.toNat = z'.toNat := by rw [← hm1, ← hm2, heq]
    rw [← hzcast1, ← hzcast2]
    exact_mod_cast hnat
  · intro m hm
    have hmI := Finset.mem_Icc.mp hm
    have hkpos : 0 < k := by omega
    refine ⟨((k * m : ℕ) : ℤ), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor
        · positivity
        · have hkm : k * m ≤ k * X ^ 2 := Nat.mul_le_mul_left k hmI.2
          exact_mod_cast hkm
      · refine ⟨m, ?_⟩
        push_cast
        ring
    · have hnat : ((k * m : ℕ) : ℤ).toNat = k * m := by
        apply Int.ofNat.inj
        exact Int.toNat_of_nonneg (by positivity)
      rw [hnat]
      exact Nat.mul_div_right m hkpos
  · intro z hz
    let m : ℕ := z.toNat / k
    have hzI := Finset.mem_Icc.mp (Finset.mem_filter.mp hz).1
    have hzcast : (z.toNat : ℤ) = z := Int.natCast_toNat_eq_self.mpr hzI.1
    have hd : k ∣ z.toNat := Int.natCast_dvd_natCast.mp (by
      simpa [hzcast] using (Finset.mem_filter.mp hz).2)
    have hmul : k * m = z.toNat := by dsimp [m]; exact Nat.mul_div_cancel' hd
    have hzm : z = ((k * m : ℕ) : ℤ) := by
      calc
        z = (z.toNat : ℤ) := hzcast.symm
        _ = ((k * m : ℕ) : ℤ) := by rw [hmul]
    have hmap : ((k * m : ℕ) : ℤ).toNat / k = m := by
      have hkpos : 0 < k := by omega
      have hnat : ((k * m : ℕ) : ℤ).toNat = k * m := by
        apply Int.ofNat.inj
        exact Int.toNat_of_nonneg (by positivity)
      rw [hnat]
      exact Nat.mul_div_right m hkpos
    have hmapInt :
        (((((k * m : ℕ) : ℤ).toNat : ℕ) : ℤ) / (k : ℤ)) = (m : ℤ) := by
      rw [← Int.natCast_ediv]
      have hnatMul : ((k * m : ℕ) : ℤ).toNat = k * m := by
        apply Int.ofNat.inj
        exact Int.toNat_of_nonneg (by positivity)
      rw [hnatMul]
      exact_mod_cast (Nat.mul_div_right m (by omega : 0 < k))
    rw [hzm]
    dsimp [A, B]
    rw [← Int.natCast_mul]
    rw [hmapInt]
    rw [dilatedLaw_at_nat_multiple X W k m (by omega)]
    have hdivkm : (k : ℤ) ∣ ((k * m : ℕ) : ℤ) := by
      refine ⟨m, ?_⟩
      push_cast
      ring
    simp [dilationReference, hdivkm]

private theorem harmonic_dilation_term_tail_bound (X W k : ℕ) (hW : 0 < W)
    (hX : 2 ≤ X) (hden : Real.log X > (W : ℝ) / X) (hk : 1 ≤ k) (hkX : k ≤ X)
    (hcop : Nat.Coprime k W) (m : ℕ) :
    |harmonicLaw X W (m : ℤ) - (k : ℝ) * harmonicLaw X W ((k * m : ℕ) : ℤ)| ≤
      (if m < X ∧ X ≤ k * m ∧ Nat.Coprime m W then
          1 / ((m : ℝ) * harmonicNormalizer X W) else 0) +
        (if X ≤ m ∧ m < X ^ 2 ∧ X ^ 2 ≤ k * m ∧ Nat.Coprime m W then
          1 / ((m : ℝ) * harmonicNormalizer X W) else 0) := by
  have hZpos : 0 < harmonicNormalizer X W := harmonicNormalizer_pos X W hW hX hden
  have hcopMul : Nat.Coprime (k * m) W ↔ Nat.Coprime m W := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨And.right, fun hm => ⟨hcop, hm⟩⟩
  have hμm : harmonicLaw X W (m : ℤ) =
      if X ≤ m ∧ m < X ^ 2 ∧ Nat.Coprime m W then
        1 / ((m : ℝ) * harmonicNormalizer X W) else 0 := by
    simp [harmonicLaw]
  have hkmCastInt : ((k : ℤ) * (m : ℤ)).toNat = k * m := by
    have hmulcast : (k : ℤ) * (m : ℤ) = ((k * m : ℕ) : ℤ) := by norm_cast
    rw [hmulcast]
    apply Int.ofNat.inj
    exact Int.toNat_of_nonneg (by positivity)
  have hμkm : harmonicLaw X W ((k : ℕ) * m : ℤ) =
      if 0 ≤ (k : ℤ) * (m : ℤ) ∧ X ≤ ((k : ℤ) * (m : ℤ)).toNat ∧
          ((k : ℤ) * (m : ℤ)).toNat < X ^ 2 ∧
            Nat.Coprime ((k : ℤ) * (m : ℤ)).toNat W then
        1 / ((((k : ℤ) * (m : ℤ)).toNat : ℝ) * harmonicNormalizer X W) else 0 := rfl
  have hμkmSimple : harmonicLaw X W ((k * m : ℕ) : ℤ) =
      if X ≤ k * m ∧ k * m < X ^ 2 ∧ Nat.Coprime (k * m) W then
        1 / ((k * m : ℕ) * harmonicNormalizer X W) else 0 := by
    have hmulcast : ((k * m : ℕ) : ℤ) = (k : ℤ) * (m : ℤ) := by norm_cast
    rw [hmulcast, hμkm]
    by_cases hQ : X ≤ k * m ∧ k * m < X ^ 2 ∧ Nat.Coprime (k * m) W
    · have hP : 0 ≤ (k : ℤ) * (m : ℤ) ∧ X ≤ ((k : ℤ) * (m : ℤ)).toNat ∧
          ((k : ℤ) * (m : ℤ)).toNat < X ^ 2 ∧ Nat.Coprime ((k : ℤ) * (m : ℤ)).toNat W := by
        refine ⟨by positivity, ?_, ?_, ?_⟩
        · rw [hkmCastInt]; exact hQ.1
        · rw [hkmCastInt]; exact hQ.2.1
        · rw [hkmCastInt]; exact hQ.2.2
      rw [if_pos hP, if_pos hQ]
      simp [hkmCastInt, Nat.cast_mul]
    · have hP : ¬(0 ≤ (k : ℤ) * (m : ℤ) ∧ X ≤ ((k : ℤ) * (m : ℤ)).toNat ∧
          ((k : ℤ) * (m : ℤ)).toNat < X ^ 2 ∧ Nat.Coprime ((k : ℤ) * (m : ℤ)).toNat W) := by
        intro hp
        apply hQ
        have hp' : X ≤ k * m ∧ k * m < X ^ 2 ∧ Nat.Coprime (k * m) W := by
          simpa [hkmCastInt] using hp.2
        exact hp'
      rw [if_neg hP, if_neg hQ]
  have hcancel (hm : 0 < m) :
      (k : ℝ) * (1 / (((k * m : ℕ) : ℝ) * harmonicNormalizer X W)) =
        1 / ((m : ℝ) * harmonicNormalizer X W) := by
    have hkR : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hk)
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    field_simp [ne_of_gt hkR, ne_of_gt hmR, hZpos.ne']
    <;> norm_cast
  have hcancelNat (hm : 0 < m) :
        (k : ℝ) * (1 / (((k * m : ℕ) : ℝ) * harmonicNormalizer X W)) =
        1 / ((m : ℝ) * harmonicNormalizer X W) := by
    simpa only [Nat.cast_mul] using hcancel hm
  by_cases hmlo : m < X
  · by_cases hkmlo : X ≤ k * m
    · have hkmhi : k * m < X ^ 2 := by
        calc
          k * m < k * X := Nat.mul_lt_mul_of_pos_left hmlo (by omega)
          _ ≤ X * X := Nat.mul_le_mul_right X hkX
          _ = X ^ 2 := by simp [pow_two]
      by_cases hcopm : Nat.Coprime m W
      · have hmpos : 0 < m := by
          by_contra hm0
          have hmz : m = 0 := Nat.eq_zero_of_not_pos hm0
          subst m
          omega
        have hμm0 : harmonicLaw X W (m : ℤ) = 0 := by rw [hμm]; simp [hmlo]
        have hkmcop : Nat.Coprime (k * m) W := hcopMul.mpr hcopm
        have hμkmVal : harmonicLaw X W ((k * m : ℕ) : ℤ) =
            1 / (((k * m : ℕ) : ℝ) * harmonicNormalizer X W) := by
          rw [hμkmSimple]
          simp [hkmlo, hkmhi, hkmcop]
        rw [hμm0, hμkmVal, hcancelNat hmpos]
        have hLower : m < X ∧ X ≤ k * m ∧ Nat.Coprime m W := ⟨hmlo, hkmlo, hcopm⟩
        have hUpper : ¬(X ≤ m ∧ m < X ^ 2 ∧ X ^ 2 ≤ k * m ∧ Nat.Coprime m W) := by
          intro hu
          omega
        rw [if_pos hLower, if_neg hUpper]
        simp [abs_of_pos hZpos]
      · have hμm0 : harmonicLaw X W (m : ℤ) = 0 := by rw [hμm]; simp [hmlo, hcopm]
        have hkmcop : ¬Nat.Coprime (k * m) W := by
          intro hkmcop
          exact hcopm (hcopMul.mp hkmcop)
        have hμkm0 : harmonicLaw X W ((k * m : ℕ) : ℤ) = 0 := by
          rw [hμkmSimple]
          simp [hkmlo, hkmhi, hkmcop]
        rw [hμm0, hμkm0]
        have hLower : ¬(m < X ∧ X ≤ k * m ∧ Nat.Coprime m W) := by
          intro hl
          exact hcopm hl.2.2
        have hUpper : ¬(X ≤ m ∧ m < X ^ 2 ∧ X ^ 2 ≤ k * m ∧ Nat.Coprime m W) := by
          intro hu
          exact hcopm hu.2.2.2
        rw [if_neg hLower, if_neg hUpper]
        simp
    · have hμm0 : harmonicLaw X W (m : ℤ) = 0 := by rw [hμm]; simp [hmlo]
      have hμkm0 : harmonicLaw X W ((k * m : ℕ) : ℤ) = 0 := by
        rw [hμkmSimple]
        simp [hkmlo]
      rw [hμm0, hμkm0]
      have hLower : ¬(m < X ∧ X ≤ k * m ∧ Nat.Coprime m W) := by
        intro hl
        exact hkmlo hl.2.1
      have hUpper : ¬(X ≤ m ∧ m < X ^ 2 ∧ X ^ 2 ≤ k * m ∧ Nat.Coprime m W) := by
        intro hu
        exact (Nat.not_le_of_gt hmlo) hu.1
      rw [if_neg hLower, if_neg hUpper]
      simp
  · have hXle : X ≤ m := le_of_not_gt hmlo
    have hkmlo : X ≤ k * m := by
      calc
        X ≤ m := hXle
        _ = 1 * m := by simp
        _ ≤ k * m := Nat.mul_le_mul_right m hk
    by_cases hmhi : m < X ^ 2
    · by_cases hkmhi : k * m < X ^ 2
      · by_cases hcopm : Nat.Coprime m W
        · have hmpos : 0 < m := lt_of_lt_of_le (by omega : 0 < X) hXle
          have hμmVal : harmonicLaw X W (m : ℤ) =
              1 / ((m : ℝ) * harmonicNormalizer X W) := by rw [hμm]; simp [hXle, hmhi, hcopm]
          have hμkmVal : harmonicLaw X W ((k * m : ℕ) : ℤ) =
              1 / (((k * m : ℕ) : ℝ) * harmonicNormalizer X W) := by
            have hkmcop : Nat.Coprime (k * m) W := hcopMul.mpr hcopm
            rw [hμkmSimple]
            simp [hkmlo, hkmhi, hkmcop]
          rw [hμmVal, hμkmVal, hcancelNat hmpos]
          have hLower : ¬(m < X ∧ X ≤ k * m ∧ Nat.Coprime m W) := by
            intro hl
            omega
          have hUpper : ¬(X ≤ m ∧ m < X ^ 2 ∧ X ^ 2 ≤ k * m ∧ Nat.Coprime m W) := by
            intro hu
            exact (Nat.not_le_of_gt hkmhi) hu.2.2.1
          rw [if_neg hLower, if_neg hUpper]
          simp
        · have hμm0 : harmonicLaw X W (m : ℤ) = 0 := by rw [hμm]; simp [hXle, hmhi, hcopm]
          have hkmcop : ¬Nat.Coprime (k * m) W := by
            intro hkmcop
            exact hcopm (hcopMul.mp hkmcop)
          have hμkm0 : harmonicLaw X W ((k * m : ℕ) : ℤ) = 0 := by
            rw [hμkmSimple]
            simp [hkmlo, hkmhi, hkmcop]
          rw [hμm0, hμkm0]
          have hLower : ¬(m < X ∧ X ≤ k * m ∧ Nat.Coprime m W) := by
            intro hl
            omega
          have hUpper : ¬(X ≤ m ∧ m < X ^ 2 ∧ X ^ 2 ≤ k * m ∧ Nat.Coprime m W) := by
            intro hu
            exact hcopm hu.2.2.2
          rw [if_neg hLower, if_neg hUpper]
          simp
      · have hkmge : X ^ 2 ≤ k * m := le_of_not_gt hkmhi
        by_cases hcopm : Nat.Coprime m W
        · have hμmVal : harmonicLaw X W (m : ℤ) =
              1 / ((m : ℝ) * harmonicNormalizer X W) := by rw [hμm]; simp [hXle, hmhi, hcopm]
          have hμkm0 : harmonicLaw X W ((k * m : ℕ) : ℤ) = 0 := by
            rw [hμkmSimple]
            simp [hkmge]
          rw [hμmVal, hμkm0]
          have hLower : ¬(m < X ∧ X ≤ k * m ∧ Nat.Coprime m W) := by
            intro hl
            omega
          have hUpper : X ≤ m ∧ m < X ^ 2 ∧ X ^ 2 ≤ k * m ∧ Nat.Coprime m W :=
            ⟨hXle, hmhi, hkmge, hcopm⟩
          rw [if_neg hLower, if_pos hUpper]
          simp [abs_of_pos hZpos]
        · have hμm0 : harmonicLaw X W (m : ℤ) = 0 := by rw [hμm]; simp [hXle, hmhi, hcopm]
          have hkmcop : ¬Nat.Coprime (k * m) W := by
            intro hkmcop
            exact hcopm (hcopMul.mp hkmcop)
          have hμkm0 : harmonicLaw X W ((k * m : ℕ) : ℤ) = 0 := by
            rw [hμkmSimple]
            simp [hkmge, hkmcop]
          rw [hμm0, hμkm0]
          have hLower : ¬(m < X ∧ X ≤ k * m ∧ Nat.Coprime m W) := by
            intro hl
            omega
          have hUpper : ¬(X ≤ m ∧ m < X ^ 2 ∧ X ^ 2 ≤ k * m ∧ Nat.Coprime m W) := by
            intro hu
            exact hcopm hu.2.2.2
          rw [if_neg hLower, if_neg hUpper]
          simp
    · have hmge : X ^ 2 ≤ m := le_of_not_gt hmhi
      have hkmge : X ^ 2 ≤ k * m := by
        calc
          X ^ 2 ≤ m := hmge
          _ = 1 * m := by simp
          _ ≤ k * m := Nat.mul_le_mul_right m hk
      have hμm0 : harmonicLaw X W (m : ℤ) = 0 := by rw [hμm]; simp [hmhi]
      have hμkm0 : harmonicLaw X W ((k * m : ℕ) : ℤ) = 0 := by
        rw [hμkmSimple]
        simp [hkmge]
      rw [hμm0, hμkm0]
      have hLower : ¬(m < X ∧ X ≤ k * m ∧ Nat.Coprime m W) := by
        intro hl
        omega
      have hUpper : ¬(X ≤ m ∧ m < X ^ 2 ∧ X ^ 2 ≤ k * m ∧ Nat.Coprime m W) := by
        intro hu
        exact Nat.not_lt_of_ge hmge hu.2.1
      rw [if_neg hLower, if_neg hUpper]
      simp

/-- Pointwise harmonic estimates underlying Lemma `lem:sampling`. -/
theorem sampling_pointwise_claim (X W : ℕ) (hW : 0 < W) (hX : 2 ≤ X)
    (hlog : Real.log X > (W : ℝ) / X) : SamplingPointwiseBounds X W := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k a A B hcop ha hA hAB
    have hfinite :
        (∑' n : ℕ, if A ≤ (n : ℝ) ∧ (n : ℝ) < B ∧
            Nat.Coprime n W ∧ n % k = a then 1 / (n : ℝ) else 0) =
          ∑ n ∈ Finset.Ico ⌈A⌉₊ ⌈B⌉₊,
            (if A ≤ (n : ℝ) ∧ (n : ℝ) < B ∧
              Nat.Coprime n W ∧ n % k = a then 1 else 0) / (n : ℝ) := by
      rw [tsum_eq_sum (s := Finset.Ico ⌈A⌉₊ ⌈B⌉₊)]
      · apply Finset.sum_congr rfl
        intro n hn
        by_cases hc : A ≤ (n : ℝ) ∧ (n : ℝ) < B ∧
            Nat.Coprime n W ∧ n % k = a
        · rw [if_pos hc]
          rw [if_pos hc]
        · simp [hc]
      · intro n hn
        by_cases hc : A ≤ (n : ℝ) ∧ (n : ℝ) < B ∧
            Nat.Coprime n W ∧ n % k = a
        · exfalso
          apply hn
          apply Finset.mem_Ico.mpr
          exact ⟨(Nat.ceil_le).2 hc.1, (Nat.lt_ceil).2 hc.2.1⟩
        · simp [hc]
    rw [hfinite]
    exact periodic_harmonic_interval_bound W k a hW (by omega) hcop ha hA hAB
  · intro hX' hden
    exact harmonicNormalizer_bound X W hW hX'
  · intro hX' hden k a hcop hk ha
    exact harmonic_residue_pointwise_bound X W hW hX' hden k a hcop hk ha
  · intro hX' hden k hcop hk
    have hpoint (a : Fin k) :
        |(k : ℝ) * harmonicResidueLaw (harmonicLaw X W) k a - 1| ≤
          harmonicResidueError X W k :=
      harmonic_residue_pointwise_bound X W hW hX' hden k a.val hcop hk a.isLt
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    unfold finiteL1 uniformResidueLaw
    change (∑ a : Fin k,
      |harmonicResidueLaw (harmonicLaw X W) k a - 1 / (k : ℝ)|) ≤
        harmonicResidueError X W k
    calc
      _ = ∑ a : Fin k,
          |(k : ℝ) * harmonicResidueLaw (harmonicLaw X W) k a - 1| / (k : ℝ) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [show harmonicResidueLaw (harmonicLaw X W) k a - 1 / (k : ℝ) =
              ((k : ℝ) * harmonicResidueLaw (harmonicLaw X W) k a - 1) / (k : ℝ) by
                field_simp [ne_of_gt hkR]
                <;> ring]
            rw [abs_div, abs_of_pos hkR]
      _ ≤ ∑ a : Fin k, harmonicResidueError X W k / (k : ℝ) :=
            Finset.sum_le_sum fun a _ => div_le_div_of_nonneg_right (hpoint a) hkR.le
      _ = harmonicResidueError X W k := by
            simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
            field_simp [ne_of_gt hkR]
  · intro hX' hden h hdiv
    let μ : ℤ → ℝ := harmonicLaw X W
    rcases le_total 0 h with hh | hh
    · have hbound := harmonic_translation_bound_nonneg X W hW hX' hden hh hdiv
      have hratio : arithmeticL1 (translatedLaw μ h) μ ≤
          2 * |(h : ℝ)| / ((X : ℝ) * (Real.log X - (W : ℝ) / X)) := by
        simpa [abs_of_nonneg (show (0 : ℝ) ≤ h by exact_mod_cast hh)] using hbound.1
      exact le_min hbound.2 hratio
    · have hdivNeg : (W : ℤ) ∣ -h := dvd_neg.mpr hdiv
      have hbound := harmonic_translation_bound_nonneg X W hW hX' hden
        (neg_nonneg.mpr hh) hdivNeg
      have hsymm : arithmeticL1 (translatedLaw μ h) μ =
          arithmeticL1 (translatedLaw μ (-h)) μ := by
        unfold arithmeticL1 translatedLaw
        calc
          (∑' z : ℤ, |μ (z - h) - μ z|) =
              ∑' z : ℤ, |μ z - μ (z - h)| := by
                apply tsum_congr
                intro z
                exact abs_sub_comm _ _
          _ = ∑' z : ℤ, |μ (z + h) - μ z| := by
                simpa [Equiv.addRight] using
                  ((Equiv.addRight h).tsum_eq
                    (f := fun z : ℤ => |μ z - μ (z - h)|)).symm
          _ = ∑' z : ℤ, |μ (z - (-h)) - μ z| := by
                simp [sub_neg_eq_add]
      rw [hsymm]
      have hratio : arithmeticL1 (translatedLaw μ (-h)) μ ≤
          2 * |(h : ℝ)| / ((X : ℝ) * (Real.log X - (W : ℝ) / X)) := by
        have hnegCast : ((-h : ℤ) : ℝ) = -h := by simp
        have habs : |(h : ℝ)| = -h := abs_of_nonpos (by exact_mod_cast hh)
        simpa [hnegCast, habs] using hbound.1
      exact le_min hbound.2 hratio
  · sorry

/-- Uniform sampling on an integer interval: residue total-mass error and translation error
from §3 lines 132–143. -/
theorem uniform_interval_sampling_bounds (a T k : ℕ) (hT : 0 < T) (hk : 0 < k) :
    finiteL1
        (fun r : Fin k =>
          ∑ n ∈ (Finset.Ico a (a + T)), if n % k = r.val then 1 / (T : ℝ) else 0)
        (uniformResidueLaw k) ≤ 2 * k / T := by
  classical
  have hmass (r : Fin k) :
      (∑ n ∈ Finset.Ico a (a + T), if n % k = r.val then 1 / (T : ℝ) else 0) =
        (({n ∈ Finset.Ico a (a + T) | n % k = r.val}.card : ℝ) / T) := by
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hdev (r : Fin k) :
      |(∑ n ∈ Finset.Ico a (a + T), if n % k = r.val then 1 / (T : ℝ) else 0) -
        1 / (k : ℝ)| ≤ 1 / (T : ℝ) := by
    rw [hmass r]
    have hr := interval_residue_card_error a T k r.val hk r.isLt
    have hTr : (0 : ℝ) < T := by exact_mod_cast hT
    have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have h' : |(↑({n ∈ Finset.Ico a (a + T) | n % k = r.val}.card : ℝ) - (T : ℝ) / k) / T| ≤
        1 / T := by
      rw [abs_div, abs_of_pos hTr]
      exact div_le_div_of_nonneg_right hr hTr.le
    have heq : ((↑({n ∈ Finset.Ico a (a + T) | n % k = r.val}.card : ℝ) / T) - 1 / k) =
        (↑({n ∈ Finset.Ico a (a + T) | n % k = r.val}.card : ℝ) - (T : ℝ) / k) / T := by
      field_simp [ne_of_gt hTr, ne_of_gt hkr]
    rw [heq]
    exact h'
  unfold finiteL1 uniformResidueLaw
  change (∑ r : Fin k, |(∑ n ∈ Finset.Ico a (a + T),
    if n % k = r.val then 1 / (T : ℝ) else 0) - 1 / (k : ℝ)|) ≤ 2 * (k : ℝ) / T
  calc
    (∑ r : Fin k, |(∑ n ∈ Finset.Ico a (a + T), if n % k = r.val then 1 / (T : ℝ) else 0) - 1 / (k : ℝ)|)
        ≤ ∑ r : Fin k, 1 / (T : ℝ) := Finset.sum_le_sum fun r _ => hdev r
    _ = (k : ℝ) / T := by simp [div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (k : ℝ) / T := by
      have hkR : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
      have hn : 0 ≤ (k : ℝ) / T := div_nonneg hkR hTR.le
      rw [show 2 * (k : ℝ) / T = 2 * ((k : ℝ) / T) by ring]
      nlinarith

/-- Translating a uniform integer interval by u changes its probability law in total-mass
norm by at most `2 min(1,|u|/T)` (§3 lines 137–140). -/
def uniformIntegerIntervalLaw (a : ℤ) (T : ℕ) (z : ℤ) : ℝ :=
  if a ≤ z ∧ z < a + T then 1 / (T : ℝ) else 0

theorem uniform_interval_translation_bound (a u : ℤ) (T : ℕ) (hT : 0 < T) :
    arithmeticL1 (translatedLaw (uniformIntegerIntervalLaw a T) u)
      (uniformIntegerIntervalLaw a T) ≤
      2 * min 1 (|u| / (T : ℝ)) := by
  classical
  let I : Finset ℤ := Finset.Ico a (a + T)
  let J : Finset ℤ := Finset.Ico (a + u) (a + u + T)
  let D : Finset ℤ := (J \ I) ∪ (I \ J)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hIcard : I.card = T := by
    have h : (I.card : ℤ) = (T : ℤ) := by
      dsimp [I]
      rw [Int.card_Ico_of_le a (a + (T : ℤ)) (by omega)
      ]
      simp
    exact_mod_cast h
  have hJcard : J.card = T := by
    have h : (J.card : ℤ) = (T : ℤ) := by
      dsimp [J]
      rw [Int.card_Ico_of_le (a + u) (a + u + (T : ℤ)) (by omega)]
      simp
    exact_mod_cast h
  have hshift (z : ℤ) :
      uniformIntegerIntervalLaw a T (z - u) = if z ∈ J then 1 / (T : ℝ) else 0 := by
    simp only [uniformIntegerIntervalLaw, J, Finset.mem_Ico]
    by_cases hz : a ≤ z - u ∧ z - u < a + (T : ℤ)
    · have hz' : a + u ≤ z ∧ z < a + u + (T : ℤ) := by omega
      simp [hz, hz']
    · have hz' : ¬ (a + u ≤ z ∧ z < a + u + (T : ℤ)) := by omega
      simp [hz, hz']
  have horig (z : ℤ) :
      uniformIntegerIntervalLaw a T z = if z ∈ I then 1 / (T : ℝ) else 0 := by
    simp only [uniformIntegerIntervalLaw, I, Finset.mem_Ico]
  have hterm (z : ℤ) :
      |(if z ∈ J then 1 / (T : ℝ) else 0) - (if z ∈ I then 1 / (T : ℝ) else 0)| =
        if z ∈ D then 1 / (T : ℝ) else 0 := by
    by_cases hj : z ∈ J <;> by_cases hi : z ∈ I <;>
      simp [D, hj, hi, abs_of_pos hTpos]
  have hL1 : arithmeticL1 (translatedLaw (uniformIntegerIntervalLaw a T) u)
      (uniformIntegerIntervalLaw a T) = (D.card : ℝ) / T := by
    unfold arithmeticL1 translatedLaw
    simp_rw [hshift, horig, hterm]
    rw [tsum_eq_sum (s := D) (fun z hz => by simp [hz])]
    calc
      (∑ z ∈ D, if z ∈ D then 1 / (T : ℝ) else 0) =
          (D.card : ℝ) * (1 / (T : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ = (D.card : ℝ) / T := by ring
  have hDlarge : D.card ≤ 2 * T := by
    calc
      D.card ≤ (J \ I).card + (I \ J).card := Finset.card_union_le _ _
      _ ≤ J.card + I.card := Nat.add_le_add
        (Finset.card_mono (Finset.sdiff_subset)) (Finset.card_mono (Finset.sdiff_subset))
      _ = 2 * T := by rw [hJcard, hIcard]; omega
  have hDsmall (hm : u.natAbs < T) : D.card = 2 * u.natAbs := by
    have hdis : Disjoint (J \ I) (I \ J) := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      simp only [Finset.mem_sdiff] at hz1 hz2
      exact hz1.2 hz2.1
    have hUnion := Finset.card_union_of_disjoint hdis
    by_cases hu : 0 ≤ u
    · have huNat : (u.natAbs : ℤ) = u := Int.natAbs_of_nonneg hu
      have hInter : I ∩ J = Finset.Ico (a + u) (a + (T : ℤ)) := by
        dsimp [I, J]
        rw [Finset.Ico_inter_Ico]
        congr 1
        · simp [max_eq_right (by omega : a ≤ a + u)]
        · simp [min_eq_left (by omega : a + (T : ℤ) ≤ a + u + (T : ℤ))]
      have hInterCard : (I ∩ J).card = T - u.natAbs := by
        have hmZ : (u.natAbs : ℤ) < (T : ℤ) := by exact_mod_cast hm
        have hle : a + u ≤ a + (T : ℤ) := by rw [← huNat]; omega
        have hraw : ((I ∩ J).card : ℤ) = (T : ℤ) - u := by
          rw [hInter, Int.card_Ico_of_le (a + u) (a + (T : ℤ)) hle]
          omega
        have hsub : ((T - u.natAbs : ℕ) : ℤ) = (T : ℤ) - u := by
          rw [Nat.cast_sub (Nat.le_of_lt hm)]
          simp [huNat]
        exact_mod_cast hraw.trans hsub.symm
      have h1 : (I \ J).card + (I ∩ J).card = T := by
        simpa [hIcard] using Finset.card_sdiff_add_card_inter I J
      have h2 : (J \ I).card + (I ∩ J).card = T := by
        simpa [hJcard, Finset.inter_comm] using Finset.card_sdiff_add_card_inter J I
      rw [hUnion]
      omega
    · have hu' : u ≤ 0 := le_of_not_ge hu
      have huNat : (u.natAbs : ℤ) = -u := by
        simpa only [Int.natAbs_neg] using
          (Int.natAbs_of_nonneg (neg_nonneg_of_nonpos hu'))
      have hInter : I ∩ J = Finset.Ico a (a + u + (T : ℤ)) := by
        dsimp [I, J]
        rw [Finset.Ico_inter_Ico]
        congr 1
        · simp [max_eq_left (by omega : a + u ≤ a)]
        · simp [min_eq_right (by omega : a + u + (T : ℤ) ≤ a + (T : ℤ))]
      have hInterCard : (I ∩ J).card = T - u.natAbs := by
        have hle : a ≤ a + u + (T : ℤ) := by
          have hm' : (u.natAbs : ℤ) < (T : ℤ) := by exact_mod_cast hm
          rw [huNat] at hm'
          omega
        have hraw : ((I ∩ J).card : ℤ) = (T : ℤ) - u.natAbs := by
          rw [hInter, Int.card_Ico_of_le a (a + u + (T : ℤ)) hle]
          rw [huNat]
          omega
        have hsub : ((T - u.natAbs : ℕ) : ℤ) = (T : ℤ) - u.natAbs := by
          rw [Nat.cast_sub (Nat.le_of_lt hm)]
        exact_mod_cast hraw.trans hsub.symm
      have h1 : (I \ J).card + (I ∩ J).card = T := by
        simpa [hIcard] using Finset.card_sdiff_add_card_inter I J
      have h2 : (J \ I).card + (I ∩ J).card = T := by
        simpa [hJcard, Finset.inter_comm] using Finset.card_sdiff_add_card_inter J I
      rw [hUnion]
      omega
  have huAbs : ((|u| : ℤ) : ℝ) = (u.natAbs : ℝ) := by
    exact congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs u).symm
  by_cases hm : u.natAbs < T
  · have hratio : (u.natAbs : ℝ) / T < 1 := (div_lt_one hTpos).2 (by exact_mod_cast hm)
    rw [hL1, hDsmall hm, huAbs, min_eq_right hratio.le]
    exact le_of_eq (by push_cast; ring)
  · have hratio : 1 ≤ (u.natAbs : ℝ) / T :=
      (one_le_div hTpos).2 (by exact_mod_cast (Nat.le_of_not_gt hm))
    rw [hL1, huAbs, min_eq_left hratio]
    have hDreal : (D.card : ℝ) ≤ 2 * (T : ℝ) := by exact_mod_cast hDlarge
    exact (div_le_iff₀ hTpos).2 (by simpa using hDreal)

/-- Telescoping bound for the total-mass distance of product laws, used for fixed disjoint
block families in §3 lines 139–143. -/
theorem finite_product_l1_telescoping {ι α : Type*} [Fintype ι] [Fintype α]
    [Fintype (ι → α)] [DecidableEq ι]
    (μ ν : ι → α → ℝ) :
    finiteL1 (fun x : ι → α => ∏ i, μ i (x i)) (fun x => ∏ i, ν i (x i)) ≤
      ∑ i, finiteL1 (μ i) (ν i) *
        ∏ j ∈ Finset.univ.erase i, max (∑ a, |μ j a|) (∑ a, |ν j a|) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  letI : LinearOrder ι := LinearOrder.lift' e e.injective
  let term (i : ι) (x : ι → α) : ℝ :=
    (μ i (x i) - ν i (x i)) *
      (∏ j ∈ Finset.univ with j < i, μ j (x j)) *
      ∏ j ∈ Finset.univ with i < j, ν j (x j)
  let weight (i j : ι) (a : α) : ℝ :=
    if j < i then |μ j a| else if i < j then |ν j a| else |μ i a - ν i a|
  have htel (x : ι → α) :
      (∏ i, μ i (x i)) - (∏ i, ν i (x i)) = ∑ i, term i x := by
    have h := Finset.prod_add_ordered (s := (Finset.univ : Finset ι))
      (fun i => ν i (x i)) (fun i => μ i (x i) - ν i (x i))
    let plus (i : ι) : ℝ := ν i (x i) + (μ i (x i) - ν i (x i))
    have hleft : (∏ i, plus i) =
        ∏ i, μ i (x i) := by
      apply Finset.prod_congr rfl
      intro i _
      dsimp [plus]
      ring
    have h' : (∏ i, μ i (x i)) = (∏ i, ν i (x i)) + ∑ i, term i x := by
      calc
        _ = ∏ i, plus i := hleft.symm
        _ = (∏ i, ν i (x i)) + ∑ i,
              ((μ i (x i) - ν i (x i)) *
                (∏ j ∈ Finset.univ with j < i,
                  (ν j (x j) + (μ j (x j) - ν j (x j)))) *
                ∏ j ∈ Finset.univ with i < j, ν j (x j)) := h
        _ = (∏ i, ν i (x i)) + ∑ i, term i x := by
              congr 1
              apply Finset.sum_congr rfl
              intro i _
              rw [show (∏ j ∈ Finset.univ with j < i, plus j : ℝ) =
                  ∏ j ∈ Finset.univ with j < i, μ j (x j) by
                    apply Finset.prod_congr rfl
                    intro j _
                    dsimp [plus]
                    ring]
    linarith
  have hterm_abs (i : ι) (x : ι → α) :
      |term i x| = ∏ j, weight i j (x j) := by
    dsimp [term, weight]
    have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
    let S : Finset ι := Finset.univ.erase i
    have hleft : S.filter (fun j => j < i) =
        (Finset.univ : Finset ι).filter (fun j => j < i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, hlt⟩
        exact hlt
      · intro hlt
        have hjS : j ∈ S := by
          dsimp [S]
          simp [Finset.mem_erase, ne_of_lt hlt]
        exact ⟨hjS, hlt⟩
    have hright : S.filter (fun j => ¬ j < i) =
        (Finset.univ : Finset ι).filter (fun j => i < j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (j ∈ Finset.univ.erase i ∧ ¬ j < i) ↔ i < j
      simp only [Finset.mem_erase, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hne, hnot⟩
        rcases hne with ⟨hne, _⟩
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact (hnot hlt).elim
        · exact hgt
      · intro hgt
        exact ⟨⟨ne_of_gt hgt, trivial⟩, not_lt_of_ge hgt.le⟩
    have hSprod :
        (∏ j ∈ S, weight i j (x j)) =
          (∏ j ∈ Finset.univ with j < i, |μ j (x j)|) *
            ∏ j ∈ Finset.univ with i < j, |ν j (x j)| := by
      calc
        _ = ∏ j ∈ S, if j < i then |μ j (x j)| else |ν j (x j)| := by
          apply Finset.prod_congr rfl
          intro j hj
          have hne : j ≠ i := (Finset.mem_erase.mp hj).1
          by_cases hlt : j < i
          · simp [weight, hlt]
          · have hgt : i < j := lt_of_not_ge (fun hle => hlt (lt_of_le_of_ne hle hne))
            simp [weight, hlt, hgt]
        _ = (∏ j ∈ S with j < i, |μ j (x j)|) *
              ∏ j ∈ S with ¬ j < i, |ν j (x j)| := by
          rw [Finset.prod_ite]
        _ = _ := by rw [hleft, hright]
    have hiweight : weight i i (x i) = |μ i (x i) - ν i (x i)| := by
      simp [weight]
    have huniv :
        (∏ j, weight i j (x j)) =
          weight i i (x i) * ∏ j ∈ S, weight i j (x j) := by
      rw [← Finset.insert_erase hi, Finset.prod_insert (by simp [S])]
    rw [huniv, hiweight, hSprod]
    rw [abs_mul, abs_mul, Finset.abs_prod, Finset.abs_prod]
    ring
  have hfactor (g : ι → α → ℝ) :
      (∑ x : ι → α, ∏ j, g j (x j)) = ∏ j, ∑ a, g j a := by
    change (∑ x ∈ (Finset.univ : Finset (ι → α)), ∏ j, g j (x j)) = _
    have hpi : Fintype.piFinset (fun _ : ι => (Finset.univ : Finset α)) =
        (Finset.univ : Finset (ι → α)) := by
      ext x
      simp [Fintype.mem_piFinset]
    rw [← hpi, Finset.sum_prod_piFinset]
  have hcoordinate (i j : ι) :
      (∑ a, weight i j a) ≤
        if j = i then finiteL1 (μ i) (ν i)
        else max (∑ a, |μ j a|) (∑ a, |ν j a|) := by
    by_cases hji : j = i
    · subst j
      simp [weight, finiteL1]
    · rcases lt_or_gt_of_ne hji with hlt | hgt
      · rw [if_neg hji]
        have hw : ∀ a, weight i j a = |μ j a| := by
          intro a
          simp [weight, hlt]
        simp_rw [hw]
        exact le_max_left _ _
      · have hnot : ¬ j < i := not_lt_of_ge hgt.le
        rw [if_neg hji]
        have hw : ∀ a, weight i j a = |ν j a| := by
          intro a
          simp [weight, hnot, hgt]
        simp_rw [hw]
        exact le_max_right _ _
  have hnorm_nonneg (i : ι) : 0 ≤ finiteL1 (μ i) (ν i) := by
    simpa [finiteL1] using
      (Finset.sum_nonneg (fun a _ => abs_nonneg (μ i a - ν i a)))
  have hnormμ_nonneg (i : ι) : 0 ≤ ∑ a, |μ i a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hnormν_nonneg (i : ι) : 0 ≤ ∑ a, |ν i a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hterm_sum (i : ι) :
      (∑ x : ι → α, |term i x|) ≤
        finiteL1 (μ i) (ν i) *
          ∏ j ∈ Finset.univ.erase i,
            max (∑ a, |μ j a|) (∑ a, |ν j a|) := by
    rw [show (∑ x : ι → α, |term i x|) =
        (∑ x : ι → α, ∏ j, weight i j (x j)) by
          apply Fintype.sum_congr
          intro x
          exact hterm_abs i x]
    rw [hfactor]
    let q : ι → ℝ := fun j =>
      if j = i then finiteL1 (μ i) (ν i)
      else max (∑ a, |μ j a|) (∑ a, |ν j a|)
    have hcoord' (j : ι) : (∑ a, weight i j a) ≤ q j := by
      simpa [q] using hcoordinate i j
    have hqnonneg (j : ι) : 0 ≤ q j := by
      by_cases hj : j = i
      · simp [q, hj, hnorm_nonneg]
      · simp [q, hj, hnormμ_nonneg, hnormν_nonneg]
    have hprod : (∏ j, ∑ a, weight i j a) ≤ ∏ j, q j :=
      Finset.prod_le_prod₀
        (fun j _ => Finset.sum_nonneg fun _ _ => by positivity)
        (fun j _ => hcoord' j)
    have hqErase :
        (∏ j ∈ Finset.univ.erase i, q j) =
          ∏ j ∈ Finset.univ.erase i,
            max (∑ a, |μ j a|) (∑ a, |ν j a|) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hne : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [q, hne]
    have hqprod : (∏ j, q j) =
        finiteL1 (μ i) (ν i) *
          ∏ j ∈ Finset.univ.erase i,
            max (∑ a, |μ j a|) (∑ a, |ν j a|) := by
      calc
        _ = q i * ∏ j ∈ Finset.univ.erase i, q j := by
          rw [← Finset.prod_erase_mul (s := Finset.univ) (f := q)
            (a := i) (Finset.mem_univ i)]
          ring
        _ = _ := by simp [q, hqErase]
    exact hprod.trans_eq hqprod
  have hpoint (x : ι → α) :
      |(∏ i, μ i (x i)) - (∏ i, ν i (x i))| ≤ ∑ i, |term i x| := by
    rw [htel x]
    exact Finset.abs_sum_le_sum_abs _ _
  unfold finiteL1
  change (∑ x : ι → α,
      |(∏ i, μ i (x i)) - (∏ i, ν i (x i))|) ≤ _
  calc
    (∑ x : ι → α, |(∏ i, μ i (x i)) - (∏ i, ν i (x i))|) ≤
        ∑ x : ι → α, ∑ i, |term i x| := by
          exact Finset.sum_le_sum fun x _ => hpoint x
    _ = ∑ i, ∑ x : ι → α, |term i x| := by
          change (∑ x ∈ (Finset.univ : Finset (ι → α)),
              ∑ i ∈ (Finset.univ : Finset ι), |term i x|) = _
          rw [Finset.sum_comm]
    _ ≤ ∑ i, (∑ a, |μ i a - ν i a|) *
          ∏ j ∈ Finset.univ.erase i, max (∑ a, |μ j a|) (∑ a, |ν j a|) := by
          apply Finset.sum_le_sum
          intro i hi
          simpa only [finiteL1, tsum_fintype] using hterm_sum i

/-- Worst-case residue error for `k≤K` in the asymptotic part of `lem:sampling`. -/
def harmonicResidueUniformError (X W K : ℕ) : ℝ := harmonicResidueError X W K

/-- Worst-case translation error for `|h|≤H` in the asymptotic part of `lem:sampling`. -/
def harmonicTranslationUniformError (X W H : ℕ) : ℝ :=
  min 2 (2 * (H : ℝ) / ((X : ℝ) * (Real.log X - (W : ℝ) / X)))

/-- Worst-case dilation error for `k≤K` in the asymptotic part of `lem:sampling`. -/
def harmonicDilationUniformError (X W K : ℕ) : ℝ :=
  (2 * Real.log K + (W : ℝ) * K / X * (1 + 1 / X)) /
    (Real.log X - (W : ℝ) / X)

private theorem dominates_rpow_div_tendsto_zero {A S : ℕ → ℝ}
    (hS : ∀ᶠ n in atTop, 1 ≤ S n)
    (hA : OAI.MicrocellScale.Dominates A S) :
    ∀ C : ℝ, 0 < C → Tendsto (fun n => S n ^ C / A n) atTop (𝓝 0) := by
  intro C hC
  have hbig := hA (C + 1) (by linarith)
  have hinv : Tendsto (fun n => (A n / S n ^ (C + 1))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hbig
  apply squeeze_zero' ?_ ?_ hinv
  · filter_upwards [hS, hbig.eventually_gt_atTop 0] with n hn hq
    have hqpos : 0 < A n / S n ^ (C + 1) := hq
    have hSpos : 0 < S n := by linarith
    have hApos : 0 < A n := by
      rcases (div_pos_iff.mp hqpos) with hp | hn
      · exact hp.1
      · have hpow : 0 < S n ^ (C + 1) := Real.rpow_pos_of_pos hSpos _
        linarith [hn.2, hpow]
    exact div_nonneg (Real.rpow_nonneg (by positivity) C) hApos.le
  filter_upwards [hS, hbig.eventually_gt_atTop 0] with n hn hq
  have hSpos : 0 < S n := by linarith
  have hqpos : 0 < A n / S n ^ (C + 1) := hq
  have hApos : 0 < A n := by
    rcases (div_pos_iff.mp hqpos) with hp | hn
    · exact hp.1
    · have hpow : 0 < S n ^ (C + 1) := Real.rpow_pos_of_pos hSpos _
      linarith [hn.2, hpow]
  have heq : S n ^ C / A n =
      (1 / S n) * (A n / S n ^ (C + 1))⁻¹ := by
    rw [Real.rpow_add hSpos C 1, Real.rpow_one]
    field_simp [ne_of_gt hSpos, ne_of_gt hApos]
    <;> ring
  rw [heq]
  calc
    (1 / S n) * (A n / S n ^ (C + 1))⁻¹ ≤
        1 * (A n / S n ^ (C + 1))⁻¹ :=
      mul_le_mul_of_nonneg_right ((div_le_one hSpos).2 hn)
        (inv_nonneg.mpr hqpos.le)
    _ = (A n / S n ^ (C + 1))⁻¹ := by ring

/-- A domination hypothesis kills every fixed power of its scale after division by the
dominating sequence. -/
private theorem dominates_power_quotient_tendsto_zero {A S : ℕ → ℝ}
    (hS : ∀ᶠ n in atTop, 1 ≤ S n)
    (hA : OAI.MicrocellScale.Dominates A S)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n => S n ^ C / A n) atTop (𝓝 0) :=
  dominates_rpow_div_tendsto_zero hS hA C hC

/-- Super-polynomial residue, translation, and dilation conclusions of `lem:sampling`.
The first two use power domination by `X`; dilation uses power domination by `log X`. -/
theorem sampling_asymptotics
    (W K H V X : ℕ → ℕ)
    (hK : ∀ n, 1 ≤ K n) (hH : ∀ n, 1 ≤ H n) (hV : ∀ n, 1 ≤ V n)
    (hW : ∀ n, W n = primorial (n + 1))
    (hX : ∀ᶠ n in atTop, 2 ≤ X n)
    (hden : ∀ᶠ n in atTop, Real.log (X n) > (W n : ℝ) / X n)
    (hDomX : OAI.MicrocellScale.Dominates (fun n => (X n : ℝ))
      (fun n => 2 + W n + K n + H n + V n))
    (hDomLogX : OAI.MicrocellScale.Dominates (fun n => Real.log (X n : ℝ))
      (fun n => 2 + W n + K n + V n)) :
    SuperPolynomialSmall
        (fun n => harmonicResidueUniformError (X n) (W n) (K n)) (fun n => (V n : ℝ)) ∧
    SuperPolynomialSmall
        (fun n => harmonicTranslationUniformError (X n) (W n) (H n)) (fun n => (V n : ℝ)) ∧
    SuperPolynomialSmall
        (fun n => harmonicDilationUniformError (X n) (W n) (K n)) (fun n => (V n : ℝ)) ∧
    (∀ A : ℝ, 0 < A →
      Tendsto (fun n => (V n : ℝ) ^ A *
        (harmonicResidueUniformError (X n) (W n) (K n) +
          harmonicTranslationUniformError (X n) (W n) (H n) +
          harmonicDilationUniformError (X n) (W n) (K n))) atTop (𝓝 0)) := by
  let SX : ℕ → ℝ := fun n => 2 + W n + K n + H n + V n
  let SL : ℕ → ℝ := fun n => 2 + W n + K n + V n
  have hSX : ∀ᶠ n in atTop, 1 ≤ SX n := by
    filter_upwards [] with n
    dsimp [SX]
    nlinarith [Nat.cast_nonneg (α := ℝ) (W n), Nat.cast_nonneg (α := ℝ) (K n),
      Nat.cast_nonneg (α := ℝ) (H n), Nat.cast_nonneg (α := ℝ) (V n)]
  have hSL : ∀ᶠ n in atTop, 1 ≤ SL n := by
    filter_upwards [] with n
    dsimp [SL]
    nlinarith [Nat.cast_nonneg (α := ℝ) (W n), Nat.cast_nonneg (α := ℝ) (K n),
      Nat.cast_nonneg (α := ℝ) (V n)]
  have hXover : Tendsto (fun n => (X n : ℝ) / SX n) atTop atTop := by
    simpa only [SX, Real.rpow_one] using hDomX 1 (by norm_num)
  have hLogover : Tendsto (fun n => Real.log (X n : ℝ) / SL n) atTop atTop := by
    simpa only [SL, Real.rpow_one] using hDomLogX 1 (by norm_num)
  have hden : ∀ᶠ n in atTop,
      1 ≤ Real.log (X n : ℝ) - (W n : ℝ) / X n := by
    filter_upwards [hX, hXover.eventually_ge_atTop 2,
      hLogover.eventually_ge_atTop 2] with n hnX hnXover hnLogover
    have hSXpos : 0 < SX n := by dsimp [SX]; positivity
    have hSLpos : 0 < SL n := by dsimp [SL]; positivity
    have hXpos : 0 < (X n : ℝ) := by exact_mod_cast (show 0 < X n by omega)
    have hWle : (W n : ℝ) ≤ SX n := by
      dsimp [SX]
      nlinarith [Nat.cast_nonneg (α := ℝ) (K n), Nat.cast_nonneg (α := ℝ) (H n),
        Nat.cast_nonneg (α := ℝ) (V n)]
    have hSLge : 1 ≤ SL n := by
      dsimp [SL]
      nlinarith [Nat.cast_nonneg (α := ℝ) (W n), Nat.cast_nonneg (α := ℝ) (K n),
        Nat.cast_nonneg (α := ℝ) (V n)]
    have hlargeX : 2 * SX n ≤ (X n : ℝ) :=
      (le_div_iff₀ hSXpos).mp hnXover
    have hWratio : (W n : ℝ) / X n ≤ 1 / 2 := by
      apply (div_le_iff₀ hXpos).2
      nlinarith
    have hlargeLog : 2 * SL n ≤ Real.log (X n : ℝ) :=
      (le_div_iff₀ hSLpos).mp hnLogover
    have hlogge : 2 ≤ Real.log (X n : ℝ) := by nlinarith
    linarith
  have hres : SuperPolynomialSmall
      (fun n => harmonicResidueUniformError (X n) (W n) (K n))
      (fun n => (V n : ℝ)) := by
    intro C hC
    apply squeeze_zero' ?_ ?_
      (dominates_power_quotient_tendsto_zero hSX hDomX (C + 2) (by linarith))
    · filter_upwards [hden, hX] with n hd hnX
      have hxpos : 0 < (X n : ℝ) := by exact_mod_cast (show 0 < X n by omega)
      have hp : 0 < Real.log (X n : ℝ) - (W n : ℝ) / X n := by linarith
      change 0 ≤ harmonicResidueUniformError (X n) (W n) (K n) * (V n : ℝ) ^ C
      apply mul_nonneg
      · unfold harmonicResidueUniformError harmonicResidueError
        apply div_nonneg
        · positivity
        · exact mul_nonneg hxpos.le hp.le
      · exact Real.rpow_nonneg (by positivity) C
    filter_upwards [hden, hX] with n hd hnX
    have hSXpos : 0 < SX n := by dsimp [SX]; positivity
    have hXpos : 0 < (X n : ℝ) := by exact_mod_cast (show 0 < X n by omega)
    have hWle : (W n : ℝ) ≤ SX n := by
      dsimp [SX]
      nlinarith [Nat.cast_nonneg (α := ℝ) (K n), Nat.cast_nonneg (α := ℝ) (H n),
        Nat.cast_nonneg (α := ℝ) (V n)]
    have hKle : (K n : ℝ) + 1 ≤ SX n := by
      dsimp [SX]
      nlinarith [Nat.cast_nonneg (α := ℝ) (W n), Nat.cast_nonneg (α := ℝ) (H n),
        Nat.cast_nonneg (α := ℝ) (V n)]
    have hVle : (V n : ℝ) ≤ SX n := by
      dsimp [SX]
      nlinarith [Nat.cast_nonneg (α := ℝ) (W n), Nat.cast_nonneg (α := ℝ) (K n),
        Nat.cast_nonneg (α := ℝ) (H n)]
    have hnum : (W n : ℝ) * ((K n : ℝ) + 1) ≤ SX n ^ 2 := by
      calc
        _ ≤ SX n * SX n := mul_le_mul hWle hKle (by positivity) (by positivity)
        _ = SX n ^ 2 := by ring
    have hpow : (V n : ℝ) ^ C ≤ SX n ^ C :=
      Real.rpow_le_rpow (by positivity) hVle hC.le
    have herror : harmonicResidueUniformError (X n) (W n) (K n) ≤
        (SX n ^ 2) / X n := by
      unfold harmonicResidueUniformError harmonicResidueError
      rw [Nat.cast_add, Nat.cast_one]
      have hdenpos : 0 < Real.log (X n : ℝ) - (W n : ℝ) / X n := by linarith
      have hxne : (X n : ℝ) ≠ 0 := ne_of_gt hXpos
      have hdenne : Real.log (X n : ℝ) - (W n : ℝ) / X n ≠ 0 := ne_of_gt hdenpos
      have hle : (W n : ℝ) * ((K n : ℝ) + 1) / (X n *
          (Real.log (X n : ℝ) - (W n : ℝ) / X n)) ≤
          ((W n : ℝ) * ((K n : ℝ) + 1) / X n) := by
        rw [show (W n : ℝ) * ((K n : ℝ) + 1) /
            (X n * (Real.log (X n : ℝ) - (W n : ℝ) / X n)) =
            ((W n : ℝ) * ((K n : ℝ) + 1) / X n) /
              (Real.log (X n : ℝ) - (W n : ℝ) / X n) by
                field_simp [hxne, hdenne]
                <;> ring]
        simpa only [div_one] using
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hd
      exact hle.trans (div_le_div_of_nonneg_right hnum (by positivity))
    have herror_nonneg : 0 ≤ harmonicResidueUniformError (X n) (W n) (K n) := by
      unfold harmonicResidueUniformError harmonicResidueError
      apply div_nonneg
      · positivity
      · exact mul_nonneg (by positivity) (by linarith)
    calc
      harmonicResidueUniformError (X n) (W n) (K n) * (V n : ℝ) ^ C
          = (V n : ℝ) ^ C * harmonicResidueUniformError (X n) (W n) (K n) := by ring
      _ ≤ SX n ^ C * (SX n ^ 2 / X n) := by
            calc
              _ ≤ SX n ^ C * harmonicResidueUniformError (X n) (W n) (K n) :=
                mul_le_mul_of_nonneg_right hpow herror_nonneg
              _ ≤ _ := mul_le_mul_of_nonneg_left herror
                (Real.rpow_nonneg (by positivity) C)
      _ = SX n ^ (C + 2) / X n := by
        rw [Real.rpow_add hSXpos]
        simp only [Real.rpow_two]
        ring
  have htrans : SuperPolynomialSmall
      (fun n => harmonicTranslationUniformError (X n) (W n) (H n))
      (fun n => (V n : ℝ)) := by
    intro C hC
    apply squeeze_zero' ?_ ?_
      (by simpa only [mul_zero] using
        (dominates_power_quotient_tendsto_zero hSX hDomX (C + 2) (by linarith)).const_mul 2)
    · filter_upwards [hden, hX] with n hd hnX
      have hxpos : 0 < (X n : ℝ) := by exact_mod_cast (show 0 < X n by omega)
      have hp : 0 < Real.log (X n : ℝ) - (W n : ℝ) / X n := by linarith
      change 0 ≤ harmonicTranslationUniformError (X n) (W n) (H n) * (V n : ℝ) ^ C
      apply mul_nonneg
      · unfold harmonicTranslationUniformError
        apply le_min
        · norm_num
        apply div_nonneg
        · positivity
        · exact mul_nonneg hxpos.le hp.le
      · exact Real.rpow_nonneg (by positivity) C
    filter_upwards [hden, hX, hXover.eventually_ge_atTop 2] with n hd hnX hXoverN
    have hXpos : 0 < (X n : ℝ) := by exact_mod_cast (show 0 < X n by omega)
    have hHle : (H n : ℝ) ≤ SX n := by
      dsimp [SX]
      nlinarith [Nat.cast_nonneg (α := ℝ) (W n), Nat.cast_nonneg (α := ℝ) (K n),
        Nat.cast_nonneg (α := ℝ) (V n)]
    have hVle : (V n : ℝ) ≤ SX n := by
      dsimp [SX]
      nlinarith [Nat.cast_nonneg (α := ℝ) (W n), Nat.cast_nonneg (α := ℝ) (K n),
        Nat.cast_nonneg (α := ℝ) (H n)]
    have hSXge : 1 ≤ SX n := by
      dsimp [SX]
      nlinarith [Nat.cast_nonneg (α := ℝ) (W n), Nat.cast_nonneg (α := ℝ) (K n),
        Nat.cast_nonneg (α := ℝ) (H n), Nat.cast_nonneg (α := ℝ) (V n)]
    have hSXsq : SX n ≤ SX n ^ 2 := by
      calc
        SX n = SX n * 1 := by ring
        _ ≤ SX n * SX n :=
          mul_le_mul_of_nonneg_left hSXge (show 0 ≤ SX n by positivity)
        _ = SX n ^ 2 := by ring
    have hHlesq : (H n : ℝ) ≤ SX n ^ 2 := hHle.trans hSXsq
    have hpow : (V n : ℝ) ^ C ≤ SX n ^ C :=
      Real.rpow_le_rpow (by positivity) hVle hC.le
    have herror : harmonicTranslationUniformError (X n) (W n) (H n) ≤
        2 * SX n ^ 2 / X n := by
      unfold harmonicTranslationUniformError
      apply (min_le_right _ _).trans
      have hdenpos : 0 < Real.log (X n : ℝ) - (W n : ℝ) / X n := by linarith
      have hxne : (X n : ℝ) ≠ 0 := ne_of_gt hXpos
      have hdenne : Real.log (X n : ℝ) - (W n : ℝ) / X n ≠ 0 := ne_of_gt hdenpos
      have hratio : 2 * (H n : ℝ) / ((X n : ℝ) *
          (Real.log (X n : ℝ) - (W n : ℝ) / X n)) ≤
          2 * (H n : ℝ) / X n := by
        rw [show 2 * (H n : ℝ) / ((X n : ℝ) *
            (Real.log (X n : ℝ) - (W n : ℝ) / X n)) =
            (2 * (H n : ℝ) / X n) /
              (Real.log (X n : ℝ) - (W n : ℝ) / X n) by
                field_simp [hxne, hdenne]
                <;> ring]
        simpa only [div_one] using
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hd
      exact hratio.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hHlesq (by norm_num)) (by positivity))
    have herror_nonneg :
        0 ≤ harmonicTranslationUniformError (X n) (W n) (H n) := by
      unfold harmonicTranslationUniformError
      apply le_min
      · norm_num
      · apply div_nonneg
        · positivity
        · exact mul_nonneg (by positivity) (by linarith)
    calc
      harmonicTranslationUniformError (X n) (W n) (H n) * (V n : ℝ) ^ C
          = (V n : ℝ) ^ C * harmonicTranslationUniformError (X n) (W n) (H n) := by ring
      _ ≤ SX n ^ C * (2 * SX n ^ 2 / X n) :=
            calc
              _ ≤ SX n ^ C * harmonicTranslationUniformError (X n) (W n) (H n) :=
                mul_le_mul_of_nonneg_right hpow herror_nonneg
              _ ≤ _ := mul_le_mul_of_nonneg_left herror
                (Real.rpow_nonneg (by positivity) C)
      _ = 2 * (SX n ^ (C + 2) / X n) := by
            rw [Real.rpow_add (by dsimp [SX]; positivity) C 2]
            simp only [Real.rpow_two]
            ring
  have hdil : SuperPolynomialSmall
      (fun n => harmonicDilationUniformError (X n) (W n) (K n))
      (fun n => (V n : ℝ)) := by
    intro C hC
    apply squeeze_zero' ?_ ?_
      (by simpa only [mul_zero] using
        (dominates_power_quotient_tendsto_zero hSL hDomLogX (C + 2) (by linarith)).const_mul 8)
    · filter_upwards [hden, hX] with n hd hnX
      have hp : 0 < Real.log (X n : ℝ) - (W n : ℝ) / X n := by linarith
      have hklog : 0 ≤ Real.log (K n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (hK n))
      change 0 ≤ harmonicDilationUniformError (X n) (W n) (K n) * (V n : ℝ) ^ C
      apply mul_nonneg
      · unfold harmonicDilationUniformError
        apply div_nonneg
        · positivity
        · exact hp.le
      · exact Real.rpow_nonneg (by positivity) C
    filter_upwards [hden, hX, hLogover.eventually_ge_atTop 2,
      hXover.eventually_ge_atTop 2] with n hd hnX hLogoverN hXoverN
    have hXpos : 0 < (X n : ℝ) := by exact_mod_cast (show 0 < X n by omega)
    have hSLpos : 0 < SL n := by dsimp [SL]; positivity
    have hWle : (W n : ℝ) ≤ SL n := by
      dsimp [SL]
      nlinarith [Nat.cast_nonneg (α := ℝ) (K n), Nat.cast_nonneg (α := ℝ) (V n)]
    have hKle : (K n : ℝ) ≤ SL n := by
      dsimp [SL]
      nlinarith [Nat.cast_nonneg (α := ℝ) (W n), Nat.cast_nonneg (α := ℝ) (V n)]
    have hVle : (V n : ℝ) ≤ SL n := by
      dsimp [SL]
      nlinarith [Nat.cast_nonneg (α := ℝ) (W n), Nat.cast_nonneg (α := ℝ) (K n)]
    have hlogge : 2 ≤ Real.log (X n : ℝ) := by
      have hlarge : 2 * SL n ≤ Real.log (X n : ℝ) :=
        (le_div_iff₀ hSLpos).mp hLogoverN
      nlinarith [Nat.cast_nonneg (α := ℝ) (W n), Nat.cast_nonneg (α := ℝ) (K n),
        Nat.cast_nonneg (α := ℝ) (V n)]
    have hWratio : (W n : ℝ) / X n ≤ 1 / 2 := by
      have hSXpos : 0 < SX n := by dsimp [SX]; positivity
      have hbig : 2 * SX n ≤ (X n : ℝ) := (le_div_iff₀ hSXpos).mp hXoverN
      have hWsmall : (W n : ℝ) ≤ SX n := by
        dsimp [SX]
        nlinarith [Nat.cast_nonneg (α := ℝ) (K n), Nat.cast_nonneg (α := ℝ) (H n),
          Nat.cast_nonneg (α := ℝ) (V n)]
      apply (div_le_iff₀ hXpos).2
      nlinarith
    have hdenhalf : Real.log (X n : ℝ) / 2 ≤
        Real.log (X n : ℝ) - (W n : ℝ) / X n := by
      nlinarith
    have hlogK : Real.log (K n : ℝ) ≤ (K n : ℝ) := by
      have hkposNat : 0 < K n := by
        have hk1 : (1 : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hK n
        exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hk1)
      have hkpos : 0 < (K n : ℝ) := by exact_mod_cast hkposNat
      have hh := Real.log_le_sub_one_of_pos hkpos
      linarith
    have hprod : (W n : ℝ) * (K n : ℝ) ≤ SL n ^ 2 := by
      calc
        _ ≤ SL n * SL n := mul_le_mul hWle hKle (by positivity) (by positivity)
        _ = SL n ^ 2 := by ring
    have hnum : 2 * Real.log (K n : ℝ) + (W n : ℝ) * K n / X n *
        (1 + 1 / X n) ≤ 4 * SL n ^ 2 := by
      have hfactor : (1 : ℝ) + 1 / (X n : ℝ) ≤ 2 := by
        have : 0 ≤ (1 : ℝ) / (X n : ℝ) := by positivity
        have hInv : (1 : ℝ) / (X n : ℝ) ≤ 1 :=
          (div_le_one hXpos).2 (by exact_mod_cast (show 1 ≤ X n by omega))
        linarith
      have hXge : 1 ≤ (X n : ℝ) := by
        exact_mod_cast (show 1 ≤ X n by omega)
      have hWKnonneg : 0 ≤ (W n : ℝ) * K n :=
        mul_nonneg (Nat.cast_nonneg (α := ℝ) (W n))
          (Nat.cast_nonneg (α := ℝ) (K n))
      have hquot : (W n : ℝ) * K n / X n ≤ (W n : ℝ) * K n :=
        div_le_self hWKnonneg hXge
      have hsecond : (W n : ℝ) * K n / X n * (1 + 1 / X n) ≤
          2 * SL n ^ 2 := by
        calc
          _ ≤ ((W n : ℝ) * K n) * (1 + 1 / X n) :=
            mul_le_mul_of_nonneg_right hquot (by positivity)
          _ ≤ ((W n : ℝ) * K n) * 2 :=
            mul_le_mul_of_nonneg_left hfactor hWKnonneg
          _ ≤ 2 * SL n ^ 2 := by nlinarith [hprod]
      have hfirst : 2 * Real.log (K n : ℝ) ≤ 2 * SL n := by
        exact mul_le_mul_of_nonneg_left (hlogK.trans hKle) (by norm_num)
      have hSLsq : SL n ≤ SL n ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) (W n), Nat.cast_nonneg (α := ℝ) (K n),
          Nat.cast_nonneg (α := ℝ) (V n)]
      nlinarith
    have hpow : (V n : ℝ) ^ C ≤ SL n ^ C :=
      Real.rpow_le_rpow (by positivity) hVle hC.le
    have herror : harmonicDilationUniformError (X n) (W n) (K n) ≤
        8 * SL n ^ 2 / Real.log (X n : ℝ) := by
      unfold harmonicDilationUniformError
      have hdenpos : 0 < Real.log (X n : ℝ) - (W n : ℝ) / X n := by linarith
      have hklog : 0 ≤ Real.log (K n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (hK n))
      have hlogpos : 0 < Real.log (X n : ℝ) := by linarith
      have hnumpos : 0 ≤ 2 * Real.log (K n : ℝ) +
          (W n : ℝ) * K n / X n * (1 + 1 / X n) := by positivity
      calc
        _ ≤ (4 * SL n ^ 2) / (Real.log (X n : ℝ) / 2) := by
          exact (div_le_div_of_nonneg_left hnumpos (by positivity) hdenhalf).trans
            (div_le_div_of_nonneg_right hnum (by positivity))
        _ = 8 * SL n ^ 2 / Real.log (X n : ℝ) := by field_simp <;> norm_num
    have hlogpos : 0 < Real.log (X n : ℝ) := by linarith
    have huppernonneg : 0 ≤ 8 * SL n ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have herror_nonneg : 0 ≤ harmonicDilationUniformError (X n) (W n) (K n) := by
      unfold harmonicDilationUniformError
      apply div_nonneg
      · have hklog : 0 ≤ Real.log (K n : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (hK n))
        positivity
      · linarith
    calc
      harmonicDilationUniformError (X n) (W n) (K n) * (V n : ℝ) ^ C
          = (V n : ℝ) ^ C * harmonicDilationUniformError (X n) (W n) (K n) := by ring
      _ ≤ SL n ^ C * (8 * SL n ^ 2 / Real.log (X n : ℝ)) :=
            calc
              _ ≤ SL n ^ C * harmonicDilationUniformError (X n) (W n) (K n) :=
                mul_le_mul_of_nonneg_right hpow herror_nonneg
              _ ≤ _ :=
                mul_le_mul_of_nonneg_left herror (Real.rpow_nonneg (by positivity) C)
      _ = 8 * (SL n ^ (C + 2) / Real.log (X n : ℝ)) := by
            rw [Real.rpow_add hSLpos]
            simp only [Real.rpow_two]
            ring
  refine ⟨hres, htrans, hdil, ?_⟩
  intro A hA
  have h1 := hres A hA
  have h2 := htrans A hA
  have h3 := hdil A hA
  convert h1.add (h2.add h3) using 1 <;> ext n <;> ring_nf

/-- Lemma `lem:sampling`: exact periodic harmonic, residue, translation, and dilation
bounds together with the super-polynomial asymptotic conclusions and their stated growth
conditions (§3 lines 34–129). -/
theorem lem_sampling (X W : ℕ) (hW : 0 < W) (hX : 2 ≤ X)
    (hlog : Real.log X > (W : ℝ) / X) :
    SamplingPointwiseBounds X W ∧
    (∀ (Wseq K H V Xseq : ℕ → ℕ),
      (∀ n, 1 ≤ K n) → (∀ n, 1 ≤ H n) → (∀ n, 1 ≤ V n) →
      (∀ n, Wseq n = primorial (n + 1)) →
      (∀ᶠ n in atTop, 2 ≤ Xseq n) →
      (∀ᶠ n in atTop, Real.log (Xseq n) > (Wseq n : ℝ) / Xseq n) →
      OAI.MicrocellScale.Dominates (fun n => (Xseq n : ℝ))
        (fun n => 2 + Wseq n + K n + H n + V n) →
      OAI.MicrocellScale.Dominates (fun n => Real.log (Xseq n : ℝ))
        (fun n => 2 + Wseq n + K n + V n) →
      SuperPolynomialSmall
        (fun n => harmonicResidueUniformError (Xseq n) (Wseq n) (K n))
        (fun n => (V n : ℝ)) ∧
      SuperPolynomialSmall
        (fun n => harmonicTranslationUniformError (Xseq n) (Wseq n) (H n))
        (fun n => (V n : ℝ)) ∧
      SuperPolynomialSmall
        (fun n => harmonicDilationUniformError (Xseq n) (Wseq n) (K n))
        (fun n => (V n : ℝ)) ∧
      (∀ A : ℝ, 0 < A →
        Tendsto (fun n => (V n : ℝ) ^ A *
          (harmonicResidueUniformError (Xseq n) (Wseq n) (K n) +
            harmonicTranslationUniformError (Xseq n) (Wseq n) (H n) +
            harmonicDilationUniformError (Xseq n) (Wseq n) (K n))) atTop (𝓝 0))) := by
  refine ⟨sampling_pointwise_claim X W hW hX hlog, ?_⟩
  intro Wseq K H V Xseq hK hH hV hW hXseq hden hDomX hDomLogX
  exact sampling_asymptotics Wseq K H V Xseq hK hH hV hW hXseq hden hDomX hDomLogX

end
end HindmanSumsProducts

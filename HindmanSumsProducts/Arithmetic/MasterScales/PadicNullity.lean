import HindmanSumsProducts.Arithmetic.Defs
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Algebra.MvPolynomial

open MeasureTheory
open Filter
open scoped Topology ENNReal

noncomputable section

namespace HindmanSumsProducts
attribute [local instance] Classical.propDecidable

instance masterPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℤ_[p] := borel ℤ_[p]

instance masterPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℤ_[p] := ⟨rfl⟩

def masterPadicCompact (p : ℕ) [Fact p.Prime] : TopologicalSpace.PositiveCompacts ℤ_[p] :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

def masterPadicHaar (p : ℕ) [Fact p.Prime] : Measure ℤ_[p] :=
  Measure.addHaarMeasure (masterPadicCompact p)

lemma masterPadicHaar_univ (p : ℕ) [Fact p.Prime] : masterPadicHaar p Set.univ = 1 := by
  change Measure.addHaarMeasure (masterPadicCompact p) (masterPadicCompact p : Set ℤ_[p]) = 1
  exact Measure.addHaarMeasure_self


instance masterPadicHaarInvariant (p : ℕ) [Fact p.Prime] : (masterPadicHaar p).IsAddLeftInvariant := by
  change (Measure.addHaarMeasure (masterPadicCompact p)).IsAddLeftInvariant
  exact Measure.isAddLeftInvariant_addHaarMeasure _

instance masterPadicHaarProbability (p : ℕ) [Fact p.Prime] : IsProbabilityMeasure (masterPadicHaar p) :=
  ⟨masterPadicHaar_univ p⟩

lemma masterPadicHaar_singleton (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) :
    masterPadicHaar p {x} = 0 := by
  let μ := masterPadicHaar p
  by_contra hzero
  have hpos : 0 < μ {x} := pos_iff_ne_zero.mpr hzero
  have hbound (k : ℕ) : (k : ℝ≥0∞) * μ {x} ≤ 1 := by
    let s : Finset (Fin k) := Finset.univ
    let f : Fin k → Set ℤ_[p] := fun i => {x + (i.val : ℤ_[p])}
    have hd : (s : Set (Fin k)).PairwiseDisjoint f := by
      intro i hi j hj hij
      apply Set.disjoint_singleton.mpr
      intro heq
      have hcast : (i.val : ℤ_[p]) = (j.val : ℤ_[p]) := add_left_cancel heq
      have hval : i.val = j.val := by exact_mod_cast hcast
      exact hij (Fin.ext hval)
    have hm : ∀ i ∈ s, MeasurableSet (f i) := by
      intro i hi
      exact measurableSet_singleton _
    have hu := MeasureTheory.measure_biUnion_finset (μ := μ) hd hm
    have htranslate (i : Fin k) : μ (f i) = μ {x} := by
      change μ {x + (i.val : ℤ_[p])} = μ {x}
      have heq : (fun z : ℤ_[p] => -(i.val : ℤ_[p]) + z) ⁻¹' ({x} : Set ℤ_[p]) =
          {x + (i.val : ℤ_[p])} := by
        ext z
        simp [eq_comm, add_comm, add_left_comm, add_assoc]
      rw [← heq]
      exact MeasureTheory.measure_preimage_add μ (-(i.val : ℤ_[p])) {x}
    have hsum : ∑ i ∈ s, μ (f i) = (k : ℝ≥0∞) * μ {x} := by
      simp [s, htranslate]
    calc
      (k : ℝ≥0∞) * μ {x} = ∑ i ∈ s, μ (f i) := hsum.symm
      _ = μ (⋃ i ∈ s, f i) := hu.symm
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := by simp [μ]
  have htop : μ {x} ≠ ∞ := measure_ne_top _ _
  have hreal : 0 < (μ {x}).toReal := ENNReal.toReal_pos hzero htop
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (μ {x}).toReal)
  have hkbound := hbound k
  have hrealbound : (k : ℝ) * (μ {x}).toReal ≤ 1 := by
    have hmono := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hkbound
    simpa [ENNReal.toReal_mul] using hmono
  have hmul := mul_lt_mul_of_pos_right hk hreal
  have hone : (1 / (μ {x}).toReal) * (μ {x}).toReal = 1 := by
    field_simp [ne_of_gt hreal]
  rw [hone] at hmul
  linarith


instance masterPadicHaarNoAtoms (p : ℕ) [Fact p.Prime] : NullSingletonClass (masterPadicHaar p) where
  measure_singleton := masterPadicHaar_singleton p

def masterPadicResidueCell (p e : ℕ) [Fact p.Prime] (r : ZMod (p ^ e)) : Set ℤ_[p] :=
  {x | PadicInt.toZModPow e x = r}

theorem masterPadicHaarResidueCell_measurable (p e : ℕ) [Fact p.Prime]
    (r : ZMod (p ^ e)) : MeasurableSet (masterPadicResidueCell p e r) := by
  let b : ℤ_[p] := (r.val : ℤ_[p])
  have hb : PadicInt.toZModPow e b = r := by simp [b, PadicInt.toZModPow]
  have hball : masterPadicResidueCell p e r =
      Metric.closedBall b ((p : ℝ) ^ (-(e : ℤ))) := by
    ext x
    change PadicInt.toZModPow e x = r ↔ dist x b ≤ (p : ℝ) ^ (-(e : ℤ))
    rw [← hb]
    constructor
    · intro h
      have hker : x - b ∈ RingHom.ker (PadicInt.toZModPow e) := by
        rw [RingHom.mem_ker, map_sub, h, hb, sub_self]
      rw [PadicInt.ker_toZModPow] at hker
      have hn := (PadicInt.norm_le_pow_iff_mem_span_pow (x - b) e).2 hker
      simpa [dist_eq_norm_sub] using hn
    · intro h
      have hn : ‖x - b‖ ≤ (p : ℝ) ^ (-(e : ℤ)) := by
        simpa [dist_eq_norm_sub] using h
      have hideal := (PadicInt.norm_le_pow_iff_mem_span_pow (x - b) e).1 hn
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker] at hideal
      have hsub : PadicInt.toZModPow e x - PadicInt.toZModPow e b = 0 := by
        simpa only [map_sub] using hideal
      exact sub_eq_zero.mp hsub
  rw [hball]
  exact Metric.isClosed_closedBall.measurableSet

theorem masterPadicHaarResidueCell_ennreal (p e : ℕ) [Fact p.Prime]
    (r : ZMod (p ^ e)) :
    masterPadicHaar p (masterPadicResidueCell p e r) = 1 / (p ^ e : ℝ≥0∞) := by
  classical
  let Q := p ^ e
  let μ := masterPadicHaar p
  let C : ZMod Q → Set ℤ_[p] := fun a => masterPadicResidueCell p e a
  have hQ : 0 < Q := by dsimp [Q]; exact pow_pos (Fact.out : p.Prime).pos e
  have hrepr (a : ZMod Q) : PadicInt.toZModPow e (a.val : ℤ_[p]) = a := by
    simp [PadicInt.toZModPow]
  have hmeas (a : ZMod Q) : MeasurableSet (C a) := by
    let b : ℤ_[p] := (a.val : ℤ_[p])
    have hb : PadicInt.toZModPow e b = a := hrepr a
    have hball : C a = Metric.closedBall b ((p : ℝ) ^ (-(e : ℤ))) := by
      ext x
      change PadicInt.toZModPow e x = a ↔ dist x b ≤ (p : ℝ) ^ (-(e : ℤ))
      rw [← hb]
      constructor
      · intro h
        have hker : x - b ∈ RingHom.ker (PadicInt.toZModPow e) := by
          rw [RingHom.mem_ker, map_sub, h, hb, sub_self]
        rw [PadicInt.ker_toZModPow] at hker
        have hn := (PadicInt.norm_le_pow_iff_mem_span_pow (x - b) e).2 hker
        simpa [dist_eq_norm_sub] using hn
      · intro h
        have hn : ‖x - b‖ ≤ (p : ℝ) ^ (-(e : ℤ)) := by
          simpa [dist_eq_norm_sub] using h
        have hideal := (PadicInt.norm_le_pow_iff_mem_span_pow (x - b) e).1 hn
        rw [← PadicInt.ker_toZModPow, RingHom.mem_ker] at hideal
        have hsub : PadicInt.toZModPow e x - PadicInt.toZModPow e b = 0 := by
          simpa only [map_sub] using hideal
        exact sub_eq_zero.mp hsub
    rw [hball]
    exact Metric.isClosed_closedBall.measurableSet
  have hsame (a b : ZMod Q) : μ (C a) = μ (C b) := by
    let d : ℤ_[p] := (((b - a).val : ℕ) : ℤ_[p])
    have hd : PadicInt.toZModPow e d = b - a := hrepr (b - a)
    have hpre : (fun x : ℤ_[p] => d + x) ⁻¹' C b = C a := by
      ext x
      change PadicInt.toZModPow e (d + x) = b ↔ PadicInt.toZModPow e x = a
      rw [map_add, hd]
      constructor
      · intro h
        calc
          PadicInt.toZModPow e x = (b - a) + PadicInt.toZModPow e x - (b - a) := by abel
          _ = b - (b - a) := by rw [h]
          _ = a := by abel
      · intro h
        rw [h]
        abel
    rw [← hpre]
    exact MeasureTheory.measure_preimage_add μ d (C b)
  let c : ℝ := (μ (C r)).toReal
  have hsum : ∑ a : ZMod Q, μ (C a) = 1 := by
    have hd : ((Finset.univ : Finset (ZMod Q)) : Set (ZMod Q)).PairwiseDisjoint C := by
      intro a ha b hb hab
      apply Set.disjoint_left.mpr
      intro x hxa hxb
      exact hab (by simpa [C, masterPadicResidueCell] using hxa.symm.trans hxb)
    have hu := MeasureTheory.measure_biUnion_finset (μ := μ) hd (fun a ha => hmeas a)
    have hset : (⋃ a : ZMod Q, C a) = Set.univ := by
      ext x
      simp [C, masterPadicResidueCell]
    calc
      _ = μ (⋃ a ∈ (Finset.univ : Finset (ZMod Q)), C a) := hu.symm
      _ = μ Set.univ := by congr 1; ext x; simp [hset]
      _ = 1 := by simp [μ]
  have hsumReal : ∑ a : ZMod Q, (μ (C a)).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a ha => measure_ne_top _ _), hsum]
    simp
  have hcard : Fintype.card (ZMod Q) = Q := by
    simpa using Fintype.card_congr (ZMod.finEquiv Q)
  have hc : c = 1 / (Q : ℝ) := by
    have hsumc : (Fintype.card (ZMod Q) : ℝ) * c = 1 := by
      calc
        (Fintype.card (ZMod Q) : ℝ) * c = ∑ a : ZMod Q, c := by simp [Finset.sum_const]
        _ = ∑ a : ZMod Q, (μ (C a)).toReal := by
          apply Finset.sum_congr rfl
          intro a ha
          dsimp [c]
          rw [hsame a r]
        _ = 1 := hsumReal
    rw [hcard] at hsumc
    have hpcast : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
    field_simp [hpcast] at hsumc ⊢
    nlinarith
  have htop : μ (C r) ≠ ∞ := measure_ne_top _ _
  have hcell : μ (C r) = (1 / (Q : ℝ≥0∞)) := by
    have hQENN : (Q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hQ.ne'
    have hRtop : (1 : ℝ≥0∞) / (Q : ℝ≥0∞) ≠ ∞ :=
      ENNReal.div_ne_top (by norm_num) hQENN
    apply (ENNReal.toReal_eq_toReal_iff' htop hRtop).mp
    simpa [c, ENNReal.toReal_div, hQ.ne'] using hc
  simpa [Q] using hcell

theorem masterPadicHaarResidueCell_real (p e : ℕ) [Fact p.Prime]
    (r : ZMod (p ^ e)) :
    (masterPadicHaar p).real (masterPadicResidueCell p e r) = 1 / (p ^ e : ℝ) := by
  rw [Measure.real, masterPadicHaarResidueCell_ennreal]
  simp

def masterPadicProductMeasure (p m : ℕ) [Fact p.Prime] :
    Measure (Fin m → ℤ_[p]) := Measure.pi (fun _ : Fin m => masterPadicHaar p)

instance masterPadicProductProbability (p m : ℕ) [Fact p.Prime] :
    IsProbabilityMeasure (masterPadicProductMeasure p m) := by
  constructor
  simp [masterPadicProductMeasure]

def masterPadicResidueFin (p e : ℕ) [Fact p.Prime] (x : ℤ_[p]) : Fin (p ^ e) :=
  ⟨(PadicInt.toZModPow e x).val, ZMod.val_lt _⟩

def masterPadicProductResidueCell (p e m : ℕ) [Fact p.Prime]
    (a : Fin m → Fin (p ^ e)) : Set (Fin m → ℤ_[p]) :=
  Set.pi Set.univ (fun i => masterPadicResidueCell p e ((a i).val : ZMod (p ^ e)))

theorem masterPadicResidueFin_zmod (p e : ℕ) [Fact p.Prime] (x : ℤ_[p]) :
    ((masterPadicResidueFin p e x).val : ZMod (p ^ e)) = PadicInt.toZModPow e x := by
  simp [masterPadicResidueFin, ZMod.natCast_zmod_val]

theorem masterPadicProductResidueCell_measure (p e m : ℕ) [Fact p.Prime]
    (a : Fin m → Fin (p ^ e)) :
    masterPadicProductMeasure p m (masterPadicProductResidueCell p e m a) =
      (1 / (p ^ e : ℝ≥0∞)) ^ m := by
  simp [masterPadicProductMeasure, masterPadicProductResidueCell, Measure.pi_pi,
    masterPadicHaarResidueCell_ennreal]

theorem masterPadicEvalResidue (p e m : ℕ) [Fact p.Prime]
    (P : IntegerPolynomial m) (x : Fin m → ℤ_[p]) (a : Fin m → Fin (p ^ e))
    (ha : ∀ i, PadicInt.toZModPow e (x i) = ((a i).val : ZMod (p ^ e))) :
    PadicInt.toZModPow e (MvPolynomial.eval x (P.map (Int.castRingHom ℤ_[p]))) =
      ((evalIntegerPolynomial P (fun i => ((a i).val : ℤ)) : ℤ) : ZMod (p ^ e)) := by
  let q : ℤ_[p] →+* ZMod (p ^ e) := PadicInt.toZModPow e
  have hcomp : q.comp (Int.castRingHom ℤ_[p]) = Int.castRingHom (ZMod (p ^ e)) := by
    ext z
    simp [q]
  calc
    q (MvPolynomial.eval x (P.map (Int.castRingHom ℤ_[p]))) =
        MvPolynomial.eval₂ q (q ∘ x) (P.map (Int.castRingHom ℤ_[p])) := by
          exact MvPolynomial.eval₂_comp q x (P.map (Int.castRingHom ℤ_[p]))
    _ = MvPolynomial.eval₂ (Int.castRingHom (ZMod (p ^ e)))
          (fun i => ((a i).val : ZMod (p ^ e))) P := by
          rw [MvPolynomial.eval₂_map, hcomp]
          rw [show (q ∘ x) = (fun i => ((a i).val : ZMod (p ^ e))) by
            funext i
            exact ha i]
    _ = ((evalIntegerPolynomial P (fun i => ((a i).val : ℤ)) : ℤ) : ZMod (p ^ e)) := by
          symm
          simpa [evalIntegerPolynomial, Function.comp_def] using
            (MvPolynomial.eval₂_comp (Int.castRingHom (ZMod (p ^ e)))
              (fun i => ((a i).val : ℤ)) P)

def masterPadicDivisibilityEvent {m : ℕ} (p e : ℕ)
    (P : IntegerPolynomial m) (a : Fin m → Fin (p ^ e)) : Prop :=
  ((p ^ e : ℕ) : ℤ) ∣ evalIntegerPolynomial P (fun i => (a i).val)

def masterPadicDivisibilitySet {m : ℕ} (p e : ℕ) [Fact p.Prime]
    (P : IntegerPolynomial m) : Set (Fin m → ℤ_[p]) :=
  {x | PadicInt.toZModPow e
      (MvPolynomial.eval x (P.map (Int.castRingHom ℤ_[p]))) = 0}

theorem masterPadicDivisibilityEvent_cell {m : ℕ} (p e : ℕ) [Fact p.Prime]
    (P : IntegerPolynomial m) (a : Fin m → Fin (p ^ e))
    (x : Fin m → ℤ_[p])
    (hx : x ∈ masterPadicProductResidueCell p e m a) :
    masterPadicDivisibilityEvent p e P a ↔ x ∈ masterPadicDivisibilitySet p e P := by
  have hcoord : ∀ i, PadicInt.toZModPow e (x i) = ((a i).val : ZMod (p ^ e)) := by
    intro i
    have hi := (Set.mem_pi.mp hx) i (Set.mem_univ i)
    exact hi
  rw [masterPadicDivisibilitySet, Set.mem_setOf_eq]
  rw [masterPadicEvalResidue p e m P x a hcoord]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd
    (evalIntegerPolynomial P (fun i => (a i).val)) (p ^ e)).symm

theorem masterPadicDivisibilitySet_iUnion {m : ℕ} (p e : ℕ) [Fact p.Prime]
    (P : IntegerPolynomial m) :
    (⋃ a ∈ (Finset.univ.filter (masterPadicDivisibilityEvent p e P)),
      masterPadicProductResidueCell p e m a) = masterPadicDivisibilitySet p e P := by
  classical
  ext x
  simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
    true_and, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, hx⟩
    exact (masterPadicDivisibilityEvent_cell p e P a x hx).mp ha
  · intro hx
    let a : Fin m → Fin (p ^ e) := fun i => masterPadicResidueFin p e (x i)
    have haCell : x ∈ masterPadicProductResidueCell p e m a := by
      change x ∈ Set.pi Set.univ
        (fun i => masterPadicResidueCell p e ((a i).val : ZMod (p ^ e)))
      apply Set.mem_pi.mpr
      intro i hi
      change PadicInt.toZModPow e (x i) = ((a i).val : ZMod (p ^ e))
      exact (masterPadicResidueFin_zmod p e (x i)).symm
    refine ⟨a, (masterPadicDivisibilityEvent_cell p e P a x haCell).mpr hx, haCell⟩

theorem masterPadicDivisibilitySet_real {m : ℕ} (p e : ℕ) [Fact p.Prime]
    (P : IntegerPolynomial m) :
    (masterPadicProductMeasure p m).real (masterPadicDivisibilitySet p e P) =
      (∑ a : Fin m → Fin (p ^ e),
        if masterPadicDivisibilityEvent p e P a then (1 : ℝ) else 0) /
        ((p ^ e : ℕ) : ℝ) ^ m := by
  classical
  let Q := p ^ e
  let μ := masterPadicProductMeasure p m
  let F := Finset.univ.filter (masterPadicDivisibilityEvent p e P)
  have hUnion : (⋃ a ∈ F, masterPadicProductResidueCell p e m a) =
      masterPadicDivisibilitySet p e P := by
    simpa [F] using masterPadicDivisibilitySet_iUnion p e P
  have hcellMeas (a : Fin m → Fin Q) :
      MeasurableSet (masterPadicProductResidueCell p e m a) := by
    apply MeasurableSet.pi Set.countable_univ
    intro i hi
    exact masterPadicHaarResidueCell_measurable p e ((a i).val : ZMod Q)
  have hdisj : (F : Set (Fin m → Fin Q)).PairwiseDisjoint
      (masterPadicProductResidueCell p e m) := by
    intro a ha b hb hab
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    have hxa' : ∀ i, PadicInt.toZModPow e (x i) = ((a i).val : ZMod Q) := by
      intro i
      exact (Set.mem_pi.mp hxa) i (Set.mem_univ i)
    have hxb' : ∀ i, PadicInt.toZModPow e (x i) = ((b i).val : ZMod Q) := by
      intro i
      exact (Set.mem_pi.mp hxb) i (Set.mem_univ i)
    have hab' : a = b := by
      funext i
      apply Fin.ext
      have hcast : ((a i).val : ZMod Q) = ((b i).val : ZMod Q) := (hxa' i).symm.trans (hxb' i)
      have hval := congrArg ZMod.val hcast
      simpa [Nat.mod_eq_of_lt (a i).isLt, Nat.mod_eq_of_lt (b i).isLt] using hval
    exact hab hab'
  have hbi := MeasureTheory.measure_biUnion_finset (μ := μ) hdisj
    (fun a ha => hcellMeas a)
  rw [Measure.real, ← hUnion, hbi]
  rw [ENNReal.toReal_sum]
  · have hQpos : (Q : ℝ) ≠ 0 := by
      dsimp [Q]
      exact_mod_cast (pow_pos (Fact.out : Nat.Prime p).pos e).ne'
    have hcellReal : ((1 / (Q : ℝ≥0∞)) ^ m).toReal =
        (1 / (Q : ℝ)) ^ m := by
      simp [ENNReal.toReal_pow, ENNReal.toReal_div, hQpos]
    have hcountNat : F.card =
        ∑ a : Fin m → Fin Q, if masterPadicDivisibilityEvent p e P a then 1 else 0 := by
      calc
        F.card = ∑ a ∈ F, (1 : ℕ) := by simp
        _ = ∑ a : Fin m → Fin Q,
              if masterPadicDivisibilityEvent p e P a then 1 else 0 := by
                dsimp [F]
                rw [Finset.sum_filter]
    have hcount : (F.card : ℝ) =
        ∑ a : Fin m → Fin Q,
          if masterPadicDivisibilityEvent p e P a then (1 : ℝ) else 0 := by
      exact_mod_cast hcountNat
    calc
      ∑ a ∈ F,
          (masterPadicProductMeasure p m (masterPadicProductResidueCell p e m a)).toReal =
        ∑ a ∈ F, ((1 / (Q : ℝ≥0∞)) ^ m).toReal := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [masterPadicProductResidueCell_measure]
          simp [Q]
      _ = (F.card : ℝ) * (1 / (Q : ℝ)) ^ m := by
          rw [hcellReal]
          simp [Finset.sum_const]
      _ = (∑ a : Fin m → Fin Q,
            if masterPadicDivisibilityEvent p e P a then (1 : ℝ) else 0) /
            (Q : ℝ) ^ m := by
            rw [hcount]
            rw [div_pow, one_pow]
            field_simp [hQpos]
  · intro a ha
    exact measure_ne_top _ _

theorem masterUniformUnitProbability_le (p e m : ℕ) [Fact p.Prime]
    (P : IntegerPolynomial m) :
    uniformUnitTupleProbability (p ^ e) m (masterPadicDivisibilityEvent p e P) ≤
      ((p ^ e : ℕ) : ℝ) ^ m / (Nat.totient (p ^ e) : ℝ) ^ m *
        (masterPadicProductMeasure p m).real (masterPadicDivisibilitySet p e P) := by
  classical
  let Q := p ^ e
  let E : (Fin m → Fin Q) → Prop := masterPadicDivisibilityEvent p e P
  let U (a : Fin m → Fin Q) : Prop := ∀ i, Nat.Coprime (a i).val Q
  have hprob : uniformUnitTupleProbability Q m E =
      (∑ a : Fin m → Fin Q, if U a ∧ E a then (1 : ℝ) else 0) /
        (Nat.totient Q : ℝ) ^ m := by
    unfold uniformUnitTupleProbability uniformUnitTupleMass
    change (∑ a : Fin m → Fin Q,
      (if U a then (1 : ℝ) / (Nat.totient Q : ℝ) ^ m else 0) *
        (if E a then 1 else 0)) = _
    calc
      _ = ∑ a : Fin m → Fin Q,
          (if U a ∧ E a then (1 : ℝ) / (Nat.totient Q : ℝ) ^ m else 0) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases hU : U a <;> by_cases hE : E a <;> simp [hU, hE]
      _ = (∑ a : Fin m → Fin Q, if U a ∧ E a then (1 : ℝ) else 0) /
            (Nat.totient Q : ℝ) ^ m := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro a ha
              split_ifs <;> simp
  have hcount :
      (∑ a : Fin m → Fin Q, if U a ∧ E a then (1 : ℝ) else 0) ≤
        ∑ a : Fin m → Fin Q, if E a then (1 : ℝ) else 0 := by
    apply Finset.sum_le_sum
    intro a ha
    by_cases hE : E a
    · by_cases hU : U a <;> simp [hE, hU]
    · simp [hE]
  have hphi : 0 < Nat.totient Q :=
    Nat.totient_pos.mpr (pow_pos (Fact.out : Nat.Prime p).pos e)
  have hcountProb : uniformUnitTupleProbability Q m E ≤
      (∑ a : Fin m → Fin Q, if E a then (1 : ℝ) else 0) /
        (Nat.totient Q : ℝ) ^ m := by
    rw [hprob]
    exact div_le_div_of_nonneg_right hcount (by positivity)
  have hmeasure := masterPadicDivisibilitySet_real p e P
  have hQpos : 0 < Q := pow_pos (Fact.out : Nat.Prime p).pos e
  have hqreal : (Q : ℝ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hφreal : (Nat.totient Q : ℝ) ≠ 0 := by exact_mod_cast hphi.ne'
  have halg :
      (∑ a : Fin m → Fin Q, if E a then (1 : ℝ) else 0) /
          (Nat.totient Q : ℝ) ^ m =
        (Q : ℝ) ^ m / (Nat.totient Q : ℝ) ^ m *
    (masterPadicProductMeasure p m).real (masterPadicDivisibilitySet p e P) := by
    rw [hmeasure]
    simp only [Q]
    field_simp [hqreal, hφreal]
    have hpow : (↑(p ^ e) : ℝ) ^ m * ((↑(p ^ e) : ℝ)⁻¹) ^ m = 1 := by
      rw [← mul_pow]
      simp [hqreal]
    calc
      _ = (Nat.totient (p ^ e) : ℝ)⁻¹ ^ m *
          (∑ a : Fin m → Fin (p ^ e),
            if masterPadicDivisibilityEvent p e P a then (1 : ℝ) else 0) := by ring
      _ = (Nat.totient (p ^ e) : ℝ)⁻¹ ^ m *
          (∑ a : Fin m → Fin (p ^ e),
            if masterPadicDivisibilityEvent p e P a then (1 : ℝ) else 0) *
            ((↑(p ^ e) : ℝ) ^ m * ((↑(p ^ e) : ℝ)⁻¹) ^ m) := by
              rw [hpow]
              ring
      _ = _ := by ring
  calc
    uniformUnitTupleProbability Q m E ≤
        (∑ a : Fin m → Fin Q, if E a then (1 : ℝ) else 0) /
          (Nat.totient Q : ℝ) ^ m := hcountProb
    _ = _ := halg

theorem masterPadicPolynomialZeroSet_measure_zero (p : ℕ) [Fact p.Prime] :
    ∀ m (P : MvPolynomial (Fin m) ℤ_[p]), P ≠ 0 →
      masterPadicProductMeasure p m {x | MvPolynomial.eval x P = 0} = 0 := by
  intro m
  induction m with
  | zero =>
      intro P hP
      have hcoeff : P.coeff 0 ≠ 0 := by
        intro h
        apply hP
        have hconst : P = MvPolynomial.C (P.coeff 0) := MvPolynomial.eq_C_of_isEmpty P
        rw [hconst, h]
        simp
      have hempty : {x : Fin 0 → ℤ_[p] | MvPolynomial.eval x P = 0} = ∅ := by
        ext x
        have hconst : P = MvPolynomial.C (P.coeff 0) := MvPolynomial.eq_C_of_isEmpty P
        rw [hconst]
        simp [hcoeff]
      rw [hempty]
      simp
  | succ m ih =>
      intro P hP
      classical
      let q : Polynomial (MvPolynomial (Fin m) ℤ_[p]) :=
        MvPolynomial.finSuccEquiv ℤ_[p] m P
      have hq : q ≠ 0 := by
        intro h
        apply hP
        exact (MvPolynomial.finSuccEquiv ℤ_[p] m).injective h
      obtain ⟨j, hj⟩ : ∃ j, q.coeff j ≠ 0 := by
        by_contra h
        have hall : ∀ j, q.coeff j = 0 := by
          intro j
          by_contra hc
          exact h ⟨j, hc⟩
        apply hq
        exact Polynomial.ext hall
      let A : MvPolynomial (Fin m) ℤ_[p] := q.coeff j
      have hA : A ≠ 0 := hj
      have hAzero : masterPadicProductMeasure p m {y | MvPolynomial.eval y A = 0} = 0 :=
        ih A hA
      let μ : Measure ℤ_[p] := masterPadicHaar p
      let ν : Measure (Fin m → ℤ_[p]) := masterPadicProductMeasure p m
      let S : Set ((Fin m → ℤ_[p]) × ℤ_[p]) :=
        {z | MvPolynomial.eval (Fin.cases z.2 z.1) P = 0}
      have hgood : ∀ᵐ y ∂ν, MvPolynomial.eval y A ≠ 0 := by
        exact (measure_eq_zero_iff_ae_notMem.mp hAzero)
      have hsection (y : Fin m → ℤ_[p]) (hy : MvPolynomial.eval y A ≠ 0) :
          μ {x | MvPolynomial.eval (Fin.cases x y) P = 0} = 0 := by
        let g : Polynomial ℤ_[p] := Polynomial.map (MvPolynomial.eval y) q
        have hgj : g.coeff j = MvPolynomial.eval y A := by
          simp [g, A]
        have hg : g ≠ 0 := by
          intro hg
          have hc := congrArg (fun r : Polynomial ℤ_[p] => r.coeff j) hg
          rw [hgj] at hc
          exact hy hc
        have hset : {x : ℤ_[p] | MvPolynomial.eval (Fin.cases x y) P = 0} =
            g.rootSet ℤ_[p] := by
          ext x
          change MvPolynomial.eval (Fin.cases x y) P = 0 ↔ x ∈ g.rootSet ℤ_[p]
          rw [show (Fin.cases x y : Fin (m + 1) → ℤ_[p]) =
              @Fin.cons m (fun _ : Fin (m + 1) => ℤ_[p]) x y by rfl]
          rw [MvPolynomial.eval_eq_eval_mv_eval' y x P]
          change Polynomial.eval x g = 0 ↔ x ∈ g.rootSet ℤ_[p]
          simp [Polynomial.mem_rootSet', hg]
        rw [hset]
        exact (Polynomial.rootSet_finite g ℤ_[p]).measure_zero μ
      have hcont : Continuous (fun z : (Fin m → ℤ_[p]) × ℤ_[p] =>
          MvPolynomial.eval (Fin.cases z.2 z.1) P) := by
        apply P.continuous_eval.comp
        apply continuous_pi
        intro i
        refine Fin.cases ?_ ?_ i
        · exact continuous_snd
        · intro j
          exact (continuous_apply j).comp continuous_fst
      have hSmeas : MeasurableSet S := (isClosed_eq hcont continuous_const).measurableSet
      have hAE : (fun y : Fin m → ℤ_[p] =>
          μ ((fun x => (y, x)) ⁻¹' S)) =ᵐ[ν] 0 := by
        filter_upwards [hgood] with y hy
        have hs := hsection y hy
        simpa [S] using hs
      have hprod : (ν.prod μ) S = 0 := (Measure.measure_prod_null hSmeas).2 hAE
      let e : (Fin (m + 1) → ℤ_[p]) ≃ᵐ ℤ_[p] × (Fin m → ℤ_[p]) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℤ_[p]) 0
      let f : (Fin (m + 1) → ℤ_[p]) → (Fin m → ℤ_[p]) × ℤ_[p] :=
        fun x => (fun i => x i.succ, x 0)
      have hef : f = fun x => Prod.swap (e x) := by
        funext x
        apply Prod.ext
        · funext i
          simp [f, e, MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
        · simp [f, e, MeasurableEquiv.piFinSuccAbove_apply]
      have hp : MeasurePreserving f (masterPadicProductMeasure p (m + 1)) (ν.prod μ) := by
        rw [hef]
        exact (MeasureTheory.Measure.measurePreserving_swap (μ := μ) (ν := ν)).comp
          (MeasureTheory.measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0)
      have hpre : f ⁻¹' S = {x : Fin (m + 1) → ℤ_[p] | MvPolynomial.eval x P = 0} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_setOf_eq, f, S, Prod.mk.injEq]
        change MvPolynomial.eval (Fin.cases (x 0) (fun i => x i.succ)) P = 0 ↔
          MvPolynomial.eval x P = 0
        rw [show Fin.cases (x 0) (fun i => x i.succ) = x by
          funext i
          exact Fin.cases (by simp) (fun _ => rfl) i]
      calc
        masterPadicProductMeasure p (m + 1) {x | MvPolynomial.eval x P = 0} =
            masterPadicProductMeasure p (m + 1) (f ⁻¹' S) := by rw [hpre]
        _ = Measure.map f (masterPadicProductMeasure p (m + 1)) S :=
            (Measure.map_apply hp.measurable hSmeas).symm
        _ = (ν.prod μ) S := by rw [hp.map_eq]
        _ = 0 := hprod


theorem masterPadicDivisibilitySet_real_tendsto_zero {m : ℕ} (p : ℕ) [Fact p.Prime]
    (P : IntegerPolynomial m) (hP : P ≠ 0) :
    Tendsto (fun e => (masterPadicProductMeasure p m).real
      (masterPadicDivisibilitySet p e P)) atTop (𝓝 0) := by
  classical
  let Pp : MvPolynomial (Fin m) ℤ_[p] := P.map (Int.castRingHom ℤ_[p])
  have hcast : Function.Injective (Int.castRingHom ℤ_[p]) := by
    intro a b hab
    exact Int.cast_injective hab
  have hPp : Pp ≠ 0 := by
    intro h
    apply hP
    exact (MvPolynomial.map_injective (Int.castRingHom ℤ_[p]) hcast) h
  let μ := masterPadicProductMeasure p m
  let s : ℕ → Set (Fin m → ℤ_[p]) := fun e => masterPadicDivisibilitySet p e P
  have hcellMeas (e : ℕ) (a : Fin m → Fin (p ^ e)) :
      MeasurableSet (masterPadicProductResidueCell p e m a) := by
    apply MeasurableSet.pi Set.countable_univ
    intro i hi
    exact masterPadicHaarResidueCell_measurable p e ((a i).val : ZMod (p ^ e))
  have hsMeas (e : ℕ) : MeasurableSet (s e) := by
    change MeasurableSet (masterPadicDivisibilitySet p e P)
    rw [← masterPadicDivisibilitySet_iUnion p e P]
    exact Finset.measurableSet_biUnion _ (fun a ha => hcellMeas e a)
  have hanti : Antitone s := by
    intro e f hef x hx
    change PadicInt.toZModPow f (MvPolynomial.eval x Pp) = 0 at hx
    change PadicInt.toZModPow e (MvPolynomial.eval x Pp) = 0
    have hcast := PadicInt.cast_toZModPow e f hef (MvPolynomial.eval x Pp)
    rw [hx] at hcast
    simpa using hcast.symm
  have hinter : (⋂ e, s e) = {x | MvPolynomial.eval x Pp = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, s]
    constructor
    · intro hx
      have hzero : ∀ e, PadicInt.toZModPow e (MvPolynomial.eval x Pp) =
          PadicInt.toZModPow e 0 := by
        intro e
        have he := hx e
        change PadicInt.toZModPow e (MvPolynomial.eval x Pp) = 0 at he
        simpa using he
      exact (PadicInt.ext_of_toZModPow).mp hzero
    · intro hx e
      change PadicInt.toZModPow e (MvPolynomial.eval x Pp) = 0
      rw [hx]
      simp
  have hzero : μ (⋂ e, s e) = 0 := by
    rw [hinter]
    exact masterPadicPolynomialZeroSet_measure_zero p m Pp hPp
  have hmeas : ∀ e, NullMeasurableSet (s e) μ := fun e => (hsMeas e).nullMeasurableSet
  have hfin : ∃ e, μ (s e) ≠ ∞ := ⟨0, measure_ne_top _ _⟩
  have hENN : Tendsto (fun e => μ (s e)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop hmeas hanti hfin
    rw [hzero] at h
    exact h
  have hreal : Tendsto (fun e => (μ (s e)).toReal) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff (fun e => measure_ne_top _ _)).2 hENN
  simpa [μ, s, Measure.real] using hreal


end HindmanSumsProducts

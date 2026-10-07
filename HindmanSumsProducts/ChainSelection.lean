import Mathlib
import HindmanSumsProducts.ChainSelection.FiniteRamsey

/-!
# Selection of a product chain (paper Lemma `lem:chain-selection`, §2)

A chain of length `m` in `Fin n` is given by tails `T d` and pivots `piv d` (`d : Fin m`) with
`∅ ≠ T 0 < T 1 < ⋯ < T (m-1) < piv 0 < ⋯ < piv (m-1)`, where `S < S'` means every element of `S`
is below every element of `S'`. Block `d` is `insert (piv d) (T d)`.
-/

namespace HindmanSumsProducts

private theorem liftFSFromPNat (a : Stream' ℕ+) (b : Stream' ℕ)
    (hmap : ∀ i, b.get i = (a.get i).val) {n : ℕ}
    (h : Hindman.FS b n) :
    ∃ p : ℕ+, Hindman.FS a p ∧ p.val = n := by
  induction h generalizing a with
  | head b =>
      exact ⟨a.head, Hindman.FS.head a, by simpa using (hmap 0).symm⟩
  | of_tail b n hb ih =>
      have hmap' : ∀ i, b.tail.get i = (a.tail.get i).val := by
        intro i
        simpa using hmap (i + 1)
      obtain ⟨p, hp, hpn⟩ := ih a.tail hmap'
      exact ⟨p, Hindman.FS.of_tail a p hp, hpn⟩
  | cons b n hb ih =>
      have hmap' : ∀ i, b.tail.get i = (a.tail.get i).val := by
        intro i
        simpa using hmap (i + 1)
      obtain ⟨p, hp, hpn⟩ := ih a.tail hmap'
      refine ⟨a.head + p, Hindman.FS.cons a p hp, ?_⟩
      change a.head.val + p.val = b.head + n
      rw [hpn, ← hmap 0]

private def shiftEmbedding (k start len : ℕ) (h : start + len ≤ k) : Fin len ↪ Fin k where
  toFun i := ⟨start + i.val, by have := i.isLt; omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    exact Nat.add_left_cancel hv

/-- The ordering condition `(eq:block-chain)` of the paper on tails and pivots. -/
def IsChain {n m : ℕ} (T : Fin m → Finset (Fin n)) (piv : Fin m → Fin n) : Prop :=
  (∀ d, (T d).Nonempty) ∧
  (∀ d d', d < d' → ∀ a ∈ T d, ∀ b ∈ T d', a < b) ∧
  (∀ d d', ∀ a ∈ T d, a < piv d') ∧
  StrictMono piv

/-- Finite sums theorem, finite form (Folkman–Rado–Sanders), as used in §2: for every `m, r`
there is `F` such that every `r`-colouring has positive `u 0, …, u (m-1)` whose nonempty subset
sums lie in `[1, F]` and have one colour. -/
theorem finite_sums_finite_form (m r : ℕ) : ∃ F : ℕ, ∀ χ : ℕ → Fin r,
    ∃ (u : Fin m → ℕ) (c : Fin r), (∀ d, 0 < u d) ∧
      ∀ J : Finset (Fin m), J.Nonempty → ∑ d ∈ J, u d ≤ F ∧ χ (∑ d ∈ J, u d) = c := by
  classical
  by_cases hr : r = 0
  · refine ⟨0, ?_⟩
    subst r
    intro χ
    exact Fin.elim0 (χ 0)
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    by_cases hm : m = 0
    · subst m
      refine ⟨0, ?_⟩
      intro χ
      refine ⟨Fin.elim0, χ 0, ?_, ?_⟩
      · intro d
        exact Fin.elim0 d
      · intro J hJ
        obtain ⟨d, hd⟩ := hJ
        exact Fin.elim0 d
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      by_contra hfail
      push_neg at hfail
      let bound (s : Finset ℕ) : ℕ := m * ∑ a ∈ s, a
      let badColoring (F : ℕ) : ℕ → Fin r := Classical.choose (hfail F)
      have hbadColoring (F : ℕ) : ∀ (u : Fin m → ℕ) (c : Fin r),
          (∀ d, 0 < u d) →
            ∃ J : Finset (Fin m), J.Nonempty ∧
              (∑ d ∈ J, u d ≤ F → badColoring F (∑ d ∈ J, u d) ≠ c) :=
        Classical.choose_spec (hfail F)
      let g : Finset ℕ → ℕ → Fin r := fun s => badColoring (bound s)
      obtain ⟨χ, hχ⟩ := Finset.rado_selection g
      let cells : Set (Set ℕ+) := Set.range fun c : Fin r => {a : ℕ+ | χ a = c}
      have hcellsFinite : cells.Finite := Set.finite_range _
      have hcellsCover : (Set.univ : Set ℕ+) ⊆ ⋃₀ cells := by
        intro a _
        change ∃ t ∈ cells, a ∈ t
        exact ⟨{b : ℕ+ | χ b = χ a}, ⟨χ a, rfl⟩, rfl⟩
      obtain ⟨C, hC, seq, hseq⟩ :=
        Hindman.exists_FS_of_finite_cover cells hcellsFinite hcellsCover
      obtain ⟨c, rfl⟩ := hC
      have hseqColor : ∀ p : ℕ+, Hindman.FS seq p → χ p = c := by
        intro p hp
        exact hseq p hp
      let u : Fin m → ℕ := fun d => (seq.get d.val).val
      let subsetSums : Finset (Finset (Fin m)) := Finset.univ.powerset.erase ∅
      let vals : Finset ℕ :=
        Finset.univ.image u ∪ subsetSums.image (fun J => ∑ d ∈ J, u d)
      obtain ⟨t, hvals, hagree⟩ := hχ vals
      have hterms : ∀ d, u d ∈ t := by
        intro d
        apply hvals
        apply Finset.mem_union.mpr
        left
        exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩
      have hsumMem (J : Finset (Fin m)) (hJ : J.Nonempty) :
          (∑ d ∈ J, u d) ∈ vals := by
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        refine ⟨J, ?_, rfl⟩
        have hJne : J ≠ ∅ := by
          intro h
          subst J
          simpa using hJ
        simp [subsetSums, hJne]
      have hsumColor (J : Finset (Fin m)) (hJ : J.Nonempty) :
          χ (∑ d ∈ J, u d) = c := by
        let b : Stream' ℕ := Stream'.map PNat.val seq
        let I : Finset ℕ := J.image Fin.val
        have hI : I.Nonempty := by
          rcases hJ with ⟨d, hd⟩
          exact ⟨d.val, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩
        have hsumI : (∑ i ∈ I, b.get i) = ∑ d ∈ J, u d := by
          simpa [b, I, u] using
            (Finset.sum_image (s := J) (g := Fin.val)
              (f := fun i : ℕ => (seq.get i).val) Fin.val_injective.injOn)
        have hFSb : Hindman.FS b (∑ i ∈ I, b.get i) := Hindman.FS.finsetSum b I hI
        obtain ⟨p, hp, hpn⟩ := liftFSFromPNat seq b (by intro i; simp [b]) hFSb
        rw [← hsumI, ← hpn]
        exact hseqColor p hp
      have hcolorInLocal (J : Finset (Fin m)) (hJ : J.Nonempty) :
          badColoring (bound t) (∑ d ∈ J, u d) = c := by
        change g t (∑ d ∈ J, u d) = c
        rw [← hagree _ (hsumMem J hJ)]
        exact hsumColor J hJ
      have htermBound (d : Fin m) : u d ≤ ∑ a ∈ t, a :=
        Finset.single_le_sum (f := fun a : ℕ => a)
          (fun _ _ => Nat.zero_le _) (hterms d)
      have hsumBound (J : Finset (Fin m)) (hJ : J.Nonempty) :
          ∑ d ∈ J, u d ≤ bound t := by
        calc
          ∑ d ∈ J, u d ≤ ∑ d ∈ J, (∑ a ∈ t, a) := by
            apply Finset.sum_le_sum
            intro d hd
            exact htermBound d
          _ = J.card * (∑ a ∈ t, a) := by simp
          _ ≤ m * (∑ a ∈ t, a) := by
            apply Nat.mul_le_mul_right
            simpa using (Finset.card_le_univ J)
      have hpositive : ∀ d, 0 < u d := fun d => (seq.get d.val).property
      obtain ⟨J, hJ, hbad⟩ := hbadColoring (bound t) u c hpositive
      exact hbad (hsumBound J hJ) (hcolorInLocal J hJ)

/-- Paper Lemma `lem:chain-selection`: for every `m, r` there is `n` such that for every
colouring `χ` and every list `x : Fin n → ℕ` some chain has all nonempty products of its block
products `x_{B_d} = ∏_{j ∈ B_d} x j` in one colour. -/
theorem chain_selection (m r : ℕ) : ∃ n : ℕ, ∀ (χ : ℕ → Fin r) (x : Fin n → ℕ),
    ∃ (T : Fin m → Finset (Fin n)) (piv : Fin m → Fin n) (c : Fin r), IsChain T piv ∧
      ∀ J : Finset (Fin m), J.Nonempty →
        χ (∏ d ∈ J, ∏ j ∈ insert (piv d) (T d), x j) = c := by
  classical
  by_cases hr : r = 0
  · refine ⟨0, ?_⟩
    subst r
    intro χ x
    exact Fin.elim0 (χ 0)
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    by_cases hm : m = 0
    · refine ⟨0, ?_⟩
      subst m
      intro χ x
      let T : Fin 0 → Finset (Fin 0) := Fin.elim0
      let piv : Fin 0 → Fin 0 := Fin.elim0
      refine ⟨T, piv, χ 0, ?_, ?_⟩
      · simp [IsChain, StrictMono]
      · intro J hJ
        obtain ⟨d, hd⟩ := hJ
        exact Fin.elim0 d
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      obtain ⟨F, hF⟩ := finite_sums_finite_form m r
      let k : ℕ := 2 * F
      obtain ⟨N, hNk, hRamsey⟩ :=
        OAI.MarkovSuperreflexivity.finite_ramsey_simultaneous_subsets
          (k + 1) k (fun _ : Fin (k + 1) => r) (by intro q; exact hrpos)
      refine ⟨N, ?_⟩
      intro χ x
      let paint : (q : Fin (k + 1)) → Finset (Fin N) → Fin r :=
        fun _ A => χ (∏ i ∈ A, x i)
      obtain ⟨H, hHN, hHcard, hHmono⟩ :=
        hRamsey (Fin N) Finset.univ (by simp) paint
      let e : Fin k ↪o Fin N := H.orderEmbOfFin hHcard
      let can (q : Fin (k + 1)) : Finset (Fin k) :=
        Finset.univ.map (Fin.castLEEmb (Nat.le_of_lt_succ q.isLt))
      let κ : Fin (k + 1) → Fin r := fun q => paint q ((can q).map e.toEmbedding)
      have hκ (q : Fin (k + 1)) (A : Finset (Fin k)) (hA : A.card = q.val) :
          paint q (A.map e.toEmbedding) = κ q := by
        have hAsub : A.map e.toEmbedding ⊆ H := by
          intro z hz
          obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hz
          exact H.orderEmbOfFin_mem hHcard a
        have hCanSub : (can q).map e.toEmbedding ⊆ H := by
          intro z hz
          obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hz
          exact H.orderEmbOfFin_mem hHcard a
        have hAcard : (A.map e.toEmbedding).card = q.val := by
          simpa using hA
        have hCanCard : ((can q).map e.toEmbedding).card = q.val := by
          simp [can]
        exact (hHmono q (A.map e.toEmbedding) hAsub hAcard
          ((can q).map e.toEmbedding) hCanSub hCanCard)
      let χsum : ℕ → Fin r := fun a =>
        if ha : 2 * a ≤ k then κ ⟨2 * a, Nat.lt_succ_of_le ha⟩ else χ 0
      obtain ⟨v, csum, hvpos, hvsum⟩ := hF χsum
      have huniv : (Finset.univ : Finset (Fin m)).Nonempty := by
        exact ⟨⟨0, hmpos⟩, Finset.mem_univ _⟩
      let qlen : Fin m → ℕ := fun d => 2 * v d
      let seglen : Fin m → ℕ := fun d => qlen d - 1
      let L : ℕ := ∑ d : Fin m, seglen d
      let start : Fin m → ℕ := fun d => ∑ i ∈ Finset.Iio d, seglen i
      have hqpos (d : Fin m) : 1 ≤ qlen d := by
        dsimp [qlen]
        have := hvpos d
        omega
      have hLplus : L + m = ∑ d : Fin m, qlen d := by
        have hones : (∑ d : Fin m, (1 : ℕ)) = m := by simp
        calc
          L + m = (∑ d : Fin m, seglen d) + ∑ d : Fin m, (1 : ℕ) := by
            simp [L, hones]
          _ = ∑ d : Fin m, (seglen d + 1) := Finset.sum_add_distrib.symm
          _ = ∑ d : Fin m, qlen d := by
            apply Finset.sum_congr rfl
            intro d hd
            dsimp [seglen]
            exact Nat.sub_add_cancel (hqpos d)
      have hqsum : (∑ d : Fin m, qlen d) = 2 * (∑ d : Fin m, v d) := by
        dsimp [qlen]
        rw [← Finset.mul_sum]
      have hLplusBound : L + m ≤ k := by
        rw [hLplus, hqsum]
        dsimp [k]
        exact Nat.mul_le_mul_left 2 (hvsum Finset.univ huniv).1
      have hStartEndTotal (d : Fin m) : start d + seglen d ≤ L := by
        have hdnot : d ∉ Finset.Iio d := by simp
        have hsub : insert d (Finset.Iio d) ⊆ (Finset.univ : Finset (Fin m)) := by
          intro i hi
          simp
        calc
          start d + seglen d = seglen d + start d := Nat.add_comm _ _
          _ = ∑ i ∈ insert d (Finset.Iio d), seglen i := by
            rw [Finset.sum_insert hdnot]
          _ ≤ L := by
            simpa [L] using
              (Finset.sum_le_sum_of_subset_of_nonneg hsub
                (fun _ _ _ => Nat.zero_le _))
      have hPrefixOrder {d d' : Fin m} (hdd : d < d') :
          start d + seglen d ≤ start d' := by
        have hdnot : d ∉ Finset.Iio d := by simp
        have hsub : insert d (Finset.Iio d) ⊆ Finset.Iio d' := by
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Finset.mem_Iio.mpr hdd
          · exact Finset.mem_Iio.mpr (lt_trans (Finset.mem_Iio.mp hi) hdd)
        calc
          start d + seglen d = seglen d + start d := Nat.add_comm _ _
          _ = ∑ i ∈ insert d (Finset.Iio d), seglen i := by
            rw [Finset.sum_insert hdnot]
          _ ≤ start d' := by
            simpa [start] using
              (Finset.sum_le_sum_of_subset_of_nonneg hsub
                (fun _ _ _ => Nat.zero_le _))
      let tailEmb (d : Fin m) : Fin (seglen d) ↪ Fin k :=
        shiftEmbedding k (start d) (seglen d) (by
          have h1 := hStartEndTotal d
          omega)
      let tailLocal (d : Fin m) : Finset (Fin k) :=
        Finset.univ.map (tailEmb d)
      let pivotPos (d : Fin m) : Fin k :=
        ⟨L + d.val, by have := d.isLt; omega⟩
      let blockLocal (d : Fin m) : Finset (Fin k) := insert (pivotPos d) (tailLocal d)
      have hTailPos {d : Fin m} {z : Fin k} (hz : z ∈ tailLocal d) :
          start d ≤ z.val ∧ z.val < start d + seglen d := by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hz
        constructor
        · change start d ≤ start d + i.val
          omega
        · have hi' : i.val < seglen d := i.isLt
          change start d + i.val < start d + seglen d
          exact Nat.add_lt_add_left hi' _
      have hTailLT {d d' : Fin m} (hdd : d < d')
          {a b : Fin k} (ha : a ∈ tailLocal d) (hb : b ∈ tailLocal d') : a < b := by
        have ha' := hTailPos ha
        have hb' := hTailPos hb
        have hpref := hPrefixOrder hdd
        change a.val < b.val
        omega
      have hPivotNotTail (d d' : Fin m) : pivotPos d ∉ tailLocal d' := by
        intro h
        have hp := hTailPos h
        change start d' ≤ L + d.val ∧ L + d.val < start d' + seglen d' at hp
        have hend := hStartEndTotal d'
        omega
      have hPivotInj {d d' : Fin m} (heq : pivotPos d = pivotPos d') : d = d' := by
        apply Fin.ext
        have hv := congrArg Fin.val heq
        dsimp [pivotPos] at hv
        exact Nat.add_left_cancel hv
      have hTailDisjoint {d d' : Fin m} (hne : d ≠ d') (z : Fin k)
          (hz : z ∈ tailLocal d) (hz' : z ∈ tailLocal d') : False := by
        rcases lt_or_gt_of_ne hne with h | h
        · have := hTailLT h hz hz'
          exact (lt_irrefl z) this
        · have := hTailLT h hz' hz
          exact (lt_irrefl z) this
      have hBlockDisjoint {d d' : Fin m} (hne : d ≠ d') :
          Disjoint (blockLocal d) (blockLocal d') := by
        rw [Finset.disjoint_left]
        intro z hz hz'
        rcases Finset.mem_insert.mp hz with hp | ht
        · rcases Finset.mem_insert.mp hz' with hp' | ht'
          · exact hne (hPivotInj (hp.symm.trans hp'))
          · subst z
            exact hPivotNotTail d d' ht'
        · rcases Finset.mem_insert.mp hz' with hp' | ht'
          · subst z
            exact hPivotNotTail d' d ht
          · exact hTailDisjoint hne z ht ht'
      let T : Fin m → Finset (Fin N) := fun d => (tailLocal d).map e.toEmbedding
      let piv : Fin m → Fin N := fun d => e (pivotPos d)
      have hBlockMap (d : Fin m) :
          (blockLocal d).map e.toEmbedding = insert (piv d) (T d) := by
        simp [blockLocal, T, piv]
      have hTcard (d : Fin m) : (T d).card = seglen d := by
        simp [T, tailLocal]
      have hBlockCard (d : Fin m) : (blockLocal d).card = qlen d := by
        have hpnot : pivotPos d ∉ tailLocal d := hPivotNotTail d d
        rw [Finset.card_insert_of_notMem hpnot]
        simp only [tailLocal, Finset.card_map, Finset.card_univ, Fintype.card_fin]
        dsimp [seglen]
        have hp := hqpos d
        omega
      have hChain : IsChain T piv := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro d
          apply Finset.card_pos.mp
          rw [hTcard]
          have := hvpos d
          dsimp [seglen, qlen]
          omega
        · intro d d' hdd a ha b hb
          obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
          obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
          exact e.strictMono (hTailLT hdd ha' hb')
        · intro d d' a ha
          obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
          have hpos := hTailPos ha'
          have hend := hStartEndTotal d
          apply e.strictMono
          change a'.val < L + d'.val
          omega
        · intro d d' hdd
          apply e.strictMono
          have hval : d.val < d'.val := Fin.lt_iff_val_lt_val.mp hdd
          change L + d.val < L + d'.val
          omega
      let unionLocal (J : Finset (Fin m)) : Finset (Fin k) := J.biUnion blockLocal
      have hPairwise (J : Finset (Fin m)) :
          (↑J : Set (Fin m)).PairwiseDisjoint blockLocal := by
        intro d hd d' hd' hne
        exact hBlockDisjoint hne
      have hNestedProd (J : Finset (Fin m)) :
          (∏ d ∈ J, ∏ j ∈ insert (piv d) (T d), x j) =
            ∏ i ∈ unionLocal J, x (e.toEmbedding i) := by
        calc
          (∏ d ∈ J, ∏ j ∈ insert (piv d) (T d), x j) =
              ∏ d ∈ J, ∏ i ∈ blockLocal d, x (e i) := by
                apply Finset.prod_congr rfl
                intro d hd
                rw [← hBlockMap d, Finset.prod_map]
                simp
          _ = ∏ i ∈ unionLocal J, x (e i) := (Finset.prod_biUnion (hPairwise J)).symm
      have hUnionCard (J : Finset (Fin m)) :
          (unionLocal J).card = ∑ d ∈ J, qlen d := by
        rw [Finset.card_biUnion (hPairwise J)]
        apply Finset.sum_congr rfl
        intro d hd
        exact hBlockCard d
      have hκLocal (q : Fin (k + 1)) (A : Finset (Fin k)) (hA : A.card = q.val) :
          paint q (A.map e.toEmbedding) = κ q := hκ q A hA
      refine ⟨T, piv, csum, hChain, ?_⟩
      intro J hJ
      let A := unionLocal J
      have hAcard : A.card = 2 * (∑ d ∈ J, v d) := by
        rw [hUnionCard]
        calc
          ∑ d ∈ J, qlen d = ∑ d ∈ J, 2 * v d := by simp [qlen]
          _ = 2 * (∑ d ∈ J, v d) := by rw [← Finset.mul_sum]
      have hSumBound := (hvsum J hJ).1
      have hSizeLe : 2 * (∑ d ∈ J, v d) ≤ k := by
        dsimp [k]
        exact Nat.mul_le_mul_left 2 hSumBound
      let q : Fin (k + 1) := ⟨2 * (∑ d ∈ J, v d), Nat.lt_succ_of_le hSizeLe⟩
      have hκSum : κ q = csum := by
        have hcolored := (hvsum J hJ).2
        simpa [χsum, q, hSizeLe] using hcolored
      have hcolorA : paint q (A.map e.toEmbedding) = csum := by
        rw [hκLocal q A hAcard]
        exact hκSum
      have hMapProd : (∏ j ∈ A.map e.toEmbedding, x j) =
          ∏ i ∈ A, x (e.toEmbedding i) := by
        rw [Finset.prod_map]
      have hEqProducts :
          (∏ d ∈ J, ∏ j ∈ insert (piv d) (T d), x j) =
            ∏ j ∈ A.map e.toEmbedding, x j := by
        exact hNestedProd J |>.trans hMapProd.symm
      calc
        χ (∏ d ∈ J, ∏ j ∈ insert (piv d) (T d), x j) =
            χ (∏ j ∈ A.map e.toEmbedding, x j) := congrArg χ hEqProducts
        _ = csum := by simpa [paint] using hcolorA

end HindmanSumsProducts

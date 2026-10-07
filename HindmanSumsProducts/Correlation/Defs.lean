import HindmanSumsProducts.Arithmetic.Defs
import HindmanSumsProducts.Correlation.FromArithmetic

/-!
# Vocabulary of §4

The setting of §4 (04:10–57) is built from §3 objects: master scales
`FromArithmetic.MasterScales K Aset s Dm` (a copy of `HindmanSumsProducts.MasterScales`; its
`core.parameters` is OpenAI's `OAI.SourceAdmissible.Parameters K`), a master chain
`HindmanSumsProducts.MasterChain K m` (§3 `Defs`; it carries the gap `l`, with
`T_1<⋯<T_m<l<i_1<⋯<i_m`), and multipliers `a : Fin m → ℚ` from `Aset`.
Laws are the §3 weight functions: `harmonicLaw X W : ℤ → ℝ` for `μ_X`, `primePoolLaw` for the
pool law `λ_l(p)=1/(pS_l)`, and `nuB` of the tail-product law for `ν_B`.

Conventions. The asymptotic index is `N`, the paper's `w` is `N+1` and `W` is
`primorial (N+1)`. The scales `c_d=h_{B_d}a_d` are rationals; they are integers, and the ratios
`c_k/c_{max J}` are integers divisible by `W` for `k<max J`, only for all sufficiently large `N`
(03:209–211, 04:22–24). Forms are therefore computed in `ℚ`, and functions on `ℤ` are evaluated at
them through `atQ` (zero at a non-integer). Every §4 conclusion is asserted for all sufficiently
large `N`, where the arguments that occur are integers.

Slots. A row or cube template has its own number `q` of prime slots. The master scales have one
polynomial list `Dm` in `s` slots, which must serve every template used later (§5 uses many cube
types with one master construction). A template is placed in the master list through an
embedding `ι : Fin q ↪ Fin s` (`TestsListed`); its `q` slots are sampled independently from the
gap's pool.
-/

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts
noncomputable section
attribute [local instance] Classical.propDecidable
open FromArithmetic

/-! ## Rational arguments -/

/-- A function on `ℤ` read at a rational argument: `g x` at an integer, `0` otherwise. -/
def atQ (g : ℤ → ℝ) (x : ℚ) : ℝ :=
  if x.den = 1 then g x.num else 0

/-! ## The chain, its scales and its linear forms (04:10–31) -/

/-- The scale `c_d=h_{B_d}a_d` of the `d`-th chain block, a positive rational. -/
def chainScale {n m : ℕ} (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m)
    (a : Fin m → ℚ) (N : ℕ) (d : Fin m) : ℚ :=
  (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
    (A.ht N) (C.block d).set : ℚ) * a d

/-- The form `L_J(z)=∑_{k∈J}(c_k/c_{a(J)})z_k` with anchor `a(J)=max J` (zero for `J=∅`). -/
def chainForm {m : ℕ} (c : Fin m → ℚ) (J : Finset (Fin m)) (z : Fin m → ℤ) : ℚ :=
  if hJ : J.Nonempty then ∑ k ∈ J, c k / c (J.max' hJ) * (z k : ℚ) else 0

/-- Joint law of the pivot variables: `z_k` has law `μ_{i_k}`, independently in `k`. -/
def pivotMass {n m : ℕ} (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m)
    (N : ℕ) (z : Fin m → ℤ) : ℝ :=
  ∏ k, harmonicLaw (A.X N (C.block k).1) (primorial (N + 1)) (z k)

/-- The divisor weight `ν_k=ν_{B_k}(y)=E_σ σ1_{σ∣y}`, `σ=t_{T_k}` (§2 `def:divisor-weight`,
03:446–449). -/
def chainWeight {n m : ℕ} (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m)
    (N : ℕ) (k : Fin m) : ℤ → ℝ :=
  nuB (FromArithmetic.parameterTailProductLaw A N (C.block k).2.val)

/-- The correlation `𝒞` of equation `eq:correlation-initial` (04:32–41):
`E_z[∏_{U≠∅} b_U(z_U) ∏_{J≠∅} g_J(L_J(z))]`, `z_U=∏_{k∈U} z_k`. -/
def maskedCorrelation {n m : ℕ} (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m)
    (a : Fin m → ℚ) (N : ℕ) (b g : Finset (Fin m) → ℤ → ℝ) : ℝ :=
  ∑' z : Fin m → ℤ, pivotMass A C N z *
    ((∏ U ∈ Finset.univ.filter Finset.Nonempty, b U (∏ k ∈ U, z k)) *
      ∏ J ∈ Finset.univ.filter Finset.Nonempty,
        atQ (g J) (chainForm (chainScale A C a N) J z))

/-- The function bounds of §4 (04:42–44): `|b_U| ≤ 1` and `|g_J(y)| ≤ 1+ν_{a(J)}(y)` for every
nonempty `U, J` and every integer `y`. -/
def FunctionsValid {n m : ℕ} (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m)
    (N : ℕ) (b g : Finset (Fin m) → ℤ → ℝ) : Prop :=
  (∀ U : Finset (Fin m), U.Nonempty → ∀ y, |b U y| ≤ 1) ∧
  ∀ (J : Finset (Fin m)) (hJ : J.Nonempty) (y : ℤ),
    |g J y| ≤ 1 + chainWeight A C N (J.max' hJ) y

/-! ## Prime slots of a gap -/

section Slots

variable {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

/-- Mass of a tuple of independent slots from gap `l`'s pool, each with law `λ_l`. -/
def gapSlotMass (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) (N : ℕ) {q : ℕ}
    (p : Fin q → ℕ) : ℝ :=
  independentPrimePoolMass (fun _ => (S.primeStage.pool N l).lower)
    (fun _ => (S.primeStage.pool N l).upper) p

/-- Probability of an event under independent slots from gap `l`'s pool. -/
def gapSlotProbability (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) (N : ℕ) {q : ℕ}
    (E : (Fin q → ℕ) → Prop) : ℝ :=
  independentPrimePoolProbability (fun _ => (S.primeStage.pool N l).lower)
    (fun _ => (S.primeStage.pool N l).upper) E

/-- Expectation under independent slots from gap `l`'s pool. -/
def gapSlotAverage (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) (N : ℕ) {q : ℕ}
    (F : (Fin q → ℕ) → ℝ) : ℝ :=
  ∑' p : Fin q → ℕ, gapSlotMass S l N p * F p

/-- Expectation under the slot law conditioned on `good` and renormalized (zero if `good` is
null). -/
def goodSlotAverage (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) (N : ℕ) {q : ℕ}
    (good : (Fin q → ℕ) → Prop) (F : (Fin q → ℕ) → ℝ) : ℝ :=
  (gapSlotProbability S l N good)⁻¹ *
    ∑' p : Fin q → ℕ, gapSlotMass S l N p * (if good p then F p else 0)

/-- Expectation of one prime `p` with law `λ_l`. -/
def poolAverage (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) (N : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑' p : ℕ, primePoolLaw (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper p * F p

/-- Good prime tuples (04:375–380): all slots in the pool, no repeated slot, no zero value of a
test polynomial, and no `π^{e_0} ∣ D(p)` for a prime `π ≤ w`. -/
def GoodTuple (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) (N : ℕ) {q : ℕ}
    (tests : Finset (IntegerPolynomial q)) (Dpoly : IntegerPolynomial q) (p : Fin q → ℕ) :
    Prop :=
  (∀ i, (S.primeStage.pool N l).lower ≤ p i ∧ p i < (S.primeStage.pool N l).upper ∧
      (p i).Prime) ∧
    Function.Injective p ∧
    (∀ P ∈ tests, evalIntegerPolynomial P (fun i => (p i : ℤ)) ≠ 0) ∧
    ∀ π : ℕ, π.Prime → π ≤ N + 1 →
      ¬ (((π ^ S.primeStage.e0 N : ℕ) : ℤ) ∣ evalIntegerPolynomial Dpoly (fun i => (p i : ℤ)))

/-- The modulus `M(p)=M|D(p)|_{>w}` of equation `eq:correlation-modulus`. -/
def directionModulus (S : FromArithmetic.MasterScales K Aset s Dm) (N : ℕ) {q : ℕ}
    (Dpoly : IntegerPolynomial q) (p : Fin q → ℕ) : ℕ :=
  S.core.parameters.M N * roughPart (N + 1) (evalIntegerPolynomial Dpoly (fun i => (p i : ℤ)))

/-- The shift length `L(p)=⌊R_l/(J_0M(p))⌋` of equation `eq:correlation-shift-length`. -/
def shiftLength (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) (J0 N : ℕ) {q : ℕ}
    (Dpoly : IntegerPolynomial q) (p : Fin q → ℕ) : ℕ :=
  S.core.parameters.H N l / (J0 * directionModulus S N Dpoly p)

end Slots

/-- Uniform average over two independent shifts `u_R^0,u_R^1 ∈ [0,L)` for each `R : ι`
(zero if `L = 0` and `ι` is nonempty; with no directions it is the single value `F` takes). -/
def shiftAverage (ι : Type*) [Fintype ι] [DecidableEq ι] (L : ℕ)
    (F : (ι → Fin 2 → ℕ) → ℝ) : ℝ :=
  ((L : ℝ) ^ (2 * Fintype.card ι))⁻¹ *
    ∑ u ∈ Fintype.piFinset (fun _ : ι => Fintype.piFinset fun _ : Fin 2 => Finset.range L), F u

/-- The tests of a template, renamed into the master slots by `ι`, belong to the master list. -/
def TestsListed {q s : ℕ} (Dm : Finset (IntegerPolynomial s)) (ι : Fin q ↪ Fin s)
    (tests : Finset (IntegerPolynomial q)) : Prop :=
  ∀ P ∈ tests, MvPolynomial.rename ι P ∈ Dm

/-! ## Row templates (04:113–126) -/

/-- A row template `A_R`: column `k` holds `0` (`none`) or the monic monomial `∏_i p_i^{e_i}`
(`some e`) in the formal prime slots. No slot occurs in two columns, and some column is
nonzero. -/
structure RowTemplate (m q : ℕ) where
  entry : Fin m → Option (Fin q → ℕ)
  support_nonempty : (Finset.univ.filter fun k => (entry k).isSome).Nonempty
  slots_disjoint : ∀ k k' e e', k ≠ k' → entry k = some e → entry k' = some e' →
    ∀ i, e i = 0 ∨ e' i = 0

namespace RowTemplate

variable {m q : ℕ} (T : RowTemplate m q)

/-- The nonzero columns. -/
def support : Finset (Fin m) := Finset.univ.filter fun k => (T.entry k).isSome

/-- The anchor `a(R)=max{k : A_{R,k} ≠ 0}`. -/
def anchor : Fin m := T.support.max' T.support_nonempty

/-- The entry `A_{R,k}(p)` at a prime tuple. -/
def value (p : Fin q → ℕ) (k : Fin m) : ℚ :=
  (T.entry k).elim 0 fun e => ∏ i, (p i : ℚ) ^ e i

/-- The entry `A_{R,k}` as an integer polynomial in the prime slots. -/
def poly (k : Fin m) : IntegerPolynomial q :=
  (T.entry k).elim 0 fun e => MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm e) 1

/-- Parallelity over the rational function field in the prime slots: for monic monomial
vectors, equal supports and a constant exponent difference. -/
def Parallel (T T' : RowTemplate m q) : Prop :=
  T.support = T'.support ∧ ∃ δ : Fin q → ℤ, ∀ k e e', T.entry k = some e →
    T'.entry k = some e' → ∀ i, (e' i : ℤ) = e i + δ i

end RowTemplate

/-- The form `ℓ_R(v)=∑_k (c_k/c_{a(R)})A_{R,k}(p)v_k` of equation
`eq:correlation-row-template`, at a rational vector `v`. -/
def rowForm {m q : ℕ} (c : Fin m → ℚ) (T : RowTemplate m q) (p : Fin q → ℕ)
    (v : Fin m → ℚ) : ℚ :=
  ∑ k, c k / c T.anchor * T.value p k * v k

/-- The response `A_R·v` of a template to an integer polynomial vector. -/
def templateResponse {m q : ℕ} (T : RowTemplate m q) (v : Fin m → IntegerPolynomial q) :
    IntegerPolynomial q :=
  ∑ k, T.poly k * v k

/-- A pairwise nonparallel family of row templates with a distinguished row `star`. -/
structure RowShape (m q r : ℕ) where
  row : Fin r → RowTemplate m q
  star : Fin r
  nonparallel : ∀ R I, R ≠ I → ¬ (row R).Parallel (row I)

/-- The nontarget rows `R ≠ *`; their number is `d=|ℛ|-1`. -/
abbrev NonTarget {m q r : ℕ} (Sh : RowShape m q r) := {R : Fin r // R ≠ Sh.star}

/-- All nonzero `2×2` minors `A_{R,j}A_{I,k}-A_{R,k}A_{I,j}` of pairs of templates. -/
def templateMinors {m q r : ℕ} (Sh : RowShape m q r) : Finset (IntegerPolynomial q) :=
  (Finset.univ.image fun x : Fin r × Fin r × Fin m × Fin m =>
    (Sh.row x.1).poly x.2.2.1 * (Sh.row x.2.1).poly x.2.2.2 -
      (Sh.row x.1).poly x.2.2.2 * (Sh.row x.2.1).poly x.2.2.1).filter (· ≠ 0)

/-- Expectation of `∏_R f_R(ℓ_R(z))` under independent pool slots and pivot variables; the
right side of equation `eq:mask-removal-output`. -/
def rowCorrelation {K m q r s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ)
    (Sh : RowShape m q r) (f : Fin r → (Fin q → ℕ) → ℤ → ℝ) : ℝ :=
  gapSlotAverage S C.gap N fun p =>
    ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
      ∏ R, atQ (f R p)
        (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p fun k => (z k : ℚ))

/-! ## Polynomial directions and integer translations (04:316–418) -/

/-- Integer polynomial vectors `w_R` (`R ≠ *`) and `w_0` of Lemma `lem:row-directions`. -/
structure RowDirections {m q r : ℕ} (Sh : RowShape m q r) where
  w : Fin r → Fin m → IntegerPolynomial q
  w0 : Fin m → IntegerPolynomial q

namespace RowDirections

variable {m q r : ℕ} {Sh : RowShape m q r} (dirs : RowDirections Sh)

/-- `A_Rw_R=0` and `A_Iw_R ≠ 0` (`I ≠ R`) for `R ≠ *`; `A_*w_0=0` and `A_Iw_0 ≠ 0`
(`I ≠ *`). -/
def Valid : Prop :=
  (∀ R, R ≠ Sh.star → templateResponse (Sh.row R) (dirs.w R) = 0) ∧
  (∀ R I, R ≠ Sh.star → I ≠ R → templateResponse (Sh.row I) (dirs.w R) ≠ 0) ∧
  templateResponse (Sh.row Sh.star) dirs.w0 = 0 ∧
  (∀ I, I ≠ Sh.star → templateResponse (Sh.row I) dirs.w0 ≠ 0)

/-- The target response `d_R=A_*w_R`. -/
def targetResponse (R : Fin r) : IntegerPolynomial q :=
  templateResponse (Sh.row Sh.star) (dirs.w R)

/-- `D=∏_{R≠*}d_R`. -/
def poly : IntegerPolynomial q :=
  ∏ R ∈ Finset.univ.erase Sh.star, dirs.targetResponse R

/-- The nonzero responses `A_Iw_R` and `A_Iw_0`. -/
def responses : Finset (IntegerPolynomial q) :=
  ((Finset.univ.image fun x : Fin r × Fin r => templateResponse (Sh.row x.1) (dirs.w x.2)) ∪
    Finset.univ.image fun I : Fin r => templateResponse (Sh.row I) dirs.w0).filter (· ≠ 0)

/-- The polynomial tests of Lemma `lem:row-directions` (04:375–377): `D`, all nonzero responses
and all nonzero template minors. -/
def tests : Finset (IntegerPolynomial q) :=
  insert dirs.poly (dirs.responses ∪ templateMinors Sh)

/-- `v_{R,k}=M(p)(c_{a_*}/c_k)w_{R,k}(p)/d_R(p)`, equation
`eq:correlation-integer-directions`. -/
def translation (c : Fin m → ℚ) (Mp : ℕ) (p : Fin q → ℕ) (R : Fin r) (k : Fin m) : ℚ :=
  (Mp : ℚ) * (c (Sh.row Sh.star).anchor / c k) *
    ((evalIntegerPolynomial (dirs.w R k) (fun i => (p i : ℤ)) : ℚ) /
      (evalIntegerPolynomial (dirs.targetResponse R) (fun i => (p i : ℤ)) : ℚ))

/-- `v_{0,k}=M(c_{a_*}/c_k)w_{0,k}(p)`, equation `eq:correlation-integer-directions`. -/
def rootTranslation (c : Fin m → ℚ) (M : ℕ) (p : Fin q → ℕ) (k : Fin m) : ℚ :=
  (M : ℚ) * (c (Sh.row Sh.star).anchor / c k) *
    (evalIntegerPolynomial (dirs.w0 k) (fun i => (p i : ℤ)) : ℚ)

end RowDirections

/-- `x` is a nonzero integer, and a unit at every prime `w<π≤V` at which no test polynomial
vanishes. -/
def ResponseUnit {q : ℕ} (N V : ℕ) (tests : Finset (IntegerPolynomial q)) (p : Fin q → ℕ)
    (x : ℚ) : Prop :=
  x ≠ 0 ∧ x.den = 1 ∧ ∀ π : ℕ, π.Prime → N + 1 < π → π ≤ V →
    (∀ P ∈ tests, ¬ ((π : ℤ) ∣ evalIntegerPolynomial P (fun i => (p i : ℤ)))) →
      ¬ ((π : ℤ) ∣ x.num)

/-- The conclusions of Lemma `lem:row-directions` at one good tuple (04:337–354): `v_R` and
`v_0` lie in `Wℤ^m` and have size at most `(P_l^++V_l)^B`, as does `M(p)`; the responses
`ℓ_*(v_R)=M(p)`, `ℓ_R(v_R)=0`, `ℓ_*(v_0)=0`; every other response is a nonzero integer that is
a unit at `w<π≤V_l` off the tests. -/
def IntegerDirectionFacts {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ)
    {Sh : RowShape m q r} (dirs : RowDirections Sh) (tests : Finset (IntegerPolynomial q))
    (B : ℕ) (p : Fin q → ℕ) : Prop :=
  let c := chainScale S.core.parameters C a N
  let W := primorial (N + 1)
  let Mp := directionModulus S N dirs.poly p
  let V := FromArithmetic.masterScaleV S.core.parameters N C.gap
  let size := (S.primeStage.pool N C.gap).upper + V
  (∀ R k, R ≠ Sh.star → ∃ v : ℤ, (v : ℚ) = dirs.translation c Mp p R k ∧
    (W : ℤ) ∣ v ∧ v.natAbs ≤ size ^ B) ∧
  (∀ k, ∃ v : ℤ, (v : ℚ) = dirs.rootTranslation c (S.core.parameters.M N) p k ∧
    (W : ℤ) ∣ v ∧ v.natAbs ≤ size ^ B) ∧
  Mp ≤ size ^ B ∧
  (∀ R, R ≠ Sh.star → rowForm c (Sh.row Sh.star) p (dirs.translation c Mp p R) = Mp) ∧
  (∀ R, R ≠ Sh.star → rowForm c (Sh.row R) p (dirs.translation c Mp p R) = 0) ∧
  rowForm c (Sh.row Sh.star) p (dirs.rootTranslation c (S.core.parameters.M N) p) = 0 ∧
  (∀ R I, R ≠ Sh.star → I ≠ R →
    ResponseUnit N V tests p (rowForm c (Sh.row I) p (dirs.translation c Mp p R))) ∧
  (∀ I, I ≠ Sh.star →
    ResponseUnit N V tests p
      (rowForm c (Sh.row I) p (dirs.rootTranslation c (S.core.parameters.M N) p)))

/-! ## Additive elimination (04:420–573) -/

section Additive

variable {K m q r s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

/-- The row correlation under the normalized good-tuple law (left side of equation
`eq:additive-elimination-output`). -/
def goodRowCorrelation (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) (f : Fin r → (Fin q → ℕ) → ℤ → ℝ) : ℝ :=
  goodSlotAverage S C.gap N (GoodTuple S C.gap N tests dirs.poly) fun p =>
    ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
      ∏ R, atQ (f R p)
        (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p fun k => (z k : ℚ))

/-- The target cube vertex `ℓ_*(z)+M(p)∑_{R≠*}u_R^{ω_R}`. -/
def targetVertex (c : Fin m → ℚ) (Sh : RowShape m q r) (p : Fin q → ℕ) (Mp : ℕ)
    (z : Fin m → ℚ) (u : NonTarget Sh → Fin 2 → ℕ) (ω : NonTarget Sh → Fin 2) : ℚ :=
  rowForm c (Sh.row Sh.star) p z + (Mp : ℚ) * ∑ R, (u R (ω R) : ℚ)

/-- The target cube `E_{p,z,u}∏_{ω∈{0,1}^d} h_p(ℓ_*(z)+M(p)∑_R u_R^{ω_R})` (right side of
equation `eq:additive-elimination-output`), with `u_R^0,u_R^1` uniform on `[0,L(p))`. -/
def additiveCube (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) (J0 : ℕ) (h : (Fin q → ℕ) → ℤ → ℝ) : ℝ :=
  goodSlotAverage S C.gap N (GoodTuple S C.gap N tests dirs.poly) fun p =>
    ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
      shiftAverage (NonTarget Sh) (shiftLength S C.gap J0 N dirs.poly p) fun u =>
        ∏ ω : NonTarget Sh → Fin 2,
          atQ (h p) (targetVertex (chainScale S.core.parameters C a N) Sh p
            (directionModulus S N dirs.poly p) (fun k => (z k : ℚ)) u ω)

/-- `B(z,u)=∏_ω(1+ν_{a_*}(ℓ_*(z)+M(p)∑_R u_R^{ω_R}))` (04:533–537). -/
def targetBound (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) {Sh : RowShape m q r} (dirs : RowDirections Sh) (p : Fin q → ℕ)
    (z : Fin m → ℚ) (u : NonTarget Sh → Fin 2 → ℕ) : ℝ :=
  ∏ ω : NonTarget Sh → Fin 2,
    (1 + atQ (chainWeight S.core.parameters C N (Sh.row Sh.star).anchor)
      (targetVertex (chainScale S.core.parameters C a N) Sh p
        (directionModulus S N dirs.poly p) z u ω))

/-- The retained weights `Ψ(z,u)` of equation `eq:correlation-retained-weights`: for each
nontarget row `I` and each choice `η` of the shifts in the other directions, one factor
`W_I(ℓ_I(z+∑_{R≠I}u_R^{η_R}v_R))`. -/
def retainedWeights (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) {Sh : RowShape m q r} (dirs : RowDirections Sh) (p : Fin q → ℕ)
    (z : Fin m → ℚ) (u : NonTarget Sh → Fin 2 → ℕ) : ℝ :=
  ∏ I : NonTarget Sh, ∏ η : {R : NonTarget Sh // R ≠ I} → Fin 2,
    (1 + atQ (chainWeight S.core.parameters C N (Sh.row I.1).anchor)
      (rowForm (chainScale S.core.parameters C a N) (Sh.row I.1) p fun k =>
        z k + ∑ R : {R : NonTarget Sh // R ≠ I}, (u R.1 (η R) : ℚ) *
          dirs.translation (chainScale S.core.parameters C a N)
            (directionModulus S N dirs.poly p) p R.1.1 k))

/-- `H(z,u)=E_{u_0}Ψ(z+v_0u_0,u)`, `u_0` uniform on `[0,R_l)` (04:530–537). -/
def averagedRetainedWeights (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) {Sh : RowShape m q r} (dirs : RowDirections Sh) (p : Fin q → ℕ)
    (z : Fin m → ℚ) (u : NonTarget Sh → Fin 2 → ℕ) : ℝ :=
  ((S.core.parameters.H N C.gap : ℝ))⁻¹ *
    ∑ u0 ∈ Finset.range (S.core.parameters.H N C.gap),
      retainedWeights S C a N dirs p
        (fun k => z k + (u0 : ℚ) *
          dirs.rootTranslation (chainScale S.core.parameters C a N) (S.core.parameters.M N) p k)
        u

/-- Expectation over good primes, pivots and shifts `u_R^0,u_R^1` uniform on `[0,L(p))`. -/
def eliminationAverage (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (N : ℕ)
    {Sh : RowShape m q r} (dirs : RowDirections Sh) (tests : Finset (IntegerPolynomial q))
    (J0 : ℕ) (F : (Fin q → ℕ) → (Fin m → ℚ) → (NonTarget Sh → Fin 2 → ℕ) → ℝ) : ℝ :=
  goodSlotAverage S C.gap N (GoodTuple S C.gap N tests dirs.poly) fun p =>
    ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
      shiftAverage (NonTarget Sh) (shiftLength S C.gap J0 N dirs.poly p) fun u =>
        F p (fun k => (z k : ℚ)) u

end Additive

/-! ## Cube templates and the one-variable cube test (04:576–611, 05:38–61) -/

/-- A cube type: `q` prime slots, cube order `d`, the polynomial `D` defining
`M(p)=M|D(p)|_{>w}`, and the finite list of nonzero tests defining the good tuples. The extra
type of §5 (dimension `s+1`, modulus `M`, no primes) is `q=0`, `D=1`, `tests={1}`. -/
structure CubeTemplate where
  q : ℕ
  d : ℕ
  D : IntegerPolynomial q
  tests : Finset (IntegerPolynomial q)
  D_mem : D ∈ tests
  tests_ne_zero : ∀ P ∈ tests, P ≠ 0

namespace CubeTemplate

variable (T : CubeTemplate) {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

/-- Good tuples of the type at gap `l`. -/
def Good (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) (N : ℕ) (p : Fin T.q → ℕ) : Prop :=
  GoodTuple S l N T.tests T.D p

/-- `M(p)=M|D(p)|_{>w}`. -/
def modulus (S : FromArithmetic.MasterScales K Aset s Dm) (N : ℕ) (p : Fin T.q → ℕ) : ℕ :=
  directionModulus S N T.D p

/-- `L(p)=⌊R_l/(J_0M(p))⌋`. -/
def length (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) (J0 N : ℕ) (p : Fin T.q → ℕ) : ℕ :=
  shiftLength S l J0 N T.D p

/-- The cube test of equation `eq:correlation-test`:
`E_{p,y,u}∏_{ω⊆[d]} h(y+M(p)∑_{j∈ω}(u_j^1-u_j^0))`, with `p` from the normalized good-tuple law
at gap `l`, `y` with law `μ_i`, and `u_j^0,u_j^1` uniform on `[0,L(p))`. -/
def cubeTest (S : FromArithmetic.MasterScales K Aset s Dm) (l i : Fin K) (J0 N : ℕ) (h : ℤ → ℝ) : ℝ :=
  goodSlotAverage S l N (T.Good S l N) fun p =>
    ∑' y : ℤ, harmonicLaw (S.core.parameters.X N i) (primorial (N + 1)) y *
      shiftAverage (Fin T.d) (T.length S l J0 N p) fun u =>
        ∏ ω : Finset (Fin T.d),
          h (y + (T.modulus S N p : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))

end CubeTemplate

/-! ## Numerical constants -/

/-- `q_mask=2^m-1`, the number of product masks. -/
def maskCount (m : ℕ) : ℕ := 2 ^ m - 1

/-- `K_m=q_mask 2^{q_mask}`, the row bound of Lemma `lem:mask-removal`. -/
def maskRowBound (m : ℕ) : ℕ := maskCount m * 2 ^ maskCount m

/-- The cube-root comparison law `k1_{y≡h (mod k)}μ(y)` of equation
`eq:correlation-root-progression`. -/
def progressionReference (μ : ℤ → ℝ) (k : ℕ) (h z : ℤ) : ℝ :=
  if (k : ℤ) ∣ z - h then (k : ℝ) * μ z else 0

end
end HindmanSumsProducts

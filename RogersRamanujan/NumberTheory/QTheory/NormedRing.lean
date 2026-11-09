module

public import RogersRamanujan.Algebra.Group.Units.Basic
import RogersRamanujan.Algebra.BigOperators.Group.Finset.Basic
public import RogersRamanujan.NumberTheory.QTheory.Defs
import RogersRamanujan.NumberTheory.QTheory.BinomialTheorem
import RogersRamanujan.NumberTheory.QTheory.Nonarchimedean
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
import RogersRamanujan.Topology.Algebra.InfiniteSum.NatInt
import RogersRamanujan.Topology.Algebra.InfiniteSum.Nonarchimedean
import RogersRamanujan.Topology.Algebra.TopologicallyNilpotent
public import RogersRamanujan.RingTheory.PowerSeries.DiscreteTopology
public import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.RingTheory.MvPowerSeries.LinearTopology

/-! # Evaluating formal power series in complete normed rings

The nonarchimedean theory of this project proves `q`-series identities in complete strongly
nonarchimedean rings, such as `R⟦X⟧` with its `X`-adic topology (see
`PowerSeries.DiscreteTopology`). A normed ring such as `ℝ` or `ℂ` is *not* nonarchimedean, so
those theorems do not apply to it directly. This file is the bridge from the formal identities in
`R⟦X⟧` to the corresponding analytic identities in a complete normed commutative ring `𝕜` with
`‖1‖ = 1` (for instance any complete normed field, such as `ℝ`, `ℂ` or `ℚ_[p]`), obtained by
evaluating at `X ↦ q`.

## Main definitions

For a ring homomorphism `φ : R →+* 𝕜`, which transports the coefficients, and `q : 𝕜`:

* `PowerSeries.evalAt φ q f = ∑' m, φ (coeff m f) * q ^ m`, the value of `f : R⟦X⟧` at `q`;
* `PowerSeries.enormAt φ q f = ∑' m, ‖φ (coeff m f) * q ^ m‖ₑ`, an `ℝ≥0∞`-valued `ℓ¹`-norm which
  controls it. It is subadditive, submultiplicative (`PowerSeries.enormAt_mul_le`) and lower
  semicontinuous for the `X`-adic topology (`PowerSeries.enormAt_le_of_tendsto`), which is what
  makes the transfer work.

On the power series with `enormAt φ q f ≠ ⊤`, `evalAt φ q` is additive and multiplicative.

## Main results

* `PowerSeries.hasSum_evalAt`: an `X`-adically convergent sum of formal power series evaluates
  termwise, provided the `ℓ¹`-norms of the terms are summable;
* `PowerSeries.evalAt_qPochhammerInf`: for `g` topologically nilpotent with `enormAt φ q g < 1`,
  the formal infinite product `(a; g)_∞` evaluates to the convergent infinite product
  `(evalAt φ q a; evalAt φ q g)_∞`;
* `PowerSeries.evalAt_bInv_qPochhammerInf`: if moreover `a` is topologically nilpotent with
  `enormAt φ q a < 1`, then the formal inverse of `(a; g)_∞` evaluates to the inverse of the
  infinite product, which is a unit (`PowerSeries.isUnit_qPochhammerInf_evalAt`);
* `isUnit_qPochhammerInf_of_norm_lt_one`: `(a; q)_∞` is a unit for `‖a‖ < 1` and `‖q‖ < 1`.

These are used to deduce, from their formal versions, the Jacobi triple product
(`RogersRamanujan/NumberTheory/QTheory/JacobiTripleProduct/NormedRing.lean`), the pentagonal number
theorem (`tsum_qPochhammerInf_self_of_norm_lt_one`) and the Rogers-Ramanujan identities
(`first_rogers_ramanujan_of_norm_lt_one`, `second_rogers_ramanujan_of_norm_lt_one`) in complete
normed commutative rings.
-/

@[expose] public section

open Filter Finset Topology SummationFilter
open QTheory PowerSeries.DiscreteTopology
open scoped ENNReal

private theorem enorm_mul_le_aux {𝕜 : Type*} [NormedRing 𝕜] (x y : 𝕜) :
    ‖x * y‖ₑ ≤ ‖x‖ₑ * ‖y‖ₑ := by
  simpa only [enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe] using nnnorm_mul_le x y

private theorem enorm_pow_le_aux {𝕜 : Type*} [NormedRing 𝕜] [NormOneClass 𝕜] (x : 𝕜) (n : ℕ) :
    ‖x ^ n‖ₑ ≤ ‖x‖ₑ ^ n := by
  simpa only [enorm_eq_nnnorm, ← ENNReal.coe_pow, ENNReal.coe_le_coe] using nnnorm_pow_le x n

namespace PowerSeries

variable {R : Type*} [CommRing R] {𝕜 : Type*} [NormedCommRing 𝕜] (φ : R →+* 𝕜) (q : 𝕜)

/-- The value at `q : 𝕜` of the formal power series `f`, with coefficients transported along
the ring homomorphism `φ`. Only meaningful when `enormAt φ q f ≠ ⊤`. -/
noncomputable def evalAt (f : R⟦X⟧) : 𝕜 := ∑' m, φ (f.coeff m) * q ^ m

/-- The `ℓ¹`-norm of `f` at `q`, valued in `ℝ≥0∞`: `∑ ‖φ (coeff m f) * q ^ m‖`. -/
noncomputable def enormAt (f : R⟦X⟧) : ℝ≥0∞ := ∑' m, ‖φ (f.coeff m) * q ^ m‖ₑ

variable {φ q}

theorem summable_norm_of_enormAt_ne_top {f : R⟦X⟧} (hf : enormAt φ q f ≠ ⊤) :
    Summable fun m ↦ ‖φ (f.coeff m) * q ^ m‖ :=
  tsum_enorm_ne_top_iff_summable_norm.mp hf

theorem enorm_evalAt_le (f : R⟦X⟧) : ‖evalAt φ q f‖ₑ ≤ enormAt φ q f := enorm_tsum_le_tsum_enorm

theorem norm_evalAt_le {f : R⟦X⟧} {B : ℝ} (hB : 0 ≤ B) (hf : enormAt φ q f ≤ .ofReal B) :
    ‖evalAt φ q f‖ ≤ B := by simpa [← ofReal_norm, hB] using (enorm_evalAt_le f).trans hf

/-! ### The `ℓ¹`-norm `enormAt` -/

@[simp] theorem enormAt_zero : enormAt φ q (0 : R⟦X⟧) = 0 := by simp [enormAt]

@[simp] theorem enormAt_C_mul_X_pow (c : R) (k : ℕ) :
    enormAt φ q (C c * X ^ k) = ‖φ c * q ^ k‖ₑ := by
  rw [enormAt, tsum_eq_single k] <;> simp +contextual [coeff_X_pow]

@[simp] theorem enormAt_C (c : R) : enormAt φ q (C c) = ‖φ c‖ₑ := by
  simpa using enormAt_C_mul_X_pow (φ := φ) (q := q) c 0

@[simp] theorem enormAt_C_mul_X (c : R) : enormAt φ q (C c * X) = ‖φ c * q‖ₑ := by
  simpa using enormAt_C_mul_X_pow (φ := φ) (q := q) c 1

@[simp] theorem enormAt_X_pow (k : ℕ) : enormAt φ q (X ^ k : R⟦X⟧) = ‖q ^ k‖ₑ := by
  simpa using enormAt_C_mul_X_pow (φ := φ) (q := q) 1 k

@[simp] theorem enormAt_X : enormAt φ q (X : R⟦X⟧) = ‖q‖ₑ := by simpa using enormAt_X_pow 1

@[simp] theorem enormAt_neg (f : R⟦X⟧) : enormAt φ q (-f) = enormAt φ q f := by simp [enormAt]

@[simp] theorem enormAt_units_smul (u : ℤˣ) (f : R⟦X⟧) : enormAt φ q (u • f) = enormAt φ q f := by
  obtain rfl | rfl := Int.units_eq_one_or u <;> simp

theorem enormAt_add_le (f g : R⟦X⟧) : enormAt φ q (f + g) ≤ enormAt φ q f + enormAt φ q g :=
  (ENNReal.tsum_le_tsum fun _ ↦ by simp only [map_add, add_mul, enorm_add_le]).trans_eq
    ENNReal.tsum_add

theorem enormAt_sub_le (f g : R⟦X⟧) : enormAt φ q (f - g) ≤ enormAt φ q f + enormAt φ q g := by
  simpa [sub_eq_add_neg] using enormAt_add_le f (-g)

/-- The Cauchy product formula for `ℝ≥0∞`-valued series. -/
private theorem tsum_sum_antidiagonal_mul (a b : ℕ → ℝ≥0∞) :
    ∑' n, ∑ p ∈ antidiagonal n, a p.1 * b p.2 = (∑' m, a m) * (∑' m, b m) := by
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_prod,
    ← Finset.sigmaAntidiagonalEquivProd.tsum_eq, ENNReal.tsum_sigma']
  exact tsum_congr fun n ↦ (Finset.tsum_subtype _ _).symm

/-- `enormAt` is submultiplicative. -/
theorem enormAt_mul_le (f g : R⟦X⟧) : enormAt φ q (f * g) ≤ enormAt φ q f * enormAt φ q g := by
  refine (ENNReal.tsum_le_tsum fun n ↦ ?_).trans_eq (tsum_sum_antidiagonal_mul _ _)
  rw [coeff_mul, map_sum, sum_mul]
  refine (enorm_sum_le _ _).trans (sum_le_sum fun p hp ↦ ?_)
  rw [map_mul, ← mem_antidiagonal.mp hp, pow_add, mul_mul_mul_comm]
  exact enorm_mul_le_aux _ _

theorem enormAt_mul_ne_top {f g : R⟦X⟧} (hf : enormAt φ q f ≠ ⊤) (hg : enormAt φ q g ≠ ⊤) :
    enormAt φ q (f * g) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top hf hg) (enormAt_mul_le f g)

theorem enormAt_sub_ne_top {f g : R⟦X⟧} (hf : enormAt φ q f ≠ ⊤) (hg : enormAt φ q g ≠ ⊤) :
    enormAt φ q (f - g) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) (enormAt_sub_le f g)

/-- Weierstrass-type estimate: `‖∏ (1 + uᵢ) - 1‖ + 1 ≤ ∏ (‖uᵢ‖ + 1)`. -/
theorem enormAt_prod_one_add_sub_one_le {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧) :
    enormAt φ q (∏ i ∈ s, (1 + f i) - 1) + 1 ≤ ∏ i ∈ s, (enormAt φ q (f i) + 1) := by
  refine (le_prod_of_submultiplicative (fun x ↦ enormAt φ q (x - 1) + 1) (by simp)
    (fun x y ↦ ?_) s (1 + f ·)).trans_eq (by simp)
  rw [show x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) by ring]
  grw [enormAt_add_le, enormAt_add_le, enormAt_mul_le]
  exact le_of_eq (by ring)

/-- The `ℓ¹`-norm is lower semicontinuous for the `X`-adic topology. -/
theorem enormAt_le_of_tendsto {ι : Type*} {u : Filter ι} [u.NeBot] {F : ι → R⟦X⟧} {f : R⟦X⟧}
    (hF : Tendsto F u (𝓝 f)) {B : ℝ≥0∞} (hB : ∀ i, enormAt φ q (F i) ≤ B) : enormAt φ q f ≤ B := by
  refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  obtain ⟨i, hi⟩ := ((eventually_all_finset (range n)).mpr fun m _ ↦
    (tendsto_iff_coeff_eventually_const F u f).mp hF m).exists
  exact (sum_congr rfl fun m hm ↦ by rw [hi m hm]).trans_le ((ENNReal.sum_le_tsum _).trans (hB i))

section Sums

variable {ι : Type*} {F : ι → R⟦X⟧} {G : R⟦X⟧}

/-- Coefficientwise, an `X`-adically convergent sum of power series converges in `𝕜`. -/
theorem hasSum_map_coeff (h : HasSum F G) (m : ℕ) :
    HasSum (fun i ↦ φ ((F i).coeff m)) (φ (G.coeff m)) :=
  EventuallyEq.tendsto <| ((tendsto_iff_coeff_eventually_const _ _ _).mp h m).mono
    fun s hs ↦ by simp [← map_sum, hs]

theorem enormAt_le_tsum_of_hasSum (h : HasSum F G) : enormAt φ q G ≤ ∑' i, enormAt φ q (F i) :=
  (ENNReal.tsum_le_tsum fun m ↦ ((hasSum_map_coeff h m).mul_right (q ^ m)).tsum_eq ▸
    enorm_tsum_le_tsum_enorm).trans_eq ENNReal.tsum_comm

end Sums

/-! ### Evaluation of monomials -/

@[simp] theorem evalAt_zero : evalAt φ q (0 : R⟦X⟧) = 0 := by simp [evalAt]

@[simp] theorem evalAt_C_mul_X_pow (c : R) (k : ℕ) : evalAt φ q (C c * X ^ k) = φ c * q ^ k := by
  rw [evalAt, tsum_eq_single k] <;> simp +contextual [coeff_X_pow]

@[simp] theorem evalAt_C (c : R) : evalAt φ q (C c) = φ c := by
  simpa using evalAt_C_mul_X_pow (φ := φ) (q := q) c 0

@[simp] theorem evalAt_C_mul_X (c : R) : evalAt φ q (C c * X) = φ c * q := by
  simpa using evalAt_C_mul_X_pow (φ := φ) (q := q) c 1

@[simp] theorem evalAt_one : evalAt φ q (1 : R⟦X⟧) = 1 := by rw [← map_one C, evalAt_C, map_one]

@[simp] theorem evalAt_X_pow (k : ℕ) : evalAt φ q (X ^ k : R⟦X⟧) = q ^ k := by
  simpa using evalAt_C_mul_X_pow (φ := φ) (q := q) 1 k

@[simp] theorem evalAt_X : evalAt φ q (X : R⟦X⟧) = q := by
  simpa using evalAt_X_pow (φ := φ) (q := q) 1

@[simp] theorem evalAt_neg (f : R⟦X⟧) : evalAt φ q (-f) = -evalAt φ q f := by
  simp [evalAt, tsum_neg]

@[simp] theorem evalAt_units_smul (u : ℤˣ) (f : R⟦X⟧) : evalAt φ q (u • f) = u • evalAt φ q f := by
  obtain rfl | rfl := Int.units_eq_one_or u <;> simp

/-! ### Bounds when `‖1‖ = 1` -/

section NormOneClass

variable [NormOneClass 𝕜]

@[simp] theorem enormAt_one : enormAt φ q (1 : R⟦X⟧) = 1 := by
  simpa using enormAt_C (φ := φ) (q := q) 1

theorem enormAt_X_pow_le (k : ℕ) : enormAt φ q (X ^ k : R⟦X⟧) ≤ ‖q‖ₑ ^ k :=
  (enormAt_X_pow k).trans_le (enorm_pow_le_aux q k)

theorem enormAt_le_enormAt_sub_one_add_one (f : R⟦X⟧) :
    enormAt φ q f ≤ enormAt φ q (f - 1) + 1 := by
  simpa using enormAt_add_le (φ := φ) (q := q) (f - 1) 1

theorem enormAt_pow_le (f : R⟦X⟧) : ∀ n : ℕ, enormAt φ q (f ^ n) ≤ enormAt φ q f ^ n
  | 0 => by simp
  | n + 1 => by grw [pow_succ, pow_succ, enormAt_mul_le, enormAt_pow_le f n]

theorem enormAt_mul_pow_le (f g : R⟦X⟧) (n : ℕ) :
    enormAt φ q (f * g ^ n) ≤ enormAt φ q f * enormAt φ q g ^ n := by
  grw [enormAt_mul_le, enormAt_pow_le]

theorem enormAt_prod_le {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧) :
    enormAt φ q (∏ i ∈ s, f i) ≤ ∏ i ∈ s, enormAt φ q (f i) :=
  le_prod_of_submultiplicative _ enormAt_one.le enormAt_mul_le s f

theorem enormAt_pow_ne_top {f : R⟦X⟧} (hf : enormAt φ q f ≠ ⊤) (n : ℕ) :
    enormAt φ q (f ^ n) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.pow_ne_top hf) (enormAt_pow_le f n)

/-- The geometric series bound `‖(1 - t)⁻¹‖ ≤ (1 - ‖t‖)⁻¹`. -/
theorem enormAt_bInv_one_sub_le {t : R⟦X⟧} (ht : IsTopologicallyNilpotent t) :
    enormAt φ q (bInv (1 - t)) ≤ (1 - enormAt φ q t)⁻¹ := by
  rw [ht.bInv_one_sub_eq, ← ENNReal.tsum_geometric]
  exact (enormAt_le_tsum_of_hasSum ht.summable_pow.hasSum).trans
    (ENNReal.tsum_le_tsum (enormAt_pow_le t))

end NormOneClass

/-! ### Evaluation in a complete normed ring -/

section CompleteSpace

variable [CompleteSpace 𝕜]

theorem summable_of_enormAt_ne_top {f : R⟦X⟧} (hf : enormAt φ q f ≠ ⊤) :
    Summable fun m ↦ φ (f.coeff m) * q ^ m :=
  .of_enorm hf

theorem evalAt_add {f g : R⟦X⟧} (hf : enormAt φ q f ≠ ⊤) (hg : enormAt φ q g ≠ ⊤) :
    evalAt φ q (f + g) = evalAt φ q f + evalAt φ q g := by
  simp [evalAt, add_mul, (summable_of_enormAt_ne_top hf).tsum_add (summable_of_enormAt_ne_top hg)]

theorem evalAt_sub {f g : R⟦X⟧} (hf : enormAt φ q f ≠ ⊤) (hg : enormAt φ q g ≠ ⊤) :
    evalAt φ q (f - g) = evalAt φ q f - evalAt φ q g := by
  rw [sub_eq_add_neg, evalAt_add hf (by simpa using hg), evalAt_neg, ← sub_eq_add_neg]

theorem evalAt_mul {f g : R⟦X⟧} (hf : enormAt φ q f ≠ ⊤) (hg : enormAt φ q g ≠ ⊤) :
    evalAt φ q (f * g) = evalAt φ q f * evalAt φ q g := by
  rw [evalAt, evalAt, evalAt, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_of_enormAt_ne_top hf) (summable_norm_of_enormAt_ne_top hg)]
  simp_rw [coeff_mul, map_sum, map_mul, sum_mul]
  exact tsum_congr fun n ↦ sum_congr rfl fun p hp ↦ by grind [mem_antidiagonal]

theorem evalAt_mul_evalAt_bInv {f : R⟦X⟧} (hu : IsUnit f) (hf : enormAt φ q f ≠ ⊤)
    (hf' : enormAt φ q (bInv f) ≠ ⊤) : evalAt φ q f * evalAt φ q (bInv f) = 1 := by
  rw [← evalAt_mul hf hf', hu.mul_bInv_cancel, evalAt_one]

theorem evalAt_bInv {f : R⟦X⟧} (hu : IsUnit f) (hf : enormAt φ q f ≠ ⊤)
    (hf' : enormAt φ q (bInv f) ≠ ⊤) : evalAt φ q (bInv f) = bInv (evalAt φ q f) :=
  (bInv_eq_of_mul_eq_one (evalAt_mul_evalAt_bInv hu hf hf')).symm

theorem isUnit_evalAt {f : R⟦X⟧} (hu : IsUnit f) (hf : enormAt φ q f ≠ ⊤)
    (hf' : enormAt φ q (bInv f) ≠ ⊤) : IsUnit (evalAt φ q f) :=
  .of_mul_eq_one _ (evalAt_mul_evalAt_bInv hu hf hf')

/-- Transfer of an `X`-adically convergent sum to a convergent sum in `𝕜`. -/
theorem hasSum_evalAt {ι : Type*} {F : ι → R⟦X⟧} {G : R⟦X⟧} (h : HasSum F G)
    (hF : ∑' i, enormAt φ q (F i) ≠ ⊤) : HasSum (fun i ↦ evalAt φ q (F i)) (evalAt φ q G) := by
  have hc : Summable fun p : ι × ℕ ↦ φ ((F p.1).coeff p.2) * q ^ p.2 :=
    .of_enorm <| by rwa [ENNReal.tsum_prod']
  rw [evalAt, (((Equiv.prodComm ℕ ι).hasSum_iff.mpr hc.hasSum).prod_fiberwise fun m ↦
    (hasSum_map_coeff h m).mul_right (q ^ m)).tsum_eq]
  exact hc.hasSum.prod_fiberwise fun i ↦ (hc.prod_factor i).hasSum

variable [NormOneClass 𝕜]

theorem evalAt_pow {f : R⟦X⟧} (hf : enormAt φ q f ≠ ⊤) :
    ∀ n : ℕ, evalAt φ q (f ^ n) = evalAt φ q f ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ, evalAt_mul (enormAt_pow_ne_top hf n) hf, evalAt_pow hf n, pow_succ]

theorem evalAt_prod {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧)
    (hf : ∀ i ∈ s, enormAt φ q (f i) ≠ ⊤) :
    evalAt φ q (∏ i ∈ s, f i) = ∏ i ∈ s, evalAt φ q (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    obtain ⟨hfi, hfs⟩ := (forall_mem_cons hi _).mp hf
    rw [prod_cons, prod_cons, evalAt_mul hfi
      (ne_top_of_le_ne_top (ENNReal.prod_ne_top hfs) (enormAt_prod_le s f)), ih hfs]

end CompleteSpace

/-! ### Transfer of the `q`-Pochhammer symbol -/

private theorem prod_mul_pow_add_one_le_exp {A G : ℝ≥0∞} (hA : A ≠ ⊤) (hG : G < 1) (N : ℕ) :
    ∏ i ∈ range N, (A * G ^ i + 1) ≤ .ofReal (Real.exp (A.toReal / (1 - G.toReal))) := by
  have key (i : ℕ) : A * G ^ i + 1 = .ofReal (1 + A.toReal * G.toReal ^ i) := by
    rw [ENNReal.ofReal_add zero_le_one (by positivity)]
    simp [ENNReal.ofReal_mul, ENNReal.ofReal_pow, hA, hG.ne_top, add_comm]
  rw [prod_congr rfl fun i _ ↦ key i, ← ENNReal.ofReal_prod_of_nonneg fun i _ ↦ by positivity]
  exact ENNReal.ofReal_le_ofReal <| (Real.prod_one_add_le_exp_sum _ fun i ↦ by positivity).trans <|
    Real.exp_le_exp.mpr <| sum_le_hasSum _ (fun i _ ↦ by positivity) <| .mul_left _ <|
      hasSum_geometric_of_lt_one ENNReal.toReal_nonneg <| ENNReal.toReal_lt_of_lt_ofReal (by simpa)

private theorem inv_one_sub_le {y A : ℝ≥0∞} (hy : y ≤ A) : (1 - y)⁻¹ ≤ y * (1 - A)⁻¹ + 1 := by
  rw [← ENNReal.tsum_geometric y, tsum_eq_zero_add' ENNReal.summable,
    ENNReal.tsum_geometric_add_one, pow_zero, add_comm]
  gcongr

private theorem prod_inv_one_sub_mul_pow_le_exp {A G : ℝ≥0∞} (hA : A < 1) (hG : G < 1) (N : ℕ) :
    ∏ i ∈ range N, (1 - A * G ^ i)⁻¹ ≤
      .ofReal (Real.exp ((A * (1 - A)⁻¹).toReal / (1 - G.toReal))) := by
  refine (prod_le_prod' fun i _ ↦ ?_).trans (prod_mul_pow_add_one_le_exp ?_ hG N)
  · rw [mul_right_comm]
    exact inv_one_sub_le (mul_le_of_le_one_right' (pow_le_one' hG.le i))
  · exact ENNReal.mul_ne_top hA.ne_top (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hA).ne')

section qPochhammer

variable [NormOneClass 𝕜] {a g : R⟦X⟧}

/-- Weierstrass bound for the truncated `q`-Pochhammer symbol. -/
theorem enormAt_qPochhammer_sub_one_add_one_le (N : ℕ) :
    enormAt φ q ((a; g)_N - 1) + 1 ≤ ∏ i ∈ range N, (enormAt φ q a * enormAt φ q g ^ i + 1) := by
  simp only [qPochhammer, sub_eq_add_neg (1 : R⟦X⟧)]
  refine (enormAt_prod_one_add_sub_one_le _ _).trans (prod_le_prod' fun i _ ↦ ?_)
  grw [enormAt_neg, enormAt_mul_pow_le]

theorem enormAt_qPochhammer_ne_top (ha : enormAt φ q a ≠ ⊤) (hg : enormAt φ q g ≠ ⊤) (N : ℕ) :
    enormAt φ q (a; g)_N ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.prod_ne_top fun i _ ↦ by finiteness) <|
    (enormAt_le_enormAt_sub_one_add_one _).trans (enormAt_qPochhammer_sub_one_add_one_le N)

theorem evalAt_qPochhammer [CompleteSpace 𝕜] (ha : enormAt φ q a ≠ ⊤) (hg : enormAt φ q g ≠ ⊤)
    (N : ℕ) : evalAt φ q (a; g)_N = (evalAt φ q a; evalAt φ q g)_N := by
  have hag (i : ℕ) := enormAt_mul_ne_top ha (enormAt_pow_ne_top hg i)
  rw [qPochhammer, evalAt_prod _ _ fun i _ ↦ enormAt_sub_ne_top (by simp) (hag i)]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [evalAt_sub (by simp) (hag i), evalAt_one, evalAt_mul ha (enormAt_pow_ne_top hg i),
    evalAt_pow hg]

variable (hg : IsTopologicallyNilpotent g) (ha : enormAt φ q a ≠ ⊤) (hg1 : enormAt φ q g < 1)
include hg ha hg1

/-- Weierstrass bound for the infinite `q`-Pochhammer symbol. -/
theorem enormAt_qPochhammerInf_sub_one_le :
    enormAt φ q ((a; g)_∞ - 1) ≤
      .ofReal (Real.exp ((enormAt φ q a).toReal / (1 - (enormAt φ q g).toReal)) - 1) := by
  rw [ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_one]
  exact enormAt_le_of_tendsto ((tendsto_qPochhammer_qPochhammerInf hg).sub tendsto_const_nhds)
    fun N ↦ ENNReal.le_sub_of_add_le_right ENNReal.one_ne_top <|
      (enormAt_qPochhammer_sub_one_add_one_le N).trans (prod_mul_pow_add_one_le_exp ha hg1 N)

theorem enormAt_qPochhammerInf_ne_top : enormAt φ q (a; g)_∞ ≠ ⊤ :=
  ne_top_of_le_ne_top (by finiteness) <| (enormAt_le_enormAt_sub_one_add_one _).trans <|
    add_le_add (enormAt_qPochhammerInf_sub_one_le hg ha hg1) le_rfl

variable [CompleteSpace 𝕜]

theorem norm_evalAt_qPochhammerInf_sub_one_le :
    ‖evalAt φ q (a; g)_∞ - 1‖ ≤
      Real.exp ((enormAt φ q a).toReal / (1 - (enormAt φ q g).toReal)) - 1 := by
  have hG : (enormAt φ q g).toReal < 1 := ENNReal.toReal_lt_of_lt_ofReal (by simpa using hg1)
  refine (norm_evalAt_le (sub_nonneg.2 <| Real.one_le_exp <| by bound)
    (enormAt_qPochhammerInf_sub_one_le hg ha hg1)).trans_eq' ?_
  rw [evalAt_sub (enormAt_qPochhammerInf_ne_top hg ha hg1) (by simp), evalAt_one]

/-- **Formal to analytic**: the formal infinite `q`-Pochhammer symbol `(a; g)_∞` evaluates to the
convergent infinite product `(evalAt φ q a; evalAt φ q g)_∞`. -/
theorem hasProd_evalAt_qPochhammerInf :
    HasProd (fun i ↦ 1 - evalAt φ q a * evalAt φ q g ^ i) (evalAt φ q (a; g)_∞)
      (conditional ℕ) := by
  have hg' := hg1.ne_top
  have ha' (N : ℕ) := enormAt_mul_ne_top ha (enormAt_pow_ne_top hg' N)
  have htend : Tendsto (fun N ↦ ‖evalAt φ q (a * g ^ N; g)_∞ - 1‖) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N ↦ enormAt φ q (a * g ^ N)) atTop (𝓝 0) := by
      refine tendsto_nhds_bot_mono' ?_ (enormAt_mul_pow_le a g)
      simpa using
        ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hg1) (.inr ha)
    refine squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun N ↦ norm_evalAt_qPochhammerInf_sub_one_le hg (ha' N) hg1) ?_
    simpa using
      ((((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0).div_const _).rexp).sub_const 1
  set E := Real.exp ((enormAt φ q a).toReal / (1 - (enormAt φ q g).toReal))
  have hbdd (N : ℕ) : ‖(evalAt φ q a; evalAt φ q g)_N‖ ≤ E := by
    rw [← evalAt_qPochhammer ha hg']
    exact norm_evalAt_le (Real.exp_nonneg _) <| (enormAt_le_enormAt_sub_one_add_one _).trans <|
      (enormAt_qPochhammer_sub_one_add_one_le N).trans (prod_mul_pow_add_one_le_exp ha hg1 N)
  rw [hasProd_conditional_iff_tendsto_prod, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) (by simpa using htend.const_mul E)
  rw [qPochhammerInf_eq_qPochhammer_mul_qPochhammerInf N hg,
    evalAt_mul (enormAt_qPochhammer_ne_top ha hg' N) (enormAt_qPochhammerInf_ne_top hg (ha' N) hg1),
    evalAt_qPochhammer ha hg']
  change ‖(evalAt φ q a; evalAt φ q g)_N - _‖ ≤ _
  rw [← mul_one_sub, ← norm_sub_rev 1]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hbdd N) (norm_nonneg _))

/-- `(a; g)_∞` evaluates to the infinite product `(evalAt φ q a; evalAt φ q g)_∞`. -/
theorem evalAt_qPochhammerInf : evalAt φ q (a; g)_∞ = (evalAt φ q a; evalAt φ q g)_∞ :=
  (hasProd_evalAt_qPochhammerInf hg ha hg1).tprod_eq.symm

end qPochhammer

/-! ### Transfer of the inverse of the `q`-Pochhammer symbol -/

section bInv

variable [NormOneClass 𝕜] {a g : R⟦X⟧} (ha : IsTopologicallyNilpotent a)
  (ha1 : enormAt φ q a < 1) (hg1 : enormAt φ q g < 1)
include ha ha1 hg1

/-- A uniform bound for the inverses of the truncated `q`-Pochhammer symbols. -/
theorem enormAt_bInv_qPochhammer_le (N : ℕ) :
    enormAt φ q (bInv (a; g)_N) ≤ .ofReal (Real.exp
      ((enormAt φ q a * (1 - enormAt φ q a)⁻¹).toReal / (1 - (enormAt φ q g).toReal))) := by
  rw [qPochhammer, bInv_prod fun i _ ↦ (ha.mul_right _).isUnit_one_sub]
  grw [enormAt_prod_le, ← prod_inv_one_sub_mul_pow_le_exp ha1 hg1 N]
  gcongr with i
  grw [enormAt_bInv_one_sub_le (ha.mul_right _), enormAt_mul_pow_le]

theorem enormAt_bInv_qPochhammer_ne_top (N : ℕ) : enormAt φ q (bInv (a; g)_N) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (enormAt_bInv_qPochhammer_le ha ha1 hg1 N)

variable (hg : IsTopologicallyNilpotent g)
include hg

theorem enormAt_bInv_qPochhammerInf_le :
    enormAt φ q (bInv (a; g)_∞) ≤ .ofReal (Real.exp
      ((enormAt φ q a * (1 - enormAt φ q a)⁻¹).toReal / (1 - (enormAt φ q g).toReal))) :=
  enormAt_le_of_tendsto
    (tendsto_bInv_qPochhammer_bInv_qPochhammerInf' hg (isUnit_qPochhammerInf ha hg))
    (enormAt_bInv_qPochhammer_le ha ha1 hg1)

theorem enormAt_bInv_qPochhammerInf_ne_top : enormAt φ q (bInv (a; g)_∞) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (enormAt_bInv_qPochhammerInf_le ha ha1 hg1 hg)

variable [CompleteSpace 𝕜]

theorem evalAt_bInv_qPochhammer (N : ℕ) :
    evalAt φ q (bInv (a; g)_N) = bInv (evalAt φ q a; evalAt φ q g)_N := by
  rw [evalAt_bInv (isUnit_qPochhammer ha hg N) (enormAt_qPochhammer_ne_top ha1.ne_top hg1.ne_top N)
    (enormAt_bInv_qPochhammer_ne_top ha ha1 hg1 N), evalAt_qPochhammer ha1.ne_top hg1.ne_top]

/-- The truncated `q`-Pochhammer symbol `(evalAt φ q a; evalAt φ q g)_N` is a unit. -/
theorem isUnit_qPochhammer_evalAt (N : ℕ) : IsUnit (evalAt φ q a; evalAt φ q g)_N := by
  rw [← evalAt_qPochhammer ha1.ne_top hg1.ne_top]
  exact isUnit_evalAt (isUnit_qPochhammer ha hg N)
    (enormAt_qPochhammer_ne_top ha1.ne_top hg1.ne_top N)
    (enormAt_bInv_qPochhammer_ne_top ha ha1 hg1 N)

/-- The formal inverse of `(a; g)_∞` evaluates to the inverse of the infinite product
`(evalAt φ q a; evalAt φ q g)_∞`. -/
theorem evalAt_bInv_qPochhammerInf :
    evalAt φ q (bInv (a; g)_∞) = bInv (evalAt φ q a; evalAt φ q g)_∞ := by
  rw [evalAt_bInv (isUnit_qPochhammerInf ha hg) (enormAt_qPochhammerInf_ne_top hg ha1.ne_top hg1)
    (enormAt_bInv_qPochhammerInf_ne_top ha ha1 hg1 hg), evalAt_qPochhammerInf hg ha1.ne_top hg1]

/-- The infinite product `(evalAt φ q a; evalAt φ q g)_∞` is a unit. -/
theorem isUnit_qPochhammerInf_evalAt : IsUnit (evalAt φ q a; evalAt φ q g)_∞ := by
  rw [← evalAt_qPochhammerInf hg ha1.ne_top hg1]
  exact isUnit_evalAt (isUnit_qPochhammerInf ha hg)
    (enormAt_qPochhammerInf_ne_top hg ha1.ne_top hg1)
    (enormAt_bInv_qPochhammerInf_ne_top ha ha1 hg1 hg)

end bInv

end PowerSeries

/-! ### Units among `q`-Pochhammer symbols -/

section Units

open PowerSeries

variable {𝕜 : Type*} [NormedCommRing 𝕜] [NormOneClass 𝕜] [CompleteSpace 𝕜] {a q : 𝕜}

/-- For `‖a‖ < 1` and `‖q‖ < 1`, the `q`-Pochhammer symbol `(a; q)_n` is a unit. -/
theorem isUnit_qPochhammer_of_norm_lt_one (ha : ‖a‖ < 1) (hq : ‖q‖ < 1) (n : ℕ) :
    IsUnit (a; q)_n := by
  have := isUnit_qPochhammer_evalAt (φ := RingHom.id 𝕜) (q := 1) (a := C a * X) (g := C q * X)
    (by simp) (by simpa [← ofReal_norm] using ha) (by simpa [← ofReal_norm] using hq) (by simp) n
  simpa using this

/-- For `‖a‖ < 1` and `‖q‖ < 1`, the infinite `q`-Pochhammer symbol `(a; q)_∞` is a unit. -/
theorem isUnit_qPochhammerInf_of_norm_lt_one (ha : ‖a‖ < 1) (hq : ‖q‖ < 1) : IsUnit (a; q)_∞ := by
  have := isUnit_qPochhammerInf_evalAt (φ := RingHom.id 𝕜) (q := 1) (a := C a * X) (g := C q * X)
    (by simp) (by simpa [← ofReal_norm] using ha) (by simpa [← ofReal_norm] using hq) (by simp)
  simpa using this

end Units

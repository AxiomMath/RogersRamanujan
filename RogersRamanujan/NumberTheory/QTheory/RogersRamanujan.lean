module

import RogersRamanujan.Algebra.BigOperators.Group.Finset.Basic
import RogersRamanujan.Algebra.BigOperators.Intervals
import RogersRamanujan.Algebra.Group.Units.Hom
import RogersRamanujan.Algebra.Ring.Parity
import RogersRamanujan.Data.Nat.Choose.Basic
public import RogersRamanujan.NumberTheory.QTheory.Bailey
import RogersRamanujan.NumberTheory.QTheory.Basic
import RogersRamanujan.NumberTheory.QTheory.JacobiTripleProduct.Basic
import RogersRamanujan.NumberTheory.QTheory.Nonarchimedean
import RogersRamanujan.NumberTheory.QTheory.NormedRing
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
import RogersRamanujan.RingTheory.PowerSeries.Evaluation
import RogersRamanujan.Topology.Algebra.InfiniteSum.NatInt
import RogersRamanujan.Topology.Algebra.TopologicallyNilpotent
import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul -- shake: keep
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt -- shake: keep

/-! # Rogers-Ramanujan identities via Bailey's lemma

## Main results

* `first_rogers_ramanujan`: `∑' j, q^(j^2) * (q; q)_j⁻¹ = 1 / [(q; q^5) * (q^4; q^5)]`
* `second_rogers_ramanujan`:
  `∑' j, q ^ (j*(j+1)) / (q; q)_j = 1 / [(q^2; q^5)_∞ * (q^3; q^5)_∞]`
* Their `HasSum` versions are also provided via `first_rogers_ramanujan_hasSum` and
  `second_rogers_ramanujan_hasSum`.
* `first_rogers_ramanujan_of_norm_lt_one`, `second_rogers_ramanujan_of_norm_lt_one`: the same
  identities for `‖q‖ < 1` in a complete normed commutative ring with `‖1‖ = 1`, obtained by
  evaluating the formal identities in `ℤ⟦X⟧` at `X ↦ q`; in a complete normed field such as `ℂ`,
  `first_rogers_ramanujan_div_of_norm_lt_one` and `second_rogers_ramanujan_div_of_norm_lt_one`
  state them with division.

## References

- S. O. Waarnar, *50 years of Bailey's lemma*
- G. Andrews, *The Theory of Partitions*
- G. Andrews, *q-Series: Their Development and Applications in Analysis, Number theory,*
              *Combinatorics, Physics, and Computer Algebra*
- P. Paule, *Concept of Bailey Chain*
-/

@[expose] public section

open Finset Nat Polynomial LaurentPolynomial Bailey
open Filter Topology NonarchimedeanAddGroup
open scoped QTheory

variable {R : Type*} [CommRing R]

namespace RogersRamanujan

/-- `α_n` for the first Rogers-Ramanujan Bailey pair: `α_0 = 1` and
`α_n = (-1)^n q^{n(n-1)/2} (1 + q^n)` for `n ≥ 1`. -/
def α₁ {R : Type*} [Ring R] (q : R) (n : ℕ) : R :=
  if n = 0 then 1 else (-1) ^ n * q ^ n.choose 2 * (1 + q ^ n)

/-- Transformed version of `α₁`. -/
def αt₁ {R : Type*} [Ring R] (q : R) (n : ℕ) : R := q ^ (n ^ 2) * α₁ q n

/-- `α_n` for the second Rogers-Ramanujan Bailey pair: `(-1)^n q^(nC2) [2n+1]_q`. -/
def α₂ (q : R) (n : ℕ) : R := (-1) ^ n * q ^ n.choose 2 * qInt q (2 * n + 1)

/-- Transformed version of `α₂`. -/
def αt₂ (q : R) (n : ℕ) : R := (-1) ^ n * q ^ (n ^ 2 + n + n.choose 2) * qInt q (2 * n + 1)

/-- `β_n` for the Rogers-Ramanujan Bailey pair: `β_0 = 1` and `β_n = 0` for `n ≥ 1`. -/
def β {R : Type*} [Zero R] [One R] (n : ℕ) : R := if n = 0 then 1 else 0

/-- Transformed version of `β`. -/
noncomputable def βt {R : Type*} [CommRing R] (q : R) (n : ℕ) : R := bInv (q; q)_n

@[simp] theorem map_α₁ {R S : Type*} [Ring R] [Ring S]
    {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) (q : R) (n : ℕ) :
    f (α₁ q n) = α₁ (f q) n := by obtain _ | n := n <;> simp [α₁]

@[simp] theorem map_α₂ {R S : Type*} [CommRing R] [CommRing S]
    {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) (q : R) (n : ℕ) :
    f (α₂ q n) = α₂ (f q) n := by simp [α₂]

@[simp] theorem map_β {R S : Type*} [Zero R] [One R] [Zero S] [One S]
    {F : Type*} [FunLike F R S] [ZeroHomClass F R S] [OneHomClass F R S] (f : F) (n : ℕ) :
    f (β n) = β n := by grind [β]

end RogersRamanujan

open RogersRamanujan

theorem α₁_mul_qChoose_eq_of_ne_zero {q : R} (hqu : IsUnit q) {n r : ℕ} (hrn : r ∈ Icc 1 n) :
    α₁ q r * qChoose q (2 * n) (n - r) =
    (-1) ^ n * q ^ (n + 1).choose 2 *
      (qChoose q (2 * n) (n - r) * (-bInv q ^ n) ^ (n - r) * q ^ (n - r).choose 2 +
      qChoose q (2 * n) (n + r) * (-bInv q ^ n) ^ (n + r) * q ^ (n + r).choose 2) := by
  trans (-1) ^ (2 * n + r) * qChoose q (2 * n) (n - r) *
    (↑(hqu.unit ^ (r.choose 2 : ℤ)) + ↑(hqu.unit ^ ((r + 1).choose 2 : ℤ)))
  · simp_rw [zpow_natCast, Units.val_pow_eq_pow_val, hqu.unit_spec]
    rw [pow_add, pow_mul, neg_one_pow_two, α₁, if_neg (by grind), choose_succ_two]
    ring
  have h₁ : ((r + 1).choose 2 : ℤ) = (n + 1).choose 2 - (n * (n - r) :) + (n - r).choose 2 := by
    rw [sub_add_eq_add_sub, ← cast_add, choose_succ_two_add_choose_two_of_ge (by grind)]
    simp [Nat.sub_sub_self (by grind : r ≤ n)]
  have h₂ : (r.choose 2 : ℤ) = (n + 1).choose 2 - (n * (n + r) :) + (n + r).choose 2 := by
    rw [sub_add_eq_add_sub, ← cast_add, choose_succ_two_add_choose_two_of_le (by grind)]
    simp
  rw [← qChoose_symm (k := n - r) (by grind), show 2 * n - (n - r) = n + r by grind,
    neg_pow _ (n - r), neg_one_pow_sub (by grind)]
  simp [h₁, h₂, zpow_add, zpow_sub, ← inv_pow, ← hqu.bInv_eq_inv_unit, pow_mul,
    -Int.natCast_mul, -cast_mul]
  ring_nf

theorem α₁_zero_mul_qChoose_eq {q : R} (hqu : IsUnit q) {n : ℕ} :
    α₁ q 0 * qChoose q (2 * n) (n - 0) =
    (-1) ^ n * q ^ (n + 1).choose 2 *
      (qChoose q (2 * n) n * (-bInv q ^ n) ^ n * q ^ n.choose 2) := by
  trans (-1) ^ (2 * n) * qChoose q (2 * n) n * (bInv q ^ (n ^ 2) * q ^ (n * n))
  · rw [pow_mul, neg_one_pow_two, sq, hqu.bInv_pow_mul_pow_same, α₁]
    simp
  rw [← choose_succ_two_add_choose_self_two]
  ring

/-- The `α₁`-sum identity when `q` is a unit. -/
theorem sum_α₁_mul_qChoose_eq_zero_of_isUnit {q : R} (hqu : IsUnit q) {n : ℕ} (hn : n ≠ 0) :
    ∑ r ∈ range (n + 1), α₁ q r * qChoose q (2 * n) (n - r) = 0 := by
  have h₁ : (bInv q ^ n; q)_(2 * n) = 0 := qPochhammer_pow_bInv_eq_zero (by grind)
  convert congr((-1) ^ n * q ^ (n + 1).choose 2 * $h₁).trans <| mul_zero _
  conv_lhs =>
    rw [range_eq_Ico, Ico_add_one_right_eq_Icc, ← sum_Ioc_add_eq_sum_Icc (by grind),
      α₁_zero_mul_qChoose_eq hqu, ← Icc_add_one_left_eq_Ioc, zero_add]
    simp +contextual only [α₁_mul_qChoose_eq_of_ne_zero hqu, mul_add]
  conv_rhs => rw [qPochhammer_eq_sum_qChoose, mul_sum, sum_range_two_mul_add_one_eq_fold]
  abel_nf

/-- **Key identity for the first Rogers-Ramanujan Bailey pair** -/
theorem sum_α₁_mul_qChoose_eq_zero (q : R) {n : ℕ} (hn : n ≠ 0) :
    ∑ r ∈ range (n + 1), α₁ q r * qChoose q (2 * n) (n - r) = 0 := by
  have key : ∑ r ∈ range (n + 1), α₁ (X (R := ℤ)) r * qChoose X (2 * n) (n - r) = 0 :=
    toLaurent_injective <| by simpa using sum_α₁_mul_qChoose_eq_zero_of_isUnit (isUnit_T 1) hn
  simpa using congr(Polynomial.aeval q $key)

/-- The Rogers-Ramanujan Bailey pair: `(α₁, β₁)` is a Bailey pair relative to `a = 1`. -/
theorem isBaileyPair_α₁_β {q : R} (hpu : ∀ k, IsUnit (q; q)_(k)) :
    IsBaileyPair 1 q (α₁ q) β := fun n ↦ by
  obtain rfl | hn := eq_or_ne n 0
  · simp [β, α₁]
  simp_rw [one_mul, mul_assoc, bInv_qPochhammer_mul_bInv_qPochhammer (hpu _)]
  simp +contextual only [show ∀ r ∈ range (n + 1), n - r + (n + r) = 2 * n by grind]
  simp_rw [← mul_assoc, ← sum_mul, sum_α₁_mul_qChoose_eq_zero q hn, zero_mul, β, if_neg hn]

theorem isBaileyPair_αt₁_βt {q : R} (hpu : ∀ k, IsUnit (q; q)_(k)) :
    IsBaileyPair 1 q (αt₁ q) (βt q) := qBaileyLemma_limit 1 q (α₁ q) β (αt₁ q) (βt q)
  (isBaileyPair_α₁_β hpu) hpu (by simpa) (by simp [αt₁]) (by simp [βt, β])

theorem eventually_αt₁_eq {R : Type*} [Ring R] (q : R) :
    αt₁ q =ᶠ[atTop] fun n ↦ (-1) ^ n * (q ^ (n ^ 2 + n.choose 2) * (1 + q ^ n)) := by
  rw [EventuallyEq, eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  simp_rw [αt₁, α₁, if_neg (by grind : n ≠ 0), pow_add, ← mul_assoc,
    ((Commute.neg_one_right q).pow_pow _ _).eq]

theorem tendsto_αt₁_zero
    {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    {q : R} (hq : IsTopologicallyNilpotent q) :
    Tendsto (αt₁ q) atTop (𝓝 0) := by
  rw [tendsto_congr' (eventually_αt₁_eq q)]
  refine Function.BoundedRange.neg_one_pow.mul_tendsto_zero ?_
  rw [show (0 : R) = 0 * (1 + 0) by grind]
  refine (hq.comp ?_).mul (hq.const_add _)
  exact tendsto_atTop_mono (by simp) (tendsto_pow_atTop (n := 2) (by grind))

/-! # Set-up for Second Rogers-Ramanujan Identity -/

theorem α₂_mul_one_sub {R : Type*} [CommRing R] (q : R) (r : ℕ) :
    α₂ q r * (1 - q) = (-1) ^ r * (q ^ r.choose 2 - q ^ (r + 2).choose 2) := by
  rw [α₂, mul_right_comm, mul_assoc, one_sub_mul_qInt, choose_succ_two, choose_succ_two]
  grind

theorem α₂_mul_one_sub_mul_qChoose_eq {q : R} (hqu : IsUnit q) {n r : ℕ} (hrn : r ∈ range (n + 1)) :
    α₂ q r * (1 - q) * qChoose q (2 * n + 1) (n - r) =
    (-1) ^ (n + 1) * q ^ (n + 2).choose 2 *
      (qChoose q (2 * n + 1) (n - r) * (-bInv q ^ (n + 1)) ^ (n - r) * q ^ (n - r).choose 2 +
      qChoose q (2 * n + 1) (n + 1 + r) * (-bInv q ^ (n + 1)) ^ (n + 1 + r) *
        q ^ (n + 1 + r).choose 2) := by
  trans (-1) ^ (2 * (n + 1) + r) * qChoose q (2 * n + 1) (n - r) *
    (↑(hqu.unit ^ (r.choose 2 : ℤ)) - ↑(hqu.unit ^ ((r + 2).choose 2 : ℤ)))
  · simp_rw [α₂_mul_one_sub, zpow_natCast, Units.val_pow_eq_pow_val, hqu.unit_spec]
    rw [pow_add, pow_mul, neg_one_pow_two]
    ring
  have h₁ : ((r + 2).choose 2 : ℤ) = (n + 2).choose 2 - ((n + 1) * (n - r) :) +
      (n - r).choose 2 := by
    rw [sub_add_eq_add_sub, ← cast_add, choose_succ_two_add_choose_two_of_ge (by grind)]
    simp [show n + 1 - (n - r) + 1 = r + 2 by grind]
  have h₂ : (r.choose 2 : ℤ) = (n + 2).choose 2 - ((n + 1) * (n + 1 + r) :) +
      (n + 1 + r).choose 2 := by
    rw [sub_add_eq_add_sub, ← cast_add, choose_succ_two_add_choose_two_of_le (by grind)]
    simp
  rw [← qChoose_symm (k := n - r) (by grind), show 2 * n + 1 - (n - r) = n + 1 + r by grind,
    neg_pow _ (n - r), neg_one_pow_sub (by grind)]
  simp [h₁, h₂, zpow_add, zpow_sub, ← inv_pow, ← hqu.bInv_eq_inv_unit, pow_mul,
    -Int.natCast_mul, -cast_mul]
  ring_nf

/-- The α₂-qChoose sum identity when `q` is a unit. Uses the q-binomial theorem
at `a = q^{-(M+1)}` and folding the sum in half. -/
theorem sum_α₂_mul_one_sub_mul_qChoose_eq_zero_of_isUnit
    {q : R} (hqu : IsUnit q) {n : ℕ} (hn : n ≠ 0) :
    ∑ r ∈ Finset.range (n + 1), α₂ q r * (1 - q) * qChoose q (2 * n + 1) (n - r) = 0 := by
  have h₁ : (bInv q ^ (n + 1); q)_(2 * n + 1) = 0 := qPochhammer_pow_bInv_eq_zero (by grind)
  convert congr((-1) ^ (n + 1) * q ^ (n + 2).choose 2 * $h₁).trans <| mul_zero _
  conv_lhs => simp +contextual only [α₂_mul_one_sub_mul_qChoose_eq hqu, mul_add]
  conv_rhs => rw [qPochhammer_eq_sum_qChoose, mul_sum, sum_range_two_mul_add_two_eq_fold]

/-- **Key identity for the second Rogers-Ramanujan Bailey pair** -/
theorem sum_α₂_mul_one_sub_mul_qChoose_eq_zero (q : R) {n : ℕ} (hn : n ≠ 0) :
    ∑ r ∈ Finset.range (n + 1), α₂ q r * (1 - q) * qChoose q (2 * n + 1) (n - r) = 0 := by
  have key : ∑ r ∈ Finset.range (n + 1), α₂ (X (R := ℤ)) r * (1 - X) *
      qChoose X (2 * n + 1) (n - r) = 0 := toLaurent_injective <| by
    simpa using sum_α₂_mul_one_sub_mul_qChoose_eq_zero_of_isUnit (isUnit_T 1) hn
  simpa using congr(Polynomial.aeval q $key)

/-- The second Rogers-Ramanujan Bailey pair: `(α₂, β)` is a Bailey pair relative to `a = q`. -/
theorem isBaileyPair_α₂_β {q : R} (hpu : ∀ k, IsUnit (q; q)_(k)) :
    IsBaileyPair q q (α₂ q) β := fun n ↦ by
  obtain rfl | hn := eq_or_ne n 0
  · simp [β, α₂]
  have h₁ (m) : bInv (q * q; q)_m = bInv (q; q)_(m + 1) * (1 - q) := by
    refine bInv_eq_of_mul_eq_one ?_
    rw [mul_comm _ (_ * _), mul_assoc, ← qPochhammer_succ]
    exact (hpu _).bInv_mul_cancel
  simp_rw [mul_assoc, h₁, ← mul_assoc _ _ (1 - q), bInv_qPochhammer_mul_bInv_qPochhammer (hpu _)]
  simp +contextual only [show ∀ r ∈ range (n + 1), n - r + (n + r + 1) = 2 * n + 1 by grind]
  simp_rw [← mul_assoc, mul_right_comm, ← sum_mul, sum_α₂_mul_one_sub_mul_qChoose_eq_zero q hn,
    zero_mul, β, if_neg hn]

theorem isBaileyPair_αt₂_βt {q : R} (hpu : ∀ k, IsUnit (q; q)_(k)) :
    IsBaileyPair q q (αt₂ q) (βt q) := qBaileyLemma_limit q q (α₂ q) β (αt₂ q) (βt q)
  (isBaileyPair_α₂_β hpu) hpu
  (fun k ↦ And.right <| by simpa [qPochhammer_succ] using hpu (k + 1))
  (by grind [αt₂, α₂]) (by simp [β, βt])

theorem tendsto_αt₂_zero
    {R : Type*} [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R]
    {q : R} (hq : IsTopologicallyNilpotent q) :
    Tendsto (αt₂ q) atTop (𝓝 0) := by
  let := IsTopologicalAddGroup.rightUniformSpace R
  have := isUniformAddGroup_of_addCommGroup (G := R)
  refine (Function.BoundedRange.neg_one_pow.mul_tendsto_zero (hq.comp ?_)).mul_topologicallyBounded
    (cauchySeq_qInt hq).boundedRange.comp
  exact tendsto_atTop_mono (by grind) tendsto_id

/-# ! Both Rogers Ramanujan Identities -/

variable [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R] [T2Space R]

section strong
variable [StrongNonarchimedeanRing R]

theorem first_rogers_ramanujan_hasSum_strong {q : R} (hq : IsTopologicallyNilpotent q) :
    HasSum (fun j ↦ q ^ j ^ 2 * bInv (q; q)_j) (bInv (q; q^5)_∞ * bInv (q^4; q^5)_∞) := by
  obtain ⟨L, h₁, h₂⟩ := qBaileyLemma_limit'_hasSum 1 q (αt₁ q) (βt q)
    (isBaileyPair_αt₁_βt <| isUnit_qPochhammer hq (by simpa)) hq (by simpa)
    (by simpa using (hq.comp <| tendsto_pow_atTop <| by grind).mul (tendsto_αt₁_zero hq))
  simp_rw [one_pow, one_mul] at h₁ h₂
  have h₃ := jacobi_triple_product_hasSum' (a := q ^ 2) (b := q ^ 3) (q := q ^ 5)
    (hq.pow (by grind)) (by grind)
  replace h₃ := h₃.ite_nat_add_neg
  have h₄ (n) : 2 * n ^ 2 + n.choose 2 = 2 * n + 5 * n.choose 2 := by
    refine mul_left_cancel₀ (by grind : 2 ≠ 0) ?_
    simp_rw [mul_add, mul_left_comm 2, two_mul_choose_two_right]
    obtain _ | n := n <;> grind
  obtain rfl := by
    refine h₁.unique <| h₃.congr_fun fun n ↦ ?_
    unfold αt₁ α₁
    obtain rfl | hn := eq_or_ne n 0
    · simp [abPow]
    simp_rw [if_neg hn, abPow_nat, abPow_neg_nat, Int.natAbs_neg, Int.natAbs_natCast]
    trans (-1) ^ n * q ^ (2 * n ^ 2 + n.choose 2) + (-1) ^ n * q ^ (2 * n ^ 2 + n.choose 2 + n)
    · ring
    simp_rw [h₄]
    ring
  have h₄ (m : ℕ) : IsUnit (q ^ (m + 1); q ^ 5)_∞ :=
    isUnit_qPochhammerInf (hq.pow (by grind)) (hq.pow (by grind))
  simp_rw [qPochhammerInf_eq_prod_range (by grind : 5 ≠ 0) hq, ← _root_.pow_succ',
    bInv_prod fun _ _ ↦ h₄ _] at h₂
  simp_rw [prod_range_succ, prod_range_zero, one_mul, reduceAdd] at h₂
  replace h₂ : HasSum (fun j ↦ q ^ j ^ 2 * βt q j)
    (((q ^ 2; q ^ 5)_∞ * bInv (q ^ 2; q ^ 5)_∞) *
      ((q ^ 3; q ^ 5)_∞ * bInv (q ^ 3; q ^ 5)_∞) *
      ((q ^ 5; q ^ 5)_∞ * bInv (q ^ 5; q ^ 5)_∞) *
      bInv (q; q ^ 5)_∞ * bInv (q ^ 4; q ^ 5)_∞) := by convert h₂ using 1; ring_nf
  simp_rw [(h₄ _).mul_bInv_cancel, one_mul] at h₂
  exact h₂

theorem second_rogers_ramanujan_hasSum_strong {q : R} (hq : IsTopologicallyNilpotent q) :
    HasSum (fun j ↦ q ^ (j * (j + 1)) * bInv (q; q)_j)
      (bInv (q ^ 2; q ^ 5)_∞ * bInv (q ^ 3; q ^ 5)_∞) := by
  have h₁ (n : ℕ) : n ≤ n + n ^ 2 := by grind
  obtain ⟨L, h₁, h₂⟩ := qBaileyLemma_limit'_hasSum q q (αt₂ q) (βt q)
    (isBaileyPair_αt₂_βt <| isUnit_qPochhammer hq (by simpa)) hq (hq.mul hq) <| by
    simpa [pow_add] using (hq.comp <| tendsto_atTop_mono h₁ tendsto_id).mul (tendsto_αt₂_zero hq)
  -- `h₁ : HasSum (fun r ↦ q ^ r * q ^ r ^ 2 * αt₂ q r) L`
  -- `h₂ : HasSum (fun j ↦ q ^ j * q ^ j ^ 2 * βt q j) (bInv (q * q; q)_∞ * L)`
  -- We need to multiply them by `1 - q`.
  have h₃ := jacobi_triple_product_hasSum' (a := q ^ 4) (b := q) (q := q ^ 5)
    (hq.pow (by grind)) (by grind)
  -- JTP gives us a sum indexed by `ℤ`.
  -- We need to group `(0, -1)`, and `(1, -2)`, etc.
  replace h₃ := h₃.nat_add_neg_add_one
  have h₄ : L * (1 - q) = (q ^ 5; q ^ 5)_∞ * (q ^ 4; q ^ 5)_∞ * (q; q ^ 5)_∞ := by
    refine (h₁.mul_right (1 - q)).unique <| h₃.congr_fun fun n ↦ ?_
    simp_rw [← Nat.cast_add_one, abPow_nat, abPow_neg_nat, Int.natAbs_neg, Int.natAbs_natCast,
      neg_pow q, neg_pow (q ^ 4), αt₂, mul_assoc, mul_comm _ (1 - q), one_sub_mul_qInt,
      mul_one_sub, mul_sub, mul_left_comm _ ((-1 : R) ^ _), ← pow_mul, ← pow_add, ← add_assoc]
    have h : n + n ^ 2 + n ^ 2 + n + n.choose 2 = 4 * n + 5 * n.choose 2 := by
      refine mul_left_cancel₀ (by grind : 2 ≠ 0) ?_
      simp_rw [mul_add, mul_left_comm 2, two_mul_choose_two_right]
      obtain _ | n := n <;> grind
    rw [h, choose_succ_two]
    ring
  convert h₂ using 1
  · simp [βt, mul_add_one, pow_add, mul_comm, sq]
  have h₅ (m : ℕ) : IsUnit (q ^ (m + 1); q ^ 5)_∞ :=
    isUnit_qPochhammerInf (hq.pow (by grind)) (hq.pow (by grind))
  simp_rw [bInv_qPochhammerInf_mul hq (isUnit_qPochhammerInf hq hq), mul_right_comm, mul_assoc, h₄,
   (isUnit_qPochhammerInf hq hq).eq_bInv_mul_iff_mul_eq, ← mul_assoc,
   (h₅ _).mul_bInv_eq_iff_eq_mul, qPochhammerInf_eq_prod_range (by grind : 5 ≠ 0) hq,
   prod_range_succ, prod_range_zero]
  ring_nf

end strong

section just_nonarchimedean
variable [NonarchimedeanRing R]

open PowerSeries
open scoped DiscreteTopology

theorem first_rogers_ramanujan_hasSum {q : R} (hq : IsTopologicallyNilpotent q) :
    HasSum (fun j ↦ q ^ j ^ 2 * bInv (q; q)_j) (bInv (q; q^5)_∞ * bInv (q^4; q^5)_∞) := by
  have hxn : IsTopologicallyNilpotent (X : ℤ⟦X⟧) := by simp
  convert (first_rogers_ramanujan_hasSum_strong hxn).map (intEval q) (by fun_prop) using 2
  · simp [hq, isUnit_qPochhammer hxn hxn, IsUnit.map_bInv, map_qPochhammer]
  · simp [hq, isUnit_qPochhammerInf, IsUnit.map_bInv, map_qPochhammerInf (intEval q) (by fun_prop)]

theorem second_rogers_ramanujan_hasSum {q : R} (hq : IsTopologicallyNilpotent q) :
    HasSum (fun j ↦ q ^ (j * (j + 1)) * bInv (q; q)_j)
      (bInv (q ^ 2; q ^ 5)_∞ * bInv (q ^ 3; q ^ 5)_∞) := by
  have hxn : IsTopologicallyNilpotent (X : ℤ⟦X⟧) := by simp
  convert (second_rogers_ramanujan_hasSum_strong hxn).map (intEval q) (by fun_prop) using 2
  · simp [hq, isUnit_qPochhammer hxn hxn, IsUnit.map_bInv, map_qPochhammer]
  · simp [hq, isUnit_qPochhammerInf, IsUnit.map_bInv, map_qPochhammerInf (intEval q) (by fun_prop)]

/-- **First Rogers-Ramanujan Identity** -/
theorem first_rogers_ramanujan
    {q : R} (hq : IsTopologicallyNilpotent q) :
    ∑' j, q ^ (j ^ 2) * bInv (q; q)_(j) = bInv (q; q^5)_∞ * bInv (q^4; q^5)_∞ :=
  (first_rogers_ramanujan_hasSum hq).tsum_eq

/-- **Second Rogers-Ramanujan Identity** -/
theorem second_rogers_ramanujan
    {q : R} (hq : IsTopologicallyNilpotent q) :
    ∑' j, q ^ (j * (j + 1)) * bInv (q; q)_j = bInv (q ^ 2; q ^ 5)_∞ * bInv (q ^ 3; q ^ 5)_∞ :=
  (second_rogers_ramanujan_hasSum hq).tsum_eq

end just_nonarchimedean

/-! # The Rogers-Ramanujan identities in complete normed rings -/

section normedRing

open PowerSeries hiding X
open PowerSeries.DiscreteTopology

variable {𝕜 : Type*} [NormedCommRing 𝕜] [NormOneClass 𝕜]

private theorem tsum_enormAt_X_pow_mul_bInv_qPochhammer_ne_top {e : ℕ → ℕ} (he : ∀ j, j ≤ e j)
    {q : 𝕜} (hq : ‖q‖ₑ < 1) :
    ∑' j, enormAt (Int.castRingHom 𝕜) q
      (PowerSeries.X ^ e j * bInv (PowerSeries.X; PowerSeries.X)_j) ≠ ⊤ :=
  have hX1 : enormAt (Int.castRingHom 𝕜) q PowerSeries.X < 1 := enormAt_X.trans_lt hq
  ne_top_of_le_ne_top (ENNReal.tsum_mul_right.trans_ne <|
      ENNReal.mul_ne_top (tsum_geometric_lt_top.2 hq).ne ENNReal.ofReal_ne_top) <|
    ENNReal.tsum_le_tsum fun j ↦ (enormAt_mul_le _ _).trans <| mul_le_mul'
      ((enormAt_X_pow_le _).trans (pow_le_pow_right_of_le_one' hq.le (he j)))
      (enormAt_bInv_qPochhammer_le isTopologicallyNilpotent_X hX1 hX1 j)

variable [CompleteSpace 𝕜]

private theorem hasSum_of_norm_lt_one_of_powerSeries {e : ℕ → ℕ} (he : ∀ j, j ≤ e j) {k l : ℕ}
    (hk : k ≠ 0) (hl : l ≠ 0) {q : 𝕜} (hq : ‖q‖ < 1)
    (h : HasSum (fun j ↦ (PowerSeries.X : ℤ⟦X⟧) ^ e j * bInv (PowerSeries.X; PowerSeries.X)_j)
      (bInv (PowerSeries.X ^ k; PowerSeries.X ^ 5)_∞ *
        bInv (PowerSeries.X ^ l; PowerSeries.X ^ 5)_∞)) :
    HasSum (fun j ↦ q ^ e j * bInv (q; q)_j) (bInv (q ^ k; q ^ 5)_∞ * bInv (q ^ l; q ^ 5)_∞) := by
  have hq' : ‖q‖ₑ < 1 := ofReal_norm q ▸ ENNReal.ofReal_lt_one.2 hq
  have hX (m : ℕ) (hm : m ≠ 0) := (isTopologicallyNilpotent_X_pow (R := ℤ) m).2 hm
  have hX1 (m : ℕ) (hm : m ≠ 0) : enormAt (Int.castRingHom 𝕜) q (PowerSeries.X ^ m) < 1 :=
    (enormAt_X_pow_le m).trans_lt (pow_lt_one' hq' hm)
  have h' := hasSum_evalAt h (tsum_enormAt_X_pow_mul_bInv_qPochhammer_ne_top he hq')
  have h5 := hX 5 (by norm_num)
  have h51 := hX1 5 (by norm_num)
  rw [evalAt_mul (enormAt_bInv_qPochhammerInf_ne_top (hX k hk) (hX1 k hk) h51 h5)
      (enormAt_bInv_qPochhammerInf_ne_top (hX l hl) (hX1 l hl) h51 h5),
    evalAt_bInv_qPochhammerInf (hX k hk) (hX1 k hk) h51 h5,
    evalAt_bInv_qPochhammerInf (hX l hl) (hX1 l hl) h51 h5] at h'
  simpa [evalAt_mul, evalAt_bInv_qPochhammer, enormAt_bInv_qPochhammer_ne_top, hq'] using h'

/-- **First Rogers-Ramanujan identity in a complete normed ring**, `HasSum` version: for
`‖q‖ < 1`, `∑ q ^ (j ^ 2) / (q; q)_j = 1 / ((q; q ^ 5)_∞ (q ^ 4; q ^ 5)_∞)`, where the series and
the infinite products converge, and all the inverted `q`-Pochhammer symbols are units
(`isUnit_qPochhammer_of_norm_lt_one`, `isUnit_qPochhammerInf_of_norm_lt_one`). -/
theorem first_rogers_ramanujan_hasSum_of_norm_lt_one {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun j ↦ q ^ j ^ 2 * bInv (q; q)_j) (bInv (q; q ^ 5)_∞ * bInv (q ^ 4; q ^ 5)_∞) := by
  simpa using hasSum_of_norm_lt_one_of_powerSeries (Nat.le_self_pow two_ne_zero) one_ne_zero
    four_ne_zero hq <| by
      simpa using first_rogers_ramanujan_hasSum_strong (isTopologicallyNilpotent_X (R := ℤ))

/-- **Second Rogers-Ramanujan identity in a complete normed ring**, `HasSum` version: for
`‖q‖ < 1`, `∑ q ^ (j (j + 1)) / (q; q)_j = 1 / ((q ^ 2; q ^ 5)_∞ (q ^ 3; q ^ 5)_∞)`, where the
series and the infinite products converge, and all the inverted `q`-Pochhammer symbols are units
(`isUnit_qPochhammer_of_norm_lt_one`, `isUnit_qPochhammerInf_of_norm_lt_one`). -/
theorem second_rogers_ramanujan_hasSum_of_norm_lt_one {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun j ↦ q ^ (j * (j + 1)) * bInv (q; q)_j)
      (bInv (q ^ 2; q ^ 5)_∞ * bInv (q ^ 3; q ^ 5)_∞) :=
  hasSum_of_norm_lt_one_of_powerSeries (fun j ↦ Nat.le_mul_of_pos_right j j.succ_pos) two_ne_zero
    three_ne_zero hq (second_rogers_ramanujan_hasSum_strong isTopologicallyNilpotent_X)

/-- **First Rogers-Ramanujan identity in a complete normed ring**: for `‖q‖ < 1`,
`∑' j, q ^ (j ^ 2) / (q; q)_j = 1 / ((q; q ^ 5)_∞ (q ^ 4; q ^ 5)_∞)`. -/
theorem first_rogers_ramanujan_of_norm_lt_one {q : 𝕜} (hq : ‖q‖ < 1) :
    ∑' j, q ^ j ^ 2 * bInv (q; q)_j = bInv (q; q ^ 5)_∞ * bInv (q ^ 4; q ^ 5)_∞ :=
  (first_rogers_ramanujan_hasSum_of_norm_lt_one hq).tsum_eq

/-- **Second Rogers-Ramanujan identity in a complete normed ring**: for `‖q‖ < 1`,
`∑' j, q ^ (j (j + 1)) / (q; q)_j = 1 / ((q ^ 2; q ^ 5)_∞ (q ^ 3; q ^ 5)_∞)`. -/
theorem second_rogers_ramanujan_of_norm_lt_one {q : 𝕜} (hq : ‖q‖ < 1) :
    ∑' j, q ^ (j * (j + 1)) * bInv (q; q)_j = bInv (q ^ 2; q ^ 5)_∞ * bInv (q ^ 3; q ^ 5)_∞ :=
  (second_rogers_ramanujan_hasSum_of_norm_lt_one hq).tsum_eq

end normedRing

private theorem bInv_eq_inv_of_isUnit {K : Type*} [Field K] {x : K} (hx : IsUnit x) :
    bInv x = x⁻¹ :=
  bInv_eq_of_mul_eq_one (mul_inv_cancel₀ hx.ne_zero)

section normedField

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {q : 𝕜}

/-- **First Rogers-Ramanujan identity in a complete normed field**, `HasSum` version: for
`‖q‖ < 1`, `∑ q ^ (j ^ 2) / (q; q)_j = 1 / ((q; q ^ 5)_∞ (q ^ 4; q ^ 5)_∞)`. -/
theorem first_rogers_ramanujan_hasSum_div_of_norm_lt_one (hq : ‖q‖ < 1) :
    HasSum (fun j ↦ q ^ j ^ 2 / (q; q)_j) ((q; q ^ 5)_∞⁻¹ * (q ^ 4; q ^ 5)_∞⁻¹) := by
  have h (k : ℕ) (hk : k ≠ 0) : ‖q ^ k‖ < 1 := by simpa using pow_lt_one₀ (norm_nonneg q) hq hk
  simpa [div_eq_mul_inv, bInv_eq_inv_of_isUnit (isUnit_qPochhammer_of_norm_lt_one hq hq _),
    bInv_eq_inv_of_isUnit (isUnit_qPochhammerInf_of_norm_lt_one hq (h 5 (by norm_num))),
    bInv_eq_inv_of_isUnit (isUnit_qPochhammerInf_of_norm_lt_one (h 4 (by norm_num))
      (h 5 (by norm_num)))] using first_rogers_ramanujan_hasSum_of_norm_lt_one hq

/-- **Second Rogers-Ramanujan identity in a complete normed field**, `HasSum` version: for
`‖q‖ < 1`, `∑ q ^ (j (j + 1)) / (q; q)_j = 1 / ((q ^ 2; q ^ 5)_∞ (q ^ 3; q ^ 5)_∞)`. -/
theorem second_rogers_ramanujan_hasSum_div_of_norm_lt_one (hq : ‖q‖ < 1) :
    HasSum (fun j ↦ q ^ (j * (j + 1)) / (q; q)_j) ((q ^ 2; q ^ 5)_∞⁻¹ * (q ^ 3; q ^ 5)_∞⁻¹) := by
  have h (k : ℕ) (hk : k ≠ 0) : ‖q ^ k‖ < 1 := by simpa using pow_lt_one₀ (norm_nonneg q) hq hk
  simpa [div_eq_mul_inv, bInv_eq_inv_of_isUnit (isUnit_qPochhammer_of_norm_lt_one hq hq _),
    bInv_eq_inv_of_isUnit (isUnit_qPochhammerInf_of_norm_lt_one (h 2 (by norm_num))
      (h 5 (by norm_num))),
    bInv_eq_inv_of_isUnit (isUnit_qPochhammerInf_of_norm_lt_one (h 3 (by norm_num))
      (h 5 (by norm_num)))] using second_rogers_ramanujan_hasSum_of_norm_lt_one hq

/-- **First Rogers-Ramanujan identity in a complete normed field** (such as `ℂ`): for `‖q‖ < 1`,
`∑' j, q ^ (j ^ 2) / (q; q)_j = 1 / ((q; q ^ 5)_∞ (q ^ 4; q ^ 5)_∞)`. -/
theorem first_rogers_ramanujan_div_of_norm_lt_one (hq : ‖q‖ < 1) :
    ∑' j, q ^ j ^ 2 / (q; q)_j = (q; q ^ 5)_∞⁻¹ * (q ^ 4; q ^ 5)_∞⁻¹ :=
  (first_rogers_ramanujan_hasSum_div_of_norm_lt_one hq).tsum_eq

/-- **Second Rogers-Ramanujan identity in a complete normed field** (such as `ℂ`): for `‖q‖ < 1`,
`∑' j, q ^ (j (j + 1)) / (q; q)_j = 1 / ((q ^ 2; q ^ 5)_∞ (q ^ 3; q ^ 5)_∞)`. -/
theorem second_rogers_ramanujan_div_of_norm_lt_one (hq : ‖q‖ < 1) :
    ∑' j, q ^ (j * (j + 1)) / (q; q)_j = (q ^ 2; q ^ 5)_∞⁻¹ * (q ^ 3; q ^ 5)_∞⁻¹ :=
  (second_rogers_ramanujan_hasSum_div_of_norm_lt_one hq).tsum_eq

end normedField

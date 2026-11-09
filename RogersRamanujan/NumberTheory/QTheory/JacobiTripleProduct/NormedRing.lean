module

import RogersRamanujan.Data.Nat.Choose.Basic
public import RogersRamanujan.NumberTheory.QTheory.JacobiTripleProduct.Basic
public import RogersRamanujan.NumberTheory.QTheory.NormedRing
public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.RingTheory.MvPowerSeries.LinearTopology

/-! # The Jacobi triple product in complete normed rings

`RogersRamanujan/NumberTheory/QTheory/JacobiTripleProduct/Basic.lean` proves the Jacobi triple
product in a complete strongly nonarchimedean ring, for a topologically nilpotent `q`. In this file
we recover the analytic statement in a complete normed commutative ring `𝕜` with `‖1‖ = 1`, such
as `ℂ`: for `a b q : 𝕜` with `‖q‖ < 1` and `a * b = q`,
`(q; q)_∞ * (-a; q)_∞ * (-b; q)_∞ = ∑' n : ℤ, abPow a b n * q ^ (|n| choose 2)`,
where the infinite products converge in `𝕜` and the sum over `ℤ` is a genuine `HasSum`.

## Main results

* `jacobi_triple_product_hasSum_of_norm_lt_one`, `jacobi_triple_product_of_norm_lt_one` (and the
  primed versions): the Jacobi triple product in `𝕜`, in the same shape as
  `jacobi_triple_product_hasSum` and `jacobi_triple_product`;
* `jacobi_triple_product_theta_hasSum`, `jacobi_triple_product_theta`: the classical two-variable
  form `∏ (1 - q^{i+1})(1 + z q^i)(1 + z⁻¹ q^{i+1}) = ∑ n : ℤ, z ^ n * q ^ (n(n-1)/2)` in a complete
  normed field.

## Implementation notes

The nonarchimedean theorem is instantiated in the ring `ℤ[A]⟦X⟧` of formal power series over the
polynomials in a variable `A`, with `a := A`, `b := X` and `q := A * X` (topologically nilpotent);
note that the coefficient ring carries no topology of its own, so all the required instances on
`ℤ[A]⟦X⟧` come from `PowerSeries.DiscreteTopology`. The resulting formal identity is then
evaluated at `A ↦ a`, `X ↦ b` with `PowerSeries.evalAt` (see
`RogersRamanujan/NumberTheory/QTheory/NormedRing.lean`), which covers all `a b : 𝕜` with
`‖a * b‖ < 1` at once.
-/

@[expose] public section

open Filter
open QTheory PowerSeries PowerSeries.DiscreteTopology

/-- The theta-type series `∑ s ^ k * t ^ (k choose 2)` converges for `0 ≤ s` and `0 ≤ t < 1`. -/
theorem summable_pow_mul_pow_choose_two {s t : ℝ} (hs : 0 ≤ s) (ht0 : 0 ≤ t) (ht : t < 1) :
    Summable fun k : ℕ ↦ s ^ k * t ^ k.choose 2 := by
  have hnn (k : ℕ) : 0 ≤ s ^ k * t ^ k.choose 2 := by positivity
  refine summable_of_ratio_norm_eventually_le one_half_lt_one ?_
  filter_upwards [((tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht).const_mul s).eventually_le_const
    (by norm_num : s * 0 < 1 / 2)] with k hk
  rw [Real.norm_of_nonneg (hnn _), Real.norm_of_nonneg (hnn _), Nat.choose_succ_two]
  exact (mul_le_mul_of_nonneg_right hk (hnn k)).trans_eq' (by ring)

/-! ### The formal Jacobi triple product in `ℤ[A]⟦X⟧` -/

private theorem toNat_mul_sub_one_div_two (n : ℤ) :
    (n * (n - 1) / 2).toNat = n.natAbs.choose 2 + (-n).toNat := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg <;> have := Nat.two_mul_cast_choose_two_right k <;>
    simp <;> lia

private theorem toNat_mul_add_one_div_two (n : ℤ) :
    (n * (n + 1) / 2).toNat = n.natAbs.choose 2 + n.toNat := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg <;> have := Nat.two_mul_cast_choose_two_right k <;>
    simp <;> lia

/-- The formal Jacobi triple product in `ℤ[A]⟦X⟧`, for `a = A`, `b = X` and `q = A * X`; its
`n`-th term is the monomial `(-1) ^ |n| * A ^ (n(n+1)/2) * X ^ (n(n-1)/2)`. -/
private theorem hasSum_jacobi_triple_product_polynomial :
    HasSum (fun n : ℤ ↦ C ((-1) ^ n.natAbs * Polynomial.X ^ (n * (n + 1) / 2).toNat) *
      X ^ (n * (n - 1) / 2).toNat)
      ((C Polynomial.X * X; C Polynomial.X * X)_∞ * (C Polynomial.X; C Polynomial.X * X)_∞ *
        (X; C Polynomial.X * X)_∞ : (Polynomial ℤ)⟦X⟧) := by
  refine (jacobi_triple_product_hasSum' (by simp) rfl).congr_fun fun n ↦ ?_
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg <;>
    simp only [toNat_mul_sub_one_div_two, toNat_mul_add_one_div_two, abPow_nat, abPow_neg_nat,
      Int.natAbs_neg, Int.natAbs_natCast, Int.toNat_natCast, Int.toNat_neg_natCast, neg_neg,
      map_mul, map_pow, map_neg, map_one] <;> ring

/-! ### Evaluation at `A ↦ a`, `X ↦ b` -/

section Evaluation

variable {𝕜 : Type*} [NormedCommRing 𝕜] (a b : 𝕜)

/-- The `n`-th summand of the formal Jacobi triple product evaluates to the `n`-th summand of the
analytic one. -/
private theorem evalAt_jtp_summand (n : ℤ) :
    evalAt (Polynomial.eval₂RingHom (Int.castRingHom 𝕜) a) b
        (C ((-1) ^ n.natAbs * Polynomial.X ^ (n * (n + 1) / 2).toNat) *
      X ^ (n * (n - 1) / 2).toNat) =
      abPow (-a) (-b) n * (a * b) ^ n.natAbs.choose 2 := by
  rw [evalAt_C_mul_X_pow]
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg <;>
    simp only [toNat_mul_sub_one_div_two, toNat_mul_add_one_div_two, abPow_nat, abPow_neg_nat,
      Int.natAbs_neg, Int.natAbs_natCast, Int.toNat_natCast, Int.toNat_neg_natCast, neg_neg,
      map_mul, map_pow, map_neg, map_one, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] <;> ring

variable {a b} [NormOneClass 𝕜]

/-- The `ℓ¹`-norms of the terms of the formal Jacobi triple product are summable at `A ↦ a`,
`X ↦ b` for `‖a * b‖ < 1`. -/
private theorem tsum_enormAt_jtp_summand_ne_top (hab : ‖a * b‖ < 1) :
    ∑' n : ℤ, enormAt (Polynomial.eval₂RingHom (Int.castRingHom 𝕜) a) b
      (C ((-1) ^ n.natAbs * Polynomial.X ^ (n * (n + 1) / 2).toNat) *
      X ^ (n * (n - 1) / 2).toNat) ≠ ⊤ := by
  have hs : Summable fun n : ℤ ↦ abPow ‖a‖ ‖b‖ n * ‖a * b‖ ^ n.natAbs.choose 2 :=
    .of_nat_of_neg (by simpa using summable_pow_mul_pow_choose_two (norm_nonneg a) (by simp) hab)
      (by simpa using summable_pow_mul_pow_choose_two (norm_nonneg b) (by simp) hab)
  have hn (n : ℤ) : ‖abPow (-a) (-b) n‖ ≤ abPow ‖a‖ ‖b‖ n := by
    obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
    · simpa using norm_pow_le (-a) k
    · simpa using norm_pow_le (-b) k
  have h0 (n : ℤ) : 0 ≤ abPow ‖a‖ ‖b‖ n := by obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg <;> simp
  simp_rw [enormAt_C_mul_X_pow, ← evalAt_C_mul_X_pow, evalAt_jtp_summand]
  exact tsum_enorm_ne_top_iff_summable_norm.mpr <| hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    fun n ↦ (norm_mul_le _ _).trans <| mul_le_mul (hn n) (norm_pow_le _ _) (norm_nonneg _) (h0 n)

end Evaluation

/-! ### The Jacobi triple product in a complete normed ring -/

section Main

variable {𝕜 : Type*} [NormedCommRing 𝕜] [NormOneClass 𝕜] [CompleteSpace 𝕜] {a b q : 𝕜}

/-- **Jacobi triple product in a complete normed ring**: for `a, b, q` with `‖q‖ < 1` and
`a * b = q`, `(q; q)_∞ (a; q)_∞ (b; q)_∞ = ∑_{n : ℤ} abPow (-a) (-b) n * q ^ (|n| choose 2)`,
where all products and sums converge.

This is the analytic counterpart of `jacobi_triple_product_hasSum'`. -/
theorem jacobi_triple_product_hasSum'_of_norm_lt_one (hq : ‖q‖ < 1) (hab : a * b = q) :
    HasSum (fun n : ℤ ↦ abPow (-a) (-b) n * q ^ n.natAbs.choose 2)
      ((q; q)_∞ * (a; q)_∞ * (b; q)_∞) := by
  subst hab
  set φ := Polynomial.eval₂RingHom (Int.castRingHom 𝕜) a
  have hX : IsTopologicallyNilpotent (C Polynomial.X * X : (Polynomial ℤ)⟦X⟧) := by simp
  have hX1 : enormAt φ b (C Polynomial.X * X) < 1 := by simpa [φ, ← ofReal_norm] using hq
  have key (c : (Polynomial ℤ)⟦X⟧) (hc : enormAt φ b c ≠ ⊤) :=
    And.intro (enormAt_qPochhammerInf_ne_top hX hc hX1) (evalAt_qPochhammerInf hX hc hX1)
  obtain ⟨n₁, p₁⟩ := key (C Polynomial.X * X) (by simp)
  obtain ⟨n₂, p₂⟩ := key (C Polynomial.X) (by simp)
  obtain ⟨n₃, p₃⟩ := key X (by simp)
  have h := hasSum_evalAt hasSum_jacobi_triple_product_polynomial
    (tsum_enormAt_jtp_summand_ne_top hq)
  rw [funext (evalAt_jtp_summand a b), evalAt_mul (enormAt_mul_ne_top n₁ n₂) n₃,
    evalAt_mul n₁ n₂, p₁, p₂, p₃] at h
  simpa [φ] using h

/-- The `tsum` version of `jacobi_triple_product_hasSum'_of_norm_lt_one`. -/
theorem jacobi_triple_product'_of_norm_lt_one (hq : ‖q‖ < 1) (hab : a * b = q) :
    (q; q)_∞ * (a; q)_∞ * (b; q)_∞ = ∑' n : ℤ, abPow (-a) (-b) n * q ^ n.natAbs.choose 2 :=
  (jacobi_triple_product_hasSum'_of_norm_lt_one hq hab).tsum_eq.symm

/-- **Jacobi triple product in a complete normed ring**: for `a, b, q` with `‖q‖ < 1` and
`a * b = q`, `(q; q)_∞ (-a; q)_∞ (-b; q)_∞ = ∑_{n : ℤ} abPow a b n * q ^ (|n| choose 2)`.

This is the analytic counterpart of `jacobi_triple_product_hasSum`. -/
theorem jacobi_triple_product_hasSum_of_norm_lt_one (hq : ‖q‖ < 1) (hab : a * b = q) :
    HasSum (fun n : ℤ ↦ abPow a b n * q ^ n.natAbs.choose 2)
      ((q; q)_∞ * (-a; q)_∞ * (-b; q)_∞) := by
  simpa using jacobi_triple_product_hasSum'_of_norm_lt_one (a := -a) (b := -b) hq
    (by simpa using hab)

/-- The `tsum` version of `jacobi_triple_product_hasSum_of_norm_lt_one`. -/
theorem jacobi_triple_product_of_norm_lt_one (hq : ‖q‖ < 1) (hab : a * b = q) :
    (q; q)_∞ * (-a; q)_∞ * (-b; q)_∞ = ∑' n : ℤ, abPow a b n * q ^ n.natAbs.choose 2 :=
  (jacobi_triple_product_hasSum_of_norm_lt_one hq hab).tsum_eq.symm

end Main

/-! ### The two-variable form in a complete normed field -/

section Theta

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {q z : 𝕜}

/-- **Jacobi triple product**, classical two-variable form: for `‖q‖ < 1` and `z ≠ 0`,
$$\prod_{i \ge 0} (1 - q^{i+1})(1 + z q^i)(1 + z^{-1} q^{i+1}) = \sum_{n \in ℤ} z^n q^{n(n-1)/2}.$$
-/
theorem jacobi_triple_product_theta_hasSum (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    HasSum (fun n : ℤ ↦ z ^ n * q ^ (n * (n - 1) / 2))
      ((q; q)_∞ * (-z; q)_∞ * (-(z⁻¹ * q); q)_∞) := by
  refine (jacobi_triple_product_hasSum_of_norm_lt_one hq
    (mul_inv_cancel_left₀ hz q)).congr_fun fun n ↦ ?_
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg <;> have := Nat.two_mul_cast_choose_two_right k
  · have : (k : ℤ) * (k - 1) / 2 = k.choose 2 := by lia
    rw [this, zpow_natCast]; simp
  · have : -(k : ℤ) * (-k - 1) / 2 = (k.choose 2 + k : ℕ) := by lia
    rw [this, zpow_natCast]; simp [mul_pow, ← pow_add, add_comm k, mul_assoc]

/-- The `tsum` version of `jacobi_triple_product_theta_hasSum`. -/
theorem jacobi_triple_product_theta (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    (q; q)_∞ * (-z; q)_∞ * (-(z⁻¹ * q); q)_∞ = ∑' n : ℤ, z ^ n * q ^ (n * (n - 1) / 2) :=
  (jacobi_triple_product_theta_hasSum hq hz).tsum_eq.symm

end Theta

module

import RogersRamanujan.Combinatorics.Enumerative.Pentagonal
public import RogersRamanujan.NumberTheory.QTheory.Defs
import RogersRamanujan.NumberTheory.QTheory.JacobiTripleProduct.Basic
import RogersRamanujan.NumberTheory.QTheory.NormedRing
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
public import RogersRamanujan.RingTheory.PowerSeries.DiscreteTopology
import RogersRamanujan.RingTheory.PowerSeries.Evaluation
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Combinatorics.Enumerative.Pentagonal
import Mathlib.RingTheory.MvPowerSeries.LinearTopology

/-! # Pentagonal number theorem

In this file we prove the well-celebrated pentagonal number theorem:
`(q; q)_∞ = ∑ k : ℤ, (-1)^k q^(k(3k-1)/2)`. This is `tsum_qPochhammerInf_self`, for a
topologically nilpotent `q` in a complete nonarchimedean ring, and
`tsum_qPochhammerInf_self_of_norm_lt_one`, for `‖q‖ < 1` in a complete normed commutative ring with
`‖1‖ = 1` (such as `ℂ`).

-/

@[expose] public section

open QTheory PowerSeries DiscreteTopology

theorem hasSum_qPochhammerInf_self_powerSeries :
    HasSum (fun k : ℤ ↦ (k.negOnePow • X ^ pentagonal k : ℤ⟦X⟧)) (X; X)_∞ := by
  convert jacobi_triple_product_hasSum' (by simp) (show (X * X ^ 2 : ℤ⟦X⟧) = X ^ 3 by ring) using 1
  · rfl
  · funext n
    rw [Units.smul_def]
    obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
    · simp [Int.coe_negOnePow_natCast, neg_pow X, mul_assoc, ← pow_mul, ← pow_add, add_comm n]
    · simp [Int.coe_negOnePow_natCast, neg_pow (X ^ 2), mul_assoc, ← pow_mul, ← pow_add,
        add_comm (2 * n)]
  · rw [qPochhammerInf_eq_prod_range (by grind : 3 ≠ 0) (by simp)]
    simp [Finset.prod_range_succ]
    ring_nf

theorem hasSum_qPochhammerInf_self {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [NonarchimedeanRing R] [CompleteSpace R] [T2Space R]
    {q : R} (hq : IsTopologicallyNilpotent q := by simp) :
    HasSum (fun k : ℤ ↦ (k.negOnePow • q ^ pentagonal k)) (q; q)_∞ := by
  convert hasSum_qPochhammerInf_self_powerSeries.map (intEval q) (by fun_prop) using 1 <;>
  simp [funext_iff, hq]

/-- **Pentagonal number theorem**: `(q; q)_∞ = ∑ k : ℤ, (-1)^k q^(k(3k-1)/2)`.

For the version with `HasSum`, see `hasSum_qPochhammerInf_self`. -/
theorem tsum_qPochhammerInf_self {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [NonarchimedeanRing R] [CompleteSpace R] [T2Space R]
    {q : R} (hq : IsTopologicallyNilpotent q := by simp) :
    ∑' k : ℤ, k.negOnePow • q ^ pentagonal k = (q; q)_∞ :=
  (hasSum_qPochhammerInf_self hq).tsum_eq

alias pentagonal_number_theorem := tsum_qPochhammerInf_self

/-- **Pentagonal number theorem in a complete normed ring**: for `‖q‖ < 1`, the convergent infinite
product `(q; q)_∞` is the sum of the convergent series `∑ k : ℤ, (-1)^k q^(k(3k-1)/2)`. -/
theorem hasSum_qPochhammerInf_self_of_norm_lt_one {𝕜 : Type*} [NormedCommRing 𝕜] [NormOneClass 𝕜]
    [CompleteSpace 𝕜] {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun k : ℤ ↦ k.negOnePow • q ^ pentagonal k) (q; q)_∞ := by
  have hq' : ‖q‖ₑ < 1 := ofReal_norm q ▸ ENNReal.ofReal_lt_one.2 hq
  have h := hasSum_evalAt (φ := Int.castRingHom 𝕜) (q := q)
    hasSum_qPochhammerInf_self_powerSeries <| ne_top_of_le_ne_top
      ((ENNReal.tsum_comp_le_tsum_of_injective pentagonal_injective _).trans_lt
        (tsum_geometric_lt_top.2 hq')).ne
      (ENNReal.tsum_le_tsum fun k ↦ (enormAt_units_smul _ _).trans_le (enormAt_X_pow_le _))
  rw [evalAt_qPochhammerInf isTopologicallyNilpotent_X (by simp) (enormAt_X.trans_lt hq')] at h
  simpa using h

/-- **Pentagonal number theorem in a complete normed ring**:
`(q; q)_∞ = ∑ k : ℤ, (-1)^k q^(k(3k-1)/2)` for `‖q‖ < 1`.

For the version with `HasSum`, see `hasSum_qPochhammerInf_self_of_norm_lt_one`. -/
theorem tsum_qPochhammerInf_self_of_norm_lt_one {𝕜 : Type*} [NormedCommRing 𝕜] [NormOneClass 𝕜]
    [CompleteSpace 𝕜] {q : 𝕜} (hq : ‖q‖ < 1) :
    ∑' k : ℤ, k.negOnePow • q ^ pentagonal k = (q; q)_∞ :=
  (hasSum_qPochhammerInf_self_of_norm_lt_one hq).tsum_eq

alias pentagonal_number_theorem_of_norm_lt_one := tsum_qPochhammerInf_self_of_norm_lt_one

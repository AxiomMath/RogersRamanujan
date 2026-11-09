module

public import RogersRamanujan.Algebra.Group.Units.Basic
public import RogersRamanujan.NumberTheory.QTheory.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.Ring.Basic

/-! # Topology on q-theoretic objects
-/

@[expose] public section

open scoped QTheory

variable {R : Type*} [CommRing R] [TopologicalSpace R] {a q : R} {n : ℕ}

section continuous
variable [IsTopologicalRing R]

@[fun_prop] theorem qPochhammer_continuous :
    Continuous (fun p : R × R ↦ (p.1; p.2)_n) := by
  unfold qPochhammer; fun_prop

@[fun_prop] theorem qPochhammer_continuous_fst : Continuous ((·; q)_n) := by fun_prop

@[fun_prop] theorem qPochhammer_continuous_snd : Continuous ((a; ·)_n) := by fun_prop

end continuous

@[simp] theorem qPochhammerInf_zero : (0; q)_∞ = 1 := by
  simp [qPochhammerInf]

section t2
variable [T2Space R]

@[simp] theorem qPochhammerInf_one : (1; q)_∞ = 0 :=
  tprod_of_exists_eq_zero ⟨0, by simp⟩

@[simp] theorem qPochhammerInf_zero_right : (a; (0 : R))_∞ = 1 - a :=
  (hasProd_single 0 (f := fun i ↦ 1 - a * (0 : R) ^ i) (fun i hi ↦ by simp [zero_pow hi])
    (.conditional ℕ)).tprod_eq.trans (by simp)

theorem qPochhammerInf_bInv_pow_eq_zero {m : ℕ} : qPochhammerInf (bInv q ^ m) q = 0 := by
  by_cases hqu : IsUnit q
  · exact tprod_of_exists_eq_zero ⟨m, by simp [← mul_pow, hqu]⟩
  · rw [bInv_eq_one_of_not_isUnit hqu, one_pow, qPochhammerInf_one]

end t2

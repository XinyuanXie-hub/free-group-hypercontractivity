module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».Representation
public import «free-group-hypercontractivity».Scalar
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

public section

namespace FreeGroupHypercontractivity

open scoped ComplexOrder InnerProductSpace

@[simp] theorem traceRe_zero {n : ℕ} : traceRe (0 : Operator n) = 0 := by
  simp [traceRe]

@[simp] theorem traceRe_one {n : ℕ} : traceRe (1 : Operator n) = 1 := by
  simp [traceRe]

@[simp] theorem traceRe_add {n : ℕ} (T U : Operator n) :
    traceRe (T + U) = traceRe T + traceRe U := by
  simp only [traceRe, add_apply, lp.coeFn_add, Pi.add_apply, Complex.add_re]

@[simp] theorem traceRe_sub {n : ℕ} (T U : Operator n) :
    traceRe (T - U) = traceRe T - traceRe U := by
  simp only [traceRe, sub_apply, lp.coeFn_sub, Pi.sub_apply, Complex.sub_re]

@[simp] theorem traceRe_ofReal_smul {n : ℕ} (c : ℝ) (T : Operator n) :
    traceRe (Complex.ofReal c • T) = c * traceRe T := by
  simp only [traceRe, smul_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, Complex.re_ofReal_mul]

theorem traceRe_star_mul_self {n : ℕ} (T : Operator n) :
    traceRe (star T * T) = ‖T (lp.single 2 1 1)‖ ^ 2 := by
  rw [traceRe_as_inner]
  change (⟪lp.single 2 (1 : Group n) (1 : ℂ),
    T.adjoint (T (lp.single 2 1 1))⟫_ℂ).re = _
  rw [ContinuousLinearMap.adjoint_inner_right, ← RCLike.re_to_complex]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem traceRe_nonneg {n : ℕ} {T : Operator n} (hT : 0 ≤ T) : 0 ≤ traceRe T := by
  rw [traceRe_as_inner, ← RCLike.re_to_complex]
  exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).re_inner_nonneg_right
    (lp.single 2 1 1)

theorem traceRe_mono {n : ℕ} {T U : Operator n} (h : T ≤ U) : traceRe T ≤ traceRe U := by
  have hp := traceRe_nonneg (sub_nonneg.mpr h)
  rwa [traceRe_sub, sub_nonneg] at hp

theorem exists_ofReal_of_spectrum_nonneg {n : ℕ} {T : Operator n}
    (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ spectrum ℂ T) :
    ∃ r : ℝ, 0 ≤ r ∧ Complex.ofReal r = z := by
  obtain ⟨hr, him⟩ := Complex.nonneg_iff.mp (spectrum_nonneg_of_nonneg hT hz)
  exact ⟨z.re, hr, Complex.ext (by simp) (by simpa using him)⟩

/-- The trace of a positive operator's square is bounded by its norm times its trace. -/
theorem traceRe_pow_two_le_norm_mul {n : ℕ} {T : Operator n} (hT : 0 ≤ T) :
    traceRe (T ^ 2) ≤ ‖T‖ * traceRe T := by
  have hnormal : IsStarNormal T :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).isSelfAdjoint.isStarNormal
  let : Nontrivial (Hilbert n) := ⟨⟨lp.single 2 1 1, 0, by
    intro h
    have he := congrArg (fun v : Hilbert n ↦ v (1 : Group n)) h
    simp at he⟩⟩
  have hspec : ∀ z ∈ spectrum ℂ T, z ^ 2 ≤ Complex.ofReal ‖T‖ * z := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := exists_ofReal_of_spectrum_nonneg hT hz
    have hn : r ≤ ‖T‖ := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] using
        spectrum.norm_le_norm_of_mem hz
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.real_le_real, pow_two]
    exact mul_le_mul_of_nonneg_right hn hr
  have hop := cfc_mono hspec (by fun_prop) (by fun_prop)
  rw [cfc_pow_id (R := ℂ) T 2 hnormal, cfc_const_mul_id _ T hnormal] at hop
  simpa only [traceRe_ofReal_smul] using traceRe_mono hop

/-- Apply the cubic majorant by functional calculus and take the canonical trace. -/
theorem traceRe_cubic_majorant {n : ℕ} {T : Operator n} (hT : 0 ≤ T) {l : ℝ}
    (hl : 0 < l) :
    traceRe (cfc (p := IsStarNormal)
      (fun s : ℂ ↦ Complex.ofReal (s.re * Real.log s.re)) (T ^ 2)) ≤
        2 / (3 * l) * traceRe (T ^ 3) +
          (2 * Real.log l + 1) * traceRe (T ^ 2) - 2 * l * traceRe T + l ^ 2 / 3 := by
  let f : ℂ → ℂ := fun s ↦ Complex.ofReal (s.re * Real.log s.re)
  let g : ℂ → ℂ := fun s ↦ Complex.ofReal (2 / (3 * l)) * s ^ 3 +
    Complex.ofReal (2 * Real.log l + 1) * s ^ 2 -
      Complex.ofReal (2 * l) * s + Complex.ofReal (l ^ 2 / 3)
  have hf : Continuous f :=
    Complex.continuous_ofReal.comp (Real.continuous_mul_log.comp Complex.continuous_re)
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hnormal : IsStarNormal T :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).isSelfAdjoint.isStarNormal
  have hfg : ∀ z ∈ spectrum ℂ T, f (z ^ 2) ≤ g z := by
    intro z hz
    obtain ⟨r, hnonneg, rfl⟩ := exists_ofReal_of_spectrum_nonneg hT hz
    have h := cubic_log_majorant hnonneg hl
    rw [show f ((r : ℂ) ^ 2) = Complex.ofReal (2 * r ^ 2 * Real.log r) by
      simp only [f, ← Complex.ofReal_pow, Complex.ofReal_re, Real.log_pow, Nat.cast_ofNat]
      congr 1
      ring]
    rw [show g (r : ℂ) = Complex.ofReal
      (2 / (3 * l) * r ^ 3 + (2 * Real.log l + 1) * r ^ 2 - 2 * l * r + l ^ 2 / 3) by
      simp only [g, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow]]
    exact Complex.real_le_real.mpr h
  have hop : cfc (fun z : ℂ ↦ f (z ^ 2)) T ≤ cfc g T :=
    cfc_mono hfg (hf.comp (continuous_id.pow 2)).continuousOn hg.continuousOn
  have hpoly : cfc g T =
      Complex.ofReal (2 / (3 * l)) • T ^ 3 +
        Complex.ofReal (2 * Real.log l + 1) • T ^ 2 -
          Complex.ofReal (2 * l) • T + Complex.ofReal (l ^ 2 / 3) • (1 : Operator n) := by
    dsimp [g]
    rw [cfc_add_const .., cfc_sub .., cfc_add .., cfc_const_mul_id ..,
      cfc_const_mul .., cfc_const_mul .., cfc_pow_id .., cfc_pow_id ..,
      Algebra.algebraMap_eq_smul_one]
  have htrace := traceRe_mono hop
  rw [cfc_comp_pow f 2 T hf.continuousOn hnormal, hpoly] at htrace
  simpa only [f, traceRe_add, traceRe_sub, traceRe_ofReal_smul, traceRe_one, mul_one] using htrace

end FreeGroupHypercontractivity

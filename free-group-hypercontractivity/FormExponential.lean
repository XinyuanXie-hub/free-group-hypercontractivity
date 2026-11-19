module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».CfcEnergyCore
public import «free-group-hypercontractivity».PositiveReduction
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

public section

namespace FreeGroupHypercontractivity

open NormedSpace
open scoped ComplexOrder

/-- The real exponential of a scalar multiple of a self-adjoint operator
agrees with its operator exponential. -/
theorem realCfcAt_exp_mul_eq {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H) (s : ℝ) :
    realCfcAt (fun x ↦ Real.exp (s * x)) H = exp (s • H) := by
  have hs : IsSelfAdjoint ((s : ℂ) • H) := by
    change star ((s : ℂ) • H) = (s : ℂ) • H
    rw [star_smul, Complex.star_def, Complex.conj_ofReal, hH.star_eq]
  calc
    _ = cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.exp ((s : ℂ) * z)) H := by
      unfold realCfcAt
      apply cfc_congr
      intro z hz
      change Complex.ofReal (Real.exp (s * z.re)) = Complex.exp ((s : ℂ) * z)
      rw [Complex.ofReal_exp, Complex.ofReal_mul, ← hH.mem_spectrum_eq_re hz]
    _ = cfc Complex.exp ((s : ℂ) • H) :=
      cfc_comp_const_mul _ _ _ Complex.continuous_exp.continuousOn hH.isStarNormal
    _ = exp (s • H) := by
      rw [CFC.complex_exp_eq_normedSpace_exp hs.isStarNormal]
      congr 1

/-- The operator exponential path is differentiable in the operator norm. -/
theorem hasDerivAt_operatorExp_smul {n : ℕ} (H : Operator n) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ exp (t • H)) (exp (s • H) * H) s :=
  hasDerivAt_exp_smul_const H s

/-- The canonical vector trace is strictly positive on the exponential
of a self-adjoint operator. -/
theorem traceRe_exp_pos {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H) :
    0 < traceRe (exp H) := by
  let : Nontrivial (Hilbert n) := ⟨⟨lp.single 2 1 1, 0, by
    intro h
    have he := congrArg (fun v : Hilbert n ↦ v (1 : Group n)) h
    simp at he⟩⟩
  have hs (z : ℂ) (hz : z ∈ spectrum ℂ H) : -‖H‖ ≤ z.re := by
    have ha : |z.re| ≤ ‖H‖ := (Complex.abs_re_le_norm z).trans (spectrum.norm_le_norm_of_mem hz)
    exact neg_le.mp (neg_le_abs _ |>.trans ha)
  have hmono : cfc (p := IsStarNormal) (fun _ : ℂ ↦ Complex.ofReal (Real.exp (-‖H‖))) H ≤
      realCfcAt Real.exp H := by
    unfold realCfcAt
    exact cfc_mono (fun z hz ↦ Complex.real_le_real.mpr (Real.exp_le_exp.mpr (hs z hz)))
      continuous_const.continuousOn
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp Complex.continuous_re)).continuousOn
  have hscalar : traceRe (cfc (p := IsStarNormal)
      (fun _ : ℂ ↦ Complex.ofReal (Real.exp (-‖H‖))) H) = Real.exp (-‖H‖) := by
    rw [cfc_const _ H hH.isStarNormal, Algebra.algebraMap_eq_smul_one, traceRe_ofReal_smul,
      traceRe_one, mul_one]
  have h := traceRe_mono hmono
  rw [hscalar, show realCfcAt Real.exp H = exp H by
    simpa only [one_mul, one_smul] using realCfcAt_exp_mul_eq H hH 1] at h
  exact (Real.exp_pos _).trans_le h

theorem operatorExp_smul_nonneg {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H) (s : ℝ) :
    0 ≤ exp (s • H) := by
  rw [← realCfcAt_exp_mul_eq H hH s, realCfcAt]
  apply cfc_nonneg
  intro z _
  change 0 ≤ Complex.ofReal (Real.exp (s * z.re))
  rw [← Complex.ofReal_zero, Complex.real_le_real]
  exact Real.exp_nonneg _

/-- Taking a nonnegative real power of a positive exponential multiplies its exponent. -/
theorem operatorRpow_exp_smul {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (s : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    operatorRpow (exp (s • H)) r = exp ((r * s) • H) := by
  rw [← realCfcAt_exp_mul_eq H hH s, ← realCfcAt_exp_mul_eq H hH (r * s)]
  let F (z : ℂ) := Complex.ofReal (z.re ^ r)
  let E (z : ℂ) := Complex.ofReal (Real.exp (s * z.re))
  have hE : Continuous E := Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul Complex.continuous_re))
  change cfc (p := IsStarNormal) F (cfc (p := IsStarNormal) E H) = _
  rw [← cfc_comp' F E H (continuous_operatorRpowSymbol hr).continuousOn
    hE.continuousOn hH.isStarNormal]
  apply cfc_congr
  intro z _
  change Complex.ofReal ((Complex.ofReal (Real.exp (s * z.re))).re ^ r) =
    Complex.ofReal (Real.exp ((r * s) * z.re))
  rw [Complex.ofReal_re, ← Real.exp_mul]
  exact congrArg (Complex.ofReal ∘ Real.exp) (by ring)

end FreeGroupHypercontractivity

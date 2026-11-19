module

public import «free-group-hypercontractivity».LpNorm
import all «free-group-hypercontractivity».Model

public section

namespace FreeGroupHypercontractivity

open scoped ComplexOrder

/-- The positive part of a signed self-adjoint operator, computed in the complex
functional calculus. -/
@[expose]
noncomputable def signedPositivePart {n : ℕ} (s : ℝ) (A : Operator n) : Operator n :=
  cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (max (s * z.re) 0)) A

private theorem continuous_signedPartSymbol (s : ℝ) :
    Continuous (fun z : ℂ ↦ Complex.ofReal (max (s * z.re) 0)) :=
  Complex.continuous_ofReal.comp ((Complex.continuous_re.const_mul s).max continuous_const)

private theorem continuous_signedPartPowerSymbol {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    Continuous (fun z : ℂ ↦ Complex.ofReal ((max (s * z.re) 0) ^ r)) :=
  Complex.continuous_ofReal.comp ((Real.continuous_rpow_const hr).comp
    ((Complex.continuous_re.const_mul s).max continuous_const))

theorem signedPositivePart_nonneg {n : ℕ} (s : ℝ) (A : Operator n) :
    0 ≤ signedPositivePart s A := by
  apply cfc_nonneg
  intro z _
  exact Complex.real_le_real.mpr (le_max_right _ _)

theorem signedPositivePart_mem {n : ℕ} {A : Operator n}
    (hA : A ∈ groupCStar n) (s : ℝ) : signedPositivePart s A ∈ groupCStar n :=
  cfc_mem_groupCStar _ hA

theorem signedPositivePart_sub {n : ℕ} {A : Operator n} (hA : IsSelfAdjoint A) :
    signedPositivePart 1 A - signedPositivePart (-1) A = A := by
  unfold signedPositivePart
  rw [← cfc_sub _ _ A (continuous_signedPartSymbol 1).continuousOn
    (continuous_signedPartSymbol (-1)).continuousOn]
  conv_rhs => rw [← cfc_id' ℂ A hA.isStarNormal]
  apply cfc_congr
  intro z hz
  change Complex.ofReal (max (1 * z.re) 0) -
    Complex.ofReal (max (-1 * z.re) 0) = z
  calc
    _ = Complex.ofReal z.re := by
      rw [← Complex.ofReal_sub]
      congr 1
      simp only [one_mul, neg_mul]
      rcases le_total 0 z.re with h | h
      · rw [max_eq_left h, max_eq_right (by linarith : -z.re ≤ 0)]
        ring
      · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -z.re)]
        ring
    _ = z := (hA.mem_spectrum_eq_re hz).symm

private theorem operatorRpow_signedPositivePart {n : ℕ} {A : Operator n}
    (hA : IsSelfAdjoint A) {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    operatorRpow (signedPositivePart s A) r =
      cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal ((max (s * z.re) 0) ^ r)) A := by
  unfold operatorRpow signedPositivePart
  rw [← cfc_comp' _ _ A (continuous_operatorRpowSymbol hr).continuousOn
    (continuous_signedPartSymbol s).continuousOn hA.isStarNormal]
  apply cfc_congr
  intro z _
  simp

private theorem mul_signedPart_rpow {s a r : ℝ} (hs : s = 1 ∨ s = -1) (hr : 0 < r) :
    a * (max (s * a) 0) ^ r = s * (max (s * a) 0) ^ (r + 1) := by
  have hmax : 0 ≤ max (s * a) 0 := le_max_right _ _
  rw [Real.rpow_add_of_nonneg hmax hr.le zero_le_one, Real.rpow_one]
  by_cases ha : 0 ≤ s * a
  · rw [max_eq_left ha]
    rcases hs with rfl | rfl <;> ring
  · rw [max_eq_right (le_of_not_ge ha), Real.zero_rpow hr.ne']
    simp

/-- A positive spectral test of a self-adjoint operator recovers its signed
moment on the corresponding half of the spectrum. -/
theorem traceRe_signedPositivePart_test {n : ℕ} {A : Operator n} (hA : IsSelfAdjoint A)
    {s r : ℝ} (hs : s = 1 ∨ s = -1) (hr : 0 < r) :
    traceRe (A * operatorRpow (signedPositivePart s A) r) =
      s * traceRe (operatorRpow (signedPositivePart s A) (r + 1)) := by
  suffices h : A * operatorRpow (signedPositivePart s A) r =
      (s : ℂ) • operatorRpow (signedPositivePart s A) (r + 1) by
    rw [h, traceRe_ofReal_smul]
  have hr1 : 0 ≤ r + 1 := by positivity
  rw [operatorRpow_signedPositivePart hA hr.le, operatorRpow_signedPositivePart hA hr1,
    ← cfc_const_mul _ _ A (continuous_signedPartPowerSymbol hr1 s).continuousOn]
  conv_lhs => enter [1]; rw [← cfc_id' ℂ A hA.isStarNormal]
  rw [← cfc_mul (fun z : ℂ ↦ z) _ A continuous_id.continuousOn
    (continuous_signedPartPowerSymbol hr.le s).continuousOn]
  apply cfc_congr
  intro z hz
  change z * Complex.ofReal ((max (s * z.re) 0) ^ r) =
    Complex.ofReal s * Complex.ofReal ((max (s * z.re) 0) ^ (r + 1))
  conv_lhs => enter [1]; rw [hA.mem_spectrum_eq_re hz]
  simp only [← Complex.ofReal_mul]
  exact congrArg Complex.ofReal (mul_signedPart_rpow hs hr)

end FreeGroupHypercontractivity

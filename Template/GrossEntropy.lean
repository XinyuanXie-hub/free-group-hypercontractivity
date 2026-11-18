module

import all Template.Model

public import Template.GroupCStar
public import Template.OperatorMajorant
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

public section

namespace FreeGroupHypercontractivity

open scoped ComplexOrder

/-- A positive input has the entropy formula used in the Gross argument, with the
trace moment and its exponent derivative written using the real functional calculus. -/
theorem entropy_sq_cfc_half_rpow {n : ℕ} (T : GroupCStar n)
    (hT : 0 ≤ (T : Operator n)) {r : ℝ} (hr : 0 < r) :
    let S := cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ (r / 2)) T
    let m := groupTraceReCLM n (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ r) T)
    entropy ((S : Operator n) ^ 2) =
      r * groupTraceReCLM n (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ r * Real.log x) T) -
        m * Real.log m := by
  let S := cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ (r / 2)) T
  let P := cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ r) T
  let f (x : ℝ) := x * Real.log x
  have hTsa : IsSelfAdjoint T := by
    change star T = T
    apply Subtype.ext
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).isSelfAdjoint.star_eq
  have hPsa : IsSelfAdjoint P := cfc_predicate _ _
  have hTspec (x : ℝ) (hx : x ∈ spectrum ℝ T) : 0 ≤ x := by
    have hxc : algebraMap ℝ ℂ x ∈ spectrum ℂ T := spectrum.algebraMap_mem ℂ hx
    rw [StarSubalgebra.spectrum_eq (S := groupCStar n)] at hxc
    simpa only [Complex.coe_algebraMap, Complex.ofReal_re] using
      (Complex.nonneg_iff.mp (spectrum_nonneg_of_nonneg hT hxc)).1
  have hhalf : Continuous (fun x : ℝ ↦ x ^ (r / 2)) :=
    Real.continuous_rpow_const (by positivity)
  have hpow : Continuous (fun x : ℝ ↦ x ^ r) := Real.continuous_rpow_const hr.le
  have hSsq : S ^ 2 = P := by
    dsimp only [S, P]
    rw [← cfc_pow _ 2 T hhalf.continuousOn hTsa]
    apply cfc_congr
    intro x hx
    change (x ^ (r / 2)) ^ (2 : ℕ) = x ^ r
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hTspec x hx)]
    congr 1
    ring
  have hpowlog (x : ℝ) (hx : x ∈ spectrum ℝ T) :
      f (x ^ r) = r * (x ^ r * Real.log x) := by
    rcases (hTspec x hx).eq_or_lt with rfl | hxpos
    · simp only [f, Real.zero_rpow hr.ne', Real.log_zero, mul_zero]
    · dsimp only [f]
      rw [Real.log_rpow hxpos]
      ring
  have hlog : ContinuousOn (fun x : ℝ ↦ x ^ r * Real.log x) (spectrum ℝ T) := by
    refine ((Real.continuous_mul_log.comp hpow).const_mul r⁻¹).continuousOn.congr ?_
    intro x hx
    change x ^ r * Real.log x = r⁻¹ * f (x ^ r)
    rw [hpowlog x hx, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hidentity : cfc (p := IsSelfAdjoint) f P =
      r • cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ r * Real.log x) T := by
    dsimp only [P]
    rw [← cfc_comp' _ _ T Real.continuous_mul_log.continuousOn hpow.continuousOn hTsa,
      ← cfc_const_mul _ _ T hlog]
    exact cfc_congr hpowlog
  have hcoeSq : (S : Operator n) ^ 2 = (P : Operator n) := by
    change ((S ^ 2 : GroupCStar n) : Operator n) = (P : Operator n)
    rw [hSsq]
  change entropy ((S : Operator n) ^ 2) = _
  rw [hcoeSq, entropy, ← groupCStar_coe_real_cfc f Real.continuous_mul_log P hPsa]
  simp only [← groupTraceReCLM_apply, hidentity, map_smul, smul_eq_mul, P]

/-- The trace of a real power is positive when the spectrum is bounded away from zero. -/
theorem groupTraceReCLM_cfc_rpow_pos {n : ℕ} (T : GroupCStar n) (hT : IsSelfAdjoint T)
    {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hspec : ∀ x ∈ spectrum ℝ T, a ≤ x) :
    0 < groupTraceReCLM n (cfc (p := IsSelfAdjoint) (fun x : ℝ ↦ x ^ r) T) := by
  let F (x : ℝ) := x ^ r
  let G (z : ℂ) := Complex.ofReal (F z.re)
  have hF : Continuous F := Real.continuous_rpow_const hr
  have hG : Continuous G := Complex.continuous_ofReal.comp (hF.comp Complex.continuous_re)
  have hT' : IsSelfAdjoint (T : Operator n) := hT.map (groupCStar n).subtype
  have hbound : algebraMap ℂ (Operator n) (Complex.ofReal (a ^ r)) ≤
      cfc (p := IsStarNormal) G (T : Operator n) := by
    refine algebraMap_le_cfc G _ _ ?_ hG.continuousOn hT'.isStarNormal
    intro z hz
    have hz' : z ∈ spectrum ℂ T := by
      rwa [StarSubalgebra.spectrum_eq (S := groupCStar n)]
    have hzre : z.re ∈ spectrum ℝ T := hT.spectrumRestricts.apply_mem hz'
    exact Complex.real_le_real.mpr (Real.rpow_le_rpow ha.le (hspec _ hzre) hr)
  have htrace := traceRe_mono hbound
  rw [Algebra.algebraMap_eq_smul_one, traceRe_ofReal_smul, traceRe_one, mul_one] at htrace
  change 0 < groupTraceReCLM n (cfc (p := IsSelfAdjoint) F T)
  rw [groupTraceReCLM_apply, groupCStar_coe_real_cfc F hF T hT]
  exact (Real.rpow_pos_of_pos ha r).trans_le htrace

end FreeGroupHypercontractivity

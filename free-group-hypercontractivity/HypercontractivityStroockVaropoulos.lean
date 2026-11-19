module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.L2Space

public section

namespace FreeGroupHypercontractivity

open MeasureTheory Set
open scoped Interval ENNReal

/-- The pointwise inequality underlying the Stroock–Varopoulos comparison of
Dirichlet forms at exponent (r>1). -/
theorem stroockVaropoulos_scalar {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 1 < r) :
    4 * (r - 1) * (a ^ (r / 2) - b ^ (r / 2)) ^ 2 ≤
      r ^ 2 * (a - b) * (a ^ (r - 1) - b ^ (r - 1)) := by
  wlog hba : b ≤ a generalizing a b
  · have h := this hb ha (le_of_not_ge hba)
    convert h using 1 <;> ring
  let e := r / 2 - 1
  let μ := (volume : Measure ℝ).restrict (Ioc b a)
  have he : -1 < e := by dsimp [e]; linarith
  have he₂ : -1 < 2 * e := by dsimp [e]; linarith
  have hLp : MemLp (fun x : ℝ ↦ x ^ e) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    have hin : Integrable (fun x : ℝ ↦ x ^ (2 * e)) μ :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hba).mp (intervalIntegral.intervalIntegrable_rpow' he₂)
    apply hin.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [mul_comm 2, Real.rpow_mul (hb.trans hx.1.le), Real.rpow_two]
  have hOne : MemLp (fun _ : ℝ ↦ (1 : ℝ)) 2 μ := by
    let : IsFiniteMeasure μ := by
      constructor
      simp [μ, Real.volume_Ioc]
    exact memLp_const 1
  have hnonneg : 0 ≤ᵐ[μ] (fun x : ℝ ↦ x ^ e) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact Real.rpow_nonneg (hb.trans hx.1.le) _
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (Real.HolderConjugate.two_two)
    hnonneg (Filter.Eventually.of_forall fun _ ↦ zero_le_one)
    (by simpa using hLp) (by simpa using hOne)
  simp only [mul_one, Real.one_rpow] at h
  have hPower : (∫ x, (x ^ e) ^ (2 : ℝ) ∂μ) = ∫ x, x ^ (2 * e) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [mul_comm 2, Real.rpow_mul (hb.trans hx.1.le)]
  rw [hPower] at h
  have h₁ : (∫ x, x ^ e ∂μ) = (a ^ (r / 2) - b ^ (r / 2)) / (r / 2) := by
    change (∫ x in Ioc b a, x ^ e) = _
    rw [← intervalIntegral.integral_of_le hba, integral_rpow (Or.inl he)]
    rw [show e + 1 = r / 2 by dsimp [e]; ring]
  have h₂ : (∫ x, x ^ (2 * e) ∂μ) =
      (a ^ (r - 1) - b ^ (r - 1)) / (r - 1) := by
    change (∫ x in Ioc b a, x ^ (2 * e)) = _
    rw [← intervalIntegral.integral_of_le hba, integral_rpow (Or.inl he₂)]
    rw [show 2 * e + 1 = r - 1 by dsimp [e]; ring]
  have h₃ : (∫ _ : ℝ, (1 : ℝ) ∂μ) = a - b := by
    change (∫ _ in Ioc b a, (1 : ℝ)) = _
    rw [← intervalIntegral.integral_of_le hba]
    simp
  rw [h₁, h₂, h₃, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  have hpos : 0 < r / 2 := by linarith
  have hp : 0 < r - 1 := by linarith
  have hdiff : 0 ≤ a ^ (r / 2) - b ^ (r / 2) :=
    sub_nonneg.mpr (Real.rpow_le_rpow hb hba hpos.le)
  have hd : 0 ≤ (a ^ (r - 1) - b ^ (r - 1)) / (r - 1) :=
    div_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hb hba hp.le)) hp.le
  have hs := pow_le_pow_left₀ (div_nonneg hdiff hpos.le) h 2
  rw [mul_pow, Real.sq_sqrt hd, Real.sq_sqrt (sub_nonneg.mpr hba), div_pow] at hs
  have hs' := (div_le_iff₀ (sq_pos_of_pos hpos)).mp hs
  apply (le_of_mul_le_mul_right ?_ hp)
  calc
    (4 * (r - 1) * (a ^ (r / 2) - b ^ (r / 2)) ^ 2) * (r - 1) ≤
        ((a ^ (r - 1) - b ^ (r - 1)) / (r - 1) * (a - b) * (r / 2) ^ 2) *
          (4 * (r - 1) ^ 2) := by
      convert mul_le_mul_of_nonneg_right hs' (by positivity : 0 ≤ 4 * (r - 1) ^ 2) using 1
      ring
    _ = _ := by field_simp; ring

end FreeGroupHypercontractivity

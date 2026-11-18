module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

public section

namespace FreeGroupHypercontractivity

open Set

/-- The logarithmic expression governing the derivative of the majorant gap. -/
private noncomputable def logarithmicSlope (x : ℝ) : ℝ :=
  x - x⁻¹ - 2 * Real.log x

private theorem hasDerivAt_logarithmicSlope {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt logarithmicSlope ((1 - x⁻¹) ^ 2) x := by
  unfold logarithmicSlope
  convert ((hasDerivAt_id x).sub (hasDerivAt_inv hx)).sub
    ((Real.hasDerivAt_log hx).const_mul 2) using 1
  · rfl
  · rw [← inv_pow]
    ring

private theorem monotoneOn_logarithmicSlope : MonotoneOn logarithmicSlope (Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · exact fun x hx ↦ (hasDerivAt_logarithmicSlope (ne_of_gt hx)).continuousAt.continuousWithinAt
  · rw [IsOpen.interior_eq isOpen_Ioi]
    exact fun x hx ↦ (hasDerivAt_logarithmicSlope (ne_of_gt hx)).differentiableAt.differentiableWithinAt
  · rw [IsOpen.interior_eq isOpen_Ioi]
    intro x hx
    rw [(hasDerivAt_logarithmicSlope (ne_of_gt hx)).deriv]
    exact sq_nonneg _

private noncomputable def cubicGap (x : ℝ) : ℝ :=
  (2 / 3 : ℝ) * x ^ 3 + x ^ 2 - 2 * x + 1 / 3 - 2 * x ^ 2 * Real.log x

private theorem hasDerivAt_cubicGap {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt cubicGap (2 * x * logarithmicSlope x) x := by
  have hid := hasDerivAt_id x
  have h₂ : HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x := by
    convert hid.pow 2 using 1 <;> first | rfl | norm_num [id]
  have h₃ : HasDerivAt (fun y : ℝ ↦ y ^ 3) (3 * x ^ 2) x := by
    convert hid.pow 3 using 1 <;> first | rfl | norm_num [id]
  unfold cubicGap logarithmicSlope
  convert ((((h₃.const_mul (2 / 3)).add h₂).sub (hid.const_mul 2)).add_const (1 / 3)).sub
    ((h₂.const_mul 2).mul (Real.hasDerivAt_log hx)) using 1
  · rfl
  · field_simp [hx]
    ring

private theorem cubicGap_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ cubicGap x := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num [cubicGap]
  have hc : ∀ y ∈ Ioi (0 : ℝ), ContinuousAt cubicGap y :=
    fun y hy ↦ (hasDerivAt_cubicGap (ne_of_gt hy)).continuousAt
  have h₁ : logarithmicSlope 1 = 0 := by norm_num [logarithmicSlope]
  have hm₁ : cubicGap 1 = 0 := by norm_num [cubicGap]
  by_cases h : x ≤ 1
  · have hanti : AntitoneOn cubicGap (Ioc 0 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 1) ?_ ?_ ?_
      · exact fun y hy ↦ (hc y hy.1).continuousWithinAt
      · rw [interior_Ioc]
        exact fun y hy ↦ (hasDerivAt_cubicGap (ne_of_gt hy.1)).differentiableAt.differentiableWithinAt
      · rw [interior_Ioc]
        intro y hy
        rw [(hasDerivAt_cubicGap (ne_of_gt hy.1)).deriv]
        have hs := monotoneOn_logarithmicSlope hy.1 (show (1 : ℝ) ∈ Ioi 0 by norm_num) hy.2.le
        rw [h₁] at hs
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hy.1.le) hs
    simpa [hm₁] using hanti ⟨hx, h⟩ (show (1 : ℝ) ∈ Ioc 0 1 from ⟨by norm_num, le_rfl⟩) h
  · have hmono : MonotoneOn cubicGap (Ici 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ ?_
      · exact fun y hy ↦ (hc y (zero_lt_one.trans_le hy)).continuousWithinAt
      · rw [interior_Ici]
        exact fun y hy ↦ (hasDerivAt_cubicGap (ne_of_gt (zero_lt_one.trans hy))).differentiableAt.differentiableWithinAt
      · rw [interior_Ici]
        intro y hy
        rw [(hasDerivAt_cubicGap (ne_of_gt (zero_lt_one.trans hy))).deriv]
        have hs := monotoneOn_logarithmicSlope
          (show (1 : ℝ) ∈ Ioi 0 by norm_num) (zero_lt_one.trans hy) (le_of_lt hy)
        rw [h₁] at hs
        exact mul_nonneg (mul_nonneg (by norm_num) (zero_lt_one.trans hy).le) hs
    simpa [hm₁] using hmono (show (1 : ℝ) ∈ Ici 1 from le_rfl) (le_of_not_ge h) (le_of_not_ge h)

/-- The cubic majorant in Lemma 3.1 of Xie and Zhang. -/
theorem cubic_log_majorant {t l : ℝ} (ht : 0 ≤ t) (hl : 0 < l) :
    2 * t ^ 2 * Real.log t ≤
      2 / (3 * l) * t ^ 3 + (2 * Real.log l + 1) * t ^ 2 - 2 * l * t + l ^ 2 / 3 := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa using div_nonneg (sq_nonneg l) (show (0 : ℝ) ≤ 3 by norm_num)
  have hscaled := mul_nonneg (sq_nonneg l) (cubicGap_nonneg (div_nonneg ht.le hl.le))
  rw [cubicGap, Real.log_div ht.ne' hl.ne'] at hscaled
  have hidentity :
      l ^ 2 * ((2 / 3 : ℝ) * (t / l) ^ 3 + (t / l) ^ 2 - 2 * (t / l) + 1 / 3 -
          2 * (t / l) ^ 2 * (Real.log t - Real.log l)) =
        (2 / (3 * l) * t ^ 3 + (2 * Real.log l + 1) * t ^ 2 - 2 * l * t + l ^ 2 / 3) -
          2 * t ^ 2 * Real.log t := by
    field_simp
    ring
  exact sub_nonneg.mp (hidentity ▸ hscaled)

/-- The numerical entropy bound without rescaling the second moment. -/
theorem entropy_le_of_cubic_unnormalized {a q m2 m3 E : ℝ} (hm2 : 0 < m2) (hl : 0 < a + q)
    (hm : m3 ≤ a ^ 3 + 3 * a * (m2 - a ^ 2) + 3 * (m2 - a ^ 2) * q + q ^ 3)
    (hE : E ≤ 2 / (3 * (a + q)) * m3 + (2 * Real.log (a + q) + 1) * m2 -
        2 * (a + q) * a + (a + q) ^ 2 / 3 - m2 * Real.log m2) :
    E ≤ 2 * (m2 - a ^ 2 + q ^ 2) := by
  let l := a + q
  change 0 < l at hl
  change E ≤ 2 / (3 * l) * m3 + (2 * Real.log l + 1) * m2 -
    2 * l * a + l ^ 2 / 3 - m2 * Real.log m2 at hE
  have hm' : m3 ≤ 3 * m2 * l - 3 * a * l ^ 2 + l ^ 3 := by
    convert hm using 1
    dsimp [l]
    ring
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (sq_pos_of_pos hl) hm2)) hm2.le
  rw [Real.log_div (pow_ne_zero 2 hl.ne') hm2.ne', Real.log_pow] at hlog
  norm_num at hlog
  have hcancel : m2 * (l ^ 2 / m2 - 1) = l ^ 2 - m2 := by
    field_simp
  rw [hcancel] at hlog
  have hmajor :
      2 / (3 * l) * (3 * m2 * l - 3 * a * l ^ 2 + l ^ 3) + (2 * Real.log l + 1) * m2 -
          2 * l * a + l ^ 2 / 3 - m2 * Real.log m2 =
        2 * (m2 - a ^ 2 + q ^ 2) - (l ^ 2 - m2 - m2 * (2 * Real.log l - Real.log m2)) := by
    field_simp
    simp only [l]
    ring
  have hmul := mul_le_mul_of_nonneg_left hm' (show 0 ≤ 2 / (3 * l) by positivity)
  linarith

end FreeGroupHypercontractivity

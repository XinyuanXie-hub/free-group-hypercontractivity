module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Calculus.MeanValue

public section

namespace FreeGroupHypercontractivity

open Set
open scoped Polynomial

private theorem exists_polynomial_primitive (p : ℝ[X]) :
    ∃ q : ℝ[X], q.derivative = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨P, rfl⟩ := hp
    obtain ⟨Q, rfl⟩ := hq
    exact ⟨P + Q, Polynomial.derivative_add⟩
  | monomial n c =>
    refine ⟨Polynomial.monomial (n + 1) (c / (n + 1)), ?_⟩
    rw [Polynomial.derivative_monomial_succ, div_mul_cancel₀ _ (by positivity)]

/-- Simultaneous uniform approximation of a function and its derivative on a closed interval. -/
theorem exists_polynomial_near_of_hasDerivWithinAt {a b : ℝ} (hab : a ≤ b)
    {f f' : ℝ → ℝ} (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hc : ContinuousOn f' (Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], (∀ x ∈ Icc a b, |p.eval x - f x| < ε) ∧
      (∀ x ∈ Icc a b, |p.derivative.eval x - f' x| < ε) := by
  let d := ε / (b - a + 1)
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hd0 : 0 < d := div_pos hε (by linarith)
  have hde : d ≤ ε := div_le_self hε.le (by linarith)
  have hdbe : d * (b - a) < ε := by
    have hmul : d * (b - a + 1) = ε := div_mul_cancel₀ _ (by positivity)
    linarith
  obtain ⟨g, hg⟩ := exists_polynomial_near_of_continuousOn a b f' hc d hd0
  obtain ⟨q, hq⟩ := exists_polynomial_primitive g
  let p := q + Polynomial.C (f a - q.eval a)
  have hpd : p.derivative = g := by simp [p, hq]
  have hpa : p.eval a = f a := by simp [p]
  refine ⟨p, ?_, ?_⟩
  · have hderiv : ∀ x ∈ Icc a b,
        HasDerivWithinAt (fun y ↦ p.eval y - f y)
          (g.eval x - f' x) (Icc a b) x := by
      intro x hx
      simpa only [hpd] using (p.hasDerivAt x).hasDerivWithinAt.fun_sub (hd x hx)
    have hbound : ∀ x ∈ Ico a b, ‖g.eval x - f' x‖ ≤ d := by
      intro x hx
      rw [Real.norm_eq_abs]
      exact (hg x (Ico_subset_Icc_self hx)).le
    intro x hx
    have he := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound x hx
    rw [hpa, sub_self, sub_zero, Real.norm_eq_abs] at he
    exact (he.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 a) hd0.le)).trans_lt hdbe
  · intro x hx
    rw [hpd]
    exact (hg x hx).trans_le hde

end FreeGroupHypercontractivity

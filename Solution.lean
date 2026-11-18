module

import all Template.Model

public import Template.FaithfulTrace
public import Template.HypercontractivityAll
public import Template.HypercontractivityBridge
public import Template.LogSobolev
public import Template.Sharpness
public import Template.ThirdMoment

public section

namespace FreeGroupHypercontractivity

/-- Theorem 1.2 of Xie and Zhang on positive Fourier polynomials. -/
theorem theorem_1_2 (n : ℕ) (_hn : 2 ≤ n) (x : GroupAlgebra n)
    (hx : 0 ≤ regularImage x) :
    entropy (regularImage x ^ 2) ≤
      2 * traceRe (regularImage x * regularImage (generator x)) := by
  by_cases hzero : x = 0
  · subst x
    simp [entropy]
  have hsa := (ContinuousLinearMap.nonneg_iff_isPositive.mp hx).isSelfAdjoint
  exact logSobolev_of_centered_cubic x hx
    (traceRe_regularImage_pos hx hzero) (traceRe_regularImage_sq_pos hx hzero)
    (third_moment_bound (centered x) (centered_coeff_one hsa))

/-- Theorem 1.1 of Xie and Zhang in its Fourier-polynomial formulation. -/
theorem theorem_1_1 (n : ℕ) (hn : 2 ≤ n) (p q t : ℝ)
    (hp : 1 < p) (hpq : p ≤ q) (ht : 0 ≤ t) :
    (∀ x : GroupAlgebra n, lpNorm q (poisson t x) ≤ lpNorm p x) ↔
      (1 / 2 : ℝ) * Real.log ((q - 1) / (p - 1)) ≤ t := by
  refine ⟨hypercontractivity_necessary n hn p q t hp hpq, ?_⟩
  intro hthreshold x
  rcases ht.eq_or_lt with rfl | htpos
  · rw [poisson_zero_time, exponents_eq_of_zero_time hp hpq hthreshold]
  have hpositive := positive_groupCStar_contractivity_of_logSobolev
    (theorem_1_2 n hn) hp hpq htpos hthreshold
  have h := groupCStar_contractivity_of_positive (zero_lt_one.trans hp) (hp.trans_le hpq)
    htpos.le hpositive (polynomialInclusion n x)
  simpa only [poissonCStar_apply_polynomial htpos.le, polynomialInclusion_coe,
    ← lpNorm_eq_operatorLpNorm] using h

end FreeGroupHypercontractivity

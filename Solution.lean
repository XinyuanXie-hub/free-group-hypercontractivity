module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».FaithfulTrace
public import «free-group-hypercontractivity».HypercontractivityAll
public import «free-group-hypercontractivity».HypercontractivityBridge
public import «free-group-hypercontractivity».LogSobolev
public import «free-group-hypercontractivity».LpCompletion
public import «free-group-hypercontractivity».LpNorm
public import «free-group-hypercontractivity».Sharpness
public import «free-group-hypercontractivity».ThirdMoment

public section

namespace FreeGroupHypercontractivity

private theorem logSobolev_fourier (n : ℕ) (x : GroupAlgebra n)
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

private theorem poisson_fourier_iff (n : ℕ) (hn : 2 ≤ n) (p q t : ℝ)
    (hp : 1 < p) (hpq : p ≤ q) (ht : 0 ≤ t) :
    (∀ x : GroupAlgebra n, lpNorm q (poisson t x) ≤ lpNorm p x) ↔
      (1 / 2 : ℝ) * Real.log ((q - 1) / (p - 1)) ≤ t := by
  refine ⟨hypercontractivity_necessary n hn p q t hp hpq, ?_⟩
  intro hthreshold x
  rcases ht.eq_or_lt with rfl | htpos
  · rw [poisson_zero_time, exponents_eq_of_zero_time hp hpq hthreshold]
  have hpositive := positive_groupCStar_contractivity_of_logSobolev
    (logSobolev_fourier n) hp hpq htpos hthreshold
  have h := groupCStar_contractivity_of_positive (zero_lt_one.trans hp) (hp.trans_le hpq)
    htpos.le hpositive (polynomialInclusion n x)
  simpa only [poissonCStar_apply_polynomial htpos.le, polynomialInclusion_coe,
    ← lpNorm_eq_operatorLpNorm] using h

/-- Theorem 1.1. The Poisson Fourier multiplier has a contractive complex
linear extension between the tracial Lp and Lq completions exactly at the
stated times. -/
theorem theorem_1_1 (n : ℕ) (hn : 2 ≤ n) (p q t : ℝ)
    (hp : 1 < p) (hpq : p ≤ q) (ht : 0 ≤ t) :
    ∃ (Np : FourierLpNorm n p) (Nq : FourierLpNorm n q),
      ((∃ P : FourierLp Np →L[ℂ] FourierLp Nq,
          (∀ x : GroupAlgebra n, P (fourierLpEmbed Np x) = fourierLpEmbed Nq (poisson t x)) ∧
          ∀ x : FourierLp Np, ‖P x‖ ≤ ‖x‖) ↔
        (1 / 2 : ℝ) * Real.log ((q - 1) / (p - 1)) ≤ t) := by
  let Np := fourierLpNorm n p hp
  let Nq := fourierLpNorm n q (hp.trans_le hpq)
  exact ⟨Np, Nq, (poisson_completion_iff Np Nq t).trans (poisson_fourier_iff n hn p q t hp hpq ht)⟩

local notation "L" => generator

/-- Theorem 1.2 of Xie and Zhang, equation (1.1). -/
theorem theorem_1_2 (n : ℕ) (_hn : 2 ≤ n) (x : GroupAlgebra n)
    (hx : 0 ≤ regularImage x) :
    Ent (x ^ 2) ≤ 2 * τ (x * L x) := by
  rw [Ent, regularImage_pow, τ, ← traceRe_regularImage, regularImage_mul]
  exact logSobolev_fourier n x hx

end FreeGroupHypercontractivity

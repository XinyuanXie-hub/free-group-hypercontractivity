module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».FaithfulTrace
public import «free-group-hypercontractivity».FormEntropy
public import «free-group-hypercontractivity».FormLogSobolev
public import «free-group-hypercontractivity».HypercontractivityAll
public import «free-group-hypercontractivity».HypercontractivityBridge
public import «free-group-hypercontractivity».LogSobolev
public import «free-group-hypercontractivity».LpInclusionInjective
public import «free-group-hypercontractivity».Sharpness
public import «free-group-hypercontractivity».ThirdMoment

public section

namespace FreeGroupHypercontractivity

open scoped ENNReal

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

local notation "P[" t "]" => poissonLp t
local notation "‖" x "‖[" q "]" => extendedLpNorm q x

/-- Theorem 1.1. The sharp hypercontractive inequality on tracial Lp. -/
theorem theorem_1_1 (n : ℕ) (hn : 2 ≤ n) (p q t : ℝ)
    (hp : 1 < p) (hpq : p ≤ q) (ht : 0 ≤ t) :
    (∀ x : Lp n p, ‖P[t] x‖[q] ≤ ‖x‖[p]) ↔
      (1 / 2 : ℝ) * Real.log ((q - 1) / (p - 1)) ≤ t := by
  have hinj := lpInclusion_injective (n := n) hp hpq
  have hq := hp.trans_le hpq
  have hself := (poisson_fourier_iff n hn p p t hp le_rfl ht).mpr (by
    rw [div_self (by linarith : p - 1 ≠ 0), Real.log_one, mul_zero]
    exact ht)
  constructor
  · intro h
    apply (poisson_fourier_iff n hn p q t hp hpq ht).mp
    intro a
    have ha := h (lpEmbed n p a)
    rw [poissonLp_coe hp hself, ← lpInclusion_coe hp hpq (poisson t a),
      extendedLpNorm_of_inclusion hinj, extendedLpNorm_self] at ha
    simpa only [enorm_le_iff_norm_le, norm_lpEmbed hp, norm_lpEmbed hq] using ha
  · intro h x
    have hc := (poisson_fourier_iff n hn p q t hp hpq ht).mpr h
    rw [extendedLpNorm_self, ← lpInclusion_poissonLpTo hp hpq hc x,
      extendedLpNorm_of_inclusion hinj]
    exact enorm_le_iff_norm_le.mpr (poissonLpTo_norm_le hp hq hc x)

private theorem poisson_two_sharp (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : 0 < t)
    (x : GroupAlgebra n) :
    lpNorm (1 + Real.exp (2 * t)) (poisson t x) ≤ lpNorm 2 x := by
  have hq : (2 : ℝ) ≤ 1 + Real.exp (2 * t) := by
    linarith [Real.one_le_exp_iff.mpr (show 0 ≤ 2 * t by positivity)]
  have hthreshold :
      (1 / 2 : ℝ) * Real.log (((1 + Real.exp (2 * t)) - 1) / (2 - 1)) ≤ t := by
    rw [show ((1 + Real.exp (2 * t)) - 1) / (2 - 1) = Real.exp (2 * t) by ring,
      Real.log_exp]
    linarith
  exact (poisson_fourier_iff n hn 2 _ t (by norm_num) hq ht.le).mpr hthreshold x

local notation "L" => generator
local notation "τ(" x ")" => traceRe (regularImage x)
local notation "Ent(" x ")" => entropy (regularImage x)

/-- Theorem 1.2, equation (1.1) and the natural form-domain extension. -/
theorem theorem_1_2 (n : ℕ) (hn : 2 ≤ n) :
    (∀ x : GroupAlgebra n, 0 ≤ regularImage x → Ent(x ^ 2) ≤ 2 * τ(x * L x)) ∧
    (∀ x : PositiveAffiliatedL2 n, inFormDomain x.fourierVector →
      x.entropySq ≤ ↑(2 * formEnergy x.fourierVector)) := by
  constructor
  · intro x hx
    rw [regularImage_pow, regularImage_mul]
    exact logSobolev_fourier n x hx
  · intro x hx
    apply affiliated_entropySq_le_of_gibbs x (2 * formEnergy x.fourierVector)
    intro K hKm hK
    exact form_logSobolev_test (poisson_two_sharp n hn) x.fourierVector hx K hKm hK

end FreeGroupHypercontractivity

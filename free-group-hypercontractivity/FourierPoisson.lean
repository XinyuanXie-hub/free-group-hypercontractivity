module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».FourierEnergy
public import «free-group-hypercontractivity».PoissonExtension

public section

namespace FreeGroupHypercontractivity

open Filter
open scoped Topology

theorem operatorCoeff_poissonCStar {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (A : GroupCStar n) (g : Group n) :
    operatorCoeff (poissonCStar n t A : Operator n) g =
      Complex.ofReal (Real.exp (-t * (FreeGroup.norm g : ℝ))) *
        operatorCoeff (A : Operator n) g := by
  simpa only [operatorCoeff, operatorEntry, inv_one, mul_one] using
    poissonCStar_operatorEntry ht A g 1

/-- The Poisson multiplier is symmetric with respect to the canonical trace. -/
theorem traceRe_poisson_mul_comm {n : ℕ} {t : ℝ} {B C : GroupCStar n} (ht : 0 ≤ t)
    (hB : IsSelfAdjoint (B : Operator n)) (hC : IsSelfAdjoint (C : Operator n)) :
    traceRe ((B : Operator n) * (poissonCStar n t C : Operator n)) =
      traceRe ((C : Operator n) * (poissonCStar n t B : Operator n)) := by
  rw [traceRe_mul_eq_tsum_of_selfAdjoint hB, traceRe_mul_eq_tsum_of_selfAdjoint hC]
  apply tsum_congr
  intro g
  rw [operatorCoeff_poissonCStar ht C, operatorCoeff_poissonCStar ht B,
    mul_left_comm (star (operatorCoeff (B : Operator n) g)),
    mul_left_comm (star (operatorCoeff (C : Operator n) g)),
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  congr 1
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem poissonCStar_generator_comparison {n : ℕ} {A B : GroupCStar n}
    (hA : IsSelfAdjoint (A : Operator n)) (hB : IsSelfAdjoint (B : Operator n))
    (x : GroupAlgebra n) {c d : ℝ} (hc : 0 < c)
    (hcomparison : ∀ t : ℝ, 0 < t →
      c * traceRe ((A : Operator n) * ((A : Operator n) - (poissonCStar n t A : Operator n))) ≤
        d * traceRe ((B : Operator n) * (regularImage x - regularImage (poisson t x)))) :
    InEnergyDomain (A : Operator n) ∧
      c * operatorEnergy (A : Operator n) ≤ d * traceRe ((B : Operator n) * regularImage (generator x)) := by
  refine generator_bound_of_poisson_comparison hB x hc ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have h := div_le_div_of_nonneg_right (hcomparison t ht) ht.le
  rw [mul_div_assoc, mul_div_assoc,
    traceRe_mul_difference_eq_fourier t hA (operatorCoeff_poissonCStar ht.le A),
    traceRe_mul_difference_eq_fourier t hB (fun g ↦ by simp [poisson_coeff])] at h
  simpa only [operatorCoeff_regularImage, Complex.star_def, Complex.conj_mul',
    ← Complex.ofReal_pow, Complex.ofReal_re] using h

end FreeGroupHypercontractivity

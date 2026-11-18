module

import all Template.Model

public import Template.PoissonExtension
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

public section

namespace FreeGroupHypercontractivity

open scoped BigOperators

theorem multiplier_eq_sum {n : ℕ} (x : GroupAlgebra n) (m : Group n → ℂ) :
    multiplier m x =
      ∑ g ∈ x.coeff.support, MonoidAlgebra.single g (m g * x.coeff g) := by
  classical
  ext g
  simp only [multiplier_coeff, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finset.sum_apply',
    Finsupp.single_apply, Finset.sum_ite_eq']
  split_ifs with hg
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hg, mul_zero]

private theorem polynomialInclusion_multiplier_eq_sum {n : ℕ}
    (x : GroupAlgebra n) (m : Group n → ℂ) :
    polynomialInclusion n (multiplier m x) =
      ∑ g ∈ x.coeff.support,
        m g • polynomialInclusion n (MonoidAlgebra.single g (x.coeff g)) := by
  classical
  rw [multiplier_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [← map_smul, MonoidAlgebra.smul_single, smul_eq_mul]

/-- The Poisson path through a Fourier polynomial has derivative (-L P_t x)
in the operator norm, with values in the reduced group algebra. -/
theorem hasDerivAt_poisson_path {n : ℕ} (x : GroupAlgebra n) (t : ℝ) :
    HasDerivAt (fun s ↦ polynomialInclusion n (poisson s x))
      (-polynomialInclusion n (generator (poisson t x))) t := by
  let wordLength (g : Group n) : ℝ := FreeGroup.norm g
  let T (g : Group n) := polynomialInclusion n (MonoidAlgebra.single g (x.coeff g))
  have hd (g : Group n) :
      HasDerivAt (fun s : ℝ ↦ Real.exp (-s * wordLength g) • T g)
        ((-wordLength g * Real.exp (-t * wordLength g)) • T g) t := by
    simpa only [Pi.neg_apply, id_eq, neg_mul, one_mul, mul_comm (Real.exp _)] using
      (((hasDerivAt_id t).neg.mul_const (wordLength g)).exp.smul_const (T g))
  have h := HasDerivAt.fun_sum (u := x.coeff.support) (fun g _ ↦ hd g)
  convert h using 1
  · ext s
    rw [poisson, polynomialInclusion_multiplier_eq_sum]
    rfl
  · have heq : generator (poisson t x) =
        multiplier (fun g ↦ Complex.ofReal (wordLength g * Real.exp (-t * wordLength g))) x := by
      ext g
      simp [wordLength, Complex.ofReal_mul, mul_assoc]
    rw [heq, polynomialInclusion_multiplier_eq_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro g _
    rw [← neg_smul, Complex.ofReal_mul, ← neg_mul, ← Complex.ofReal_neg,
      ← Complex.ofReal_mul]
    exact IsScalarTower.algebraMap_smul (R := ℝ) (A := ℂ) (M := GroupCStar n) _ (T g)

@[simp]
theorem poisson_zero_time {n : ℕ} (x : GroupAlgebra n) : poisson 0 x = x := by
  ext g
  simp

end FreeGroupHypercontractivity

module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».Trace
public import «free-group-hypercontractivity».Moments
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

public section

namespace FreeGroupHypercontractivity

open Filter
open scoped Topology

/-- Fourier weight of the Poisson difference quotient at time zero. -/
@[expose]
noncomputable def poissonDifferenceWeight (t l : ℝ) : ℝ :=
  (1 - Real.exp (-t * l)) / t

theorem poissonDifferenceWeight_nonneg {t l : ℝ} (ht : 0 < t) (hl : 0 ≤ l) :
    0 ≤ poissonDifferenceWeight t l := by
  unfold poissonDifferenceWeight
  apply div_nonneg _ ht.le
  apply sub_nonneg.mpr
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem poissonDifferenceWeight_le_length {t l : ℝ} (ht : 0 < t) :
    poissonDifferenceWeight t l ≤ l := by
  unfold poissonDifferenceWeight
  rw [div_le_iff₀ ht]
  linarith [Real.add_one_le_exp (-t * l)]

theorem poissonDifferenceWeight_le_inv {t l : ℝ} (ht : 0 < t) :
    poissonDifferenceWeight t l ≤ 1 / t := by
  exact div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_nonneg _)) ht.le

theorem tendsto_poissonDifferenceWeight (l : ℝ) :
    Tendsto (fun t ↦ poissonDifferenceWeight t l) (𝓝[>] (0 : ℝ)) (𝓝 l) := by
  have harg : HasDerivAt (fun t : ℝ ↦ -t * l) (-l) 0 := by
    simpa only [id_eq, Pi.neg_apply, neg_one_mul] using
      ((hasDerivAt_id (0 : ℝ)).neg).mul_const l
  have hd := (Real.hasDerivAt_exp (- (0 : ℝ) * l)).comp 0 harg
  have hf : HasDerivAt (fun t : ℝ ↦ 1 - Real.exp (-t * l)) l 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hd using 1
    · funext t; rfl
    · norm_num
  simpa [poissonDifferenceWeight, div_eq_mul_inv, mul_comm] using hf.tendsto_slope_zero_right

theorem tendsto_poisson_energy {ι : Type*} (l : ι → ℝ) (b : ι → ℝ)
    (hl : ∀ i, 0 ≤ l i) (hs : Summable (fun i ↦ l i * |b i|)) :
    Tendsto (fun t ↦ ∑' i, poissonDifferenceWeight t (l i) * b i)
      (𝓝[>] (0 : ℝ)) (𝓝 (∑' i, l i * b i)) := by
  refine tendsto_tsum_of_dominated_convergence hs
    (fun i ↦ (tendsto_poissonDifferenceWeight (l i)).mul_const (b i)) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht i
  change 0 < t at ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poissonDifferenceWeight_nonneg ht (hl i))]
  exact mul_le_mul_of_nonneg_right (poissonDifferenceWeight_le_length ht) (abs_nonneg _)

/-- A uniform bound on the Poisson difference quotients gives summability of the
word-length weighted Fourier energies. -/
theorem summable_of_poisson_energy_bound {ι : Type*} {l b : ι → ℝ}
    (hl : ∀ i, 0 ≤ l i) (hb : ∀ i, 0 ≤ b i) (hs : Summable b) {C : ℝ}
    (hC : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∑' i, poissonDifferenceWeight t (l i) * b i) ≤ C) :
    Summable (fun i ↦ l i * b i) := by
  refine summable_of_sum_le (c := C) (fun i ↦ mul_nonneg (hl i) (hb i)) fun s ↦ ?_
  have hlim : Tendsto (fun t : ℝ ↦ ∑ i ∈ s, poissonDifferenceWeight t (l i) * b i)
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ i ∈ s, l i * b i)) :=
    tendsto_finsetSum _ fun i _ ↦ (tendsto_poissonDifferenceWeight (l i)).mul_const (b i)
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin, hC] with t ht htC
  change 0 < t at ht
  have hnonneg i := mul_nonneg (poissonDifferenceWeight_nonneg ht (hl i)) (hb i)
  have hsum : Summable (fun i ↦ poissonDifferenceWeight t (l i) * b i) :=
    Summable.of_nonneg_of_le hnonneg
      (fun i ↦ mul_le_mul_of_nonneg_right (poissonDifferenceWeight_le_inv ht) (hb i))
      (hs.mul_left (1 / t))
  exact (hsum.sum_le_tsum s (fun i _ ↦ hnonneg i)).trans htC

open scoped InnerProductSpace

/-- Fourier coefficient of an operator obtained by applying it to the identity vector. -/
@[expose]
noncomputable def operatorCoeff {n : ℕ} (A : Operator n) (g : Group n) : ℂ :=
  A (lp.single 2 1 1) g

@[simp]
theorem operatorCoeff_regularImage {n : ℕ} (x : GroupAlgebra n) (g : Group n) :
    operatorCoeff (regularImage x) g = x.coeff g := regularImage_delta x g

theorem summable_operatorCoeff_norm_sq {n : ℕ} (A : Operator n) :
    Summable (fun g ↦ ‖operatorCoeff A g‖ ^ 2) := by
  have h := (lp.memℓp (A (lp.single 2 1 1))).summable (by norm_num)
  simpa [operatorCoeff, ENNReal.toReal_ofNat, Real.rpow_natCast] using h

theorem traceRe_mul_eq_tsum_of_selfAdjoint {n : ℕ} {A B : Operator n}
    (hA : IsSelfAdjoint A) :
    traceRe (A * B) = ∑' g, (star (operatorCoeff A g) * operatorCoeff B g).re := by
  let v : Hilbert n := lp.single 2 1 1
  rw [traceRe_as_inner]
  change (⟪v, A (B v)⟫_ℂ).re = _
  have hAd : A.adjoint = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hA
  rw [← hAd, ContinuousLinearMap.adjoint_inner_right, hAd, lp.inner_eq_tsum]
  rw [← RCLike.re_to_complex, RCLike.re_tsum ℂ (lp.summable_inner (A v) (B v))]
  simp only [RCLike.re_to_complex, RCLike.inner_apply', operatorCoeff, v]
  rfl

/-- Difference of two Fourier multipliers expressed through the trace pairing. -/
theorem traceRe_mul_difference_eq_fourier {n : ℕ} {A B W : Operator n} (t : ℝ)
    (hA : IsSelfAdjoint A)
    (hW : ∀ g, operatorCoeff W g =
      Complex.ofReal (Real.exp (-t * (FreeGroup.norm g : ℝ))) * operatorCoeff B g) :
    traceRe (A * (B - W)) / t = ∑' g, poissonDifferenceWeight t (FreeGroup.norm g) *
      (star (operatorCoeff A g) * operatorCoeff B g).re := by
  rw [traceRe_mul_eq_tsum_of_selfAdjoint hA, div_eq_mul_inv, ← tsum_mul_right]
  apply tsum_congr
  intro g
  have hcoeff : operatorCoeff (B - W) g = operatorCoeff B g - operatorCoeff W g := by
    simp [operatorCoeff]
  rw [hcoeff, hW, mul_sub, mul_left_comm (star (operatorCoeff A g)),
    Complex.sub_re, Complex.re_ofReal_mul]
  unfold poissonDifferenceWeight
  ring

/-- The word-length quadratic form on the Fourier coefficients of an operator. -/
@[expose]
noncomputable def operatorEnergy {n : ℕ} (A : Operator n) : ℝ :=
  ∑' g, (FreeGroup.norm g : ℝ) * ‖operatorCoeff A g‖ ^ 2

/-- An operator is in the quadratic form domain when its weighted squares are summable. -/
@[expose]
def InEnergyDomain {n : ℕ} (A : Operator n) : Prop :=
  Summable (fun g ↦ (FreeGroup.norm g : ℝ) * ‖operatorCoeff A g‖ ^ 2)

theorem regularImage_inEnergyDomain {n : ℕ} (x : GroupAlgebra n) :
    InEnergyDomain (regularImage x) := by
  apply summable_of_ne_finset_zero (s := x.coeff.support)
  intro g hg
  simp [Finsupp.notMem_support_iff.mp hg]

theorem operatorEnergy_regularImage {n : ℕ} {x : GroupAlgebra n}
    (hx : IsSelfAdjoint (regularImage x)) :
    operatorEnergy (regularImage x) =
      traceRe (regularImage x * regularImage (generator x)) := by
  rw [traceRe_image_generator x (coeff_inv_of_selfAdjoint hx)]
  unfold operatorEnergy
  simp only [operatorCoeff_regularImage]
  exact tsum_eq_sum (fun g hg ↦ by simp [Finsupp.notMem_support_iff.mp hg])

theorem poisson_energy_limit_polynomial {n : ℕ} {A : Operator n}
    (hA : IsSelfAdjoint A) (x : GroupAlgebra n) :
    Tendsto (fun t ↦ ∑' g, poissonDifferenceWeight t (FreeGroup.norm g) *
      (star (operatorCoeff A g) * x.coeff g).re) (𝓝[>] (0 : ℝ))
      (𝓝 (traceRe (A * regularImage (generator x)))) := by
  have h := tendsto_poisson_energy (fun g : Group n ↦ (FreeGroup.norm g : ℝ))
    (fun g ↦ (star (operatorCoeff A g) * x.coeff g).re) (fun _ ↦ by positivity)
    (summable_of_ne_finset_zero (s := x.coeff.support)
      (fun g hg ↦ by simp [Finsupp.notMem_support_iff.mp hg]))
  convert h using 1
  rw [traceRe_mul_eq_tsum_of_selfAdjoint hA]
  congr 1
  apply tsum_congr
  intro g
  rw [operatorCoeff_regularImage, generator_coeff, mul_left_comm (star (operatorCoeff A g))]
  rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]

/-- Transfer a finite-time difference-quotient comparison to the generator at a
Fourier polynomial, allowing the tested operators themselves to have infinite support. -/
theorem generator_bound_of_poisson_comparison {n : ℕ} {A B : Operator n}
    (hB : IsSelfAdjoint B) (x : GroupAlgebra n) {c d : ℝ} (hc : 0 < c)
    (hcompare : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      c * (∑' g, poissonDifferenceWeight t (FreeGroup.norm g) * ‖operatorCoeff A g‖ ^ 2) ≤
        d * (∑' g, poissonDifferenceWeight t (FreeGroup.norm g) *
          (star (operatorCoeff B g) * x.coeff g).re)) :
    InEnergyDomain A ∧ c * operatorEnergy A ≤ d * traceRe (B * regularImage (generator x)) := by
  have hright := (poisson_energy_limit_polynomial hB x).const_mul d
  have hC := hright.eventually (gt_mem_nhds (lt_add_one _))
  have hdomain : InEnergyDomain A := by
    apply summable_of_poisson_energy_bound (fun _ ↦ by positivity) (fun _ ↦ sq_nonneg _)
      (summable_operatorCoeff_norm_sq A) (C := (d * traceRe (B * regularImage (generator x)) + 1) / c)
    filter_upwards [hC, hcompare] with t hlt hle
    apply (le_div_iff₀ hc).mpr
    rw [mul_comm]
    exact hle.trans hlt.le
  refine ⟨hdomain, le_of_tendsto_of_tendsto ?_ hright hcompare⟩
  apply Tendsto.const_mul
  apply tendsto_poisson_energy _ _ (fun _ ↦ by positivity)
  simpa only [InEnergyDomain, abs_pow, abs_norm] using hdomain

end FreeGroupHypercontractivity

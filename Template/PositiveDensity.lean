module

import all Template.Model

public import Template.HypercontractivityNorm
public import Template.PoissonExtension
public import Template.OperatorMajorant

public section

namespace FreeGroupHypercontractivity

open Filter Set
open scoped Topology ComplexOrder

/-- Extend the estimate from strictly positive to positive Fourier polynomials
by adding a scalar tending to zero from above. -/
theorem positive_fourier_contractivity_of_strict {n : ℕ} {p q t : ℝ}
    (hp : 0 < p) (hq : 0 < q)
    (hstrict : ∀ x : GroupAlgebra n,
      (∃ a : ℝ, 0 < a ∧ (a : ℂ) • (1 : Operator n) ≤ regularImage x) →
      lpNorm q (poisson t x) ≤ lpNorm p x)
    (x : GroupAlgebra n) (hx : 0 ≤ regularImage x) :
    lpNorm q (poisson t x) ≤ lpNorm p x := by
  let F (x : GroupAlgebra n) (a : ℝ) := regularImage x + (a : ℂ) • (1 : Operator n)
  have hF (x : GroupAlgebra n) : Continuous (F x) := by
    dsimp [F]
    exact continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hlim (p : ℝ) (hp : 0 < p) (y : GroupAlgebra n) :
      Tendsto (fun a ↦ operatorLpNorm p (F y a)) (𝓝[>] (0 : ℝ)) (𝓝 (lpNorm p y)) := by
    have h : Tendsto (fun a : ℝ ↦ operatorLpNorm p (F y a)) (𝓝 0)
        (𝓝 (operatorLpNorm p (F y 0))) :=
      ((continuous_operatorLpNorm hp).comp (hF y)).continuousAt.tendsto
    have hzero : F y 0 = regularImage y := by
      change regularImage y + (Complex.ofReal (0 : ℝ)) • (1 : Operator n) = regularImage y
      ext v g
      simp
    rw [hzero, ← lpNorm_eq_operatorLpNorm] at h
    exact h.mono_left nhdsWithin_le_nhds
  let _ := nhdsGT_neBot (0 : ℝ)
  apply le_of_tendsto_of_tendsto (hlim q hq (poisson t x)) (hlim p hp x)
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with a ha
  have h := hstrict (x + (a : ℂ) • 1) ⟨a, ha, by
    simp only [regularImage_add, regularImage_smul, regularImage_one]
    exact le_add_of_nonneg_left hx⟩
  simpa only [lpNorm_eq_operatorLpNorm, poisson_add, poisson_smul, poisson_one,
    regularImage_add, regularImage_smul, regularImage_one, F] using h

private theorem exists_groupCStar_star_mul_self {n : ℕ} {x : GroupCStar n}
    (hx : 0 ≤ (x : Operator n)) : ∃ z : GroupCStar n, x = star z * z := by
  let X : Operator n := x
  let f (z : ℂ) := Complex.ofReal (Real.sqrt z.re)
  let T := cfc (p := IsStarNormal) f X
  have hf : Continuous f := Complex.continuous_ofReal.comp
    (Real.continuous_sqrt.comp Complex.continuous_re)
  have hX := (ContinuousLinearMap.nonneg_iff_isPositive.mp hx).isSelfAdjoint.isStarNormal
  have hT : 0 ≤ T := cfc_nonneg (f := f) (a := X) fun z _ ↦ by
    dsimp only [f]
    rw [← Complex.ofReal_zero, Complex.real_le_real]
    exact Real.sqrt_nonneg _
  have hTs : star T = T :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).isSelfAdjoint.star_eq
  have hTT : T * T = X := calc
    _ = cfc (p := IsStarNormal) (fun z ↦ f z * f z) X := by
      exact (cfc_mul f f X hf.continuousOn hf.continuousOn).symm
    _ = cfc (p := IsStarNormal) id X := by
      apply cfc_congr
      intro z hz
      obtain ⟨s, hs, rfl⟩ := exists_ofReal_of_spectrum_nonneg hx hz
      simp only [f, Complex.ofReal_re, ← Complex.ofReal_mul, id_eq]
      rw [Real.mul_self_sqrt hs]
    _ = X := cfc_id' ℂ X hX
  refine ⟨⟨T, cfc_mem_groupCStar f x.property⟩, Subtype.ext ?_⟩
  change X = star T * T
  rw [hTs, hTT]

/-- A positive Fourier contractivity estimate extends in operator norm to positive
elements of the reduced group C*-algebra. -/
theorem positive_groupCStar_contractivity_of_fourier {n : ℕ} {p q t : ℝ}
    (hp : 0 < p) (hq : 0 < q) (ht : 0 ≤ t)
    (hpoly : ∀ x : GroupAlgebra n, 0 ≤ regularImage x →
      lpNorm q (poisson t x) ≤ lpNorm p x)
    (x : GroupCStar n) (hx : 0 ≤ (x : Operator n)) :
    operatorLpNorm q (poissonCStar n t x : Operator n) ≤ operatorLpNorm p (x : Operator n) := by
  obtain ⟨z, rfl⟩ := exists_groupCStar_star_mul_self hx
  let S (y : GroupCStar n) := star y * y
  have hstarOp : Continuous (fun a : Operator n ↦ star a) := by
    simp_rw [ContinuousLinearMap.star_eq_adjoint]
    exact (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Hilbert n) (F := Hilbert n)).continuous
  have hstar : Continuous (star : GroupCStar n → GroupCStar n) :=
    Topology.IsInducing.subtypeVal.continuous_iff.mpr (hstarOp.comp continuous_subtype_val)
  have hS : Continuous S := hstar.mul continuous_id
  let F (y : GroupCStar n) := operatorLpNorm q (poissonCStar n t (S y) : Operator n)
  let G (y : GroupCStar n) := operatorLpNorm p (S y : Operator n)
  have hF : Continuous F :=
    (continuous_operatorLpNorm hq).comp (continuous_subtype_val.comp
      ((poissonCStar n t).continuous.comp hS))
  have hG : Continuous G :=
    (continuous_operatorLpNorm hp).comp (continuous_subtype_val.comp hS)
  change F z ≤ G z
  refine (denseRange_polynomialInclusion n).induction_on
    (p := fun y ↦ F y ≤ G y) z (isClosed_le hF hG) ?_
  intro y
  have he : S (polynomialInclusion n y) = polynomialInclusion n (fourierAdjoint y * y) := by
    apply Subtype.ext
    change star (polynomialInclusion n y : Operator n) * (polynomialInclusion n y : Operator n) =
      (polynomialInclusion n (fourierAdjoint y * y) : Operator n)
    simp only [polynomialInclusion_coe, regularImage_mul, regularImage_fourierAdjoint]
  have h := hpoly (fourierAdjoint y * y) (by
    rw [regularImage_mul, regularImage_fourierAdjoint]
    exact star_mul_self_nonneg _)
  simpa only [F, G, he, poissonCStar_apply_polynomial ht, polynomialInclusion_coe,
    ← lpNorm_eq_operatorLpNorm] using h

end FreeGroupHypercontractivity

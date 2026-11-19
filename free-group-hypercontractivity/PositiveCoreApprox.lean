module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».OperatorMajorant
public import «free-group-hypercontractivity».TraceC1Approx
import Mathlib.Analysis.Calculus.MeanValue

public section

namespace FreeGroupHypercontractivity

open Set
open scoped ComplexOrder Polynomial

/-- Approximate a strictly positive scalar function of a Fourier polynomial by positive
Fourier polynomials, controlling both the operator norm and the scalar error's Lipschitz
constant. -/
theorem exists_positive_fourier_cfc_approx {n : ℕ} (x : GroupAlgebra n)
    (hx : 0 ≤ regularImage x) {a b : ℝ} (hab : a ≤ b)
    (hspec : ∀ z ∈ spectrum ℂ (regularImage x), z.re ∈ Icc a b)
    {f f' : ℝ → ℝ} (hd : ∀ z ∈ Icc a b, HasDerivWithinAt f (f' z) (Icc a b) z)
    (hc : ContinuousOn f' (Icc a b)) {m : ℝ} (hm : 0 < m)
    (hf : ∀ z ∈ Icc a b, m ≤ f z) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∃ y : GroupAlgebra n,
      regularImage y = cfc (p := IsStarNormal)
        (fun z : ℂ ↦ Complex.ofReal (p.eval z.re)) (regularImage x) ∧
      0 ≤ regularImage y ∧
      ‖regularImage y - cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (f z.re))
        (regularImage x)‖ ≤ ε ∧
      ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, |(p.eval r - f r) - (p.eval s - f s)| ≤ ε * |r - s| := by
  let T := regularImage x
  let δ := min ε m
  have hδ : 0 < δ := lt_min hε hm
  obtain ⟨p, hp, hp'⟩ := exists_polynomial_near_of_hasDerivWithinAt hab hd hc hδ
  let pC := p.map (algebraMap ℝ ℂ)
  let y : GroupAlgebra n := Polynomial.aeval x pC
  let F (z : ℂ) : ℂ := Complex.ofReal (f z.re)
  let P (z : ℂ) : ℂ := Complex.ofReal (p.eval z.re)
  have hnormal : IsStarNormal T :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hx).isSelfAdjoint.isStarNormal
  have hP : Continuous P := Complex.continuous_ofReal.comp
    (p.continuous.comp Complex.continuous_re)
  have hfc : ContinuousOn f (Icc a b) := fun r hr ↦ (hd r hr).continuousWithinAt
  have hF : ContinuousOn F (spectrum ℂ T) :=
    Complex.continuous_ofReal.continuousOn.comp
      (hfc.comp Complex.continuous_re.continuousOn hspec) (mapsTo_univ _ _)
  have hy : regularImage y = cfc (p := IsStarNormal) P T := by
    rw [← regularHom_apply]
    change regularHom n (Polynomial.aeval x pC) = _
    rw [← Polynomial.aeval_algHom_apply, regularHom_apply, ← cfc_polynomial pC T hnormal]
    apply cfc_congr
    intro z hz
    obtain ⟨r, _, rfl⟩ := exists_ofReal_of_spectrum_nonneg hx hz
    change (p.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r) = _
    rw [Polynomial.eval_map_apply]
    simp [P]
  refine ⟨p, y, hy, ?_, ?_, ?_⟩
  · rw [hy]
    apply cfc_nonneg
    intro z hz
    apply Complex.real_le_real.mpr
    have h := (abs_lt.mp (hp z.re (hspec z hz))).1
    linarith [hf z.re (hspec z hz), min_le_right ε m]
  · rw [hy, ← cfc_sub P F T hP.continuousOn hF]
    apply norm_cfc_le hε.le
    intro z hz
    rw [show P z - F z = Complex.ofReal (p.eval z.re - f z.re) by simp [P, F]]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (hp z.re (hspec z hz)).le.trans (min_le_left ε m)
  · intro r hr s hs
    have hd' : ∀ z ∈ Icc a b, HasDerivWithinAt (fun u ↦ p.eval u - f u)
        (p.derivative.eval z - f' z) (Icc a b) z :=
      fun z hz ↦ (p.hasDerivAt z).hasDerivWithinAt.fun_sub (hd z hz)
    have hbound : ∀ z ∈ Icc a b, ‖p.derivative.eval z - f' z‖ ≤ ε := by
      intro z hz
      rw [Real.norm_eq_abs]
      exact (hp' z hz).le.trans (min_le_left ε m)
    simpa only [Real.norm_eq_abs] using
      (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hd' hbound hs hr

end FreeGroupHypercontractivity

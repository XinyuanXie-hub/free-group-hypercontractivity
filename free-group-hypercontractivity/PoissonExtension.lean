module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».PoissonPositive
public import «free-group-hypercontractivity».GroupCStar
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Normed.Operator.Extend

public section

namespace FreeGroupHypercontractivity

open scoped InnerProductSpace Topology

/-- The coefficient involution on Fourier polynomials. -/
noncomputable def fourierAdjoint {n : ℕ} (x : GroupAlgebra n) : GroupAlgebra n :=
  MonoidAlgebra.ofCoeff ((x.coeff.mapDomain (Equiv.inv (Group n))).mapRange star (star_zero ℂ))

@[simp] theorem fourierAdjoint_coeff {n : ℕ} (x : GroupAlgebra n) (g : Group n) :
    (fourierAdjoint x).coeff g = star (x.coeff g⁻¹) := by
  rw [fourierAdjoint, MonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply,
    Finsupp.mapDomain_equiv_apply]
  rfl

@[simp] theorem regularImage_fourierAdjoint {n : ℕ} (x : GroupAlgebra n) :
    regularImage (fourierAdjoint x) = star (regularImage x) := by
  classical
  simp only [regularImage, Finsupp.sum]
  rw [star_sum x.coeff.support (fun g ↦ (x.coeff g • leftRegular g : Operator n))]
  simp only [star_smul, star_leftRegular]
  refine Finset.sum_nbij (fun (g : Group n) ↦ g⁻¹) ?_ ?_ ?_ ?_
  · intro g hg
    simpa only [Finset.mem_coe, Finsupp.mem_support_iff, fourierAdjoint_coeff, star_ne_zero,
      inv_inv] using hg
  · exact fun _ _ _ _ h ↦ inv_injective h
  · intro g hg
    refine ⟨g⁻¹, ?_, inv_inv _⟩
    simpa only [Finset.mem_coe, Finsupp.mem_support_iff, fourierAdjoint_coeff, star_ne_zero,
      inv_inv] using hg
  · simp

/-- The Fourier multiplier as a linear transformation on the group algebra. -/
noncomputable def poissonLinear (n : ℕ) (t : ℝ) : GroupAlgebra n →ₗ[ℂ] GroupAlgebra n where
  toFun := poisson t
  map_add' x y := by
    ext g
    simp [poisson_coeff, mul_add]
  map_smul' r x := by
    ext g
    simp [poisson_coeff, mul_left_comm, smul_eq_mul]

@[simp] theorem poissonLinear_apply (n : ℕ) (t : ℝ) (x : GroupAlgebra n) :
    poissonLinear n t x = poisson t x := by rw [poissonLinear]; rfl

@[simp] theorem poisson_one {n : ℕ} (t : ℝ) :
    poisson t (1 : GroupAlgebra n) = 1 := by
  classical
  ext g
  rw [poisson_coeff, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with hg
  · subst g
    simp
  · simp

@[simp] theorem poisson_add {n : ℕ} (t : ℝ) (x y : GroupAlgebra n) :
    poisson t (x + y) = poisson t x + poisson t y := by
  simp only [← poissonLinear_apply, map_add]

@[simp] theorem poisson_sub {n : ℕ} (t : ℝ) (x y : GroupAlgebra n) :
    poisson t (x - y) = poisson t x - poisson t y := by
  simp only [← poissonLinear_apply, map_sub]

@[simp] theorem poisson_smul {n : ℕ} (t : ℝ) (r : ℂ) (x : GroupAlgebra n) :
    poisson t (r • x) = r • poisson t x := by
  simp only [← poissonLinear_apply, map_smul]

@[simp] theorem poisson_fourierAdjoint {n : ℕ} (t : ℝ) (x : GroupAlgebra n) :
    poisson t (fourierAdjoint x) = fourierAdjoint (poisson t x) := by
  ext g
  simp only [poisson_coeff, fourierAdjoint_coeff, FreeGroup.norm_inv_eq, star_mul',
    Complex.star_def, Complex.conj_ofReal]

/-- Kadison–Schwarz on finite Fourier polynomials. -/
theorem star_mul_regularImage_poisson_le {n : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (x : GroupAlgebra n) :
    star (regularImage (poisson t x)) * regularImage (poisson t x) ≤
      regularImage (poisson t (fourierAdjoint x * x)) := by
  let X := regularImage x
  let P := regularImage (poisson t x)
  let Q := regularImage (poisson t (fourierAdjoint x * x))
  let B : Fin 2 → Fin 2 → GroupAlgebra n := fun i j ↦
    if i = 0 then if j = 0 then fourierAdjoint x * x else fourierAdjoint x
    else if j = 0 then x else 1
  have hB : FourierBlockNonneg B := by
    intro v
    have hr : 0 ≤ (⟪X (v 0) + v 1, X (v 0) + v 1⟫_ℂ).re := by
      change 0 ≤ RCLike.re ⟪X (v 0) + v 1, X (v 0) + v 1⟫_ℂ
      rw [inner_self_eq_norm_sq]
      exact sq_nonneg _
    simp only [Fin.sum_univ_two, B, ite_true, ite_false, Fin.isValue,
      show (1 : Fin 2) ≠ 0 by decide, regularImage_fourierAdjoint, regularImage_mul,
      regularImage_one, one_apply_eq_self, ContinuousLinearMap.star_eq_adjoint]
    change 0 ≤ (⟪v 0, X.adjoint (X (v 0))⟫_ℂ).re + (⟪v 0, X.adjoint (v 1)⟫_ℂ).re +
      ((⟪v 1, X (v 0)⟫_ℂ).re + (⟪v 1, v 1⟫_ℂ).re)
    simpa only [ContinuousLinearMap.adjoint_inner_right, inner_add_left, inner_add_right,
      Complex.add_re, add_assoc, add_comm, add_left_comm] using hr
  have hQ : 0 ≤ Q := by
    apply regularImage_poisson_nonneg ht
    rw [regularImage_mul, regularImage_fourierAdjoint]
    exact star_mul_self_nonneg _
  have hCP := poisson_fourierBlockNonneg ht hB
  apply sub_nonneg.mp
  refine ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (ContinuousLinearMap.isPositive_def'.mpr ⟨?_, fun v ↦ ?_⟩)
  · exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hQ).isSelfAdjoint.sub
      (IsSelfAdjoint.star_mul_self _)
  · let V (i : Fin 2) : Hilbert n := if i = 0 then v else -P v
    have h := hCP V
    simp only [Fin.sum_univ_two, V, B, ite_true, ite_false, Fin.isValue,
      show (1 : Fin 2) ≠ 0 by decide, poisson_fourierAdjoint, regularImage_fourierAdjoint,
      poisson_one, regularImage_one, one_apply_eq_self] at h
    change 0 ≤ RCLike.re ⟪(Q - star P * P) v, v⟫_ℂ
    rw [inner_re_symm]
    change 0 ≤ (⟪v, Q v - P.adjoint (P v)⟫_ℂ).re
    simp only [inner_sub_right, ContinuousLinearMap.adjoint_inner_right, Complex.sub_re]
    change 0 ≤ (⟪v, Q v⟫_ℂ).re + (⟪v, P.adjoint (-P v)⟫_ℂ).re +
      ((⟪-P v, P v⟫_ℂ).re + (⟪-P v, -P v⟫_ℂ).re) at h
    simp only [ContinuousLinearMap.adjoint_inner_right, inner_neg_right, inner_neg_left,
      neg_neg, Complex.neg_re] at h
    linarith

/-- Poisson is contractive in operator norm. -/
theorem norm_regularImage_poisson_le {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (x : GroupAlgebra n) : ‖regularImage (poisson t x)‖ ≤ ‖regularImage x‖ := by
  let r := ‖regularImage x‖ ^ 2
  let y := (r : ℂ) • (1 : GroupAlgebra n) - fourierAdjoint x * x
  have hscalar : (r : ℂ) • (1 : Operator n) = algebraMap ℝ (Operator n) r := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (IsScalarTower.algebraMap_apply ℝ ℂ (Operator n) r).symm
  have hy : 0 ≤ regularImage y := by
    simp only [y, regularImage_sub, regularImage_smul, regularImage_one, hscalar,
      regularImage_mul, regularImage_fourierAdjoint]
    exact sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq _)
  have hyp := regularImage_poisson_nonneg ht hy
  simp only [y, poisson_sub, poisson_smul, poisson_one, regularImage_sub, regularImage_smul,
    regularImage_one, hscalar] at hyp
  have h := (star_mul_regularImage_poisson_le ht x).trans (sub_nonneg.mp hyp)
  have hN := (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg ‖regularImage x‖)
    (star_mul_self_nonneg _)).mpr h
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    ‖regularImage (poisson t x)‖ ^ 2 =
        ‖star (regularImage (poisson t x)) * regularImage (poisson t x)‖ := by
      rw [pow_two]
      exact (CStarRing.norm_star_mul_self (x := regularImage (poisson t x))).symm
    _ ≤ ‖regularImage x‖ ^ 2 := hN

/-- The dense inclusion of Fourier polynomials into the reduced group C*-algebra. -/
noncomputable def polynomialInclusion (n : ℕ) : GroupAlgebra n →ₗ[ℂ] GroupCStar n :=
  LinearMap.codRestrict (groupCStar n).toSubalgebra.toSubmodule (regularHom n).toLinearMap
    (fun x ↦ regularHom_apply x ▸ regularImage_mem_groupCStar x)

@[simp] theorem polynomialInclusion_coe (n : ℕ) (x : GroupAlgebra n) :
    (polynomialInclusion n x : Operator n) = regularImage x := by
  change regularHom n x = regularImage x
  exact regularHom_apply x

theorem denseRange_polynomialInclusion (n : ℕ) : DenseRange (polynomialInclusion n) := by
  intro x
  apply closure_subtype.mpr
  rw [← Set.range_comp]
  rw [show (Subtype.val : GroupCStar n → Operator n) ∘ polynomialInclusion n = regularImage from
    funext (polynomialInclusion_coe n)]
  exact mem_groupCStar_iff.mp x.property

/-- Operator norm continuous extension of Poisson to the reduced group C*-algebra. -/
noncomputable def poissonCStar (n : ℕ) (t : ℝ) : GroupCStar n →L[ℂ] GroupCStar n :=
  ((polynomialInclusion n).comp (poissonLinear n t)).extendOfNorm (polynomialInclusion n)

theorem poissonCStar_apply_polynomial {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (x : GroupAlgebra n) :
    poissonCStar n t (polynomialInclusion n x) = polynomialInclusion n (poisson t x) := by
  unfold poissonCStar
  apply LinearMap.extendOfNorm_eq (denseRange_polynomialInclusion n) ⟨1, ?_⟩
  intro y
  simp only [LinearMap.comp_apply, poissonLinear_apply, one_mul]
  change ‖(polynomialInclusion n (poisson t y) : Operator n)‖ ≤
    ‖(polynomialInclusion n y : Operator n)‖
  simpa only [polynomialInclusion_coe] using norm_regularImage_poisson_le ht y

theorem norm_poissonCStar_le_one {n : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    ‖poissonCStar n t‖ ≤ 1 := by
  unfold poissonCStar
  apply LinearMap.opNorm_extendOfNorm_le (denseRange_polynomialInclusion n) zero_le_one
  intro y
  simp only [LinearMap.comp_apply, poissonLinear_apply, one_mul]
  change ‖(polynomialInclusion n (poisson t y) : Operator n)‖ ≤
    ‖(polynomialInclusion n y : Operator n)‖
  simpa only [polynomialInclusion_coe] using norm_regularImage_poisson_le ht y

theorem poissonCStar_operatorEntry {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (x : GroupCStar n) (g h : Group n) :
    operatorEntry (poissonCStar n t x : Operator n) g h =
      (Real.exp (-t * (FreeGroup.norm (g * h⁻¹) : ℝ)) : ℂ) * operatorEntry (x : Operator n) g h := by
  let P (x : GroupCStar n) : ℂ := operatorEntry (poissonCStar n t x : Operator n) g h
  let Q (x : GroupCStar n) : ℂ :=
    (Real.exp (-t * (FreeGroup.norm (g * h⁻¹) : ℝ)) : ℂ) * operatorEntry (x : Operator n) g h
  have hP : Continuous P :=
    (continuous_operatorEntry g h).comp (continuous_subtype_val.comp (poissonCStar n t).continuous)
  have hQ : Continuous Q := continuous_const.mul ((continuous_operatorEntry g h).comp continuous_subtype_val)
  change P x = Q x
  refine (denseRange_polynomialInclusion n).induction_on
    (p := fun y ↦ P y = Q y) x (isClosed_eq hP hQ) ?_
  intro y
  simp only [P, Q, poissonCStar_apply_polynomial ht, polynomialInclusion_coe,
    operatorEntry_regularImage, poisson_coeff]

/-- Complete preservation of nonnegative operator quadratic forms by the Poisson semigroup
on the reduced group algebra. -/
theorem poissonCStar_operatorBlockNonneg {n : ℕ} {t : ℝ} {ι : Type*} [Fintype ι]
    {x : ι → ι → GroupCStar n} (ht : 0 ≤ t)
    (hx : OperatorBlockNonneg (fun i j ↦ (x i j : Operator n))) :
    OperatorBlockNonneg (fun i j ↦ (poissonCStar n t (x i j) : Operator n)) :=
  operatorBlockNonneg_of_poisson_kernel ht (fun i j ↦ poissonCStar_operatorEntry ht (x i j)) hx

@[simp] theorem polynomialInclusion_one (n : ℕ) :
    polynomialInclusion n (1 : GroupAlgebra n) = 1 := by
  apply Subtype.ext
  rw [polynomialInclusion_coe]
  exact regularImage_one

@[simp] theorem polynomialInclusion_fourierAdjoint {n : ℕ} (x : GroupAlgebra n) :
    polynomialInclusion n (fourierAdjoint x) = star (polynomialInclusion n x) := by
  apply Subtype.ext
  change (polynomialInclusion n (fourierAdjoint x) : Operator n) =
    star (polynomialInclusion n x : Operator n)
  simp only [polynomialInclusion_coe, regularImage_fourierAdjoint]

theorem poissonCStar_one {n : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    poissonCStar n t (1 : GroupCStar n) = 1 := by
  rw [← polynomialInclusion_one n, poissonCStar_apply_polynomial ht, poisson_one]

theorem poissonCStar_star {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (x : GroupCStar n) :
    poissonCStar n t (star x) = star (poissonCStar n t x) := by
  have hstarOp : Continuous (fun a : Operator n ↦ star a) := by
    simp_rw [ContinuousLinearMap.star_eq_adjoint]
    exact (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Hilbert n) (F := Hilbert n)).continuous
  have hstar : Continuous (star : GroupCStar n → GroupCStar n) :=
    Topology.IsInducing.subtypeVal.continuous_iff.mpr (hstarOp.comp continuous_subtype_val)
  refine (denseRange_polynomialInclusion n).induction_on
    (p := fun y ↦ poissonCStar n t (star y) = star (poissonCStar n t y)) x
    (isClosed_eq ((poissonCStar n t).continuous.comp hstar)
      (hstar.comp (poissonCStar n t).continuous)) ?_
  intro y
  rw [← polynomialInclusion_fourierAdjoint, poissonCStar_apply_polynomial ht,
    poisson_fourierAdjoint, polynomialInclusion_fourierAdjoint, poissonCStar_apply_polynomial ht]

/-- The Poisson semigroup is positive on the reduced group C*-algebra. -/
theorem poissonCStar_nonneg {n : ℕ} {t : ℝ} (ht : 0 ≤ t) {x : GroupCStar n}
    (hx : 0 ≤ (x : Operator n)) : 0 ≤ (poissonCStar n t x : Operator n) := by
  have hpos := ContinuousLinearMap.nonneg_iff_isPositive.mp hx
  have hx' : OperatorBlockNonneg (fun (_ _ : Unit) ↦ (x : Operator n)) := by
    intro v
    simpa using hpos.re_inner_nonneg_right (v ())
  have hp := poissonCStar_operatorBlockNonneg (x := fun (_ _ : Unit) ↦ x) ht hx'
  refine ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (ContinuousLinearMap.isPositive_def'.mpr ⟨?_, fun v ↦ ?_⟩)
  · have hstar : star x = x := Subtype.ext hpos.isSelfAdjoint.star_eq
    have h := poissonCStar_star ht x
    rw [hstar] at h
    exact congrArg (Subtype.val : GroupCStar n → Operator n) h.symm
  · simpa [ContinuousLinearMap.reApplyInnerSelf, inner_re_symm] using hp (fun _ ↦ v)

theorem traceRe_poissonCStar {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (x : GroupCStar n) :
    traceRe (poissonCStar n t x : Operator n) = traceRe (x : Operator n) := by
  have h := poissonCStar_operatorEntry ht x 1 1
  simpa only [operatorEntry, traceRe, inv_one, mul_one, FreeGroup.norm_one, Nat.cast_zero,
    mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul] using congrArg Complex.re h

end FreeGroupHypercontractivity

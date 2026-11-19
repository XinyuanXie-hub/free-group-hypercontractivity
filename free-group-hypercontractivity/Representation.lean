module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».Model

public section

namespace FreeGroupHypercontractivity

open scoped ComplexOrder InnerProductSpace

@[simp]
theorem leftRegular_one {n : ℕ} : leftRegular (1 : Group n) = 1 := by
  ext v h
  simp

@[simp]
theorem leftRegular_mul {n : ℕ} (g h : Group n) :
    leftRegular (g * h) = leftRegular g * leftRegular h := by
  ext v k
  change leftRegular (g * h) v k = leftRegular g (leftRegular h v) k
  simp only [leftRegular_apply]
  simp [mul_assoc]

@[simp]
theorem star_leftRegular {n : ℕ} (g : Group n) :
    star (leftRegular g) = leftRegular g⁻¹ := by
  symm
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [lp.inner_eq_tsum, leftRegular_apply, inv_inv]
  simpa [mul_assoc] using
    (Equiv.mulLeft g).tsum_eq (fun h ↦ ⟪x h, y (g⁻¹ * h)⟫_ℂ)

noncomputable def regularHom (n : ℕ) : GroupAlgebra n →ₐ[ℂ] Operator n :=
  MonoidAlgebra.lift ℂ (Operator n) (Group n)
    { toFun := leftRegular
      map_one' := leftRegular_one
      map_mul' := leftRegular_mul }

theorem regularHom_apply {n : ℕ} (x : GroupAlgebra n) :
    regularHom n x = regularImage x := MonoidAlgebra.lift_apply _ _

@[simp]
theorem regularImage_zero {n : ℕ} : regularImage (0 : GroupAlgebra n) = 0 := by
  rw [← regularHom_apply, map_zero]

@[simp]
theorem regularImage_one {n : ℕ} : regularImage (1 : GroupAlgebra n) = 1 := by
  rw [← regularHom_apply, map_one]

@[simp]
theorem regularImage_add {n : ℕ} (x y : GroupAlgebra n) :
    regularImage (x + y) = regularImage x + regularImage y := by
  simp only [← regularHom_apply, map_add]

@[simp]
theorem regularImage_mul {n : ℕ} (x y : GroupAlgebra n) :
    regularImage (x * y) = regularImage x * regularImage y := by
  simp only [← regularHom_apply, map_mul]

@[simp]
theorem regularImage_single {n : ℕ} (g : Group n) (c : ℂ) :
    regularImage (MonoidAlgebra.single g c) = c • leftRegular g := by
  rw [← regularHom_apply]
  exact MonoidAlgebra.lift_single _ _ _

@[simp]
theorem regularImage_smul {n : ℕ} (c : ℂ) (x : GroupAlgebra n) :
    regularImage (c • x) = c • regularImage x := by
  simp only [← regularHom_apply, map_smul]

theorem regularImage_delta_at {n : ℕ} (x : GroupAlgebra n) (g h : Group n) :
    regularImage x (lp.single 2 g 1) h = x.coeff (h * g⁻¹) := by
  classical
  rw [regularImage, Finsupp.sum]
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
    smul_apply, lp.coeFn_smul, Pi.smul_apply, leftRegular_apply,
    lp.single_apply, Pi.single_apply, smul_eq_mul]
  simp only [← eq_mul_inv_iff_mul_eq, inv_eq_iff_eq_inv, mul_inv_rev, inv_inv, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs <;> simp_all

theorem regularImage_delta {n : ℕ} (x : GroupAlgebra n) (h : Group n) :
    regularImage x (lp.single 2 1 1) h = x.coeff h := by
  simpa using regularImage_delta_at x 1 h

@[simp]
theorem regularImage_pow {n : ℕ} (x : GroupAlgebra n) (k : ℕ) :
    regularImage (x ^ k) = regularImage x ^ k := by
  simp only [← regularHom_apply, map_pow]

@[simp]
theorem regularImage_sub {n : ℕ} (x y : GroupAlgebra n) :
    regularImage (x - y) = regularImage x - regularImage y := by
  simp only [← regularHom_apply, map_sub]

@[simp]
theorem traceRe_regularImage {n : ℕ} (x : GroupAlgebra n) :
    traceRe (regularImage x) = (x.coeff 1).re := by
  rw [traceRe, regularImage_delta]

theorem coeff_inv_of_selfAdjoint {n : ℕ} {x : GroupAlgebra n}
    (hx : IsSelfAdjoint (regularImage x)) (g : Group n) :
    x.coeff g⁻¹ = star (x.coeff g) := by
  classical
  have h := (ContinuousLinearMap.eq_adjoint_iff (regularImage x) (regularImage x)).mp
    (by simpa only [← ContinuousLinearMap.star_eq_adjoint] using hx.symm)
    (lp.single 2 1 1) (lp.single 2 g 1)
  rw [lp.inner_single_right, lp.inner_single_left, regularImage_delta,
    regularImage_delta_at] at h
  simpa [RCLike.inner_apply] using h.symm

theorem traceRe_as_inner {n : ℕ} (T : Operator n) :
    traceRe T = (⟪lp.single 2 1 1, T (lp.single 2 1 1)⟫_ℂ).re := by
  classical
  simp [traceRe, lp.inner_single_left, RCLike.inner_apply]

theorem regularImage_injective {n : ℕ} :
    Function.Injective (regularImage (n := n)) := by
  intro x y hxy
  ext g
  rw [← regularImage_delta, hxy, regularImage_delta]

end FreeGroupHypercontractivity

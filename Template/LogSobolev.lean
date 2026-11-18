module

import all Template.Model

public import Template.Moments
public import Template.OperatorMajorant

public section

namespace FreeGroupHypercontractivity

open scoped InnerProductSpace

/-- Remove the real scalar part of a self-adjoint Fourier polynomial. -/
@[expose]
noncomputable def centered {n : ℕ} (x : GroupAlgebra n) : GroupAlgebra n :=
  x - Complex.ofReal (traceRe (regularImage x)) • 1

theorem centered_coeff_one {n : ℕ} {x : GroupAlgebra n}
    (hx : IsSelfAdjoint (regularImage x)) : (centered x).coeff 1 = 0 := by
  have hreal : Complex.ofReal (x.coeff 1).re = x.coeff 1 := by
    have h := coeff_inv_of_selfAdjoint hx (1 : Group n)
    rw [inv_one] at h
    apply Complex.ext
    · simp
    · have hi := congrArg Complex.im h
      simp at hi
      simp
      linarith
  simp [centered, MonoidAlgebra.coeff_sub, hreal]

theorem centered_image_selfAdjoint {n : ℕ} {x : GroupAlgebra n}
    (hx : IsSelfAdjoint (regularImage x)) : IsSelfAdjoint (regularImage (centered x)) := by
  change star (regularImage x) = regularImage x at hx
  rw [centered, regularImage_sub, regularImage_smul, regularImage_one]
  unfold IsSelfAdjoint
  simp only [ContinuousLinearMap.star_eq_adjoint] at hx ⊢
  rw [map_sub, hx, map_smulₛₗ, ContinuousLinearMap.adjoint_one]
  simp only [Complex.conj_ofReal]

theorem regularImage_eq_centered_add {n : ℕ} (x : GroupAlgebra n) :
    regularImage x = Complex.ofReal (traceRe (regularImage x)) • 1 +
      regularImage (centered x) := by
  rw [centered, regularImage_sub, regularImage_smul, regularImage_one]
  abel

theorem centered_sq {n : ℕ} (x : GroupAlgebra n)
    (hx : IsSelfAdjoint (regularImage x)) :
    traceRe (regularImage x ^ 2) =
      traceRe (regularImage x) ^ 2 + traceRe (regularImage (centered x) ^ 2) := by
  let a := traceRe (regularImage x)
  let U := regularImage (centered x)
  have hU : traceRe U = 0 := by simp [U, centered_coeff_one hx]
  have h := regularImage_eq_centered_add x
  change regularImage x = Complex.ofReal a • 1 + U at h
  change _ = a ^ 2 + traceRe (U ^ 2)
  conv_lhs => rw [h]
  simp only [pow_two, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, traceRe_add, traceRe_ofReal_smul, traceRe_one,
    hU, mul_zero, add_zero, zero_add]

theorem centered_cube {n : ℕ} (x : GroupAlgebra n)
    (hx : IsSelfAdjoint (regularImage x)) :
    traceRe (regularImage x ^ 3) = traceRe (regularImage x) ^ 3 +
      3 * traceRe (regularImage x) * traceRe (regularImage (centered x) ^ 2) +
      traceRe (regularImage (centered x) ^ 3) := by
  let a := traceRe (regularImage x)
  let U := regularImage (centered x)
  have hU : traceRe U = 0 := by simp [U, centered_coeff_one hx]
  have h := regularImage_eq_centered_add x
  change regularImage x = Complex.ofReal a • 1 + U at h
  change _ = a ^ 3 + 3 * a * traceRe (U ^ 2) + traceRe (U ^ 3)
  conv_lhs => rw [h]
  simp only [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, pow_zero, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    traceRe_add, traceRe_ofReal_smul, traceRe_one, hU, mul_zero, add_zero, zero_add]
  ring

theorem centered_energy {n : ℕ} (x : GroupAlgebra n) :
    traceRe (regularImage x * regularImage (generator x)) =
      traceRe (regularImage (centered x) * regularImage (generator (centered x))) := by
  have hL : generator (centered x) = generator x := by
    exact generator_center x _
  conv_lhs =>
    arg 1
    arg 1
    rw [regularImage_eq_centered_add x]
  simp [hL, add_mul, smul_mul_assoc]

/-- The log-Sobolev bound obtained from the centered third-moment estimate. -/
theorem logSobolev_of_centered_cubic {n : ℕ} (x : GroupAlgebra n)
    (hx : 0 ≤ regularImage x) (ha : 0 < traceRe (regularImage x))
    (hm2 : 0 < traceRe (regularImage x ^ 2))
    (hCubic : let u := centered x
      let S2 := ∑ g ∈ u.coeff.support, ‖u.coeff g‖ ^ 2
      let Q := Real.sqrt
        (∑ g ∈ u.coeff.support, ((FreeGroup.norm g - 1 : ℕ) : ℝ) * ‖u.coeff g‖ ^ 2)
      traceRe (regularImage u ^ 3) ≤ 3 * S2 * Q + Q ^ 3) :
    entropy (regularImage x ^ 2) ≤
      2 * traceRe (regularImage x * regularImage (generator x)) := by
  have hsa := (ContinuousLinearMap.nonneg_iff_isPositive.mp hx).isSelfAdjoint
  let a := traceRe (regularImage x)
  let u := centered x
  let s2 := ∑ g ∈ u.coeff.support, ‖u.coeff g‖ ^ 2
  let q2 := ∑ g ∈ u.coeff.support, ((FreeGroup.norm g - 1 : ℕ) : ℝ) * ‖u.coeff g‖ ^ 2
  let q := Real.sqrt q2
  have hu := coeff_inv_of_selfAdjoint (centered_image_selfAdjoint hsa)
  have hs2 : traceRe (regularImage u ^ 2) = s2 := traceRe_image_sq u hu
  have hq2 : q ^ 2 = q2 := Real.sq_sqrt (by dsimp [q2]; positivity)
  have hl : 0 < a + q := add_pos_of_pos_of_nonneg ha (Real.sqrt_nonneg _)
  have h2 := centered_sq x hsa
  have h3 := centered_cube x hsa
  have he := (centered_energy x).trans
    (traceRe_image_generator_centered u (centered_coeff_one hsa) hu)
  change traceRe (regularImage x ^ 2) = a ^ 2 + traceRe (regularImage u ^ 2) at h2
  change traceRe (regularImage x ^ 3) = a ^ 3 + 3 * a * traceRe (regularImage u ^ 2) +
    traceRe (regularImage u ^ 3) at h3
  change traceRe (regularImage x * regularImage (generator x)) = s2 + q2 at he
  change traceRe (regularImage u ^ 3) ≤ 3 * s2 * q + q ^ 3 at hCubic
  rw [hs2] at h2 h3
  have hmajor := traceRe_cubic_majorant hx hl
  have h := entropy_le_of_cubic_unnormalized (q := q) hm2 hl
    (m3 := traceRe (regularImage x ^ 3)) (E := entropy (regularImage x ^ 2))
    (by linarith only [hCubic, h3, congrArg (3 * a * ·) h2, congrArg (3 * q * ·) h2])
    (by unfold entropy; linarith only [hmajor])
  linarith only [h, h2, he, hq2]

end FreeGroupHypercontractivity

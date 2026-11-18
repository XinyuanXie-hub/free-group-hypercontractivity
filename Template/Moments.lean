module

import all Template.Model

public import Template.Representation

public section

namespace FreeGroupHypercontractivity

open scoped ComplexOrder InnerProductSpace

@[simp]
theorem generator_coeff {n : ℕ} (x : GroupAlgebra n) (g : Group n) :
    (generator x).coeff g = (FreeGroup.norm g : ℂ) * x.coeff g := by
  rw [generator, multiplier_coeff]

@[simp]
theorem poisson_coeff {n : ℕ} (t : ℝ) (x : GroupAlgebra n) (g : Group n) :
    (poisson t x).coeff g = (Real.exp (-t * (FreeGroup.norm g : ℝ)) : ℂ) * x.coeff g := by
  rw [poisson, multiplier_coeff]

theorem traceRe_mul_multiplier {n : ℕ} (x : GroupAlgebra n)
    (hx : ∀ g, x.coeff g⁻¹ = star (x.coeff g)) (w : Group n → ℝ) :
    traceRe (regularImage x * regularImage (multiplier (fun g ↦ Complex.ofReal (w g)) x)) =
      ∑ g ∈ x.coeff.support, w g⁻¹ * ‖x.coeff g‖ ^ 2 := by
  rw [← regularImage_mul, traceRe_regularImage, MonoidAlgebra.coeff_mul_apply_left]
  simp only [Finsupp.sum, mul_one, multiplier_coeff, hx, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [mul_left_comm, Complex.star_def, Complex.mul_conj']
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem traceRe_image_sq {n : ℕ} (x : GroupAlgebra n)
    (hx : ∀ g, x.coeff g⁻¹ = star (x.coeff g)) :
    traceRe (regularImage x ^ 2) = ∑ g ∈ x.coeff.support, ‖x.coeff g‖ ^ 2 := by
  have h : multiplier (fun _ : Group n ↦ (1 : ℂ)) x = x := by
    ext g
    simp
  simpa [h, pow_two] using traceRe_mul_multiplier x hx (fun _ ↦ 1)

theorem traceRe_image_generator {n : ℕ} (x : GroupAlgebra n)
    (hx : ∀ g, x.coeff g⁻¹ = star (x.coeff g)) :
    traceRe (regularImage x * regularImage (generator x)) =
      ∑ g ∈ x.coeff.support, (FreeGroup.norm g : ℝ) * ‖x.coeff g‖ ^ 2 := by
  simpa [generator, FreeGroup.norm_inv_eq] using
    traceRe_mul_multiplier x hx (fun g ↦ (FreeGroup.norm g : ℝ))

theorem generator_center {n : ℕ} (x : GroupAlgebra n) (a : ℂ) :
    generator (x - a • 1) = generator x := by
  classical
  ext g
  by_cases hg : g = 1
  · subst g
    simp [FreeGroup.norm_one]
  · simp [hg, MonoidAlgebra.one_def, MonoidAlgebra.coeff_sub]

@[simp]
theorem traceRe_image_generator_zero {n : ℕ} (x : GroupAlgebra n) :
    traceRe (regularImage (generator x)) = 0 := by
  simp [FreeGroup.norm_one]

theorem traceRe_image_generator_centered {n : ℕ} (x : GroupAlgebra n)
    (hx : x.coeff 1 = 0) (hs : ∀ g, x.coeff g⁻¹ = star (x.coeff g)) :
    traceRe (regularImage x * regularImage (generator x)) =
      (∑ g ∈ x.coeff.support, ‖x.coeff g‖ ^ 2) +
        ∑ g ∈ x.coeff.support, ((FreeGroup.norm g - 1 : ℕ) : ℝ) * ‖x.coeff g‖ ^ 2 := by
  rw [traceRe_image_generator x hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g hg ↦ ?_
  have hg1 : g ≠ 1 := by
    intro he
    exact (Finsupp.mem_support_iff.mp hg) (he ▸ hx)
  have hpos : 1 ≤ FreeGroup.norm g := Nat.pos_of_ne_zero
    (fun h ↦ hg1 (FreeGroup.norm_eq_zero.mp h))
  rw [Nat.cast_sub hpos]
  push_cast
  ring

end FreeGroupHypercontractivity

module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».Representation

public section

namespace FreeGroupHypercontractivity

/-- Canonical real trace as a continuous real linear functional on the ambient operators. -/
noncomputable def traceReCLM (n : ℕ) : Operator n →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (((lp.evalCLM ℂ (fun _ : Group n ↦ ℂ) 2 1).comp
      (ContinuousLinearMap.apply ℂ (Hilbert n) (lp.single 2 (1 : Group n) (1 : ℂ)))).restrictScalars ℝ)

@[simp]
theorem traceReCLM_apply {n : ℕ} (T : Operator n) : traceReCLM n T = traceRe T := by
  rfl

theorem continuous_traceRe (n : ℕ) : Continuous (traceRe (n := n)) := by
  have heq : traceRe (n := n) = ⇑(traceReCLM n) := funext fun T ↦ (traceReCLM_apply T).symm
  rw [heq]
  exact (traceReCLM n).continuous

theorem traceRe_image_mul_comm {n : ℕ} (x y : GroupAlgebra n) :
    traceRe (regularImage x * regularImage y) =
      traceRe (regularImage y * regularImage x) := by
  simp only [← regularImage_mul, traceRe_regularImage]
  rw [MonoidAlgebra.coeff_mul_apply_left, MonoidAlgebra.coeff_mul_apply_right]
  simp only [mul_one, one_mul]
  congr 1
  unfold Finsupp.sum
  exact Finset.sum_congr rfl (fun _ _ ↦ mul_comm _ _)

/-- The vector trace is cyclic on the operator-norm closure of the Fourier polynomials. -/
theorem traceRe_mul_comm_closure {n : ℕ} {T U : Operator n}
    (hT : T ∈ closure (Set.range (regularImage (n := n))))
    (hU : U ∈ closure (Set.range (regularImage (n := n)))) :
    traceRe (T * U) = traceRe (U * T) := by
  have hleft (x : GroupAlgebra n) (V : Operator n)
      (hV : V ∈ closure (Set.range (regularImage (n := n)))) :
      traceRe (regularImage x * V) = traceRe (V * regularImage x) := by
    have hclosed : IsClosed {W : Operator n |
        traceRe (regularImage x * W) = traceRe (W * regularImage x)} :=
      isClosed_eq ((continuous_traceRe n).comp (continuous_const.mul continuous_id))
        ((continuous_traceRe n).comp (continuous_id.mul continuous_const))
    exact closure_minimal (by rintro _ ⟨y, rfl⟩; exact traceRe_image_mul_comm x y)
      hclosed hV
  have hclosed : IsClosed {W : Operator n |
      traceRe (W * U) = traceRe (U * W)} :=
    isClosed_eq ((continuous_traceRe n).comp (continuous_id.mul continuous_const))
      ((continuous_traceRe n).comp (continuous_const.mul continuous_id))
  exact closure_minimal (by rintro _ ⟨x, rfl⟩; exact hleft x U hU) hclosed hT

end FreeGroupHypercontractivity

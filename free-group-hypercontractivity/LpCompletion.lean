module

import all «free-group-hypercontractivity».Model
public import «free-group-hypercontractivity».PoissonExtension

public section

namespace FreeGroupHypercontractivity

/-- The completion embedding preserves the tracial norm of each Fourier polynomial. -/
@[simp]
theorem norm_fourierLpEmbed {n : ℕ} {p : ℝ} (N : FourierLpNorm n p) (x : GroupAlgebra n) :
    ‖fourierLpEmbed N x‖ = lpNorm p x := by
  exact (UniformSpace.Completion.norm_coe (show FourierLpCore N from x)).trans (N.norm_eq x)

/-- A contractive Fourier multiplier extends to the completed spaces, and every
such extension restricts to a contractive multiplier on the dense core. -/
theorem poisson_completion_iff {n : ℕ} {p q : ℝ} (Np : FourierLpNorm n p)
    (Nq : FourierLpNorm n q) (t : ℝ) :
    (∃ P : FourierLp Np →L[ℂ] FourierLp Nq,
      (∀ x : GroupAlgebra n, P (fourierLpEmbed Np x) = fourierLpEmbed Nq (poisson t x)) ∧
      (∀ x : FourierLp Np, ‖P x‖ ≤ ‖x‖)) ↔
      ∀ x : GroupAlgebra n, lpNorm q (poisson t x) ≤ lpNorm p x := by
  constructor
  · rintro ⟨P, hagree, hcontract⟩ x
    simpa only [hagree x, norm_fourierLpEmbed] using hcontract (fourierLpEmbed Np x)
  · intro h
    let L : FourierLpCore Np →ₗ[ℂ] FourierLpCore Nq := poissonLinear n t
    have hLapply (x : FourierLpCore Np) : L x = (show FourierLpCore Nq from poisson t x) :=
      poissonLinear_apply n t x
    have hL (x : FourierLpCore Np) : ‖L x‖ ≤ ‖x‖ := by
      rw [hLapply x]
      exact (le_of_eq (Nq.norm_eq (poisson t x))).trans ((h x).trans_eq (Np.norm_eq x).symm)
    let F := L.mkContinuous 1 (fun x ↦ by simpa only [one_mul] using hL x)
    refine ⟨F.completion, ?_, ?_⟩
    · intro x
      calc
        F.completion (fourierLpEmbed Np x) =
            ((F (show FourierLpCore Np from x)) : FourierLp Nq) :=
          F.completion_apply_coe (show FourierLpCore Np from x)
        _ = fourierLpEmbed Nq (poisson t x) := by
          change ((L (show FourierLpCore Np from x)) : FourierLp Nq) = _
          exact congrArg (fun y : FourierLpCore Nq ↦ (y : FourierLp Nq))
            (hLapply (show FourierLpCore Np from x))
    · intro x
      refine UniformSpace.Completion.induction_on x
        (isClosed_le (continuous_norm.comp F.completion.continuous) continuous_norm) ?_
      intro x
      rw [ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.norm_coe,
        UniformSpace.Completion.norm_coe]
      exact hL x

end FreeGroupHypercontractivity

module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».OperatorMajorant

public section

namespace FreeGroupHypercontractivity

/-- The second moment of a nonzero positive Fourier polynomial is positive. -/
theorem traceRe_regularImage_sq_pos {n : ℕ} {x : GroupAlgebra n}
    (hT : 0 ≤ regularImage x) (hx : x ≠ 0) : 0 < traceRe (regularImage x ^ 2) := by
  have hsa := (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).isSelfAdjoint
  have hsq : regularImage x ^ 2 = star (regularImage x) * regularImage x := by
    rw [hsa.star_eq, pow_two]
  rw [hsq, traceRe_star_mul_self]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hv
  apply hx
  apply MonoidAlgebra.coeff_injective
  ext g
  have hg := congrArg (fun v : Hilbert n ↦ v g) hv
  simpa only [regularImage_delta, lp.coeFn_zero, Pi.zero_apply, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hg

/-- The canonical trace is faithful on positive Fourier polynomials. -/
theorem traceRe_regularImage_pos {n : ℕ} {x : GroupAlgebra n}
    (hT : 0 ≤ regularImage x) (hx : x ≠ 0) : 0 < traceRe (regularImage x) := by
  have hp := (traceRe_regularImage_sq_pos hT hx).trans_le (traceRe_pow_two_le_norm_mul hT)
  exact pos_of_mul_pos_right hp (norm_nonneg _)

end FreeGroupHypercontractivity

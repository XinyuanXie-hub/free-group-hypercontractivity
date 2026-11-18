module

import all Template.Model

public import Template.AbsoluteValueBlock

public section

namespace FreeGroupHypercontractivity

open scoped Matrix

private theorem operatorLpNorm_nonneg {n : ℕ} (q : ℝ) (T : Operator n) :
    0 ≤ operatorLpNorm q T := by
  unfold operatorLpNorm
  exact Real.rpow_nonneg (traceRe_nonneg (operatorRpow_nonneg (star_mul_self_nonneg T))) _

private theorem operatorLpNorm_sq {n : ℕ} (q : ℝ) (T : Operator n) :
    operatorLpNorm q T ^ 2 = traceRe (operatorRpow (star T * T) (q / 2)) ^ (2 / q) := by
  unfold operatorLpNorm
  change (traceRe (operatorRpow (star T * T) (q / 2)) ^ (1 / q)) ^ 2 = _
  have h := traceRe_nonneg
    (operatorRpow_nonneg (r := q / 2) (star_mul_self_nonneg T))
  rw [← Real.rpow_natCast, ← Real.rpow_mul h]
  congr 1
  push_cast
  ring

/-- Complete positivity extends positive-cone Poisson contractivity to
all Fourier inputs, by applying it to the canonical positive two-by-two block. -/
theorem groupCStar_contractivity_of_positive {n : ℕ} {p q t : ℝ}
    (hp : 0 < p) (hq : 1 < q) (ht : 0 ≤ t)
    (hpositive : ∀ X : GroupCStar n, 0 ≤ (X : Operator n) →
      operatorLpNorm q (poissonCStar n t X : Operator n) ≤ operatorLpNorm p (X : Operator n))
    (X : GroupCStar n) :
    operatorLpNorm q (poissonCStar n t X : Operator n) ≤ operatorLpNorm p (X : Operator n) := by
  let T := (X : Operator n)
  let P := poissonCStar n t
  have hT : T ∈ groupCStar n := X.property
  have hTstar : star T ∈ groupCStar n := star_mem hT
  have hTstarstar : star (star T) ∈ groupCStar n := star_mem hTstar
  let L : GroupCStar n := ⟨absoluteValueOperator (star T),
    operatorRpow_mem_groupCStar ((groupCStar n).mul_mem
      hTstarstar hTstar) _⟩
  let R : GroupCStar n := ⟨absoluteValueOperator T,
    operatorRpow_mem_groupCStar ((groupCStar n).mul_mem hTstar hT) _⟩
  let M : Matrix (Fin 2) (Fin 2) (GroupCStar n) := !![L, X; star X, R]
  have hM : OperatorBlockNonneg (fun i j ↦ (M i j : Operator n)) := by
    have hc := (operatorBlockNonneg_iff_hermitianBlockNonneg
      (absoluteValueOperator (star T)) T (absoluteValueOperator T)).mpr
      (absolute_value_block_nonneg T)
    have hmatrix : (fun i j ↦ (M i j : Operator n)) =
        (!![absoluteValueOperator (star T), T; star T, absoluteValueOperator T] :
          Matrix (Fin 2) (Fin 2) (Operator n)) := by
      funext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [hmatrix]
    exact hc
  have hPM := poissonCStar_operatorBlockNonneg ht hM
  have hPM' : HermitianBlockNonneg (P L : Operator n) (P X : Operator n) (P R : Operator n) := by
    apply (operatorBlockNonneg_iff_hermitianBlockNonneg _ _ _).mp
    have hmatrix : (fun i j ↦ (P (M i j) : Operator n)) =
        (!![(P L : Operator n), (P X : Operator n); star (P X : Operator n), (P R : Operator n)] :
          Matrix (Fin 2) (Fin 2) (Operator n)) := by
      funext i j
      fin_cases i <;> fin_cases j
      · rfl
      · rfl
      · exact congrArg (Subtype.val : GroupCStar n → Operator n) (poissonCStar_star ht X)
      · rfl
    rw [← hmatrix]
    exact hPM
  have hL : 0 ≤ (L : Operator n) :=
    operatorRpow_nonneg (star_mul_self_nonneg (star T))
  have hR : 0 ≤ (R : Operator n) :=
    operatorRpow_nonneg (star_mul_self_nonneg T)
  have hpL := poissonCStar_nonneg ht hL
  have hpR := poissonCStar_nonneg ht hR
  have hq' : 0 < q := zero_lt_one.trans hq
  have hblock := block_power_trace_le hpL hpR (P L).property (P X).property (P R).property hPM' hq
  rw [← operatorLpNorm_sq q, ← operatorLpNorm_of_nonneg_eq_trace_rpow hq'.le hpL,
    ← operatorLpNorm_of_nonneg_eq_trace_rpow hq'.le hpR] at hblock
  have hLt : operatorLpNorm p (L : Operator n) = operatorLpNorm p T := by
    change operatorLpNorm p (operatorRpow (star (star T) * star T) (1 / 2)) =
      operatorLpNorm p T
    rw [operatorLpNorm_absoluteValue_eq hp.le, operatorLpNorm_star_eq hp.le hT]
  have hRt : operatorLpNorm p (R : Operator n) = operatorLpNorm p T :=
    operatorLpNorm_absoluteValue_eq hp.le T
  have hl := hpositive L hL
  have hr := hpositive R hR
  rw [hLt] at hl
  rw [hRt] at hr
  apply (sq_le_sq₀ (operatorLpNorm_nonneg q _) (operatorLpNorm_nonneg p _)).mp
  apply hblock.trans
  rw [pow_two]
  exact mul_le_mul hl hr (operatorLpNorm_nonneg q _) (operatorLpNorm_nonneg p _)

end FreeGroupHypercontractivity

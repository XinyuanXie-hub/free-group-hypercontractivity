module

public import «free-group-hypercontractivity».TraceC1Approx
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

public section

namespace FreeGroupHypercontractivity

open Set Polynomial Filter
open scoped Polynomial Topology

section Polynomial

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable (τ : A →L[ℝ] ℝ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
include hτ

/-- Cyclicity reduces the noncommutative derivative of a traced power to a
single term. -/
theorem hasDerivAt_trace_pow {X : ℝ → A} {X' : A} {t : ℝ}
    (hX : HasDerivAt X X' t) (n : ℕ) :
    HasDerivAt (fun s ↦ τ (X s ^ n)) ((n : ℝ) * τ (X t ^ (n - 1) * X')) t := by
  have h := τ.hasFDerivAt.comp_hasDerivAt t (hX.fun_pow' n)
  change HasDerivAt (fun s ↦ τ (X s ^ n)) _ t at h
  convert h using 1
  rw [map_sum]
  have hd (i : ℕ) (hi : i ∈ Finset.range n) :
      τ (X t ^ (n.pred - i) * X' * X t ^ i) = τ (X t ^ (n - 1) * X') := by
    rw [hτ _ (X t ^ i), ← mul_assoc, ← pow_add]
    have hi' := Finset.mem_range.mp hi
    congr 3
    rw [Nat.pred_eq_sub_one] at *
    omega
  symm
  simp only [Finset.sum_congr rfl hd, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The derivative of the trace of a polynomial in an operator-valued path. -/
theorem hasDerivAt_trace_polynomial {X : ℝ → A} {X' : A} {t : ℝ}
    (hX : HasDerivAt X X' t) (p : ℝ[X]) :
    HasDerivAt (fun s ↦ τ (aeval (X s) p)) (τ (aeval (X t) p.derivative * X')) t := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [derivative_add, map_add, add_mul, Pi.add_apply] using hp.fun_add hq
  | monomial n a =>
    have h := (hasDerivAt_trace_pow τ hτ hX n).const_smul a
    simp only [smul_eq_mul] at h
    simp only [aeval_monomial, derivative_monomial]
    convert h using 1
    · ext s
      rw [← Algebra.smul_def, map_smul, smul_eq_mul]
      rfl
    · rw [← Algebra.smul_def, smul_mul_assoc, map_smul, smul_eq_mul]
      ring

end Polynomial


section FunctionalCalculus

variable {A : Type*} [CStarAlgebra A]
variable (τ : A →L[ℝ] ℝ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

/-- Uniform scalar approximation controls the operator norm at every
self-adjoint operator with spectrum in the given interval. -/
theorem norm_aeval_sub_cfc_le {a b ε : ℝ} (hε : 0 ≤ ε) {T : A}
    (hT : IsSelfAdjoint T) (hspec : spectrum ℝ T ⊆ Icc a b)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) (p : ℝ[X])
    (hp : ∀ x ∈ Icc a b, |p.eval x - f x| ≤ ε) :
    ‖aeval T p - cfc (p := IsSelfAdjoint) f T‖ ≤ ε := by
  rw [← cfc_polynomial p T hT, ← cfc_sub _ _ T p.continuous.continuousOn (hf.mono hspec)]
  apply norm_cfc_le hε
  intro x hx
  exact hp x (hspec hx)

include hτ in
/-- The traced continuous functional calculus differentiates with the usual
scalar derivative, even when the path does not commute with its derivative. -/
theorem hasDerivAt_trace_cfc {S : Set ℝ} (hS : IsOpen S)
    {a b C : ℝ} (hab : a ≤ b)
    (X dX : ℝ → A)
    (hXd : ∀ t ∈ S, HasDerivAt X (dX t) t)
    (hXsa : ∀ t ∈ S, IsSelfAdjoint (X t))
    (hXspec : ∀ t ∈ S, spectrum ℝ (X t) ⊆ Icc a b)
    (hdXB : ∀ t ∈ S, ‖dX t‖ ≤ C)
    (f f' : ℝ → ℝ)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hf' : ContinuousOn f' (Icc a b))
    {t : ℝ} (ht : t ∈ S) :
    HasDerivAt (fun s ↦ τ (cfc (p := IsSelfAdjoint) f (X s)))
      (τ (cfc (p := IsSelfAdjoint) f' (X t) * dX t)) t := by
  let ε (n : ℕ) := (1 : ℝ) / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hfc : ContinuousOn f (Icc a b) := fun x hx ↦ (hf x hx).continuousWithinAt
  choose P hP using fun n ↦ exists_polynomial_near_of_hasDerivWithinAt hab hf hf' (hε n)
  let F (n : ℕ) (s : ℝ) := τ (aeval (X s) (P n))
  let F' (n : ℕ) (s : ℝ) := τ (aeval (X s) (P n).derivative * dX s)
  have hFbound (n : ℕ) (s : ℝ) (hs : s ∈ S) :
      dist (τ (cfc (p := IsSelfAdjoint) f (X s))) (F n s) ≤ ‖τ‖ * ε n := by
    rw [dist_comm, dist_eq_norm]
    change ‖τ (aeval (X s) (P n)) - τ (cfc (p := IsSelfAdjoint) f (X s))‖ ≤ _
    rw [← map_sub]
    exact (τ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (norm_aeval_sub_cfc_le (hε n).le (hXsa s hs) (hXspec s hs) f hfc (P n)
        (fun x hx ↦ ((hP n).1 x hx).le)) (norm_nonneg _))
  have hF'bound (n : ℕ) (s : ℝ) (hs : s ∈ S) :
      dist (τ (cfc (p := IsSelfAdjoint) f' (X s) * dX s)) (F' n s) ≤
        ‖τ‖ * (ε n * C) := by
    rw [dist_comm, dist_eq_norm]
    change ‖τ (aeval (X s) (P n).derivative * dX s) -
      τ (cfc (p := IsSelfAdjoint) f' (X s) * dX s)‖ ≤ _
    rw [← map_sub, ← sub_mul]
    refine (τ.le_opNorm _).trans <| mul_le_mul_of_nonneg_left ((norm_mul_le ..).trans ?_)
      (norm_nonneg _)
    exact mul_le_mul
      (norm_aeval_sub_cfc_le (hε n).le (hXsa s hs) (hXspec s hs) f' hf' (P n).derivative
        (fun x hx ↦ ((hP n).2 x hx).le)) (hdXB s hs) (norm_nonneg _) (hε n).le
  have hF'lim : TendstoUniformlyOn F' (fun s ↦ τ (cfc (p := IsSelfAdjoint) f' (X s) * dX s)) atTop S := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have hlim : Tendsto (fun n ↦ ‖τ‖ * (ε n * C)) atTop (𝓝 0) := by
      simpa using (hεlim.mul_const C).const_mul ‖τ‖
    filter_upwards [hlim.eventually_lt_const hδ] with n hn s hs
    exact (hF'bound n s hs).trans_lt hn
  refine hasDerivAt_of_tendstoUniformlyOn hS hF'lim
    (Eventually.of_forall fun n s hs ↦ hasDerivAt_trace_polynomial τ hτ (hXd s hs) (P n)) ?_ ht
  intro s hs
  refine Metric.tendsto_nhds.2 (fun δ hδ ↦ ?_)
  have hlim : Tendsto (fun n ↦ ‖τ‖ * ε n) atTop (𝓝 0) := by
    simpa using hεlim.const_mul ‖τ‖
  filter_upwards [hlim.eventually_lt_const hδ] with n hn
  rw [dist_comm]
  exact (hFbound n s hs).trans_lt hn

end FunctionalCalculus

end FreeGroupHypercontractivity

module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».Trace
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

public section

namespace FreeGroupHypercontractivity

open scoped ENNReal InnerProductSpace ComplexOrder

private theorem star_range_leftRegular (n : ℕ) :
    star (Set.range (leftRegular (n := n))) = Set.range (leftRegular (n := n)) := by
  ext x
  rw [Set.mem_star]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g⁻¹, by rw [← star_leftRegular, hg, star_star]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, (star_leftRegular g).symm⟩

/-- The bicommutant as a closed star subalgebra of the bounded operators. -/
noncomputable def vonNeumannStarSubalgebra (n : ℕ) : StarSubalgebra ℂ (Operator n) :=
  StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (Set.range (leftRegular (n := n))) : Set (Operator n))

theorem coe_vonNeumannStarSubalgebra (n : ℕ) :
    (vonNeumannStarSubalgebra n : Set (Operator n)) = groupVonNeumann n := by
  rw [vonNeumannStarSubalgebra, StarSubalgebra.coe_centralizer_centralizer,
    star_range_leftRegular, Set.union_self, groupVonNeumann]

@[simp] theorem mem_vonNeumannStarSubalgebra_iff {n : ℕ} {T : Operator n} :
    T ∈ vonNeumannStarSubalgebra n ↔ T ∈ groupVonNeumann n := by
  rw [← SetLike.mem_coe, coe_vonNeumannStarSubalgebra]

theorem groupVonNeumann_isClosed (n : ℕ) : IsClosed (groupVonNeumann n) :=
  Set.isClosed_centralizer _

instance vonNeumannStarSubalgebra_isClosed (n : ℕ) :
    IsClosed (vonNeumannStarSubalgebra n : Set (Operator n)) :=
  coe_vonNeumannStarSubalgebra n ▸ groupVonNeumann_isClosed n

theorem leftRegular_mem_groupVonNeumann {n : ℕ} (g : Group n) :
    leftRegular g ∈ groupVonNeumann n := by
  intro U hU
  exact (hU _ ⟨g, rfl⟩).symm

theorem regularImage_mem_groupVonNeumann {n : ℕ} (x : GroupAlgebra n) :
    regularImage x ∈ groupVonNeumann n := by
  apply mem_vonNeumannStarSubalgebra_iff.mp
  rw [regularImage, Finsupp.sum]
  exact (vonNeumannStarSubalgebra n).sum_mem fun g _ ↦
    (vonNeumannStarSubalgebra n).smul_mem
      (mem_vonNeumannStarSubalgebra_iff.mpr (leftRegular_mem_groupVonNeumann g)) _

theorem cfc_mem_groupVonNeumann {n : ℕ} (f : ℂ → ℂ) {T : Operator n}
    (hT : T ∈ groupVonNeumann n) :
    cfc (p := IsStarNormal) f T ∈ groupVonNeumann n :=
  mem_vonNeumannStarSubalgebra_iff.mp
    (cfc_mem (𝕜' := ℂ) f (mem_vonNeumannStarSubalgebra_iff.mpr hT))

theorem exp_mem_groupVonNeumann {n : ℕ} {T : Operator n}
    (hT : T ∈ groupVonNeumann n) : NormedSpace.exp T ∈ groupVonNeumann n :=
  mem_vonNeumannStarSubalgebra_iff.mp
    (NormedSpace.exp_mem (s := vonNeumannStarSubalgebra n) inferInstance
      (mem_vonNeumannStarSubalgebra_iff.mpr hT))

/-- Right regular translation on the free-group Hilbert space. -/
noncomputable def rightRegular {n : ℕ} (g : Group n) : Operator n :=
  let e : Group n ≃ Group n := Equiv.mulRight g⁻¹
  let translate (v : Hilbert n) : Hilbert n :=
    ⟨fun h ↦ v (e h), memℓp_gen (e.summable_iff.mpr ((lp.memℓp v).summable (by norm_num)))⟩
  LinearMap.mkContinuous
    { toFun := translate
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
    1 (by
      intro v
      simp only [one_mul]
      change ‖translate v‖ ≤ ‖v‖
      rw [lp.norm_eq_tsum_rpow (by norm_num) (translate v),
        lp.norm_eq_tsum_rpow (by norm_num) v]
      change (∑' h, ‖v (e h)‖ ^ (2 : ℝ≥0∞).toReal) ^ _ ≤
        (∑' h, ‖v h‖ ^ (2 : ℝ≥0∞).toReal) ^ _
      have hsum := e.tsum_eq (fun h : Group n ↦ ‖v h‖ ^ (2 : ℝ≥0∞).toReal)
      exact le_of_eq (congrArg (fun x : ℝ ↦ x ^ (1 / (2 : ℝ≥0∞).toReal)) hsum))

@[simp] theorem rightRegular_apply {n : ℕ} (g h : Group n) (v : Hilbert n) :
    rightRegular g v h = v (h * g⁻¹) := by
  rfl

theorem commute_leftRegular_rightRegular {n : ℕ} (g h : Group n) :
    Commute (leftRegular g) (rightRegular h) := by
  show leftRegular g * rightRegular h = rightRegular h * leftRegular g
  ext v k
  change leftRegular g (rightRegular h v) k = rightRegular h (leftRegular g v) k
  simp [mul_assoc]

@[simp] theorem rightRegular_identityVector {n : ℕ} (g : Group n) :
    rightRegular g (lp.single 2 1 1) = lp.single 2 g 1 := by
  ext h
  simp only [rightRegular_apply]
  by_cases h' : h = g
  · subst h
    simp
  · have hm : h * g⁻¹ ≠ 1 := fun hc ↦ h' (mul_inv_eq_one.mp hc)
    rw [lp.single_apply_ne 2 1 1 hm, lp.single_apply_ne 2 g 1 h']

/-- All operators in the bicommutant commute with right translations. -/
theorem commute_rightRegular_of_mem_groupVonNeumann {n : ℕ} {T : Operator n}
    (hT : T ∈ groupVonNeumann n) (g : Group n) : Commute (rightRegular g) T :=
  hT _ (by rintro _ ⟨h, rfl⟩; exact commute_leftRegular_rightRegular h g)

/-- The matrix entries in the group basis depend only on the quotient of indices. -/
theorem vonNeumann_entry {n : ℕ} {T : Operator n} (hT : T ∈ groupVonNeumann n)
    (g h : Group n) :
    T (lp.single 2 h 1) g = T (lp.single 2 1 1) (g * h⁻¹) := by
  have he := congrArg (fun U : Operator n ↦ U (lp.single 2 1 1) g)
    (commute_rightRegular_of_mem_groupVonNeumann hT h).eq
  change rightRegular h (T (lp.single 2 1 1)) g = T (rightRegular h (lp.single 2 1 1)) g at he
  simpa only [rightRegular_apply, rightRegular_identityVector] using he.symm

theorem vonNeumann_adjoint_identityVector {n : ℕ} {T : Operator n}
    (hT : T ∈ groupVonNeumann n) (g : Group n) :
    star T (lp.single 2 1 1) g = star (T (lp.single 2 1 1) g⁻¹) := by
  classical
  have h := ContinuousLinearMap.adjoint_inner_right T
    (lp.single 2 g 1) (lp.single 2 1 1)
  rw [lp.inner_single_left, lp.inner_single_right, RCLike.inner_apply, RCLike.inner_apply] at h
  rw [vonNeumann_entry hT] at h
  simpa only [← ContinuousLinearMap.star_eq_adjoint, starRingEnd_apply, star_one, mul_one,
    one_mul] using h

/-- The canonical vector state is a trace on the bicommutant of the left regular representation. -/
theorem traceRe_mul_comm_vonNeumann {n : ℕ} {T U : Operator n}
    (hT : T ∈ groupVonNeumann n) (hU : U ∈ groupVonNeumann n) :
    traceRe (T * U) = traceRe (U * T) := by
  have hpair (A B : Operator n) (hA : A ∈ groupVonNeumann n) :
      traceRe (A * B) =
        (∑' g : Group n, A (lp.single 2 1 1) g⁻¹ * B (lp.single 2 1 1) g).re := by
    rw [traceRe_as_inner]
    let δ : Hilbert n := lp.single 2 1 1
    change (⟪δ, A (B δ)⟫_ℂ).re = _
    rw [← ContinuousLinearMap.adjoint_inner_left, lp.inner_eq_tsum]
    congr 1
    apply tsum_congr
    intro g
    rw [RCLike.inner_apply']
    change star (star A δ g) * B δ g = _
    rw [vonNeumann_adjoint_identityVector hA, star_star]
  rw [hpair T U hT, hpair U T hU]
  congr 1
  rw [← (Equiv.inv (Group n)).tsum_eq (fun g ↦ U (lp.single 2 1 1) g⁻¹ * T (lp.single 2 1 1) g)]
  apply tsum_congr
  intro g
  change T (lp.single 2 1 1) g⁻¹ * U (lp.single 2 1 1) g =
    U (lp.single 2 1 1) g⁻¹⁻¹ * T (lp.single 2 1 1) g⁻¹
  rw [inv_inv, mul_comm]

end FreeGroupHypercontractivity

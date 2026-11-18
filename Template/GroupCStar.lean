module

import all Template.Model

public import Template.Trace
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

public section

namespace FreeGroupHypercontractivity

open scoped BigOperators

/-- The left regular image of the finite Fourier polynomials. -/
noncomputable def polynomialStarSubalgebra (n : ℕ) : StarSubalgebra ℂ (Operator n) where
  toSubalgebra := (regularHom n).range
  star_mem' := by
    rintro _ ⟨x, rfl⟩
    refine ⟨∑ g ∈ x.coeff.support, MonoidAlgebra.single g⁻¹ (star (x.coeff g)), ?_⟩
    change regularHom n _ = star (regularHom n x)
    rw [map_sum, regularHom_apply x, regularImage, Finsupp.sum,
      ContinuousLinearMap.star_eq_adjoint, map_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [regularHom_apply, regularImage_single, ← ContinuousLinearMap.star_eq_adjoint,
      star_smul, star_leftRegular]

/-- The reduced group C*-algebra, the operator norm closure of Fourier polynomials. -/
noncomputable def groupCStar (n : ℕ) : StarSubalgebra ℂ (Operator n) :=
  (polynomialStarSubalgebra n).topologicalClosure

theorem mem_groupCStar_iff {n : ℕ} {T : Operator n} :
    T ∈ groupCStar n ↔ T ∈ closure (Set.range (regularImage : GroupAlgebra n → Operator n)) := by
  have hrange : (polynomialStarSubalgebra n : Set (Operator n)) =
      Set.range (regularImage : GroupAlgebra n → Operator n) := by
    change Set.range (regularHom n) = _
    exact congrArg Set.range (funext regularHom_apply)
  change T ∈ closure (polynomialStarSubalgebra n : Set (Operator n)) ↔ _
  rw [hrange]

theorem regularImage_mem_groupCStar {n : ℕ} (x : GroupAlgebra n) :
    regularImage x ∈ groupCStar n :=
  mem_groupCStar_iff.mpr (subset_closure ⟨x, rfl⟩)

instance groupCStar_isClosed (n : ℕ) : IsClosed (groupCStar n : Set (Operator n)) :=
  (polynomialStarSubalgebra n).isClosed_topologicalClosure

noncomputable abbrev GroupCStar (n : ℕ) := ↥(groupCStar n)

/-- Continuous functional calculus in the ambient operator algebra preserves the
reduced group algebra. -/
theorem cfc_mem_groupCStar {n : ℕ} (f : ℂ → ℂ) {T : Operator n}
    (hT : T ∈ groupCStar n) : cfc (p := IsStarNormal) f T ∈ groupCStar n :=
  cfc_mem (𝕜' := ℂ) f hT

/-- Canonical trace as a continuous real linear functional on the reduced group algebra. -/
noncomputable def groupTraceReCLM (n : ℕ) : GroupCStar n →L[ℝ] ℝ :=
  (traceReCLM n).comp
    ((groupCStar n).toSubalgebra.toSubmodule.subtypeL.restrictScalars ℝ)

@[simp]
theorem groupTraceReCLM_apply {n : ℕ} (T : GroupCStar n) :
    groupTraceReCLM n T = traceRe (T : Operator n) := by
  exact traceReCLM_apply _

theorem groupTraceReCLM_mul_comm {n : ℕ} (T U : GroupCStar n) :
    groupTraceReCLM n (T * U) = groupTraceReCLM n (U * T) := by
  simp only [groupTraceReCLM_apply]
  exact traceRe_mul_comm_closure (mem_groupCStar_iff.mp T.property)
    (mem_groupCStar_iff.mp U.property)

theorem groupCStar_coe_cfc {n : ℕ} (f : ℂ → ℂ) (hf : Continuous f)
    (T : GroupCStar n) (hT : IsStarNormal T) :
    ((cfc (p := IsStarNormal) f T : GroupCStar n) : Operator n) =
      cfc (p := IsStarNormal) f (T : Operator n) := by
  have h' : IsStarNormal ((groupCStar n).subtype T) := hT.map (groupCStar n).subtype
  exact (groupCStar n).subtype.map_cfc f T hf.continuousOn continuous_subtype_val hT h'

theorem groupCStar_coe_real_cfc {n : ℕ} (f : ℝ → ℝ) (hf : Continuous f)
    (T : GroupCStar n) (hT : IsSelfAdjoint T) :
    ((cfc (p := IsSelfAdjoint) f T : GroupCStar n) : Operator n) =
      cfc (p := IsStarNormal) (fun z : ℂ ↦ Complex.ofReal (f z.re)) (T : Operator n) := by
  rw [cfc_real_eq_complex f hT]
  exact groupCStar_coe_cfc _ (Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re))
    T hT.isStarNormal

end FreeGroupHypercontractivity

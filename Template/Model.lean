module

meta import Lean.Elab.Command

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Sharp hypercontractivity for free group von Neumann algebras

Definitions for the independent solution of Xie and Zhang, arXiv:2606.03423v3.
-/

-- Comparator checks definition bodies by name, including generated private proofs.
-- Reproduce the names of the generated proofs when elaborating the independent model.
open Lean Elab Command in
elab "#with_challenge_auxiliary_names " declarations:command*
    "#end_challenge_auxiliary_names" : command => do
  let mainModule := (← getEnv).mainModule
  modifyEnv (·.setMainModule `Challenge)
  try
    for declaration in declarations do
      elabCommand declaration
  finally
    modifyEnv (·.setMainModule mainModule)

public section

namespace FreeGroupHypercontractivity

open scoped ENNReal

#with_challenge_auxiliary_names
abbrev Group (n : ℕ) := FreeGroup (Fin n)
abbrev GroupAlgebra (n : ℕ) := MonoidAlgebra ℂ (Group n)
noncomputable abbrev Hilbert (n : ℕ) := lp (fun _ : Group n ↦ ℂ) 2
noncomputable abbrev Operator (n : ℕ) := Hilbert n →L[ℂ] Hilbert n

/-- The left regular representation, acting by translation by the inverse on functions. -/
noncomputable def leftRegular {n : ℕ} (g : Group n) : Operator n :=
  let e : Group n ≃ Group n := Equiv.mulLeft g⁻¹
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

/-- Represent a finite Fourier sum as a bounded operator. -/
noncomputable def regularImage {n : ℕ} (x : GroupAlgebra n) : Operator n :=
  x.coeff.sum fun g c ↦ c • leftRegular g

/-- Real part of the canonical trace, given by the identity coefficient of `T δ₁`. -/
noncomputable def traceRe {n : ℕ} (T : Operator n) : ℝ :=
  (T (lp.single 2 1 1) 1).re

/-- The noncommutative Lp norm on Fourier polynomials, using |T|ᵖ = (T* T)ᵖᐟ². -/
noncomputable def lpNorm {n : ℕ} (p : ℝ) (x : GroupAlgebra n) : ℝ :=
  let T := regularImage x
  let Tpow := cfc (p := IsStarNormal) (fun s : ℂ ↦ Complex.ofReal (s.re ^ (p / 2)))
    (star T * T)
  traceRe Tpow ^ (1 / p)

/-- A Fourier multiplier with scalar symbol `m`. -/
noncomputable def multiplier {n : ℕ} (m : Group n → ℂ) (x : GroupAlgebra n) :
    GroupAlgebra n :=
  MonoidAlgebra.ofCoeff <| Finsupp.onFinset x.coeff.support
    (fun g ↦ m g * x.coeff g) (by
      intro g hg
      exact Finsupp.mem_support_iff.mpr (fun h ↦ hg (by rw [h, mul_zero])))

/-- The Poisson semigroup on Fourier polynomials. -/
noncomputable def poisson {n : ℕ} (t : ℝ) (x : GroupAlgebra n) : GroupAlgebra n :=
  multiplier (fun g ↦ (Real.exp (-t * (FreeGroup.norm g : ℝ)) : ℂ)) x

/-- The word-length generator of the Poisson semigroup. -/
noncomputable def generator {n : ℕ} (x : GroupAlgebra n) : GroupAlgebra n :=
  multiplier (fun g ↦ (FreeGroup.norm g : ℂ)) x

/-- Entropy for a positive bounded operator, with the continuous convention at zero. -/
noncomputable def entropy {n : ℕ} (T : Operator n) : ℝ :=
  traceRe (cfc (p := IsStarNormal) (fun s : ℂ ↦ Complex.ofReal (s.re * Real.log s.re)) T) -
    traceRe T * Real.log (traceRe T)

#end_challenge_auxiliary_names

@[simp]
theorem leftRegular_apply {n : ℕ} (g h : Group n) (v : Hilbert n) :
    leftRegular g v h = v (g⁻¹ * h) := by
  rfl

@[simp]
theorem multiplier_coeff {n : ℕ} (m : Group n → ℂ) (x : GroupAlgebra n) (g : Group n) :
    (multiplier m x).coeff g = m g * x.coeff g := by
  simp [multiplier, MonoidAlgebra.coeff_ofCoeff]

end FreeGroupHypercontractivity

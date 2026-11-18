module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Sharp hypercontractivity for free group von Neumann algebras

Challenge for Xie and Zhang, arXiv:2606.03423v3, Theorems 1.1 and 1.2.
-/

public section

namespace FreeGroupHypercontractivity

open scoped ENNReal

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

/-- Theorem 1.1 in its dense-core formulation. The contractive inequality on Fourier
polynomials is the condition for a contractive extension from Lp to Lq. -/
theorem theorem_1_1 (n : ℕ) (hn : 2 ≤ n) (p q t : ℝ)
    (hp : 1 < p) (hpq : p ≤ q) (ht : 0 ≤ t) :
    (∀ x : GroupAlgebra n, lpNorm q (poisson t x) ≤ lpNorm p x) ↔
      (1 / 2 : ℝ) * Real.log ((q - 1) / (p - 1)) ≤ t := by
  sorry

/-- Theorem 1.2, the inequality on positive Fourier polynomials. -/
theorem theorem_1_2 (n : ℕ) (hn : 2 ≤ n) (x : GroupAlgebra n)
    (hx : 0 ≤ regularImage x) :
    entropy (regularImage x ^ 2) ≤
      2 * traceRe (regularImage x * regularImage (generator x)) := by
  sorry

end FreeGroupHypercontractivity

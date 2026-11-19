module

import all «free-group-hypercontractivity».Model

public import «free-group-hypercontractivity».HypercontractivityPoisson
public import «free-group-hypercontractivity».Moments

public section

namespace FreeGroupHypercontractivity

open scoped InnerProductSpace Topology

private noncomputable def truncate {n : ℕ} (s : Finset (Group n)) (v : Hilbert n) : Hilbert n :=
  ∑ g ∈ s, lp.single 2 g (v g)

private theorem tendsto_truncate {n : ℕ} (v : Hilbert n) :
    Filter.Tendsto (fun s ↦ truncate s v) Filter.atTop (𝓝 v) :=
  lp.hasSum_single ENNReal.ofNat_ne_top v

/-- Matrix entry relative to the standard basis of the regular representation. -/
@[expose] noncomputable def operatorEntry {n : ℕ} (T : Operator n) (g h : Group n) : ℂ :=
  T (lp.single 2 h 1) g

theorem continuous_operatorEntry {n : ℕ} (g h : Group n) :
    Continuous fun T : Operator n ↦ operatorEntry T g h := by
  unfold operatorEntry
  exact (lp.evalCLM ℂ (fun _ : Group n ↦ ℂ) 2 g).continuous.comp
    (ContinuousLinearMap.apply ℂ (Hilbert n) (lp.single 2 h 1)).continuous

@[simp] theorem operatorEntry_regularImage {n : ℕ} (x : GroupAlgebra n) (g h : Group n) :
    operatorEntry (regularImage x) g h = x.coeff (g * h⁻¹) := by
  rw [operatorEntry, regularImage_delta_at]

private theorem operatorEntry_delta_scalar {n : ℕ} (T : Operator n)
    (g h : Group n) (c : ℂ) :
    T (lp.single 2 h c) g = operatorEntry T g h * c := by
  have he : lp.single 2 h c = c • lp.single (E := fun _ : Group n ↦ ℂ) 2 h 1 := by
    rw [← lp.single_smul]
    simp
  rw [he, map_smul, lp.coeFn_smul, Pi.smul_apply, operatorEntry, smul_eq_mul, mul_comm]

private theorem inner_truncate {n : ℕ} (T : Operator n) (s : Finset (Group n))
    (v w : Group n → ℂ) :
    ⟪∑ g ∈ s, lp.single 2 g (v g), T (∑ h ∈ s, lp.single 2 h (w h))⟫_ℂ =
      ∑ g ∈ s, ∑ h ∈ s, star (v g) * operatorEntry T g h * w h := by
  classical
  simp only [map_sum, sum_inner, inner_sum, lp.inner_single_left, operatorEntry_delta_scalar,
    RCLike.inner_apply, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change operatorEntry T i j * (w j * star (v i)) = star (v i) * (operatorEntry T i j * w j)
  ring

/-- Positivity of a block operator's quadratic form, expressed through its real part. -/
@[expose] def OperatorBlockNonneg {n : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → ι → Operator n) : Prop :=
  ∀ v : ι → Hilbert n, 0 ≤ ∑ i, ∑ j, (⟪v i, x i j (v j)⟫_ℂ).re

/-- Nonnegativity of a Fourier polynomial matrix in the regular representation. -/
@[expose] def FourierBlockNonneg {n : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → ι → GroupAlgebra n) : Prop :=
  OperatorBlockNonneg (fun i j ↦ regularImage (x i j))

private theorem truncate_block_form {n : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → ι → Operator n) (s : Finset (Group n))
    (c : ι × Group n → ℂ) :
    (∑ i, ∑ j, (⟪∑ g ∈ s, lp.single 2 g (c (i,g)),
      x i j (∑ h ∈ s, lp.single 2 h (c (j,h)))⟫_ℂ).re) =
      ∑ i ∈ (Finset.univ ×ˢ s), ∑ j ∈ (Finset.univ ×ˢ s),
        (star (c i) * operatorEntry (x i.1 j.1) i.2 j.2 * c j).re := by
  simp only [inner_truncate, Complex.re_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

/-- Multiplication of every matrix entry by the Poisson kernel preserves nonnegative
quadratic forms at every finite matrix size. -/
theorem operatorBlockNonneg_of_poisson_kernel {n : ℕ} {ι : Type*} [Fintype ι]
    {x y : ι → ι → Operator n} {t : ℝ} (ht : 0 ≤ t)
    (hxy : ∀ i j g h, operatorEntry (y i j) g h =
      (Real.exp (-t * (FreeGroup.norm (g*h⁻¹) : ℝ)) : ℂ) * operatorEntry (x i j) g h)
    (hx : OperatorBlockNonneg x) : OperatorBlockNonneg y := by
  classical
  intro v
  have hv (i : ι) := tendsto_truncate (v i)
  have hlim : Filter.Tendsto
      (fun s ↦ ∑ i, ∑ j, (⟪truncate s (v i), y i j (truncate s (v j))⟫_ℂ).re)
      Filter.atTop (𝓝 (∑ i, ∑ j, (⟪v i, y i j (v j)⟫_ℂ).re)) := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    apply Complex.continuous_re.continuousAt.tendsto.comp
    exact (hv i).inner ((y i j).continuous.continuousAt.tendsto.comp (hv j))
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
  intro s
  let E := (Finset.univ : Finset ι) ×ˢ s
  let K (i j : ι × Group n) := operatorEntry (x i.1 j.1) i.2 j.2
  have hK (c : ι × Group n → ℂ) :
      0 ≤ ∑ i ∈ E, ∑ j ∈ E, (star (c i) * K i j * c j).re := by
    exact (truncate_block_form x s c) ▸ hx (fun i ↦ ∑ g ∈ s, lp.single 2 g (c (i,g)))
  have hb := poisson_schur_nonneg ht E Prod.snd K hK (fun i ↦ v i.1 i.2)
  dsimp only [truncate]
  rw [truncate_block_form y s (fun i ↦ v i.1 i.2)]
  refine hb.trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hxy]
  let z := Real.exp (-t * (FreeGroup.norm (i.2 * j.2⁻¹) : ℝ))
  change (star (v i.1 i.2) * K i j * v j.1 j.2).re * z =
    (star (v i.1 i.2) * ((z : ℂ) * K i j) * v j.1 j.2).re
  rw [show star (v i.1 i.2) * ((z : ℂ) * K i j) * v j.1 j.2 =
      (z : ℂ) * (star (v i.1 i.2) * K i j * v j.1 j.2) by ring]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_comm]

/-- Poisson preserves nonnegative quadratic forms of finite Fourier polynomial matrices. -/
theorem poisson_fourierBlockNonneg {n : ℕ} {ι : Type*} [Fintype ι]
    {x : ι → ι → GroupAlgebra n} {t : ℝ} (ht : 0 ≤ t) (hx : FourierBlockNonneg x) :
    FourierBlockNonneg (fun i j ↦ poisson t (x i j)) := by
  apply operatorBlockNonneg_of_poisson_kernel ht _ hx
  intro i j g h
  simp only [operatorEntry_regularImage, poisson_coeff]

private theorem selfAdjoint_regularImage_of_coeff_inv {n : ℕ} {x : GroupAlgebra n}
    (hx : ∀ g, x.coeff g⁻¹ = star (x.coeff g)) :
    IsSelfAdjoint (regularImage x) := by
  classical
  change star (regularImage x) = regularImage x
  simp only [regularImage, Finsupp.sum]
  rw [star_sum x.coeff.support (fun g ↦ (x.coeff g • leftRegular g : Operator n))]
  simp only [star_smul, star_leftRegular]
  refine Finset.sum_nbij (fun (g : Group n) ↦ g⁻¹) ?_ ?_ ?_ ?_
  · intro g hg
    simpa only [Finset.mem_coe, Finsupp.mem_support_iff, hx, star_ne_zero] using hg
  · exact fun _ _ _ _ h ↦ inv_injective h
  · intro g hg
    refine ⟨g⁻¹, ?_, inv_inv _⟩
    simpa only [Finset.mem_coe, Finsupp.mem_support_iff, hx, star_ne_zero] using hg
  · simp [hx]

/-- Positivity of Fourier polynomials is preserved by the Poisson semigroup. -/
theorem regularImage_poisson_nonneg {n : ℕ} {t : ℝ} {x : GroupAlgebra n}
    (ht : 0 ≤ t) (hx : 0 ≤ regularImage x) : 0 ≤ regularImage (poisson t x) := by
  have hpos := ContinuousLinearMap.nonneg_iff_isPositive.mp hx
  have hx' : FourierBlockNonneg (fun (_ _ : Unit) ↦ x) := by
    intro v
    simpa using hpos.re_inner_nonneg_right (v ())
  have hp := poisson_fourierBlockNonneg ht hx'
  refine ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (ContinuousLinearMap.isPositive_def'.mpr ⟨?_, fun v ↦ ?_⟩)
  · apply selfAdjoint_regularImage_of_coeff_inv
    intro g
    simp only [poisson_coeff, FreeGroup.norm_inv_eq, coeff_inv_of_selfAdjoint hpos.isSelfAdjoint,
      star_mul', Complex.star_def, Complex.conj_ofReal]
  · simpa [ContinuousLinearMap.reApplyInnerSelf, inner_re_symm] using hp (fun _ ↦ v)

end FreeGroupHypercontractivity

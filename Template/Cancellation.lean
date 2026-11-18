module

public import Template.CancellationWords
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.Complex.Basic

public section

namespace FreeGroupHypercontractivity.Cancellation

open FreeGroup

variable {n : ℕ}

local notation "G" => FreeGroup (Fin n)
local notation "A" => MonoidAlgebra ℂ G

/-- The finite shell of reduced words of length `k`. -/
noncomputable def wordShell (n k : ℕ) : Finset (FreeGroup (Fin n)) := by
  classical
  exact ((Finset.univ : Finset (Fin k → Fin n × Bool)).image
    (fun f ↦ mk (List.ofFn f))).filter (fun g ↦ norm g = k)

@[simp] theorem mem_wordShell {k : ℕ} {g : G} : g ∈ wordShell n k ↔ norm g = k := by
  classical
  simp only [wordShell, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  change g.toWord.length = k at h
  refine ⟨fun i ↦ g.toWord.get (i.cast h.symm), ?_⟩
  subst k
  simpa using (mk_toWord (x := g))

/-- Projection onto one length shell. -/
noncomputable def shell (k : ℕ) (x : A) : A :=
  MonoidAlgebra.ofCoeff (x.coeff.filter (fun g ↦ norm g = k))

@[simp] theorem shell_coeff (k : ℕ) (x : A) (g : G) :
    (shell k x).coeff g = if norm g = k then x.coeff g else 0 := by rw [shell, MonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply]

/-- Squared Euclidean norm of the finite coefficient array. -/
@[expose] noncomputable def coeffL2Sq (x : A) : ℝ :=
  ∑ g ∈ x.coeff.support, ‖x.coeff g‖ ^ 2

theorem coeffL2Sq_nonneg (x : A) : 0 ≤ coeffL2Sq x :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- A polynomial supported in the specified word-length shell. -/
@[expose] def Supported (k : ℕ) (x : A) : Prop :=
  ∀ g ∈ x.coeff.support, norm g = k

theorem shell_supported (k : ℕ) (x : A) : Supported k (shell k x) := by
  intro g hg
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hg) (by simp [hn])

private theorem coeff_zero_of_not_supported {k : ℕ} {x : A}
    (hx : Supported k x) {g : G} (hg : norm g ≠ k) :
    x.coeff g = 0 :=
  Finsupp.notMem_support_iff.mp fun hs ↦ hg (hx g hs)

theorem coeffL2Sq_eq_sum_wordShell {k : ℕ} {x : A} (hx : Supported k x) :
    coeffL2Sq x = ∑ g ∈ wordShell n k, ‖x.coeff g‖ ^ 2 := by
  classical
  exact Finset.sum_subset (fun g hg ↦ mem_wordShell.mpr (hx g hg))
    (fun g _ hg ↦ by simp [Finsupp.notMem_support_iff.mp hg])

/-- The triangle and parity conditions for a convolution coefficient. -/
def Admissible (i j k : ℕ) : Prop :=
  k ≤ i + j ∧ i ≤ j + k ∧ j ≤ i + k ∧ Even (i + j + k)

theorem admissible_iff_exists (i j k : ℕ) :
    Admissible i j k ↔ ∃ d : ℕ, d ≤ i ∧ d ≤ j ∧ i + j = k + 2*d := by
  constructor
  · rintro ⟨_, _, _, a, ha⟩
    exact ⟨(i+j-k)/2, by omega, by omega, by omega⟩
  · rintro ⟨d, _, _, hd⟩
    exact ⟨by omega, by omega, by omega, k+d, by omega⟩

/-- A product of two group elements can only occur in an admissible shell. -/
theorem admissible_norm_mul (u v : G) : Admissible (norm u) (norm v) (norm (u*v)) :=
  (admissible_iff_exists _ _ _).mpr (additive_lengths u v)

theorem shell_mul_eq_zero_of_not_admissible {i j k : ℕ} {x y : A}
    (hx : Supported i x) (hy : Supported j y) (hk : ¬ Admissible i j k) :
    shell k (x * y) = 0 := by
  classical
  apply MonoidAlgebra.coeff_injective
  ext g
  change (shell k (x*y)).coeff g = 0
  rw [shell_coeff]
  split_ifs with hg
  · rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro u hu
    apply mul_eq_zero_of_right
    apply coeff_zero_of_not_supported hy
    intro hv
    apply hk
    simpa only [hx u hu, hv, mul_inv_cancel_left, hg] using admissible_norm_mul u (u⁻¹*g)
  · rfl


private theorem sum_filter_nonzero {ι K : Type*} [AddCommMonoid K] (s : Finset ι)
    (f : ι → K) [DecidablePred (fun i ↦ f i ≠ 0)] :
    (∑ i ∈ s.filter (fun i ↦ f i ≠ 0), f i) = ∑ i ∈ s, f i := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi his
  by_contra hn
  exact his (Finset.mem_filter.mpr ⟨hi, hn⟩)

private theorem coeff_mul_eq_cancellation_sum {a b d : ℕ} {x y : A}
    (hx : Supported (a + d) x) (hy : Supported (d + b) y)
    {z r t : G} (hz : z = r * t) (hr : norm r = a) (ht : norm t = b)
    (hl : norm z = a + b) :
    (x * y).coeff z = ∑ s ∈ wordShell n d, x.coeff (r * s) * y.coeff (s⁻¹ * t) := by
  classical
  let f (u : G) := x.coeff u * y.coeff (u⁻¹ * z)
  have hf (s : G) : f (r * s) = x.coeff (r * s) * y.coeff (s⁻¹ * t) := by
    simp [f, hz, mul_inv_rev, mul_assoc]
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
  change ∑ u ∈ x.coeff.support, f u = _
  simp only [← hf]
  rw [← sum_filter_nonzero x.coeff.support f,
    ← sum_filter_nonzero (wordShell n d) (fun s ↦ f (r * s))]
  symm
  refine Finset.sum_nbij (fun s ↦ r * s) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro s hs
    have hne := (Finset.mem_filter.mp hs).2
    exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (fun h ↦ hne (by simp [f, h])), hne⟩
  · intro s _ s' _ h
    exact mul_left_cancel h
  · intro u hu
    obtain ⟨hu, hne⟩ := Finset.mem_filter.mp hu
    have hux := hx u hu
    have hvy : norm (u⁻¹ * z) = d + b := by
      by_contra h
      exact hne (by simp [f, coeff_zero_of_not_supported hy h])
    obtain ⟨R, S, T, hu', _, hp, h₁, h₂, h₃⟩ := exists_reduced_product u (u⁻¹ * z)
    rw [mul_inv_cancel_left] at hp h₃
    have hS : norm S = d := by omega
    have hR : norm R = a := by omega
    have hRT : norm (R * T) = norm R + norm T := by rwa [← hp]
    have hrt : norm (r * t) = norm r + norm t := by rwa [← hz, hr, ht]
    have hR' : R = r :=
      (mul_eq_mul_of_additive_norm hRT hrt (hR.trans hr.symm) (hp.symm.trans hz)).1
    rw [hR'] at hu'
    exact ⟨S, Finset.mem_filter.mpr ⟨mem_wordShell.mpr hS, hu' ▸ hne⟩, hu'.symm⟩

private theorem sum_norm_sq_mul_le_sum_of_norms {a b : ℕ} {x : A}
    (hx : Supported (a + b) x) :
    (∑ r ∈ wordShell n a, ∑ s ∈ wordShell n b, ‖x.coeff (r*s)‖ ^ 2) ≤ coeffL2Sq x := by
  classical
  rw [← Finset.sum_product' (wordShell n a) (wordShell n b) (fun r s ↦ ‖x.coeff (r*s)‖ ^ 2)]
  let f (p : G × G) := ‖x.coeff (p.1*p.2)‖ ^ 2
  let P := (wordShell n a ×ˢ wordShell n b)
  change ∑ p ∈ P, f p ≤ _
  rw [← sum_filter_nonzero P f]
  unfold coeffL2Sq
  refine Finset.sum_le_sum_of_injOn (fun p : G × G ↦ p.1*p.2) ?_ ?_ ?_ ?_
  · intro p hp q hq h
    have supp {p : G × G} (hp : p ∈ P.filter (fun p ↦ f p ≠ 0)) :
        p.1 * p.2 ∈ x.coeff.support := by
      apply Finsupp.mem_support_iff.mpr
      intro hpz
      exact (Finset.mem_filter.mp hp).2 (by simp [f, hpz])
    have productLength {p : G × G} (hp : p ∈ P.filter (fun p ↦ f p ≠ 0)) :
        norm p.1 = a ∧ norm p.2 = b := by
      simpa only [P, Finset.mem_product, mem_wordShell] using (Finset.mem_filter.mp hp).1
    obtain ⟨hp₁, hp₂⟩ := productLength hp
    obtain ⟨hq₁, hq₂⟩ := productLength hq
    have hp' : norm (p.1 * p.2) = norm p.1 + norm p.2 := by
      simpa only [hp₁, hp₂] using hx _ (supp hp)
    have hq' : norm (q.1 * q.2) = norm q.1 + norm q.2 := by
      simpa only [hq₁, hq₂] using hx _ (supp hq)
    exact Prod.ext_iff.mpr
      (mul_eq_mul_of_additive_norm hp' hq' (hp₁.trans hq₁.symm) h)
  · intro g hg
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hg
    apply Finsupp.mem_support_iff.mpr
    intro hpz
    exact (Finset.mem_filter.mp hp).2 (by simp [f, hpz])
  · intro p _
    exact le_rfl
  · intro g _ _
    exact sq_nonneg _

private theorem sum_norm_sq_inv_mul_le_sum_of_norms {b d : ℕ} {x : A}
    (hx : Supported (d + b) x) :
    (∑ t ∈ wordShell n b, ∑ s ∈ wordShell n d, ‖x.coeff (s⁻¹*t)‖ ^ 2) ≤ coeffL2Sq x := by
  classical
  calc
    _ = ∑ t ∈ wordShell n b, ∑ s ∈ wordShell n d, ‖x.coeff (s*t)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t _
      refine Finset.sum_nbij (fun (s : G) ↦ s⁻¹) ?_ ?_ ?_ (fun _ _ ↦ rfl)
      · intro s hs
        simpa only [Finset.mem_coe, mem_wordShell, norm_inv_eq] using hs
      · exact fun _ _ _ _ h ↦ inv_injective h
      · intro s hs
        exact ⟨s⁻¹, by simpa only [Finset.mem_coe, mem_wordShell, norm_inv_eq] using hs, inv_inv s⟩
    _ = ∑ s ∈ wordShell n d, ∑ t ∈ wordShell n b, ‖x.coeff (s*t)‖ ^ 2 := Finset.sum_comm
    _ ≤ coeffL2Sq x := sum_norm_sq_mul_le_sum_of_norms hx

/-- The squared L2 shell bound in Lemma 2.1. -/
theorem shell_mul_coeffL2Sq_le {i j : ℕ} {x y : A}
    (hx : Supported i x) (hy : Supported j y) (k : ℕ) :
    coeffL2Sq (shell k (x*y)) ≤ coeffL2Sq x * coeffL2Sq y := by
  classical
  by_cases hk : Admissible i j k
  · obtain ⟨d, hdi, hdj, hd⟩ := (admissible_iff_exists i j k).mp hk
    let a := i - d
    let b := j - d
    have hi : i = a + d := by dsimp [a]; omega
    have hj : j = d + b := by dsimp [b]; omega
    have hk : k = a + b := by dsimp [a, b]; omega
    rw [hi] at hx
    rw [hj] at hy
    rw [hk]
    have hsplit (z : G) : ∃ r t, z ∈ wordShell n (a+b) →
        z = r*t ∧ norm r = a ∧ norm t = b := by
      by_cases hz : z ∈ wordShell n (a+b)
      · obtain ⟨r, t, hr, hnr, hnt⟩ := exists_additive_factor z a b (mem_wordShell.mp hz)
        exact ⟨r, t, fun _ ↦ ⟨hr, hnr, hnt⟩⟩
      · exact ⟨1, 1, fun h ↦ (hz h).elim⟩
    choose R T hRT using hsplit
    let L (r : G) := ∑ s ∈ wordShell n d, ‖x.coeff (r*s)‖ ^ 2
    let M (t : G) := ∑ s ∈ wordShell n d, ‖y.coeff (s⁻¹*t)‖ ^ 2
    have bound (z : G) (hz : z ∈ wordShell n (a+b)) :
        ‖(x*y).coeff z‖ ^ 2 ≤ L (R z) * M (T z) := by
      obtain ⟨heq, hR, hT⟩ := hRT z hz
      rw [coeff_mul_eq_cancellation_sum hx hy heq hR hT (mem_wordShell.mp hz)]
      apply le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq
        (wordShell n d) (fun s ↦ ‖x.coeff (R z*s)‖) (fun s ↦ ‖y.coeff (s⁻¹*T z)‖))
      apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦
        mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      simpa only [norm_mul] using norm_sum_le (wordShell n d)
        (fun s ↦ x.coeff (R z*s) * y.coeff (s⁻¹*T z))
    calc
      _ = ∑ z ∈ wordShell n (a+b), ‖(x*y).coeff z‖ ^ 2 := by
        rw [coeffL2Sq_eq_sum_wordShell (shell_supported _ _)]
        apply Finset.sum_congr rfl
        intro z hz
        rw [shell_coeff, ite_eq_left (mem_wordShell.mp hz)]
      _ ≤ ∑ z ∈ wordShell n (a+b), L (R z) * M (T z) := Finset.sum_le_sum bound
      _ ≤ ∑ p ∈ (wordShell n a ×ˢ wordShell n b), L p.1 * M p.2 := by
        refine Finset.sum_le_sum_of_injOn (fun z ↦ (R z, T z)) ?_ ?_ ?_ ?_
        · intro z hz z' hz' h
          change (R z, T z) = (R z', T z') at h
          rw [(hRT z hz).1, (hRT z' hz').1]
          exact congrArg (fun p : G × G ↦ p.1 * p.2) h
        · intro p hp
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
          exact Finset.mem_product.mpr
            ⟨mem_wordShell.mpr (hRT z hz).2.1, mem_wordShell.mpr (hRT z hz).2.2⟩
        · intro _ _
          exact le_rfl
        · intro p _ _
          apply mul_nonneg <;> exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
      _ = (∑ r ∈ wordShell n a, L r) * (∑ t ∈ wordShell n b, M t) := by
        rw [Finset.sum_product, Finset.sum_mul]
        simp only [Finset.mul_sum]
      _ ≤ coeffL2Sq x * coeffL2Sq y :=
        mul_le_mul (sum_norm_sq_mul_le_sum_of_norms hx) (sum_norm_sq_inv_mul_le_sum_of_norms hy)
          (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
          (coeffL2Sq_nonneg x)
  · rw [shell_mul_eq_zero_of_not_admissible hx hy hk]
    simpa [coeffL2Sq] using mul_nonneg (coeffL2Sq_nonneg x) (coeffL2Sq_nonneg y)

end FreeGroupHypercontractivity.Cancellation

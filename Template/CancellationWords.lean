module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Data.List.OfFn

public section

namespace FreeGroupHypercontractivity.Cancellation

open FreeGroup

variable {α : Type*} [DecidableEq α]

theorem exists_common_prefix (u v : List α) :
    ∃ s r t, u = s ++ r ∧ v = s ++ t ∧ ∀ a ∈ r.head?, ∀ b ∈ t.head?, a ≠ b := by
  induction u generalizing v with
  | nil => exact ⟨[], [], v, rfl, rfl, by simp⟩
  | cons a u ih =>
    cases v with
    | nil => exact ⟨[], a :: u, [], rfl, rfl, by simp⟩
    | cons b v =>
      by_cases h : a = b
      · subst b
        obtain ⟨s, r, t, hu, hv, hrt⟩ := ih v
        exact ⟨a :: s, r, t, congrArg (a :: ·) hu, congrArg (a :: ·) hv, hrt⟩
      · exact ⟨[], a :: u, b :: v, rfl, rfl, by simpa using h⟩

omit [DecidableEq α] in
private theorem invRev_reduced {u : List (α × Bool)} (h : IsReduced u) :
    IsReduced (invRev u) := by
  apply IsReduced.of_forall_not_step
  intro v hv
  exact h.not_step (by simpa only [invRev_invRev] using hv.invRev)

omit [DecidableEq α] in
theorem uncancelled_append {r t : List (α × Bool)}
    (hr : IsReduced r) (ht : IsReduced t)
    (hrt : ∀ a ∈ r.head?, ∀ b ∈ t.head?, a ≠ b) :
    IsReduced (invRev r ++ t) := by
  unfold IsReduced at *
  apply (invRev_reduced hr).append ht
  intro a ha b hb hab
  rw [invRev, List.getLast?_reverse, List.head?_map] at ha
  obtain ⟨c, hc, hca⟩ := Option.mem_map.mp ha
  subst a
  by_contra hsign
  apply hrt c hc b hb
  exact Prod.ext hab (by cases hc₂ : c.2 <;> cases hb₂ : b.2 <;> simp_all)

/-- A word whose multiplication has maximal length is the concatenation of the two reduced words. -/
theorem word_mul_of_additive_norm {u v : FreeGroup α}
    (h : norm (u * v) = norm u + norm v) :
    (u * v).toWord = u.toWord ++ v.toWord := by
  rw [toWord_mul]
  apply List.Sublist.eq_of_length
  · exact Red.sublist reduce.red
  simpa only [norm, toWord_mul, List.length_append] using h

/-- A reduced product determines its two factors uniquely when the length of the first is fixed. -/
theorem mul_eq_mul_of_additive_norm {u v r t : FreeGroup α}
    (huv : norm (u * v) = norm u + norm v)
    (hrt : norm (r * t) = norm r + norm t) (hur : norm u = norm r)
    (hprod : u * v = r * t) : u = r ∧ v = t := by
  have h := congrArg toWord hprod
  rw [word_mul_of_additive_norm huv, word_mul_of_additive_norm hrt] at h
  exact ⟨toWord_injective (List.append_inj_left h hur),
    toWord_injective (List.append_inj_right h hur)⟩

/-- Split two factors into the cancelled block and the two surviving blocks. -/
theorem exists_reduced_product (u v : FreeGroup α) :
    ∃ r s t,
      u = r * s ∧ v = s⁻¹ * t ∧ u * v = r * t ∧
      norm u = norm r + norm s ∧ norm v = norm s + norm t ∧
      norm (u * v) = norm r + norm t := by
  obtain ⟨s, r, t, hu, hv, hrt⟩ := exists_common_prefix u⁻¹.toWord v.toWord
  have hu' : u.toWord = invRev r ++ invRev s := by
    simpa only [toWord_inv, invRev_invRev, invRev_append] using congrArg invRev hu
  have hrs : IsReduced (invRev r ++ invRev s) := hu' ▸ isReduced_toWord
  have hst : IsReduced (s ++ t) := hv ▸ isReduced_toWord
  have hr : IsReduced (invRev r) := hrs.left_of_append
  have hs : IsReduced (invRev s) := hrs.right_of_append
  have ht : IsReduced t := hst.right_of_append
  have hrt' : IsReduced (invRev r ++ t) :=
    uncancelled_append (by simpa only [invRev_invRev] using invRev_reduced hr) ht hrt
  let R := mk (invRev r)
  let S := mk (invRev s)
  let T := mk t
  have hR : R.toWord = invRev r := hr.reduce_eq
  have hS : S.toWord = invRev s := hs.reduce_eq
  have hT : T.toWord = t := ht.reduce_eq
  have hU : u = R * S := by rw [← mk_toWord (x := u), hu']; rfl
  have hV : v = S⁻¹ * T := by
    rw [← mk_toWord (x := v), hv, show S⁻¹ = mk s by simp only [S, inv_mk, invRev_invRev]]
    rfl
  have hUV : u * v = R * T := by rw [hU, hV]; simp [mul_assoc]
  refine ⟨R, S, T, hU, hV, hUV, ?_, ?_, ?_⟩
  · simp only [norm, hu', hR, hS, List.length_append]
  · simp only [norm, hv, hS, hT, List.length_append, invRev_length]
  · simp only [norm, hUV, toWord_mul, hR, hT, hrt'.reduce_eq, List.length_append]

/-- Split a reduced word at any chosen position. -/
theorem exists_additive_factor (z : FreeGroup α) (a b : ℕ) (hz : norm z = a + b) :
    ∃ r t, z = r * t ∧ norm r = a ∧ norm t = b := by
  let r := z.toWord.take a
  let t := z.toWord.drop a
  have hrt : r ++ t = z.toWord := List.take_append_drop _ _
  have hrt' : IsReduced (r ++ t) := hrt ▸ isReduced_toWord
  refine ⟨mk r, mk t, ?_, ?_, ?_⟩
  · rw [mul_mk, hrt, mk_toWord]
  · rw [norm, toWord_mk, IsReduced.reduce_eq (L := r) hrt'.left_of_append]
    change (z.toWord.take a).length = a
    rw [List.length_take]
    exact Nat.min_eq_left (by change z.toWord.length = a + b at hz; omega)
  · rw [norm, toWord_mk, IsReduced.reduce_eq (L := t) hrt'.right_of_append]
    change (z.toWord.drop a).length = b
    rw [List.length_drop]
    change z.toWord.length = a + b at hz
    omega

/-- The two letters adjacent to a maximal common prefix are the only possible
place for further cancellation. This yields the triangle and parity restrictions. -/
theorem additive_lengths (u v : FreeGroup α) :
    ∃ d : ℕ,
      d ≤ norm u ∧ d ≤ norm v ∧ norm u + norm v = norm (u * v) + 2 * d := by
  obtain ⟨r, s, t, _, _, _, hu, hv, huv⟩ := exists_reduced_product u v
  exact ⟨norm s, by omega, by omega, by omega⟩

end FreeGroupHypercontractivity.Cancellation

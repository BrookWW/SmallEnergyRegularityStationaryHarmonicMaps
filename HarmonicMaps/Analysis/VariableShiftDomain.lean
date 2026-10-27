module

public import HarmonicMaps.Analysis.VariableShiftBasic

/-!
# Domains and shells under variable translations

A radius bounded by `hbar` moves each point by at most `hbar`. The support
condition keeps the enlarged ball invariant, and the displacement bound
localizes the image of the transition shell.
-/

@[expose] public section

open Set

namespace HarmonicMaps

/-- The shift is the identity wherever its radius vanishes. -/
theorem variableShift_eq_self_of_zero {n : ℕ} {s : Domain n → ℝ}
    {y x : Domain n} (hx : s x = 0) : variableShift s y x = x := by
  simp only [variableShift, hx, zero_smul, sub_zero]

/-- A nonnegative radius bounded by `hbar` gives the source displacement bound. -/
theorem variableShift_displacement_le {n : ℕ} {s : Domain n → ℝ}
    {y x : Domain n} {hbar : ℝ}
    (hs : 0 ≤ s x ∧ s x ≤ hbar) (hy : y ∈ Metric.ball 0 1) :
    ‖variableShift s y x - x‖ ≤ hbar := by
  have hylt : ‖y‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hy
  have hy' : ‖y‖ ≤ 1 := hylt.le
  have heq : variableShift s y x - x = -(s x • y) := by
    dsimp [variableShift]
    abel
  rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact (mul_le_of_le_one_right hs.1 hy').trans hs.2

/-- The enlarged source ball is mapped into itself. -/
theorem variableShift_mapsTo_outerBall {n : ℕ} {s : Domain n → ℝ}
    {y : Domain n} {theta delta hbar : ℝ}
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar) (hhbar : hbar ≤ delta)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    (hy : y ∈ Metric.ball 0 1) :
    MapsTo (variableShift s y) (Metric.ball 0 (theta + 2 * delta))
      (Metric.ball 0 (theta + 2 * delta)) := by
  intro x hx
  by_cases hin : x ∈ Metric.ball (0 : Domain n) (theta + delta)
  · have hx' : ‖x‖ < theta + delta := by
      simpa only [Metric.mem_ball, dist_zero_right] using hin
    have hd := (variableShift_displacement_le (hvalues x) hy).trans hhbar
    have hn : ‖variableShift s y x‖ ≤ ‖x‖ + ‖variableShift s y x - x‖ := by
      simpa only [add_sub_cancel] using norm_add_le x (variableShift s y x - x)
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  · rw [variableShift_eq_self_of_zero (hoff x hin)]
    exact hx

/-- Outside the enlarged ball the map is the identity. -/
theorem variableShift_eq_self_outside_outerBall {n : ℕ} {s : Domain n → ℝ}
    {y x : Domain n} {theta delta : ℝ} (hdelta : 0 ≤ delta)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    (hx : x ∉ Metric.ball (0 : Domain n) (theta + 2 * delta)) :
    variableShift s y x = x := by
  apply variableShift_eq_self_of_zero
  apply hoff x
  intro hin
  have hnx : theta + 2 * delta ≤ ‖x‖ := by
    simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hx
  have hnin : ‖x‖ < theta + delta := by
    simpa only [Metric.mem_ball, dist_zero_right] using hin
  linarith

/-- Surjectivity, together with the source displacement and support bounds,
upgrades preservation to equality of the enlarged ball's image. -/
theorem variableShift_image_outerBall_of_surjective {n : ℕ} {s : Domain n → ℝ}
    {y : Domain n} {theta delta hbar : ℝ} (hdelta : 0 ≤ delta)
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar) (hhbar : hbar ≤ delta)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    (hy : y ∈ Metric.ball 0 1) (hsurj : Function.Surjective (variableShift s y)) :
    variableShift s y '' Metric.ball 0 (theta + 2 * delta) =
      Metric.ball 0 (theta + 2 * delta) := by
  apply Subset.antisymm
  · exact (variableShift_mapsTo_outerBall hvalues hhbar hoff hy).image_subset
  · intro z hz
    obtain ⟨x, hx⟩ := hsurj z
    refine ⟨x, ?_, hx⟩
    by_contra hnot
    have hid := variableShift_eq_self_outside_outerBall (y := y) hdelta hoff hnot
    rw [hid] at hx
    exact hnot (hx ▸ hz)

/-- The transition shell maps into its enlarged shell. -/
theorem variableShift_mapsTo_shell {n : ℕ} {s : Domain n → ℝ}
    {y : Domain n} {theta delta hbar : ℝ}
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar) (hhbar : hbar ≤ delta)
    (hy : y ∈ Metric.ball 0 1) :
    MapsTo (variableShift s y)
      (Metric.ball 0 (theta + delta) \ Metric.closedBall 0 theta)
      (Metric.ball 0 (theta + 2 * delta) \ Metric.closedBall 0 (theta - delta)) := by
  intro x hx
  have hupper : ‖x‖ < theta + delta := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx.1
  have hlower : theta < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx.2
  have hd := (variableShift_displacement_le (hvalues x) hy).trans hhbar
  have hu : ‖variableShift s y x‖ ≤ ‖x‖ + ‖variableShift s y x - x‖ := by
    simpa only [add_sub_cancel] using norm_add_le x (variableShift s y x - x)
  have hl : ‖x‖ ≤ ‖variableShift s y x‖ + ‖variableShift s y x - x‖ := by
    simpa only [add_sub_cancel, norm_sub_rev] using
      norm_add_le (variableShift s y x) (x - variableShift s y x)
  constructor
  · simp only [Metric.mem_ball, dist_zero_right]
    linarith
  · simp only [Metric.mem_closedBall, dist_zero_right, not_le]
    linarith

end HarmonicMaps

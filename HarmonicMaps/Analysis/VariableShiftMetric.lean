module

public import HarmonicMaps.Analysis.VariableShiftBasic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Metric estimates for variable translations

A global derivative bound on the smooth radius gives the two-sided distance
estimate for the variable translation. The contraction equation supplies a
unique preimage at every point and an inverse with the stated metric bound.
-/

@[expose] public section

open scoped ContDiff

namespace HarmonicMaps

/-- A bounded derivative of the smooth radius gives its global Lipschitz bound. -/
theorem variableShift_radius_lipschitz {n : ℕ} {s : Domain n → ℝ} {L : ℝ}
    (hs : ContDiff ℝ ∞ s) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL0 : 0 ≤ L) :
    LipschitzWith ⟨L, hL0⟩ s := by
  apply lipschitzWith_of_nnnorm_fderiv_le (hs.differentiable (by simp))
  intro x
  exact_mod_cast hDs x

/-- The source derivative bound controls the scalar radius difference. -/
theorem variableShift_radius_sub_le {n : ℕ} {s : Domain n → ℝ} {L : ℝ}
    (hs : ContDiff ℝ ∞ s) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL0 : 0 ≤ L)
    (x z : Domain n) : ‖s x - s z‖ ≤ L * ‖x - z‖ := by
  have hb := (variableShift_radius_lipschitz hs hDs hL0).dist_le_mul x z
  change dist (s x) (s z) ≤ L * dist x z at hb
  simpa only [dist_eq_norm] using hb

/-- The variable displacement difference has norm at most `L ‖x-z‖`. -/
theorem variableShift_displacement_sub_le {n : ℕ} {s : Domain n → ℝ} {L : ℝ}
    (hs : ContDiff ℝ ∞ s) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL0 : 0 ≤ L)
    {y : Domain n} (hy : y ∈ Metric.ball 0 1) (x z : Domain n) :
    ‖(s x - s z) • y‖ ≤ L * ‖x - z‖ := by
  have hy1 : ‖y‖ ≤ 1 := (mem_ball_zero_iff.mp hy).le
  calc
    ‖(s x - s z) • y‖ = ‖s x - s z‖ * ‖y‖ := norm_smul _ _
    _ ≤ ‖s x - s z‖ * 1 := mul_le_mul_of_nonneg_left hy1 (norm_nonneg _)
    _ = ‖s x - s z‖ := mul_one _
    _ ≤ L * ‖x - z‖ := variableShift_radius_sub_le hs hDs hL0 x z

/-- The precise two-sided estimate for the variable translation. -/
theorem variableShift_norm_sub_bounds {n : ℕ} {s : Domain n → ℝ} {L : ℝ}
    (hs : ContDiff ℝ ∞ s) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL0 : 0 ≤ L)
    {y : Domain n} (hy : y ∈ Metric.ball 0 1) (x z : Domain n) :
    (1 - L) * ‖x - z‖ ≤ ‖variableShift s y x - variableShift s y z‖ ∧
      ‖variableShift s y x - variableShift s y z‖ ≤ (1 + L) * ‖x - z‖ := by
  have hdiff : variableShift s y x - variableShift s y z =
      (x - z) - (s x - s z) • y := by
    dsimp only [variableShift]
    rw [sub_smul]
    abel
  have hb := variableShift_displacement_sub_le hs hDs hL0 hy x z
  rw [hdiff]
  constructor
  · have hn := norm_sub_norm_le (x - z) ((s x - s z) • y)
    nlinarith only [hn, hb]
  · have hn := norm_sub_le (x - z) ((s x - s z) • y)
    nlinarith only [hn, hb]

/-- The fixed-point equation has contraction constant `L`. -/
theorem variableShift_contracting {n : ℕ} {s : Domain n → ℝ} {L : ℝ}
    (hs : ContDiff ℝ ∞ s) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 4) {y : Domain n} (hy : y ∈ Metric.ball 0 1)
    (z : Domain n) : ContractingWith ⟨L, hL0⟩ (fun x => z + s x • y) := by
  constructor
  · change L < 1
    linarith only [hL]
  · apply LipschitzWith.of_dist_le_mul
    intro x w
    have hdiff : (z + s x • y) - (z + s w • y) = (s x - s w) • y := by
      rw [sub_smul]
      abel
    change dist (z + s x • y) (z + s w • y) ≤ L * dist x w
    simpa only [dist_eq_norm, hdiff] using
      variableShift_displacement_sub_le hs hDs hL0 hy x w

/-- Each target point has a unique solution of the contraction equation. -/
theorem variableShift_existsUnique_fixedEquation {n : ℕ} {s : Domain n → ℝ} {L : ℝ}
    (hs : ContDiff ℝ ∞ s) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 4) {y : Domain n} (hy : y ∈ Metric.ball 0 1)
    (z : Domain n) : ∃! x, x = z + s x • y := by
  have hc := variableShift_contracting hs hDs hL0 hL hy z
  refine ⟨hc.fixedPoint, hc.fixedPoint_isFixedPt.symm, ?_⟩
  intro x hx
  exact hc.fixedPoint_unique' hx.symm hc.fixedPoint_isFixedPt

/-- The translation and fixed-point equations are equivalent on the whole space. -/
theorem variableShift_eq_iff_fixedEquation {n : ℕ} (s : Domain n → ℝ)
    (y x z : Domain n) : variableShift s y x = z ↔ x = z + s x • y := by
  exact sub_eq_iff_eq_add

/-- Every target point has a unique preimage under the variable translation. -/
theorem variableShift_existsUnique_preimage {n : ℕ} {s : Domain n → ℝ} {L : ℝ}
    (hs : ContDiff ℝ ∞ s) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 4) {y : Domain n} (hy : y ∈ Metric.ball 0 1)
    (z : Domain n) : ∃! x, variableShift s y x = z := by
  simpa only [variableShift_eq_iff_fixedEquation] using
    variableShift_existsUnique_fixedEquation hs hDs hL0 hL hy z

/-- The variable translation is a global bijection. -/
theorem variableShift_bijective {n : ℕ} {s : Domain n → ℝ} {L : ℝ}
    (hs : ContDiff ℝ ∞ s) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 4) {y : Domain n} (hy : y ∈ Metric.ball 0 1) :
    Function.Bijective (variableShift s y) := by
  constructor
  · intro x z hxz
    obtain ⟨w, hw, hu⟩ := variableShift_existsUnique_preimage hs hDs hL0 hL hy
      (variableShift s y z)
    exact (hu x hxz).trans (hu z rfl).symm
  · intro z
    exact (variableShift_existsUnique_preimage hs hDs hL0 hL hy z).exists

/-- A globally characterized inverse exists and has constant `1/(1-L)`.
The selected witness is local to this theorem and comes from unique preimages. -/
theorem variableShift_exists_inverse {n : ℕ} {s : Domain n → ℝ} {L : ℝ}
    (hs : ContDiff ℝ ∞ s) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 4) {y : Domain n} (hy : y ∈ Metric.ball 0 1) :
    ∃ g : Domain n → Domain n,
      (∀ z, variableShift s y (g z) = z) ∧
      (∀ x, g (variableShift s y x) = x) ∧
      (∀ z, g z = z + s (g z) • y) ∧
      (∀ z x, variableShift s y x = z ↔ x = g z) ∧
      (∀ z w, ‖g z - g w‖ ≤ (1 / (1 - L)) * ‖z - w‖) := by
  classical
  have hu : ∀ z, ∃! x, variableShift s y x = z :=
    variableShift_existsUnique_preimage hs hDs hL0 hL hy
  let g : Domain n → Domain n := fun z => Classical.choose (hu z)
  have hg : ∀ z, variableShift s y (g z) = z := fun z =>
    (Classical.choose_spec (hu z)).1
  have huniq : ∀ z x, variableShift s y x = z ↔ x = g z := by
    intro z x
    constructor
    · exact (Classical.choose_spec (hu z)).2 x
    · intro hx
      rw [hx]
      exact hg z
  refine ⟨g, hg, ?_, ?_, huniq, ?_⟩
  · intro x
    exact ((huniq (variableShift s y x) x).mp rfl).symm
  · intro z
    exact (variableShift_eq_iff_fixedEquation s y (g z) z).mp (hg z)
  · intro z w
    have hpos : 0 < 1 - L := by linarith only [hL]
    have hbound := (variableShift_norm_sub_bounds hs hDs hL0 hy (g z) (g w)).1
    rw [hg z, hg w] at hbound
    rw [one_div, ← div_eq_inv_mul]
    exact (le_div_iff₀ hpos).2 (by simpa only [mul_comm] using hbound)

end HarmonicMaps

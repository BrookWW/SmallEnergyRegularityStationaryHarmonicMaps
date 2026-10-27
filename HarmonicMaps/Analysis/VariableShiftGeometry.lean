module

public import HarmonicMaps.Analysis.VariableShiftCalculus
public import HarmonicMaps.Analysis.VariableShiftMetric
public import HarmonicMaps.Analysis.VariableShiftDomain

/-!
# Geometry of the source variable translation

The source cutoff conditions give the differential, positive Jacobian,
two-sided distance estimates, unique contraction inverse, and ball and shell
mapping properties. The inverse is characterized existentially; no selected
inverse definition or smooth-inverse conclusion is introduced.
-/

@[expose] public section

open Set
open scoped ContDiff

namespace HarmonicMaps

/-- The contraction inverse is unique as a function, with its full equations
and the quantitative inverse distance bound. -/
theorem variableShift_existsUnique_inverse {n : ℕ} {s : Domain n → ℝ} {L : ℝ}
    (hs : ContDiff ℝ ∞ s) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 4) {y : Domain n} (hy : y ∈ Metric.ball 0 1) :
    ∃! g : Domain n → Domain n,
      (∀ z, variableShift s y (g z) = z) ∧
      (∀ x, g (variableShift s y x) = x) ∧
      (∀ z, g z = z + s (g z) • y) ∧
      (∀ z x, variableShift s y x = z ↔ x = g z) ∧
      (∀ z w, ‖g z - g w‖ ≤ (1 / (1 - L)) * ‖z - w‖) := by
  obtain ⟨g, hg⟩ := variableShift_exists_inverse hs hDs hL0 hL hy
  refine ⟨g, hg, ?_⟩
  intro k hk
  funext z
  exact (hg.2.2.2.1 z (k z)).mp (hk.1 z)

/-- The bounded geometric part of the variable-smoothing argument.
`L` is a uniform derivative norm bound. Radiality, both plateaux, and all
source radius conditions are retained. Smoothness of the global inverse is
a separate inverse-function obligation. -/
theorem variableShift_geometry {n : ℕ} {s : Domain n → ℝ}
    {theta delta hbar L : ℝ}
    (hdelta : 0 < delta) (_htheta : delta < theta)
    (_hhalf : theta + 2 * delta < 1 / 2)
    (hs : ContDiff ℝ ∞ s)
    (_hradial : ∀ x z : Domain n, ‖x‖ = ‖z‖ → s x = s z)
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar)
    (hplateau : ∀ x ∈ Metric.ball (0 : Domain n) theta, s x = hbar)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    (hhbar : hbar ≤ delta) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L)
    (hL0 : 0 ≤ L) (hL : L ≤ 1 / 4) (y : Domain n) (hy : y ∈ Metric.ball 0 1) :
    ContDiff ℝ ∞ (variableShift s y) ∧
    (∀ x, HasFDerivAt (variableShift s y)
      (ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y) x) ∧
    (∀ x, Matrix.det (fun i j : Fin n =>
      (fderiv ℝ (variableShift s y) x (EuclideanSpace.single j 1)) i) =
        1 - fderiv ℝ s x y) ∧
    (∀ x, 1 - L ≤ Matrix.det (fun i j : Fin n =>
      (fderiv ℝ (variableShift s y) x (EuclideanSpace.single j 1)) i)) ∧
    0 < 1 - L ∧
    (∀ x, ‖fderiv ℝ (variableShift s y) x‖ ≤ 1 + L) ∧
    (∀ x z, (1 - L) * ‖x - z‖ ≤ ‖variableShift s y x - variableShift s y z‖ ∧
      ‖variableShift s y x - variableShift s y z‖ ≤ (1 + L) * ‖x - z‖) ∧
    (∀ z, ContractingWith ⟨L, hL0⟩ (fun x => z + s x • y)) ∧
    (∀ z, ∃! x, variableShift s y x = z) ∧
    (∃! g : Domain n → Domain n,
      (∀ z, variableShift s y (g z) = z) ∧
      (∀ x, g (variableShift s y x) = x) ∧
      (∀ z, g z = z + s (g z) • y) ∧
      (∀ z x, variableShift s y x = z ↔ x = g z) ∧
      (∀ z w, ‖g z - g w‖ ≤ (1 / (1 - L)) * ‖z - w‖)) ∧
    (∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), variableShift s y x = x) ∧
    (variableShift s y '' Metric.ball 0 (theta + 2 * delta) =
      Metric.ball 0 (theta + 2 * delta)) ∧
    (∀ x, ‖variableShift s y x - x‖ ≤ hbar) ∧
    MapsTo (variableShift s y)
      (Metric.ball 0 (theta + delta) \ Metric.closedBall 0 theta)
      (Metric.ball 0 (theta + 2 * delta) \ Metric.closedBall 0 (theta - delta)) ∧
    (∀ x ∈ Metric.ball (0 : Domain n) theta, variableShift s y x = x - hbar • y) := by
  have hdiff : ∀ x, DifferentiableAt ℝ s x := hs.differentiable (by norm_num)
  refine ⟨contDiff_variableShift hs y,
    (fun x => hasFDerivAt_variableShift (hdiff x) y),
    (fun x => det_fderiv_variableShift (hdiff x) y),
    (fun x => variableShift_det_lower_bound (hdiff x) hDs y hy),
    (by linarith only [hL]),
    (fun x => norm_fderiv_variableShift_le (hdiff x) hDs y hy),
    variableShift_norm_sub_bounds hs hDs hL0 hy,
    variableShift_contracting hs hDs hL0 hL hy,
    variableShift_existsUnique_preimage hs hDs hL0 hL hy,
    variableShift_existsUnique_inverse hs hDs hL0 hL hy,
    (fun x hx => variableShift_eq_self_of_zero (hoff x hx)),
    variableShift_image_outerBall_of_surjective hdelta.le hvalues hhbar hoff hy
      (variableShift_bijective hs hDs hL0 hL hy).2,
    (fun x => variableShift_displacement_le (hvalues x) hy),
    variableShift_mapsTo_shell hvalues hhbar hy, ?_⟩
  intro x hx
  simp only [variableShift, hplateau x hx]

end HarmonicMaps

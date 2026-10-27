module

public import HarmonicMaps.Analysis.VariableShiftGeometry
public import HarmonicMaps.Analysis.VariableShiftInverseSmooth

/-!
# Complete variable-translation diffeomorphism

The source variable translation has a unique smooth global inverse. The
derivative, Jacobian, distance bounds and domain mappings use the existing
geometry, and inverse smoothness follows from the local inverse theorem.
No inverse function is introduced as a public selected definition.
-/

public section

open Set
open scoped ContDiff

namespace HarmonicMaps

/-- The existing uniquely characterized inverse is smooth, with both inverse
equations and the source distance bound unchanged. -/
theorem variableShift_existsUnique_smooth_inverse {n : ℕ} {s : Domain n → ℝ} {L : ℝ}
    (hs : ContDiff ℝ ∞ s) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 4) {y : Domain n} (hy : y ∈ Metric.ball 0 1) :
    ∃! g : Domain n → Domain n,
      (∀ z, variableShift s y (g z) = z) ∧
      (∀ x, g (variableShift s y x) = x) ∧
      (∀ z, g z = z + s (g z) • y) ∧
      (∀ z x, variableShift s y x = z ↔ x = g z) ∧
      (∀ z w, ‖g z - g w‖ ≤ (1 / (1 - L)) * ‖z - w‖) ∧
      ContDiff ℝ ∞ g := by
  obtain ⟨g, hg, huniq⟩ := variableShift_existsUnique_inverse hs hDs hL0 hL hy
  refine ⟨g, ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2,
    variableShift_contDiff_inverse hs hDs hL0 hL hy g hg.1⟩, ?_⟩
  intro k hk
  exact huniq k ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1⟩

/-- Complete source geometry for `F_y(x)=x-s(x)y`: both directions are
smooth, the unique inverse retains its equations and distance constant,
and the source balls and shells have their stated images. -/
theorem variableShift_diffeomorphism {n : ℕ} {s : Domain n → ℝ}
    {theta delta hbar L : ℝ}
    (hdelta : 0 < delta) (htheta : delta < theta)
    (hhalf : theta + 2 * delta < 1 / 2)
    (hs : ContDiff ℝ ∞ s)
    (hradial : ∀ x z : Domain n, ‖x‖ = ‖z‖ → s x = s z)
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
      (∀ z w, ‖g z - g w‖ ≤ (1 / (1 - L)) * ‖z - w‖) ∧
      ContDiff ℝ ∞ g) ∧
    (∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), variableShift s y x = x) ∧
    (variableShift s y '' Metric.ball 0 (theta + 2 * delta) =
      Metric.ball 0 (theta + 2 * delta)) ∧
    (∀ x, ‖variableShift s y x - x‖ ≤ hbar) ∧
    MapsTo (variableShift s y)
      (Metric.ball 0 (theta + delta) \ Metric.closedBall 0 theta)
      (Metric.ball 0 (theta + 2 * delta) \ Metric.closedBall 0 (theta - delta)) ∧
    (∀ x ∈ Metric.ball (0 : Domain n) theta, variableShift s y x = x - hbar • y) := by
  obtain ⟨hforward, hdifferential, hjacobian, hjacobianBound, hpositive, hnorm,
    hdistance, hcontraction, hpreimages, _, hidentity, houter, hdisplacement,
    hshell, hinner⟩ := variableShift_geometry hdelta htheta hhalf hs hradial
      hvalues hplateau hoff hhbar hDs hL0 hL y hy
  exact ⟨hforward, hdifferential, hjacobian, hjacobianBound, hpositive, hnorm,
    hdistance, hcontraction, hpreimages,
    variableShift_existsUnique_smooth_inverse hs hDs hL0 hL hy,
    hidentity, houter, hdisplacement, hshell, hinner⟩

end HarmonicMaps

module

public import HarmonicMaps.Analysis.QuantitativeRadialCutoff
public import HarmonicMaps.Analysis.VariableShiftDiffeomorphism

/-!
# Source-scale geometry of the constructed quantitative cutoff

At the source scale `hbar = delta^2`, the derivative bound is exactly
`2 * delta`. The same supplied density defines the literal cutoff used in
the complete variable-translation diffeomorphism theorem.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace HarmonicMaps

/-- The literal constructed cutoff satisfies and consumes all source geometry. -/
theorem quantitativeRadialCutoff_sourceScale (b : ℝ → ℝ)
    (hb : ContDiff ℝ ∞ b) (hcompact : HasCompactSupport b)
    (hsupport : tsupport b ⊆ Ioo 0 1)
    (hvalues : ∀ t, 0 ≤ b t ∧ b t ≤ 2) (hmass : (∫ t, b t) = 1) :
      ∀ (n : ℕ) (theta delta : ℝ) (hdelta : 0 < delta),
        delta < theta → theta + 2 * delta < 1 / 2 →
        2 * delta ≤ 1 / 4 →
        let hbar := delta ^ 2
        let beta : ℝ → ℝ := fun t => 1 - ∫ y in Iic t, b y
        let s : Domain n → ℝ := fun x => hbar * beta ((‖x‖ - theta) / delta)
        let L := 2 * hbar / delta
        hbar ≤ delta ∧ L = 2 * delta ∧ L ≤ 1 / 4 ∧
        ContDiff ℝ ∞ s ∧ HasCompactSupport s ∧
        tsupport s ⊆ Metric.closedBall 0 (theta + delta) ∧
        (∀ x z : Domain n, ‖x‖ = ‖z‖ → s x = s z) ∧
        (∀ x, 0 ≤ s x ∧ s x ≤ hbar) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) theta, s x = hbar) ∧
        (∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0) ∧
        (∀ x, ‖fderiv ℝ s x‖ ≤ L) ∧
        ∀ y : Domain n, y ∈ Metric.ball 0 1 →
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
          (∀ z, ContractingWith ⟨L, div_nonneg
            (mul_nonneg (by norm_num) (sq_nonneg delta)) hdelta.le⟩ (fun x => z + s x • y)) ∧
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
  intro n theta delta hdelta htheta hhalf hsmall
  dsimp only
  have hdeltaOne : delta ≤ 1 := by linarith only [hsmall]
  have hscale : delta ^ 2 ≤ delta := by
    nlinarith only [hdelta.le, hdeltaOne]
  have hL : 2 * delta ^ 2 / delta = 2 * delta := by
    field_simp
  have hL0 : 0 ≤ 2 * delta ^ 2 / delta := by
    rw [hL]
    exact mul_nonneg (by norm_num) hdelta.le
  have hLquarter : 2 * delta ^ 2 / delta ≤ 1 / 4 := by
    rw [hL]
    exact hsmall
  obtain ⟨hs, hcompactS, hsupportS, hradial, hvaluesS, hplateau, hoff,
    _, _, hDs⟩ := quantitativeRadialCutoff_properties b hb hcompact hsupport hvalues hmass
      n theta delta (delta ^ 2) hdelta htheta hhalf (sq_nonneg delta) hscale
  refine ⟨hscale, hL, hLquarter, hs, hcompactS, hsupportS, hradial, hvaluesS,
    hplateau, hoff, hDs, ?_⟩
  intro y hy
  exact variableShift_diffeomorphism hdelta htheta hhalf hs hradial hvaluesS
    hplateau hoff hscale hDs hL0 hLquarter y hy

end HarmonicMaps

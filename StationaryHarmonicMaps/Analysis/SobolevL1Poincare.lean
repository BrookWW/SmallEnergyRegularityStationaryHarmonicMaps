module

public import StationaryHarmonicMaps.Analysis.SmoothL1Poincare
public import StationaryHarmonicMaps.Analysis.L1SobolevLimit
public import HarmonicMaps.Analysis.SobolevSmoothDensity

/-!
# The L1 Poincare inequality for the displayed weak gradient

Whole-ball smooth Sobolev density produces the approximating maps and their
actual derivative columns. L2 approximation gives convergence of the centered
L1 integrals and of each column norm integral, closing the smooth inequality.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology

namespace StationaryHarmonicMaps

/-- Finite Sobolev data on the actual ball satisfy the L1 Poincare inequality. -/
theorem sobolev_poincare_l1_ball {n q : ℕ} (a : Domain n) {r : ℝ} (hr : 0 < r)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a r) u Du) :
    (∫ x in Metric.ball a r, ‖u x - (⨍ y in Metric.ball a r, u y)‖) ≤
      (2 : ℝ) ^ (n + 1) * r * ∫ x in Metric.ball a r,
        ∑ i : Fin n, ‖Du x i‖ := by
  classical
  let μ : Measure (Domain n) := volume.restrict (Metric.ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (ballDomain a r).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  obtain ⟨m, hm, hmW, hconv, hDconv⟩ := hu.smoothDensity_memW12_ball hr
  have hleft : Tendsto (fun k => ∫ x, ‖m k x - (⨍ y, m k y ∂μ)‖ ∂μ)
      atTop (𝓝 (∫ x, ‖u x - (⨍ y, u y ∂μ)‖ ∂μ)) :=
    tendsto_integral_centered_norm_of_L2 (fun k => (hmW k).2.1) hu.2.1 hconv
  have hcolumns (i : Fin n) :
      Tendsto (fun k => ∫ x, ‖fderiv ℝ (m k) x (EuclideanSpace.single i 1)‖ ∂μ)
        atTop (𝓝 (∫ x, ‖Du x i‖ ∂μ)) :=
    tendsto_integral_norm_of_L2 (fun k => (hmW k).2.2 i) (hu.2.2 i) (hDconv i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hcolumns i)
  have hsum_m (k : ℕ) :
      (∫ x, ∑ i : Fin n, ‖fderiv ℝ (m k) x (EuclideanSpace.single i 1)‖ ∂μ) =
        ∑ i : Fin n, ∫ x, ‖fderiv ℝ (m k) x (EuclideanSpace.single i 1)‖ ∂μ :=
    integral_finsetSum Finset.univ
      (fun i _ => (((hmW k).2.2 i).integrable (by norm_num)).norm)
  have hsum_u : (∫ x, ∑ i : Fin n, ‖Du x i‖ ∂μ) =
      ∑ i : Fin n, ∫ x, ‖Du x i‖ ∂μ :=
    integral_finsetSum Finset.univ
      (fun i _ => ((hu.2.2 i).integrable (by norm_num)).norm)
  have hright : Tendsto
      (fun k => ∫ x, ∑ i : Fin n, ‖fderiv ℝ (m k) x (EuclideanSpace.single i 1)‖ ∂μ)
      atTop (𝓝 (∫ x, ∑ i : Fin n, ‖Du x i‖ ∂μ)) := by
    simpa only [hsum_m, hsum_u] using hsum
  exact le_of_tendsto_of_tendsto hleft
    (hright.const_mul ((2 : ℝ) ^ (n + 1) * r))
    (Eventually.of_forall fun k => smooth_poincare_l1_ball a hr
      ((hm k).contDiffOn.of_le (by simp))
      ((hmW k).2.1.integrable (by norm_num))
      (fun i => ((hmW k).2.2 i).integrable (by norm_num)))

end StationaryHarmonicMaps

end

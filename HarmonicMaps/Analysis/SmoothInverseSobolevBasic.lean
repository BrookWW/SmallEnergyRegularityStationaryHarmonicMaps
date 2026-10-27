module

public import HarmonicMaps.Analysis.SmoothInverseLp
public import HarmonicMaps.Analysis.SobolevCutoffBoundary

/-!
# Analytic ingredients for smooth inverse Sobolev composition

L2 convergence is preserved by the actual inverse-coordinate pullback.
The coordinate coefficients of a smooth inverse are bounded on every ball,
and the classical coordinate chain rule has its literal finite-sum form.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace HarmonicMaps

/-- The actual inverse pullback preserves convergence of L2 errors to zero. -/
theorem tendsto_eLpNorm_comp_smooth_inverse_ball {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {a : Domain n} {R : ℝ} {v : ℕ → Domain n → E}
    (hv : ∀ k, MemLp (v k) 2 (volume.restrict (Metric.ball a R)))
    (hlim : Tendsto (fun k => eLpNorm (v k) 2 (volume.restrict (Metric.ball a R)))
      atTop (𝓝 0))
    {f g : Domain n → Domain n} (hf : ContDiff ℝ ∞ f) (hg : Continuous g)
    (hfg : Function.RightInverse g f) (hgf : Function.LeftInverse g f)
    (hfball : MapsTo f (Metric.ball a R) (Metric.ball a R))
    (hgball : MapsTo g (Metric.ball a R) (Metric.ball a R)) :
    Tendsto (fun k => eLpNorm (v k ∘ g) 2 (volume.restrict (Metric.ball a R)))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := smooth_inverse_map_restrict_le hf hg hfg hgf hfball hgball
  have hfinite : C ^ (1 / (2 : ℝ≥0∞)).toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hC
  have hb : Tendsto (fun k => C ^ (1 / (2 : ℝ≥0∞)).toReal *
      eLpNorm (v k) 2 (volume.restrict (Metric.ball a R))) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr hfinite)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => zero_le)
  intro k
  dsimp only
  rw [← eLpNorm_map_measure (((hv k).of_measure_le_smul hC hbound).aestronglyMeasurable)
    hg.measurable.aemeasurable]
  exact eLpNorm_le_of_measure_le_smul hbound

/-- Each coordinate coefficient of a smooth map's actual derivative is
essentially bounded on a ball by compactness of its closed ball. -/
theorem smooth_inverse_coefficient_memLp_top {n : ℕ} {g : Domain n → Domain n}
    (hg : ContDiff ℝ ∞ g) (a : Domain n) (R : ℝ) (i j : Fin n) :
    MemLp (fun x => (fderiv ℝ g x (EuclideanSpace.single i 1)) j)
      ∞ (volume.restrict (Metric.ball a R)) := by
  have hcont : Continuous (fun x => (fderiv ℝ g x (EuclideanSpace.single i 1)) j) :=
    (EuclideanSpace.proj j).continuous.comp
      ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)
  obtain ⟨C, hC⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn hcont.continuousOn
  apply memLp_top_of_bound hcont.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact hC x (Metric.ball_subset_closedBall hx)

/-- The classical coordinate chain rule expressed in actual derivative columns. -/
theorem coordinateDerivative_comp_smooth {n q : ℕ}
    {m : Domain n → Ambient q} {g : Domain n → Domain n}
    (hm : ContDiff ℝ ∞ m) (hg : ContDiff ℝ ∞ g) (i : Fin n) (x : Domain n) :
    coordinateDerivative (m ∘ g) (hm.comp hg) i x =
      ∑ j : Fin n, (fderiv ℝ g x (EuclideanSpace.single i 1)) j •
        coordinateDerivative m hm j (g x) := by
  let w := fderiv ℝ g x (EuclideanSpace.single i 1)
  have hrepr : (∑ j : Fin n, w j • EuclideanSpace.single j 1) = w := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w
  simp only [coordinateDerivative, fderiv_comp x (hm.differentiable (by simp) (g x))
    (hg.differentiable (by simp) x), ContinuousLinearMap.comp_apply]
  change fderiv ℝ m (g x) w = _
  conv_lhs => rw [← hrepr]
  simp only [map_sum, map_smul]
  rfl

end HarmonicMaps

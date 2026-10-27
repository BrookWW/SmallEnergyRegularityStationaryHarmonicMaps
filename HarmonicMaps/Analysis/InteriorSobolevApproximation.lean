module

public import HarmonicMaps.Analysis.MollificationL2Convergence

/-!
# Sobolev approximation on smaller concentric balls

The explicit smooth domain convolution approximates both the map and its
displayed weak-gradient columns on every smaller ball. The strict radius
margin makes the derivative formula valid at all sufficiently small scales.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace HarmonicMaps

noncomputable section

/-- Finite-domain L2 data give global L2 for the smooth domain convolution. -/
theorem euclideanMollification_memLp {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hInt : IntegrableOn u Ω.val)
    (hL2 : MemLp u 2 (volume.restrict Ω.val)) (h : PositiveRadius) :
    MemLp (euclideanMollification Ω u hInt h) 2 volume := by
  have hz := (memLp_indicator_iff_restrict Ω.property.measurableSet).mpr hL2
  have ha := fixedKernelAverage_memLp (zeroExtensionOn_integrable Ω u hInt) hz h
  convert ha using 1
  funext x
  exact (fixedKernelAverage_eq_scaledConvolution (zeroExtensionOn Ω u) h x).symm

/-- Domain convolution converges to the original map on each contained measurable set. -/
theorem tendsto_eLpNorm_euclideanMollification_sub {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hInt : IntegrableOn u Ω.val)
    (hL2 : MemLp u 2 (volume.restrict Ω.val)) {s : Set (Domain n)}
    (hs : MeasurableSet s) (hsΩ : s ⊆ Ω.val) :
    Tendsto (fun h : PositiveRadius => eLpNorm
      (fun x => euclideanMollification Ω u hInt h x - u x) 2 (volume.restrict s))
      (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) (𝓝 0) := by
  have hz : MemLp (zeroExtensionOn Ω u) 2 volume :=
    (memLp_indicator_iff_restrict Ω.property.measurableSet).mpr hL2
  have hglobal := tendsto_eLpNorm_fixedKernelAverage_sub
    (zeroExtensionOn_integrable Ω u hInt) hz
  have ht : Tendsto (fun h : PositiveRadius => eLpNorm
      (fun x => euclideanMollification Ω u hInt h x - zeroExtensionOn Ω u x) 2 volume)
      (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) (𝓝 0) := by
    convert hglobal using 1
    funext h
    apply congrArg (fun f : Domain n → Ambient q => eLpNorm f 2 volume)
    funext x
    rw [fixedKernelAverage_eq_scaledConvolution]
    rfl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) (fun h => ?_)
  have heq : (fun x => euclideanMollification Ω u hInt h x - u x) =ᵐ[volume.restrict s]
      (fun x => euclideanMollification Ω u hInt h x - zeroExtensionOn Ω u x) := by
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [zeroExtensionOn, indicator_of_mem (hsΩ hx)]
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

theorem MemW12.euclideanMollification_memLp_inner_ball {n q : ℕ}
    {a : Domain n} {R r : ℝ} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12 (ballDomain a R) u Du)
    (h : PositiveRadius) :
    MemLp (euclideanMollification (ballDomain a R) u hu.integrable_ball h) 2
      (volume.restrict (Metric.ball a r)) :=
  (euclideanMollification_memLp (ballDomain a R) u hu.integrable_ball hu.2.1 h).mono_measure
    Measure.restrict_le_self

/-- With an interior support margin, every actual classical derivative column is L2. -/
theorem MemW12.euclideanMollification_column_memLp_inner_ball {n q : ℕ}
    {a : Domain n} {R r : ℝ} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12 (ballDomain a R) u Du)
    (h : PositiveRadius) (hh : h.val / 2 ≤ R - r) (i : Fin n) :
    MemLp (coordinateDerivative
      (euclideanMollification (ballDomain a R) u hu.integrable_ball h)
      (euclideanMollification_contDiff (ballDomain a R) u hu.integrable_ball h) i) 2
      (volume.restrict (Metric.ball a r)) := by
  have hcol := euclideanMollification_memLp (ballDomain a R) (fun x => Du x i)
    (hu.column_integrable_ball i) (hu.2.2 i) h
  have heq : coordinateDerivative
      (euclideanMollification (ballDomain a R) u hu.integrable_ball h)
      (euclideanMollification_contDiff (ballDomain a R) u hu.integrable_ball h) i
      =ᵐ[volume.restrict (Metric.ball a r)]
      euclideanMollification (ballDomain a R) (fun x => Du x i)
        (hu.column_integrable_ball i) h := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [Metric.mem_ball] at hx
    exact hu.euclideanMollification_ball_coordinateDerivative h x
      (scaledMollifierKernel_sampling_ball h a x R (by linarith only [hx, hh])) i
  exact (memLp_congr_ae heq).mpr (hcol.mono_measure Measure.restrict_le_self)

theorem MemW12.tendsto_eLpNorm_mollification_inner_ball {n q : ℕ}
    {a : Domain n} {R r : ℝ} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12 (ballDomain a R) u Du) (hr : r < R) :
    Tendsto (fun h : PositiveRadius => eLpNorm
      (fun x => euclideanMollification (ballDomain a R) u hu.integrable_ball h x - u x)
      2 (volume.restrict (Metric.ball a r)))
      (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) (𝓝 0) :=
  tendsto_eLpNorm_euclideanMollification_sub (ballDomain a R) u hu.integrable_ball hu.2.1
    measurableSet_ball (Metric.ball_subset_ball hr.le)

/-- The same positive-scale limit holds for each actual classical derivative column. -/
theorem MemW12.tendsto_eLpNorm_mollification_column_inner_ball {n q : ℕ}
    {a : Domain n} {R r : ℝ} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12 (ballDomain a R) u Du) (hr : r < R)
    (i : Fin n) :
    Tendsto (fun h : PositiveRadius => eLpNorm (fun x => coordinateDerivative
      (euclideanMollification (ballDomain a R) u hu.integrable_ball h)
      (euclideanMollification_contDiff (ballDomain a R) u hu.integrable_ball h) i x - Du x i)
      2 (volume.restrict (Metric.ball a r)))
      (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) (𝓝 0) := by
  have hcol := tendsto_eLpNorm_euclideanMollification_sub (ballDomain a R)
    (fun x => Du x i) (hu.column_integrable_ball i) (hu.2.2 i) measurableSet_ball
    (Metric.ball_subset_ball hr.le)
  have hval : Tendsto (fun h : PositiveRadius => h.val)
      (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) (𝓝 0) := tendsto_comap
  have hsmall := hval.eventually_lt_const (by linarith only [hr] : 0 < 2 * (R - r))
  apply hcol.congr'
  filter_upwards [hsmall] with h hh
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  rw [Metric.mem_ball] at hx
  rw [hu.euclideanMollification_ball_coordinateDerivative h x
    (scaledMollifierKernel_sampling_ball h a x R (by linarith only [hx, hh])) i]
  rfl

/-- One globally smooth map approximates both the map and all displayed columns
on a smaller ball with arbitrarily small L2 error. -/
theorem MemW12.exists_smooth_approximation_inner_ball {n q : ℕ}
    {a : Domain n} {R r : ℝ} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12 (ballDomain a R) u Du)
    (hr : r < R) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ m : Domain n → Ambient q, ∃ hm : ContDiff ℝ ∞ m,
      MemLp m 2 (volume.restrict (Metric.ball a r)) ∧
      (∀ i, MemLp (coordinateDerivative m hm i) 2 (volume.restrict (Metric.ball a r))) ∧
      eLpNorm (m - u) 2 (volume.restrict (Metric.ball a r)) ≤ ε ∧
      ∀ i, eLpNorm (fun x => coordinateDerivative m hm i x - Du x i) 2
        (volume.restrict (Metric.ball a r)) ≤ ε := by
  let scale : ℕ → PositiveRadius := fun k => ⟨1 / ((k : ℝ) + 1), by positivity⟩
  have hs : Tendsto scale atTop (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) := by
    apply tendsto_comap_iff.mpr
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  letI := hs.neBot
  have hmap := (hu.tendsto_eLpNorm_mollification_inner_ball hr).eventually_lt_const hε
  have hcol := eventually_all.mpr fun i =>
    (hu.tendsto_eLpNorm_mollification_column_inner_ball hr i).eventually_lt_const hε
  have hval : Tendsto (fun h : PositiveRadius => h.val)
      (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) (𝓝 0) := tendsto_comap
  have hsmall := hval.eventually_lt_const (by linarith only [hr] : 0 < 2 * (R - r))
  obtain ⟨h, hmerr, hderr, hh⟩ := (hmap.and (hcol.and hsmall)).exists
  refine ⟨euclideanMollification (ballDomain a R) u hu.integrable_ball h,
    euclideanMollification_contDiff (ballDomain a R) u hu.integrable_ball h,
    hu.euclideanMollification_memLp_inner_ball h,
    (fun i => hu.euclideanMollification_column_memLp_inner_ball h
      (by linarith only [hh]) i), hmerr.le, fun i => (hderr i).le⟩

end
end HarmonicMaps

end

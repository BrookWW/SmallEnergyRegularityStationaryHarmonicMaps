module

public import StationaryHarmonicMaps.Analysis.SmoothTranslationEnergy
public import StationaryHarmonicMaps.Analysis.ZeroBoundaryPoincare
public import HarmonicMaps.Analysis.SobolevSmoothDensity

/-!
# Actual interior translation moduli from the displayed weak gradient

Whole-ball smooth graph density preserves the same map and weak columns.
The actual restricted translation operator is bounded on L2, so the smooth
energy estimate passes to the Sobolev limit. Uniform gradient energy gives
a common interior translation modulus for an arbitrary Sobolev sequence.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem translated_L2_convergence {n q : ℕ}
    {f : ℕ → Domain n → Ambient q} {u : Domain n → Ambient q}
    (a h : Domain n) {r R : ℝ} (hh : ‖h‖ ≤ R - r)
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict (Metric.ball a R)))
    (hu : MemLp u 2 (volume.restrict (Metric.ball a R)))
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2
      (volume.restrict (Metric.ball a R))) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun x => f k (x + h) - u (x + h)) 2
      (volume.restrict (Metric.ball a r))) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
    (fun _ => zero_le)
  intro k
  exact (inner_translate_memLp_and_eLpNorm_le (f k - u) a h hh ((hf k).sub hu)).2

private theorem increment_L2_convergence {n q : ℕ}
    {f : ℕ → Domain n → Ambient q} {u : Domain n → Ambient q}
    (a h : Domain n) {r R : ℝ} (hrR : r < R) (hh : ‖h‖ ≤ R - r)
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict (Metric.ball a R)))
    (hu : MemLp u 2 (volume.restrict (Metric.ball a R)))
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2
      (volume.restrict (Metric.ball a R))) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm
      ((fun x => f k (x + h) - f k x) - (fun x => u (x + h) - u x)) 2
        (volume.restrict (Metric.ball a r))) atTop (𝓝 0) := by
  have hshift := translated_L2_convergence a h hh hf hu hconv
  have hinner : Tendsto (fun k => eLpNorm (f k - u) 2
      (volume.restrict (Metric.ball a r))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun _ => zero_le)
    intro k
    exact eLpNorm_mono_measure _
      (Measure.restrict_mono_set volume (Metric.ball_subset_ball hrR.le))
  have hsum : Tendsto (fun k =>
      eLpNorm (fun x => f k (x + h) - u (x + h)) 2 (volume.restrict (Metric.ball a r)) +
      eLpNorm (f k - u) 2 (volume.restrict (Metric.ball a r))) atTop (𝓝 0) := by
    simpa only [add_zero] using hshift.add hinner
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le)
  intro k
  have heq : ((fun x => f k (x + h) - f k x) - (fun x => u (x + h) - u x)) =
      (fun x => f k (x + h) - u (x + h)) - (f k - u) := by
    funext x
    simp only [Pi.sub_apply]
    abel
  dsimp only
  rw [heq]
  exact eLpNorm_sub_le
    (inner_translate_memLp_and_eLpNorm_le (f k - u) a h hh ((hf k).sub hu)).1.aestronglyMeasurable
    (((hf k).sub hu).mono_measure
      (Measure.restrict_mono_set volume (Metric.ball_subset_ball hrR.le))).aestronglyMeasurable
    (by norm_num)

/-- The same actual weak columns control the L2 translation error with the exact factor ‖h‖². -/
theorem integral_translation_sub_sq_le {n q : ℕ} (a : Domain n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12 (ballDomain a R) u Du)
    (h : Domain n) (hh : ‖h‖ ≤ R - r) :
    (∫ x in Metric.ball a r, ‖u (x + h) - u x‖ ^ 2) ≤
      ‖h‖ ^ 2 * ∫ x in Metric.ball a R, hsNormSq (Du x) := by
  obtain ⟨f, hf, hfW, hconv, hDconv⟩ := hu.smoothDensity_memW12_ball (hr.trans hrR)
  have hmeasure : volume.restrict (Metric.ball a r) ≤ volume.restrict (Metric.ball a R) :=
    Measure.restrict_mono_set volume (Metric.ball_subset_ball hrR.le)
  have hinc (k : ℕ) : MemLp (fun x => f k (x + h) - f k x) 2
      (volume.restrict (Metric.ball a r)) :=
    ((inner_translate_memLp_and_eLpNorm_le (f k) a h hh (hfW k).2.1).1).sub
      ((hfW k).2.1.mono_measure hmeasure)
  have huinc : MemLp (fun x => u (x + h) - u x) 2
      (volume.restrict (Metric.ball a r)) :=
    ((inner_translate_memLp_and_eLpNorm_le u a h hh hu.2.1).1).sub
      (hu.2.1.mono_measure hmeasure)
  have hleft := tendsto_integral_norm_sq_of_L2 hinc huinc
    (increment_L2_convergence a h hrR hh (fun k => (hfW k).2.1) hu.2.1 hconv)
  have hright := tendsto_integral_hsNormSq_of_columns_L2
    (fun k i => (hfW k).2.2 i) hu.2.2 hDconv
  exact le_of_tendsto_of_tendsto hleft (hright.const_mul (‖h‖ ^ 2))
    (Eventually.of_forall fun k =>
      smooth_integral_translation_sub_sq_le (f k) (hf k) a hr hrR h hh (fun i => (hfW k).2.2 i))

/-- Uniform actual gradient energy gives a common interior translation modulus. -/
theorem uniform_integral_translation_sub_sq_modulus {n q : ℕ}
    (a : Domain n) {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (hM : 0 ≤ M)
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (hu : ∀ k, MemW12 (ballDomain a R) (u k) (Du k))
    (henergy : ∀ k, (∫ x in Metric.ball a R, hsNormSq (Du k x)) ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : Domain n,
      ‖h‖ < δ → ∀ k : ℕ, (∫ x in Metric.ball a r, ‖u k (x + h) - u k x‖ ^ 2) < ε := by
  intro ε hε
  let δ : ℝ := min (R - r) (min 1 (ε / (M + 1)))
  have hδ : 0 < δ := lt_min (sub_pos.mpr hrR) (lt_min zero_lt_one (div_pos hε (by positivity)))
  refine ⟨δ, hδ, ?_⟩
  intro h hh k
  have hmargin : ‖h‖ ≤ R - r := hh.le.trans (min_le_left _ _)
  have hsmall : ‖h‖ ≤ 1 := hh.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heps : ‖h‖ * (M + 1) < ε :=
    (lt_div_iff₀ (by positivity : 0 < M + 1)).mp
      (hh.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hsquare : ‖h‖ ^ 2 ≤ ‖h‖ := by nlinarith only [norm_nonneg h, hsmall]
  calc
    _ ≤ ‖h‖ ^ 2 * ∫ x in Metric.ball a R, hsNormSq (Du k x) :=
      integral_translation_sub_sq_le a hr hrR (hu k) h hmargin
    _ ≤ ‖h‖ ^ 2 * M := mul_le_mul_of_nonneg_left (henergy k) (sq_nonneg _)
    _ ≤ ‖h‖ * M := mul_le_mul_of_nonneg_right hsquare hM
    _ ≤ ‖h‖ * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ < ε := heps

end StationaryHarmonicMaps.Analysis

end

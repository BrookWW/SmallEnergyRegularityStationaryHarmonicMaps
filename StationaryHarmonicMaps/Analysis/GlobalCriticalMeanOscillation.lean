module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyMeanOscillation
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# All-ball scalar mean oscillation from a genuine global critical graph

The original full-space native graph restricts to every actual ball.
Each term of its complete critical Morrey supremum controls the true
vector mean oscillation. Continuous linear observables commute with
the actual mean and retain the same scalar oscillation bound.
-/

public section

open HarmonicMaps MeasureTheory Set

namespace StationaryHarmonicMaps.Analysis

/-- The actual global critical graph controls all positive-ball scalar mean oscillations, uniformly before the map and observable are chosen. -/
theorem exists_global_scalar_mean_oscillation_bound_of_criticalMorrey (n : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
      (M : ℝ),MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) u Du → 0≤M →
      criticalGradientMorreySquare Du univ≤ENNReal.ofReal M →
      ∀ (L : Ambient q →L[ℝ] ℝ) (x : Domain n) (r : ℝ),0<r →
        IntegrableOn (fun y=>L (u y)) (Metric.ball x r) volume ∧
        (⨍ y in Metric.ball x r,|L (u y)-(⨍ z in Metric.ball x r,L (u z))|)≤
          C*‖L‖*Real.sqrt M := by
  let C₀ : ℝ := ((2 : ℝ)^(n+1)*Real.sqrt (n : ℝ))*
    (volume.real (Metric.ball (0 : Domain n) 1))^(-(1/(2 : ℝ)))
  let C : ℝ := 1+C₀
  have hC₀ : 0≤C₀ := by dsimp only [C₀];positivity
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro q u Du M hu hM hMorrey L x r hr
  let μ := volume.restrict (Metric.ball x r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hLocal : MemW12 (ballDomain x r) u Du :=
    memW12_of_openDomain_subset hu (subset_univ _)
  have hULp : MemLp u 2 μ := hLocal.2.1
  have hUI : Integrable u μ := hULp.integrable (by norm_num)
  have hLI : Integrable (fun y=>L (u y)) μ := L.integrable_comp hUI
  have hN := (normalizedEnergy_le_criticalMorrey_of_ball_subset Du (x := x) hr (subset_univ _)).trans hMorrey
  have hVec := meanOscillation_le_of_normalizedEnergy_bound x hr hM hLocal hN
  have hMean : (⨍ z in Metric.ball x r,L (u z))=L (⨍ z in Metric.ball x r,u z) :=
    L.integral_comp_comm hUI.to_average
  have hOscI : Integrable (fun y=>‖u y-(⨍ z in Metric.ball x r,u z)‖) μ :=
    (hUI.sub (integrable_const _)).norm
  have hScalarI : Integrable (fun y=>|L (u y)-(⨍ z in Metric.ball x r,L (u z))|) μ :=
    (hLI.sub (integrable_const _)).abs
  refine ⟨hLI,?_⟩
  calc
    _ ≤ ⨍ y in Metric.ball x r,‖L‖*‖u y-(⨍ z in Metric.ball x r,u z)‖ := by
      apply integral_mono hScalarI.to_average (hOscI.const_mul ‖L‖).to_average
      intro y
      dsimp only
      rw [hMean,← L.map_sub,← Real.norm_eq_abs]
      exact L.le_opNorm _
    _ = ‖L‖*(⨍ y in Metric.ball x r,‖u y-(⨍ z in Metric.ball x r,u z)‖) := integral_const_mul _ _
    _ ≤ ‖L‖*(C₀*Real.sqrt M) := mul_le_mul_of_nonneg_left hVec (norm_nonneg _)
    _ ≤ C*‖L‖*Real.sqrt M := by
      have H : C₀≤C := by dsimp only [C];linarith
      nlinarith only [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right H (norm_nonneg L)) (Real.sqrt_nonneg M)]

end StationaryHarmonicMaps.Analysis

end

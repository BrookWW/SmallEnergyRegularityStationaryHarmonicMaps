module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyMeanOscillation
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import StationaryHarmonicMaps.Analysis.EffectiveEuclideanVolume

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

@[expose] noncomputable def globalCriticalMeanOscillationConstant (n : ℕ) : ℝ :=
  1 + ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) *
    (volume.real (Metric.ball (0 : Domain n) 1)) ^ (-(1 / (2 : ℝ)))

@[expose] def effectiveGlobalCriticalMeanOscillationConstant (n : ℕ) : ℕ :=
  1 + 2 ^ (n + 1) * (n + 1) * (1 + (n + 1) ^ n)

theorem globalCriticalMeanOscillationConstant_pos (n : ℕ) :
    0 < globalCriticalMeanOscillationConstant n := by
  unfold globalCriticalMeanOscillationConstant
  positivity

theorem globalCriticalMeanOscillationConstant_le_effective (n : ℕ) :
    globalCriticalMeanOscillationConstant n ≤
      (effectiveGlobalCriticalMeanOscillationConstant n : ℝ) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) + 1 := by
    have H := Real.sq_sqrt hn
    have Hn := Real.sqrt_nonneg (n : ℝ)
    nlinarith only [H, Hn, hn, sq_nonneg (n : ℝ)]
  have hvolume := euclidean_unit_ball_inverse_rpow_le n (1 / 2) (by norm_num) (by norm_num)
  have hproduct := mul_le_mul
    (mul_le_mul_of_nonneg_left hsqrt (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n + 1)))
    hvolume (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n + 1)) (by positivity))
  dsimp only [globalCriticalMeanOscillationConstant]
  simp only [effectiveGlobalCriticalMeanOscillationConstant, Nat.cast_add, Nat.cast_one,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  linarith only [hproduct]

/-- The actual global critical graph controls all positive-ball scalar mean oscillations, uniformly before the map and observable are chosen. -/
theorem global_scalar_mean_oscillation_bound_of_criticalMorrey (n : ℕ) :
    ∀ (q : ℕ) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
      (M : ℝ),MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) u Du → 0≤M →
      criticalGradientMorreySquare Du univ≤ENNReal.ofReal M →
      ∀ (L : Ambient q →L[ℝ] ℝ) (x : Domain n) (r : ℝ),0<r →
        IntegrableOn (fun y=>L (u y)) (Metric.ball x r) volume ∧
        (⨍ y in Metric.ball x r,|L (u y)-(⨍ z in Metric.ball x r,L (u z))|)≤
          globalCriticalMeanOscillationConstant n*‖L‖*Real.sqrt M := by
  let C₀ : ℝ := ((2 : ℝ)^(n+1)*Real.sqrt (n : ℝ))*
    (volume.real (Metric.ball (0 : Domain n) 1))^(-(1/(2 : ℝ)))
  let C : ℝ := 1+C₀
  have hC₀ : 0≤C₀ := by dsimp only [C₀];positivity
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

theorem effective_global_scalar_mean_oscillation_bound_of_criticalMorrey (n : ℕ) :
    ∀ (q : ℕ) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
      (M : ℝ), MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain n) u Du → 0 ≤ M →
      criticalGradientMorreySquare Du univ ≤ ENNReal.ofReal M →
      ∀ (L : Ambient q →L[ℝ] ℝ) (x : Domain n) (r : ℝ), 0 < r →
        IntegrableOn (fun y => L (u y)) (Metric.ball x r) volume ∧
        (⨍ y in Metric.ball x r, |L (u y) - (⨍ z in Metric.ball x r, L (u z))|) ≤
          (effectiveGlobalCriticalMeanOscillationConstant n : ℝ) * ‖L‖ * Real.sqrt M := by
  intro q u Du M hu hM hMorrey L x r hr
  obtain ⟨hI, hBound⟩ := global_scalar_mean_oscillation_bound_of_criticalMorrey n
    q u Du M hu hM hMorrey L x r hr
  refine ⟨hI, hBound.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (globalCriticalMeanOscillationConstant_le_effective n) (norm_nonneg L))
    (Real.sqrt_nonneg M)

theorem exists_global_scalar_mean_oscillation_bound_of_criticalMorrey (n : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
      (M : ℝ),MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) u Du → 0≤M →
      criticalGradientMorreySquare Du univ≤ENNReal.ofReal M →
      ∀ (L : Ambient q →L[ℝ] ℝ) (x : Domain n) (r : ℝ),0<r →
        IntegrableOn (fun y=>L (u y)) (Metric.ball x r) volume ∧
        (⨍ y in Metric.ball x r,|L (u y)-(⨍ z in Metric.ball x r,L (u z))|)≤
          C*‖L‖*Real.sqrt M := by
  exact ⟨globalCriticalMeanOscillationConstant n, globalCriticalMeanOscillationConstant_pos n,
    global_scalar_mean_oscillation_bound_of_criticalMorrey n⟩

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds
public import HolderToCK.Foundation.BallVolume

/-!
# Forward L² critical Morrey control gives actual lower-power growth

Every ball has actual L² columns from compact localization. The finite-measure
Hölder comparison has its correct volume factor. Exact real-power algebra
then gives the exponent n-p, without reversing an Lp estimate to L².
-/

public section

open HarmonicMaps MeasureTheory Set

namespace StationaryHarmonicMaps.Analysis

/-- The literal pth HS-gradient integral has the correct all-radius forward growth. -/
theorem integral_hs_rpow_le_of_global_criticalMorrey {n q : ℕ}
    (F : Domain n → Gradient n q)
    (hF : ∀ i, LocallyMemL2 (⟨univ, isOpen_univ⟩ : OpenDomain n) (fun x => F x i))
    {M p : ℝ} (hM : 0 ≤ M) (hp : 0 < p) (hpTwo : p ≤ 2)
    (hcritical : criticalGradientMorreySquare F univ ≤ ENNReal.ofReal M)
    (x : Domain n) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y => (Real.sqrt (hsNormSq (F y))) ^ p) (Metric.ball x r) volume ∧
      (∫ y in Metric.ball x r, (Real.sqrt (hsNormSq (F y))) ^ p) ≤
        (volume.real (Metric.ball (0 : Domain n) 1)) ^ (1 - p / 2) * M ^ (p / 2) *
          r ^ ((n : ℝ) - p) := by
  let μ := volume.restrict (Metric.ball x r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hcols (i : Fin n) : MemLp (fun y => F y i) 2 μ :=
    (hF i (Metric.closedBall x r) (isCompact_closedBall _ _) (subset_univ _)).mono_measure
      (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
  have hI0 : 0 ≤ ∫ y in Metric.ball x r, hsNormSq (F y) :=
    integral_nonneg fun y => hsNormSq_nonneg _
  have hE : (∫ y in Metric.ball x r, hsNormSq (F y)) ≤ M * r ^ ((n : ℝ) - 2) :=
    integral_hsNormSq_le_of_criticalMorrey F (mem_univ x) hr hM
      (by intro y hy; exact ⟨hy, mem_univ y⟩) hcols hcritical
  have hforward := integral_sqrt_sum_norm_sq_rpow_le (μ := μ) F hp hpTwo hcols
  have hmass : μ.real univ = r ^ n * volume.real (Metric.ball (0 : Domain n) 1) := by
    rw [measureReal_restrict_apply_univ]
    exact HolderToCK.ball_volume_real x hr
  have hV : 0 ≤ volume.real (Metric.ball (0 : Domain n) 1) := ENNReal.toReal_nonneg
  have hpower := Real.rpow_le_rpow hI0 hE (by linarith only [hp] : 0 ≤ p / 2)
  refine ⟨integrable_sqrt_sum_norm_sq_rpow F hp.le hpTwo hcols, ?_⟩
  calc
    _ ≤ (μ.real univ) ^ (1 - p / 2) *
        (∫ y in Metric.ball x r, hsNormSq (F y)) ^ (p / 2) := hforward
    _ ≤ (μ.real univ) ^ (1 - p / 2) * (M * r ^ ((n : ℝ) - 2)) ^ (p / 2) :=
      mul_le_mul_of_nonneg_left hpower (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    _ = _ := by
      rw [hmass, Real.mul_rpow (pow_nonneg hr.le n) hV,
        Real.mul_rpow hM (Real.rpow_nonneg hr.le _), ← Real.rpow_natCast r n,
        ← Real.rpow_mul hr.le, ← Real.rpow_mul hr.le]
      have he : (n : ℝ) * (1 - p / 2) + ((n : ℝ) - 2) * (p / 2) = n - p := by ring
      calc
        _ = (volume.real (Metric.ball (0 : Domain n) 1)) ^ (1 - p / 2) * M ^ (p / 2) *
            (r ^ ((n : ℝ) * (1 - p / 2)) * r ^ (((n : ℝ) - 2) * (p / 2))) := by ring
        _ = _ := by rw [← Real.rpow_add hr, he]

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.DyadicBallMaximal

/-!
# Original ball energy from a nearby dyadic maximal good point

An arbitrary real query radius is enclosed in an actual dyadic ball at
the original nearby good point. Its radius is at most 64 times the query
radius. Exact volume comparison gives both the original ball energy and
its actual average, without a pointwise finiteness assumption.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- A genuine nearby maximal good point bounds the original density on every sufficiently large real-radius query ball. -/
theorem ball_lintegral_le_of_dyadic_maximal_goodpoint {n : ℕ}
    (f : Domain n → ℝ≥0∞) (a y : Domain n) (r R : ℝ) (hr : 0<r)
    (hy : dist y a≤20*r) (hR : r≤R) (L : ℝ≥0∞) (hGood : dyadicBallMaximal f y≤L) :
    (∫⁻ z in Metric.ball a R,f z)≤ENNReal.ofReal ((64 : ℝ)^n)*L*volume (Metric.ball a R) ∧
      centeredBallAverageENN f a ⟨R,hr.trans_le hR⟩≤ENNReal.ofReal ((64 : ℝ)^n)*L := by
  have hR0 : 0<R := hr.trans_le hR
  obtain ⟨j,hj⟩ := exists_mem_Ioc_zpow (show 0<32*R by positivity) (by norm_num : (1 : ℝ)<2)
  let S := (2 : ℝ)^(j+1)
  have hS : 0<S := zpow_pos (by norm_num) _
  have hS32 : 32*R≤S := hj.2
  have hS64 : S≤64*R := by
    dsimp only [S]
    rw [zpow_add₀ (by norm_num : (2 : ℝ)≠0),zpow_one]
    linarith only [hj.1]
  have hSub : Metric.ball a R⊆Metric.ball y S := by
    intro z hz
    have hza : dist z a<R := hz
    have hay : dist a y≤20*r := by simpa only [dist_comm] using hy
    change dist z y<S
    exact lt_of_le_of_lt (dist_triangle z a y) (by linarith)
  have hVolumeScale : volume (Metric.ball y (64*R))=
      ENNReal.ofReal ((64 : ℝ)^n)*volume (Metric.ball a R) := by
    rw [Measure.addHaar_ball_of_pos volume y (by positivity : 0<64*R),Measure.addHaar_ball_of_pos volume a hR0]
    simp only [finrank_euclideanSpace,Fintype.card_fin,mul_pow,
      ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ)≤64) n),mul_assoc]
  have hVolume : volume (Metric.ball y S)≤ENNReal.ofReal ((64 : ℝ)^n)*volume (Metric.ball a R) :=
    (measure_mono (Metric.ball_subset_ball hS64)).trans_eq hVolumeScale
  have hAverage : centeredBallAverageENN f y ⟨S,hS⟩≤L :=
    (le_iSup (fun k : ℤ=>centeredBallAverageENN f y
      ⟨(2 : ℝ)^k,zpow_pos (by norm_num) k⟩) (j+1)).trans hGood
  have hIntegral : (∫⁻ z in Metric.ball a R,f z)≤ENNReal.ofReal ((64 : ℝ)^n)*L*volume (Metric.ball a R) := by
    calc
      _ ≤ ∫⁻ z in Metric.ball y S,f z := lintegral_mono_set hSub
      _ = volume (Metric.ball y S)*centeredBallAverageENN f y ⟨S,hS⟩ := by
        rw [centeredBallAverageENN,← mul_assoc,
          ENNReal.mul_inv_cancel (Metric.measure_ball_pos volume y hS).ne' measure_ball_ne_top,one_mul]
      _ ≤ (ENNReal.ofReal ((64 : ℝ)^n)*volume (Metric.ball a R))*L := mul_le_mul hVolume hAverage zero_le zero_le
      _ = _ := by ac_rfl
  refine ⟨hIntegral,?_⟩
  unfold centeredBallAverageENN
  calc
    _ ≤ (volume (Metric.ball a R))⁻¹*(ENNReal.ofReal ((64 : ℝ)^n)*L*volume (Metric.ball a R)) :=
      mul_le_mul_of_nonneg_left hIntegral zero_le
    _ = (ENNReal.ofReal ((64 : ℝ)^n)*L)*((volume (Metric.ball a R))⁻¹*volume (Metric.ball a R)) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel (Metric.measure_ball_pos volume a hR0).ne' measure_ball_ne_top,mul_one]

end StationaryHarmonicMaps.Analysis

end

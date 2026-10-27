module

public import StationaryHarmonicMaps.Analysis.DyadicBallMaximal

/-!
# Actual large-radius localization at a nearby good point

The original ball at x lies in the genuine integer-scale j+6 ball at
the supplied good point. Exact Euclidean volumes give the factor 64^n.
All averages and the full maximal function remain extended quantities;
no global pointwise finiteness or desired localization bound is assumed.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- A genuine nearby maximal good point controls every original dyadic average whose radius is at least the Whitney radius. -/
theorem dyadicBallAverage_large_radius_le_of_goodpoint {n : ℕ}
    (f : Domain n → ℝ≥0∞) (a x y : Domain n) (r : ℝ) (_hr : 0<r)
    (hy : dist y a≤20*r) (hx : x∈Metric.ball a (5*r)) (L : ℝ≥0∞)
    (hGood : dyadicBallMaximal f y≤L) (j : ℤ) (hLarge : r≤(2 : ℝ)^j) :
    centeredBallAverageENN f x ⟨(2 : ℝ)^j,zpow_pos (by norm_num) j⟩≤
      ENNReal.ofReal ((64 : ℝ)^n)*L := by
  let R := (2 : ℝ)^j
  let Q := (2 : ℝ)^(j+6)
  have hR : 0<R := zpow_pos (by norm_num) j
  have hQ : 0<Q := zpow_pos (by norm_num) (j+6)
  have hScale : Q=64*R := by
    dsimp only [Q,R]
    rw [zpow_add₀ (by norm_num : (2 : ℝ)≠0)]
    norm_num
    ring
  have hSub : Metric.ball x R⊆Metric.ball y Q := by
    intro z hz
    have hzx : dist z x<R := hz
    have hxa : dist x a<5*r := hx
    have hay : dist a y≤20*r := by simpa only [dist_comm] using hy
    have hTriangle : dist z y≤dist z x+dist x a+dist a y :=
      (dist_triangle z a y).trans (add_le_add (dist_triangle z x a) le_rfl)
    change dist z y<Q
    rw [hScale]
    dsimp only [R] at hR
    change r≤R at hLarge
    linarith
  have hVolume : volume (Metric.ball y Q)=ENNReal.ofReal ((64 : ℝ)^n)*volume (Metric.ball x R) := by
    rw [hScale,Measure.addHaar_ball_of_pos volume y (by positivity : 0<64*R),
      Measure.addHaar_ball_of_pos volume x hR]
    simp only [finrank_euclideanSpace,Fintype.card_fin,mul_pow,
      ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ)≤64) n),mul_assoc]
  have hInverse : (volume (Metric.ball x R))⁻¹=
      ENNReal.ofReal ((64 : ℝ)^n)*(volume (Metric.ball y Q))⁻¹ := by
    have hX0 := (Metric.measure_ball_pos volume x hR).ne'
    have hY0 := (Metric.measure_ball_pos volume y hQ).ne'
    calc
      _ = volume (Metric.ball y Q)*((volume (Metric.ball x R))⁻¹*(volume (Metric.ball y Q))⁻¹) := by
        calc
          _ = (volume (Metric.ball x R))⁻¹*(volume (Metric.ball y Q)*(volume (Metric.ball y Q))⁻¹) := by
            rw [ENNReal.mul_inv_cancel hY0 measure_ball_ne_top,mul_one]
          _ = _ := by ac_rfl
      _ = (ENNReal.ofReal ((64 : ℝ)^n)*volume (Metric.ball x R))*
          ((volume (Metric.ball x R))⁻¹*(volume (Metric.ball y Q))⁻¹) := congrArg (fun z=>z*((volume (Metric.ball x R))⁻¹*(volume (Metric.ball y Q))⁻¹)) hVolume
      _ = ENNReal.ofReal ((64 : ℝ)^n)*(volume (Metric.ball x R)*(volume (Metric.ball x R))⁻¹)*(volume (Metric.ball y Q))⁻¹ := by ac_rfl
      _ = _ := by rw [ENNReal.mul_inv_cancel hX0 measure_ball_ne_top,mul_one]
  calc
    _ ≤ (volume (Metric.ball x R))⁻¹*∫⁻ z in Metric.ball y Q,f z :=
      mul_le_mul_of_nonneg_left (lintegral_mono_set hSub) zero_le
    _ = ENNReal.ofReal ((64 : ℝ)^n)*centeredBallAverageENN f y ⟨Q,hQ⟩ := by
      rw [hInverse,centeredBallAverageENN,mul_assoc]
    _ ≤ ENNReal.ofReal ((64 : ℝ)^n)*dyadicBallMaximal f y :=
      mul_le_mul_of_nonneg_left (le_iSup (fun k : ℤ=>centeredBallAverageENN f y
        ⟨(2 : ℝ)^k,zpow_pos (by norm_num) k⟩) (j+6)) zero_le
    _ ≤ _ := mul_le_mul_of_nonneg_left hGood zero_le

end StationaryHarmonicMaps.Analysis

end

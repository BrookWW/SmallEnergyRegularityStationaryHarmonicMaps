module

public import StationaryHarmonicMaps.Analysis.BoundaryStrongerMorreyRepresentative
public import Mathlib.MeasureTheory.Integral.Average

/-!
# The original mean controls the whole-ball stronger Morrey supremum

The actual closed-ball representative has diameter-controlled oscillation.
Integrating its difference from the original map gives a bound by the norm
of the actual original ball mean and the original stronger growth amplitude.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Original strictly stronger derivative growth produces a whole-source-ball
AE bound in terms of the actual original mean, with no boundedness or
continuous-representative premise. -/
theorem exists_stronger_morrey_ae_bound_by_mean
    (n : ℕ) (hn : 2 ≤ n) (γ : ℝ) (hγ : 0 < γ) (hγTwo : γ < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (K : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ K →
      (∀ a ∈ ball (0 : Domain n) 1, ∀ r : ℝ, 0 < r →
        (∫ x in ball a r ∩ ball (0 : Domain n) 1, hsNormSq (Du x)) ≤
          K * r^((n : ℝ)-2+γ)) →
      ∃ W : closedBall (0 : Domain n) 1 → Ambient q,
        Continuous W ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ∀ hx : x ∈ ball (0 : Domain n) 1,
          W ⟨x,ball_subset_closedBall hx⟩ = u x) ∧
        (∀ x : closedBall (0 : Domain n) 1,
          ‖W x‖ ≤ ‖(⨍ y in ball (0 : Domain n) 1, u y)‖ + C * Real.sqrt K) ∧
        ∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),
          ‖u x‖ ≤ ‖(⨍ y in ball (0 : Domain n) 1, u y)‖ + C * Real.sqrt K := by
  obtain ⟨H,hH,Hrep⟩ := existsUnique_closedBall_holder_representative_of_stronger_morrey
    n hn γ hγ hγTwo
  let C := H * (2 : ℝ)^(γ/2)
  have hC : 0 < C := mul_pos hH (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨C,hC,?_⟩
  intro q u Du K hu hK hGrowth
  obtain ⟨W,⟨hW,hAE,hHolder⟩,_hUnique⟩ := Hrep q u Du K hu hK hGrowth
  let μ := volume.restrict (ball (0 : Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hVolume : 0 < μ.real univ := by
    simpa only [μ,measureReal_restrict_apply_univ] using
      HolderToCK.ball_volume_real_pos (0 : Domain n) (by norm_num : (0 : ℝ) < 1)
  have huLp : MemLp u 2 μ := hu.2.1
  have huI : Integrable u μ := huLp.integrable (by norm_num)
  let c := ⨍ y, u y ∂μ
  let T := C * Real.sqrt K
  have hDifference (x : closedBall (0 : Domain n) 1) :
      ∀ᵐ y ∂μ, ‖W x-u y‖ ≤ T := by
    filter_upwards [hAE,ae_restrict_mem measurableSet_ball] with y hy hyBall
    have hx0 : dist (x : Domain n) 0 ≤ 1 := x.property
    have hy0 : dist (0 : Domain n) y ≤ 1 := by
      rw [dist_comm]
      exact ball_subset_closedBall hyBall
    have hDist : dist (x : Domain n) y ≤ 2 :=
      (dist_triangle (x : Domain n) 0 y).trans (by linarith only [hx0,hy0])
    rw [←hy hyBall]
    calc
      _ ≤ H * Real.sqrt K * (dist (x : Domain n) y)^(γ/2) :=
        hHolder x ⟨y,ball_subset_closedBall hyBall⟩
      _ ≤ H * Real.sqrt K * (2 : ℝ)^(γ/2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg hDist (half_pos hγ).le)
        (mul_nonneg hH.le (Real.sqrt_nonneg K))
      _ = T := by dsimp only [T,C]; ring
  have hMeanBound (x : closedBall (0 : Domain n) 1) : ‖W x‖ ≤ ‖c‖+T := by
    have hAverage : (⨍ y, W x-u y ∂μ) = W x-c := by
      dsimp only [c]
      simp only [average_eq]
      rw [integral_sub (integrable_const (W x)) huI,integral_const,smul_sub,smul_smul,
        inv_mul_cancel₀ hVolume.ne',one_smul]
    have hIntegral : ‖∫ y, W x-u y ∂μ‖ ≤ T * μ.real univ :=
      norm_integral_le_of_norm_le_const (hDifference x)
    have hCentered : ‖W x-c‖ ≤ T := by
      rw [←hAverage,average_eq,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hVolume.le)]
      calc
        _ ≤ (μ.real univ)⁻¹ * (T * μ.real univ) :=
          mul_le_mul_of_nonneg_left hIntegral (inv_nonneg.mpr hVolume.le)
        _ = T := by
          rw [mul_left_comm,inv_mul_cancel₀ hVolume.ne',mul_one]
    calc
      _ ≤ ‖W x-c‖+‖c‖ := norm_le_norm_sub_add (W x) c
      _ ≤ T+‖c‖ := add_le_add hCentered le_rfl
      _ = _ := add_comm _ _
  refine ⟨W,hW,hAE,hMeanBound,?_⟩
  filter_upwards [hAE,ae_restrict_mem measurableSet_ball] with x hx hxBall
  have Hx := hMeanBound ⟨x,ball_subset_closedBall hxBall⟩
  rw [hx hxBall] at Hx
  exact Hx

end StationaryHarmonicMaps.Analysis

end

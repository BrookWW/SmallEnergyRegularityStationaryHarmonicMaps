module

public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # A rational lower bound for the Euclidean unit-ball volume

A coordinate cube lies strictly inside the L2 unit ball. Its product volume
and the canonical measure-preserving coordinate map give a dimension-only
bound without evaluating gamma functions or selecting a linear equivalence.
-/

public section

open HarmonicMaps MeasureTheory Set Metric

namespace StationaryHarmonicMaps.Analysis

theorem euclidean_unit_ball_volume_lower_bound (n : ℕ) :
    (1 / ((n : ℝ) + 1)) ^ n ≤ volume.real (ball (0 : Domain n) 1) := by
  let r : ℝ := 1 / (2 * ((n : ℝ) + 1))
  let C : Set (Fin n → ℝ) := Icc (fun _ => -r) (fun _ => r)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hr : 0 < r := by dsimp only [r]; positivity
  have hC : C ⊆ (WithLp.toLp 2) ⁻¹' ball (0 : Domain n) 1 := by
    intro x hx
    have hcoord (i : Fin n) : |x i| ≤ r := abs_le.mpr ⟨hx.1 i, hx.2 i⟩
    have hsum : ∑ i : Fin n, ‖x i‖ ^ 2 ≤ (n : ℝ) * r ^ 2 := by
      calc
        _ ≤ ∑ _i : Fin n, r ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsmall : (n : ℝ) * r ^ 2 < 1 := by
      have hden : 0 < (2 * ((n : ℝ) + 1)) ^ 2 := by positivity
      have heq : (n : ℝ) * r ^ 2 = (n : ℝ) / (2 * ((n : ℝ) + 1)) ^ 2 := by
        dsimp only [r]
        field_simp
      rw [heq]
      apply (div_lt_iff₀ hden).mpr
      nlinarith only [sq_nonneg (n : ℝ), hn]
    have hnorm : ‖WithLp.toLp 2 x‖ ^ 2 ≤ (n : ℝ) * r ^ 2 := by
      simpa only [PiLp.norm_sq_eq_of_L2] using hsum
    change ‖WithLp.toLp 2 x - (0 : Domain n)‖ < 1
    rw [sub_zero]
    nlinarith only [hnorm, hsmall, norm_nonneg (WithLp.toLp 2 x)]
  have hpres : volume ((WithLp.toLp 2) ⁻¹' ball (0 : Domain n) 1) =
      volume (ball (0 : Domain n) 1) :=
    (PiLp.volume_preserving_toLp (Fin n)).measure_preimage measurableSet_ball.nullMeasurableSet
  have hmeasure : volume C ≤ volume (ball (0 : Domain n) 1) :=
    (measure_mono hC).trans_eq hpres
  have hvol : (volume C).toReal = (1 / ((n : ℝ) + 1)) ^ n := by
    have hle : (fun _ : Fin n => -r) ≤ (fun _ => r) := fun _ => by linarith only [hr]
    rw [show C = Icc (fun _ : Fin n => -r) (fun _ => r) by rfl,
      Real.volume_Icc_pi_toReal hle]
    have hwidth : r - -r = 1 / ((n : ℝ) + 1) := by
      dsimp only [r]
      field_simp [ne_of_gt (show 0 < (n : ℝ) + 1 by positivity)]
      ring
    simp only [hwidth, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← hvol]
  exact ENNReal.toReal_mono measure_ball_ne_top hmeasure

theorem euclidean_unit_ball_inverse_volume_le (n : ℕ) :
    (volume.real (ball (0 : Domain n) 1))⁻¹ ≤ ((n : ℝ) + 1)^n := by
  have hsmall : 0 < (1 / ((n : ℝ) + 1)) ^ n := by positivity
  have H := one_div_le_one_div_of_le hsmall (euclidean_unit_ball_volume_lower_bound n)
  simpa only [one_div, inv_pow, inv_inv] using H

theorem euclidean_unit_ball_inverse_rpow_le (n : ℕ) (s : ℝ)
    (hs : 0 ≤ s) (hsOne : s ≤ 1) :
    (volume.real (ball (0 : Domain n) 1)) ^ (-s) ≤ 1 + ((n : ℝ) + 1)^n := by
  let V : ℝ := volume.real (ball (0 : Domain n) 1)
  have hV : 0 < V := ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 (by norm_num)).ne' measure_ball_ne_top
  have hInv : 0 ≤ V⁻¹ := inv_nonneg.mpr hV.le
  have hpower : V⁻¹ ^ s ≤ 1 + V⁻¹ := by
    by_cases hOne : V⁻¹ ≤ 1
    · exact (Real.rpow_le_one hInv hOne hs).trans (le_add_of_nonneg_right hInv)
    · exact (Real.rpow_le_self_of_one_le (not_le.mp hOne).le hsOne).trans
        (le_add_of_nonneg_left zero_le_one)
  have heq : V ^ (-s) = V⁻¹ ^ s := by
    rw [Real.rpow_neg hV.le, Real.inv_rpow hV.le]
  change V ^ (-s) ≤ _
  rw [heq]
  exact hpower.trans (add_le_add_right (euclidean_unit_ball_inverse_volume_le n) 1)

theorem euclidean_unit_ball_volume_upper_bound (n : ℕ) :
    volume.real (ball (0 : Domain n) 1) ≤ (2 : ℝ)^n := by
  let C : Set (Fin n → ℝ) := Icc (fun _ => -1) (fun _ => 1)
  have hsubset : (WithLp.toLp 2) ⁻¹' ball (0 : Domain n) 1 ⊆ C := by
    intro x hx
    have hxNorm : ‖WithLp.toLp 2 x‖ < 1 := by
      simpa only [mem_preimage, mem_ball, dist_zero_right] using hx
    have hcoord (i : Fin n) : |x i| ≤ 1 := by
      have H := PiLp.norm_apply_le (WithLp.toLp 2 x) i
      have H' : |x i| ≤ ‖WithLp.toLp 2 x‖ := by
        simpa only [Real.norm_eq_abs] using H
      exact H'.trans hxNorm.le
    exact ⟨fun i => (abs_le.mp (hcoord i)).1, fun i => (abs_le.mp (hcoord i)).2⟩
  have hpres : volume ((WithLp.toLp 2) ⁻¹' ball (0 : Domain n) 1) =
      volume (ball (0 : Domain n) 1) :=
    (PiLp.volume_preserving_toLp (Fin n)).measure_preimage measurableSet_ball.nullMeasurableSet
  have hmeasure : volume (ball (0 : Domain n) 1) ≤ volume C :=
    hpres.symm.trans_le (measure_mono hsubset)
  have hfin : volume C ≠ ⊤ := isCompact_Icc.measure_ne_top
  calc
    _ ≤ (volume C).toReal := ENNReal.toReal_mono hfin hmeasure
    _ = _ := by
      rw [show C = Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1) by rfl,
        Real.volume_Icc_pi_toReal (fun _ => by norm_num)]
      norm_num

end StationaryHarmonicMaps.Analysis

end

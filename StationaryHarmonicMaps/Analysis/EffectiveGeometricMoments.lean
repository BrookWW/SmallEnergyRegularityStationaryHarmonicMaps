module

public import StationaryHarmonicMaps.Analysis.GeometricTailLp
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Integer moment bounds for geometric tails with ratio at most one half

An exponential majorant bounds the actual shifted polynomial series in the
native moment theorem. The resulting coefficient is a computable integer.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

def geometricMomentMajorant (k : ℕ) : ℕ := 1 + 24 * 2^k * k.factorial

private theorem exp_half_le_seven_quarters : Real.exp (1/2 : ℝ) ≤ 7/4 := by
  have hsq : Real.exp (1/2 : ℝ)^2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hthree := Real.exp_one_lt_three
  have hpos := Real.exp_pos (1/2 : ℝ)
  nlinarith only [hsq, hthree, hpos]

theorem shifted_geometric_weight_le (k m : ℕ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρHalf : ρ ≤ 1/2) :
    ((m : ℝ)+2)^k * ρ^m ≤
      (3 * (2 : ℝ)^k * (k.factorial : ℝ)) * (7/8 : ℝ)^m := by
  let x : ℝ := ((m : ℝ)+2)/2
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hfac : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have Hpow := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp x hx k)
  have hlinear : (m : ℝ)+2 = 2*x := by dsimp only [x]; ring
  have hpoly : ((m : ℝ)+2)^k ≤ (2 : ℝ)^k * (k.factorial : ℝ) * Real.exp x := by
    rw [hlinear, mul_pow]
    exact (mul_le_mul_of_nonneg_left Hpow (by positivity)).trans_eq (by ring)
  have hexpEq : Real.exp x = Real.exp 1 * Real.exp (1/2 : ℝ)^m := by
    rw [show x = 1 + (m : ℝ)*(1/2 : ℝ) by dsimp only [x]; ring,
      Real.exp_add, Real.exp_nat_mul]
  have hexp : Real.exp x ≤ 3 * (7/4 : ℝ)^m := by
    rw [hexpEq]
    exact mul_le_mul Real.exp_one_lt_three.le
      (pow_le_pow_left₀ (Real.exp_pos _).le exp_half_le_seven_quarters m)
      (pow_nonneg (Real.exp_pos _).le _) (by norm_num)
  have hrho : ρ^m ≤ (1/2 : ℝ)^m := pow_le_pow_left₀ hρ hρHalf m
  calc
    _ ≤ ((2 : ℝ)^k * (k.factorial : ℝ) * Real.exp x) * ρ^m :=
      mul_le_mul_of_nonneg_right hpoly (pow_nonneg hρ m)
    _ ≤ ((2 : ℝ)^k * (k.factorial : ℝ) * (3 * (7/4 : ℝ)^m)) * (1/2 : ℝ)^m :=
      mul_le_mul (mul_le_mul_of_nonneg_left hexp (by positivity)) hrho
        (pow_nonneg hρ m) (by positivity)
    _ = _ := by
      rw [show (7/8 : ℝ)^m = (7/4 : ℝ)^m * (1/2 : ℝ)^m by rw [← mul_pow]; norm_num]
      ring

theorem shifted_geometric_series_le (k : ℕ) (ρ : ℝ)
    (hρ : 0 < ρ) (hρHalf : ρ ≤ 1/2) :
    (∑' m : ℕ, ((m : ℝ)+2)^k * ρ^m) ≤ 24 * (2 : ℝ)^k * (k.factorial : ℝ) := by
  have hρOne : ρ < 1 := by linarith only [hρHalf]
  have hs := summable_shifted_pow_mul_geometric k hρ hρOne
  have hg : Summable (fun m : ℕ => (7/8 : ℝ)^m) :=
    summable_geometric_of_norm_lt_one (by norm_num : ‖(7/8 : ℝ)‖ < 1)
  have hmaj := hg.mul_left (3 * (2 : ℝ)^k * (k.factorial : ℝ))
  have H := hs.tsum_le_tsum (fun m => shifted_geometric_weight_le k m ρ hρ.le hρHalf) hmaj
  calc
    _ ≤ ∑' m : ℕ, (3 * (2 : ℝ)^k * (k.factorial : ℝ)) * (7/8 : ℝ)^m := H
    _ = (3 * (2 : ℝ)^k * (k.factorial : ℝ)) * (1 - (7/8 : ℝ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(7/8 : ℝ)‖ < 1)]
    _ = _ := by norm_num; ring

theorem shiftedGeometricMomentConstant_le (k : ℕ) (ρ : ℝ)
    (hρ : 0 < ρ) (hρHalf : ρ ≤ 1/2) :
    shiftedGeometricMomentConstant k ρ ≤ (geometricMomentMajorant k : ℝ) := by
  have H := add_le_add_right (shifted_geometric_series_le k ρ hρ hρHalf) 1
  simpa only [shiftedGeometricMomentConstant, geometricMomentMajorant,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] using H

/-- The actual measurable field with the original geometric tail has its
integer moment bounded by the stated computable factorial coefficient. -/
theorem geometric_tail_integer_moment_effective (k : ℕ) (hk : 1 ≤ k)
    (ρ : ℝ) (hρ : 0 < ρ) (hρHalf : ρ ≤ 1/2)
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → E)
    (hf : AEStronglyMeasurable f μ) {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (htail : ∀ m : ℕ, μ {x | a * ((m : ℝ)+1) < ‖f x‖} ≤
      ENNReal.ofReal (M * ρ^m)) :
    MemLp f (k : ℝ≥0∞) μ ∧ Integrable (fun x => ‖f x‖^k) μ ∧
      (∫ x, ‖f x‖^k ∂μ) ≤ (geometricMomentMajorant k : ℝ) * a^k * (μ.real Set.univ + M) := by
  have hρOne : ρ < 1 := by linarith only [hρHalf]
  obtain ⟨C, _hC, hFormula, H⟩ := geometric_tail_integer_moment_explicit k hk ρ hρ hρOne
  obtain ⟨hmem, hI, hBound⟩ := H μ f hf ha hM htail
  have hCbound : C ≤ (geometricMomentMajorant k : ℝ) := by
    rw [hFormula]
    exact shiftedGeometricMomentConstant_le k ρ hρ hρHalf
  refine ⟨hmem, hI, hBound.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbound (pow_nonneg ha.le k))
    (add_nonneg ENNReal.toReal_nonneg hM)

end StationaryHarmonicMaps.Analysis

end

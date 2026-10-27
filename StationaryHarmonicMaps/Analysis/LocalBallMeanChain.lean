module

public import HarmonicMaps.Sobolev
public import StationaryHarmonicMaps.Analysis.MeanOscillation
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Actual local ball means and their damped dyadic comparison

Uniform oscillation on the original small balls bounds each true dyadic
mean difference. An actual dyadic radius comparable to the queried radius
and a contained outer-ball comparison then give the radius-damped bound.
-/

public section

open HarmonicMaps MeasureTheory Set Metric

namespace StationaryHarmonicMaps.Analysis

/-- Actual scalar means at the original dyadic radii differ by at most the number of genuine steps times the uniform original oscillation. -/
theorem scalar_ballMean_dyadic_difference_le {n : ℕ}
    (f : Domain n → ℝ) (x : Domain n) {R B : ℝ} (hR : 0<R)
    (hf : IntegrableOn f (Metric.ball x R) volume)
    (hOsc : ∀ r : ℝ,0<r → r≤R →
      (⨍ y in Metric.ball x r,|f y-(⨍ z in Metric.ball x r,f z)|)≤B) :
    ∀ k : ℕ,|(⨍ y in Metric.ball x (R*(1/2 : ℝ)^k),f y)-
      (⨍ y in Metric.ball x R,f y)|≤(k : ℝ)*(2 : ℝ)^n*B := by
  intro k
  induction k with
  | zero => simp only [pow_zero,mul_one,sub_self,abs_zero,Nat.cast_zero,zero_mul,le_refl]
  | succ k ih =>
      let r := R*(1/2 : ℝ)^k
      have hr : 0<r := mul_pos hR (pow_pos (by norm_num) k)
      have hrR : r≤R := mul_le_of_le_one_right hR.le
        (pow_le_one₀ (by norm_num : (0 : ℝ)≤1/2) (by norm_num))
      have hNext : R*(1/2 : ℝ)^(k+1)=r/2 := by dsimp only [r];rw [pow_succ];ring
      have hStep := norm_ballAverage_sub_le_meanOscillation f (half_pos hr) hr
        (Metric.ball_subset_ball (by linarith only [hr] : r/2≤r))
        (show r≤2*(r/2) by linarith)
        (hf.mono_set (Metric.ball_subset_ball hrR))
      have hStepBound : |(⨍ y in Metric.ball x (r/2),f y)-(⨍ y in Metric.ball x r,f y)|≤(2 : ℝ)^n*B := by
        simpa only [Real.norm_eq_abs] using hStep.trans
          (mul_le_mul_of_nonneg_left (hOsc r hr hrR) (by positivity))
      rw [hNext]
      calc
        _ ≤ |(⨍ y in Metric.ball x (r/2),f y)-(⨍ y in Metric.ball x r,f y)|+
            |(⨍ y in Metric.ball x r,f y)-(⨍ y in Metric.ball x R,f y)| := abs_sub_le _ _ _
        _ ≤ (2 : ℝ)^n*B+(k : ℝ)*(2 : ℝ)^n*B := add_le_add hStepBound ih
        _ = _ := by push_cast;ring

/-- Genuine local oscillation bounds control the original mean difference after multiplying by the small-to-reference radius ratio. -/
theorem local_ballMean_difference_damped_le {n : ℕ}
    (f : Domain n → ℝ) (a x : Domain n) {t r B : ℝ} (ht : 0<t) (hr : 0<r)
    (hrt : r≤2*t) (hxa : dist x a≤2*t) (hB : 0≤B)
    (hf : ∀ (z : Domain n) (s : ℝ),0<s → IntegrableOn f (Metric.ball z s) volume)
    (hOsc : ∀ (z : Domain n) (s : ℝ),0<s → s≤8*t →
      (⨍ y in Metric.ball z s,|f y-(⨍ v in Metric.ball z s,f v)|)≤B) :
    (r/t)*|(⨍ y in Metric.ball x r,f y)-(⨍ y in Metric.ball a (8*t),f y)|≤
      (2*(2 : ℝ)^n+2*(4 : ℝ)^n)*B := by
  have hTwo : 0<2*t := mul_pos (by norm_num) ht
  obtain ⟨k,hLower,hUpper⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr hTwo) ((div_le_one hTwo).mpr hrt)
    (by norm_num : (0 : ℝ)<1/2) (by norm_num : (1/2 : ℝ)<1)
  let ρ := 2*t*(1/2 : ℝ)^k
  have hρ : 0<ρ := mul_pos hTwo (pow_pos (by norm_num) k)
  have hρt : ρ≤2*t := mul_le_of_le_one_right hTwo.le
    (pow_le_one₀ (by norm_num : (0 : ℝ)≤1/2) (by norm_num))
  have hrρ : r≤ρ := by
    have H := (div_le_iff₀ hTwo).mp hUpper
    simpa only [ρ,mul_comm] using H
  have hρr : ρ≤2*r := by
    have H := (lt_div_iff₀ hTwo).mp hLower
    rw [pow_succ] at H
    dsimp only [ρ]
    nlinarith only [H]
  have hRatio : r/t≤2*(1/2 : ℝ)^k := by
    apply (div_le_iff₀ ht).mpr
    calc
      r ≤ ρ := hrρ
      _ = 2*(1/2 : ℝ)^k*t := by dsimp only [ρ];ring
  have hStep := norm_ballAverage_sub_le_meanOscillation f hr hρ
    (Metric.ball_subset_ball hrρ) hρr (hf x ρ hρ)
  have hStepB : |(⨍ y in Metric.ball x r,f y)-(⨍ y in Metric.ball x ρ,f y)|≤(2 : ℝ)^n*B := by
    simpa only [Real.norm_eq_abs] using hStep.trans
      (mul_le_mul_of_nonneg_left (hOsc x ρ hρ (hρt.trans (by linarith))) (by positivity))
  have hDyadic := scalar_ballMean_dyadic_difference_le f x hTwo (hf x (2*t) hTwo)
    (fun s hs hsR=>hOsc x s hs (hsR.trans (by linarith))) k
  have hSub : Metric.ball x (2*t)⊆Metric.ball a (8*t) := by
    intro y hy
    exact (dist_triangle y x a).trans_lt (by have H : dist y x<2*t := hy;linarith only [H,hxa,ht])
  have hOuter := norm_ballAverage_sub_le_meanOscillation f hTwo (by positivity : 0<8*t)
    hSub (show 8*t≤4*(2*t) by linarith) (hf a (8*t) (by positivity))
  have hOuterB : |(⨍ y in Metric.ball x (2*t),f y)-(⨍ y in Metric.ball a (8*t),f y)|≤(4 : ℝ)^n*B := by
    simpa only [Real.norm_eq_abs] using hOuter.trans
      (mul_le_mul_of_nonneg_left (hOsc a (8*t) (by positivity) le_rfl) (by positivity))
  have hDifference : |(⨍ y in Metric.ball x r,f y)-(⨍ y in Metric.ball a (8*t),f y)|≤
      (((k : ℝ)+1)*(2 : ℝ)^n+(4 : ℝ)^n)*B := by
    have H₁ := abs_sub_le (⨍ y in Metric.ball x r,f y) (⨍ y in Metric.ball x ρ,f y)
      (⨍ y in Metric.ball a (8*t),f y)
    have H₂ := abs_sub_le (⨍ y in Metric.ball x ρ,f y) (⨍ y in Metric.ball x (2*t),f y)
      (⨍ y in Metric.ball a (8*t),f y)
    have hD : |(⨍ y in Metric.ball x ρ,f y)-(⨍ y in Metric.ball x (2*t),f y)|≤(k : ℝ)*(2 : ℝ)^n*B := hDyadic
    linarith only [H₁,H₂,hStepB,hD,hOuterB]
  have hNatGeneral (j : ℕ) : (j : ℝ)+1≤(2 : ℝ)^j := by
    induction j with
    | zero => norm_num
    | succ j ih =>
        rw [pow_succ,Nat.cast_add,Nat.cast_one]
        have hPos : 1≤(2 : ℝ)^j := one_le_pow₀ (by norm_num)
        linarith only [ih,hPos]
  have hNat := hNatGeneral k
  have hDamp : ((k : ℝ)+1)*(1/2 : ℝ)^k≤1 := by
    calc
      _ ≤ (2 : ℝ)^k*(1/2 : ℝ)^k := mul_le_mul_of_nonneg_right hNat (by positivity)
      _ = 1 := by rw [← mul_pow];norm_num
  have hHalf : (1/2 : ℝ)^k≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hCore : 2*(1/2 : ℝ)^k*(((k : ℝ)+1)*(2 : ℝ)^n+(4 : ℝ)^n)≤2*(2 : ℝ)^n+2*(4 : ℝ)^n := by
    calc
      _ = (2*(2 : ℝ)^n)*(((k : ℝ)+1)*(1/2 : ℝ)^k)+(2*(4 : ℝ)^n)*(1/2 : ℝ)^k := by ring
      _ ≤ (2*(2 : ℝ)^n)*1+(2*(4 : ℝ)^n)*1 := add_le_add
        (mul_le_mul_of_nonneg_left hDamp (by positivity))
        (mul_le_mul_of_nonneg_left hHalf (by positivity))
      _ = _ := by ring
  calc
    _ ≤ (r/t)*((((k : ℝ)+1)*(2 : ℝ)^n+(4 : ℝ)^n)*B) :=
      mul_le_mul_of_nonneg_left hDifference (div_nonneg hr.le ht.le)
    _ ≤ (2*(1/2 : ℝ)^k)*((((k : ℝ)+1)*(2 : ℝ)^n+(4 : ℝ)^n)*B) :=
      mul_le_mul_of_nonneg_right hRatio (by positivity)
    _ ≤ _ := by rw [← mul_assoc];exact mul_le_mul_of_nonneg_right hCore hB

end StationaryHarmonicMaps.Analysis

end

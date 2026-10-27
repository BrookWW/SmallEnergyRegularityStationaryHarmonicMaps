module

public import HarmonicMaps.Analysis.IterationScales
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Scalar iteration over every positive radius

Successive geometric radii bracket each radius below the reference scale.
Monotonicity transfers a discrete power bound to all radii. Homogeneous and
inhomogeneous recurrences are proved without division by the initial mass.
-/

public section

open HarmonicMaps

namespace HolderToCK

theorem all_radius_decay_of_geometric_bound (f : ℝ → ℝ)
    {θ r₀ ν B E : ℝ} (hθ : 0 < θ) (hθOne : θ < 1) (hr₀ : 0 < r₀)
    (hν : 0 ≤ ν) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hmono : ∀ r s : ℝ, 0 < r → r ≤ s → s ≤ r₀ → f r ≤ f s)
    (hdiscrete : ∀ k : ℕ, f (θ ^ k * r₀) ≤ B * E * (θ ^ k * r₀) ^ ν) :
    ∀ r : ℝ, 0 < r → r ≤ r₀ → f r ≤ θ ^ (-ν) * B * E * r ^ ν := by
  intro r hr hrr₀
  obtain ⟨k, hLower, hUpper⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr hr₀) ((div_le_one hr₀).mpr hrr₀) hθ hθOne
  have hkr : 0 < θ ^ k * r₀ := mul_pos (pow_pos hθ k) hr₀
  have hrk : r ≤ θ ^ k * r₀ := (div_le_iff₀ hr₀).mp hUpper
  have hk₀ : θ ^ k * r₀ ≤ r₀ :=
    mul_le_of_le_one_left hr₀.le (pow_le_one₀ hθ.le hθOne.le)
  have hθkr : θ * (θ ^ k * r₀) < r := by
    have hl := (lt_div_iff₀ hr₀).mp hLower
    rw [pow_succ] at hl
    nlinarith only [hl]
  have hPower := Real.rpow_le_rpow (mul_pos hθ hkr).le hθkr.le hν
  have hscale : (θ ^ k * r₀) ^ ν ≤ θ ^ (-ν) * r ^ ν := by
    have hmul := mul_le_mul_of_nonneg_left hPower (Real.rpow_nonneg hθ.le (-ν))
    rw [Real.mul_rpow hθ.le hkr.le, ← mul_assoc, ← Real.rpow_add hθ,
      neg_add_cancel, Real.rpow_zero, one_mul] at hmul
    exact hmul
  calc
    f r ≤ f (θ ^ k * r₀) := hmono r _ hr hrk hk₀
    _ ≤ B * E * (θ ^ k * r₀) ^ ν := hdiscrete k
    _ ≤ B * E * (θ ^ (-ν) * r ^ ν) :=
      mul_le_mul_of_nonneg_left hscale (mul_nonneg hB hE)
    _ = θ ^ (-ν) * B * E * r ^ ν := by ring

theorem all_radius_decay_of_homogeneous_recurrence (f : ℝ → ℝ)
    {θ r₀ ell E : ℝ} (hθ : 0 < θ) (hθOne : θ < 1) (hr₀ : 0 < r₀)
    (hell : 0 ≤ ell) (hE : 0 ≤ E)
    (hmono : ∀ r s : ℝ, 0 < r → r ≤ s → s ≤ r₀ → f r ≤ f s)
    (hbase : f r₀ ≤ E)
    (hstep : ∀ r : ℝ, 0 < r → r ≤ r₀ → f (θ * r) ≤ θ ^ ell * f r) :
    ∀ r : ℝ, 0 < r → r ≤ r₀ →
      f r ≤ θ ^ (-ell) * r₀ ^ (-ell) * E * r ^ ell := by
  have hproduct : r₀ ^ (-ell) * r₀ ^ ell = 1 := by
    rw [← Real.rpow_add hr₀, neg_add_cancel, Real.rpow_zero]
  have hdiscrete : ∀ k : ℕ,
      f (θ ^ k * r₀) ≤ r₀ ^ (-ell) * E * (θ ^ k * r₀) ^ ell := by
    intro k
    induction k with
    | zero =>
        simpa only [pow_zero, one_mul, ← mul_assoc, mul_right_comm _ E,
          hproduct, one_mul] using hbase
    | succ k ih =>
        have hkr : 0 < θ ^ k * r₀ := mul_pos (pow_pos hθ k) hr₀
        have hk₀ : θ ^ k * r₀ ≤ r₀ :=
          mul_le_of_le_one_left hr₀.le (pow_le_one₀ hθ.le hθOne.le)
        have hnext : θ ^ (k + 1) * r₀ = θ * (θ ^ k * r₀) := by rw [pow_succ]; ring
        rw [hnext, Real.mul_rpow hθ.le hkr.le]
        calc
          _ ≤ θ ^ ell * f (θ ^ k * r₀) := hstep _ hkr hk₀
          _ ≤ θ ^ ell * (r₀ ^ (-ell) * E * (θ ^ k * r₀) ^ ell) :=
            mul_le_mul_of_nonneg_left ih (Real.rpow_nonneg hθ.le ell)
          _ = _ := by ring
  exact all_radius_decay_of_geometric_bound f hθ hθOne hr₀ hell
    (Real.rpow_nonneg hr₀.le (-ell)) hE hmono hdiscrete

theorem all_radius_decay_of_inhomogeneous_recurrence (f : ℝ → ℝ)
    {θ r₀ ν μ A E : ℝ} (hθ : 0 < θ) (hθOne : θ < 1) (hr₀ : 0 < r₀)
    (hν : 0 ≤ ν) (hμν : ν < μ) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hmono : ∀ r s : ℝ, 0 < r → r ≤ s → s ≤ r₀ → f r ≤ f s)
    (hbase : f r₀ ≤ E)
    (hstep : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      f (θ * r) ≤ (1 / 2 : ℝ) * θ ^ ν * f r + A * E * r ^ μ) :
    ∀ r : ℝ, 0 < r → r ≤ r₀ →
      f r ≤ θ ^ (-ν) * (r₀ ^ (-ν) + 2 * A * θ ^ (-ν) * r₀ ^ (μ - ν)) * E * r ^ ν := by
  let B : ℝ := r₀ ^ (-ν) + 2 * A * θ ^ (-ν) * r₀ ^ (μ - ν)
  have hθprod : θ ^ (-ν) * θ ^ ν = 1 := by
    rw [← Real.rpow_add hθ, neg_add_cancel, Real.rpow_zero]
  have hrprod : r₀ ^ (-ν) * r₀ ^ ν = 1 := by
    rw [← Real.rpow_add hr₀, neg_add_cancel, Real.rpow_zero]
  have hterm : 0 ≤ 2 * A * θ ^ (-ν) * r₀ ^ (μ - ν) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) (Real.rpow_nonneg hθ.le _))
      (Real.rpow_nonneg hr₀.le _)
  have hBge : r₀ ^ (-ν) ≤ B := le_add_of_nonneg_right hterm
  have hB : 0 ≤ B := (Real.rpow_nonneg hr₀.le _).trans hBge
  have hBcoef : 2 * A * r₀ ^ (μ - ν) ≤ B * θ ^ ν := by
    have heq : B * θ ^ ν =
        r₀ ^ (-ν) * θ ^ ν + 2 * A * r₀ ^ (μ - ν) := by
      calc
        _ = r₀ ^ (-ν) * θ ^ ν +
            (2 * A * r₀ ^ (μ - ν)) * (θ ^ (-ν) * θ ^ ν) := by dsimp only [B]; ring
        _ = _ := by rw [hθprod, mul_one]
    rw [heq]
    exact le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hr₀.le _) (Real.rpow_nonneg hθ.le _))
  have hcoefficient : (1 / 2 : ℝ) * θ ^ ν * B + A * r₀ ^ (μ - ν) ≤ B * θ ^ ν := by
    linarith only [hBcoef]
  have hdiscrete : ∀ k : ℕ, f (θ ^ k * r₀) ≤ B * E * (θ ^ k * r₀) ^ ν := by
    intro k
    induction k with
    | zero =>
        simp only [pow_zero, one_mul]
        calc
          f r₀ ≤ E := hbase
          _ = r₀ ^ (-ν) * E * r₀ ^ ν := by
            rw [mul_right_comm _ E, hrprod, one_mul]
          _ ≤ B * E * r₀ ^ ν := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hBge hE) (Real.rpow_nonneg hr₀.le _)
    | succ k ih =>
        let s := θ ^ k * r₀
        have hs : 0 < s := mul_pos (pow_pos hθ k) hr₀
        have hs₀ : s ≤ r₀ :=
          mul_le_of_le_one_left hr₀.le (pow_le_one₀ hθ.le hθOne.le)
        have hnext : θ ^ (k + 1) * r₀ = θ * s := by dsimp only [s]; rw [pow_succ]; ring
        have hsplit : s ^ μ = s ^ ν * s ^ (μ - ν) := by
          rw [← Real.rpow_add hs]
          congr 1
          ring
        have hgap := Real.rpow_le_rpow hs.le hs₀ (sub_pos.mpr hμν).le
        have herr : A * E * s ^ μ ≤ A * E * (s ^ ν * r₀ ^ (μ - ν)) := by
          rw [hsplit]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hgap (Real.rpow_nonneg hs.le _)) (mul_nonneg hA hE)
        rw [hnext, Real.mul_rpow hθ.le hs.le]
        calc
          f (θ * s) ≤ (1 / 2 : ℝ) * θ ^ ν * f s + A * E * s ^ μ := hstep s hs hs₀
          _ ≤ (1 / 2 : ℝ) * θ ^ ν * (B * E * s ^ ν) + A * E * (s ^ ν * r₀ ^ (μ - ν)) :=
            add_le_add (mul_le_mul_of_nonneg_left ih
              (mul_nonneg (by norm_num) (Real.rpow_nonneg hθ.le _))) herr
          _ = ((1 / 2 : ℝ) * θ ^ ν * B + A * r₀ ^ (μ - ν)) * E * s ^ ν := by ring
          _ ≤ (B * θ ^ ν) * E * s ^ ν := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoefficient hE) (Real.rpow_nonneg hs.le _)
          _ = _ := by ring
  exact all_radius_decay_of_geometric_bound f hθ hθOne hr₀ hν hB hE hmono hdiscrete

end HolderToCK
end

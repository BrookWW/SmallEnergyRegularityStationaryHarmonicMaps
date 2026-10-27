module

public import StationaryHarmonicMaps.Analysis.GeometricIteration

/-! # Equal-power forcing in a geometric radius recurrence

The original unweighted monotone quantity is iterated. No finiteness or
monotonicity of a normalized supremum is required.
-/

public section

namespace StationaryHarmonicMaps

theorem geometric_radius_power_bound (f : ℝ → ℝ) (d : ℕ)
    {θ ρ A B r₀ : ℝ} (hθ : 0 < θ) (hθOne : θ < 1)
    (hρ : 0 ≤ ρ) (hρθ : ρ < θ ^ d) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hr₀ : 0 < r₀) (hbase : f r₀ ≤ B * r₀ ^ d)
    (hstep : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      f (θ * r) ≤ ρ * f r + A * r ^ d) :
    ∀ k : ℕ, f (θ ^ k * r₀) ≤
      (B + A / (θ ^ d - ρ)) * (θ ^ k * r₀) ^ d := by
  let C := B + A / (θ ^ d - ρ)
  have hgap : 0 < θ ^ d - ρ := sub_pos.mpr hρθ
  have hBC : B ≤ C := le_add_of_nonneg_right (div_nonneg hA hgap.le)
  have habsorb : ρ * C + A ≤ θ ^ d * C := by
    have hcancel : (θ ^ d - ρ) * (A / (θ ^ d - ρ)) = A := by
      field_simp [hgap.ne']
    have hprod : 0 ≤ (θ ^ d - ρ) * B := mul_nonneg hgap.le hB
    dsimp only [C]
    nlinarith only [hcancel, hprod]
  intro k
  induction k with
  | zero =>
      simp only [pow_zero, one_mul]
      exact hbase.trans (mul_le_mul_of_nonneg_right hBC (pow_nonneg hr₀.le d))
  | succ k ih =>
      have hkr : 0 < θ ^ k * r₀ := mul_pos (pow_pos hθ k) hr₀
      have hkr₀ : θ ^ k * r₀ ≤ r₀ :=
        mul_le_of_le_one_left hr₀.le (pow_le_one₀ hθ.le hθOne.le)
      have hnext : θ ^ (k + 1) * r₀ = θ * (θ ^ k * r₀) := by
        rw [pow_succ]
        ring
      rw [hnext, mul_pow]
      calc
        f (θ * (θ ^ k * r₀)) ≤
            ρ * f (θ ^ k * r₀) + A * (θ ^ k * r₀) ^ d := hstep _ hkr hkr₀
        _ ≤ ρ * (C * (θ ^ k * r₀) ^ d) + A * (θ ^ k * r₀) ^ d :=
          add_le_add (mul_le_mul_of_nonneg_left ih hρ) le_rfl
        _ = (ρ * C + A) * (θ ^ k * r₀) ^ d := by ring
        _ ≤ (θ ^ d * C) * (θ ^ k * r₀) ^ d :=
          mul_le_mul_of_nonneg_right habsorb (pow_nonneg hkr.le d)
        _ = C * (θ ^ d * (θ ^ k * r₀) ^ d) := by ring

theorem all_radius_power_bound_of_recurrence (f : ℝ → ℝ) (d : ℕ)
    {θ ρ A B r₀ : ℝ} (hθ : 0 < θ) (hθOne : θ < 1)
    (hρ : 0 ≤ ρ) (hρθ : ρ < θ ^ d) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hr₀ : 0 < r₀)
    (hmono : ∀ r s : ℝ, 0 < r → r ≤ s → s ≤ r₀ → f r ≤ f s)
    (hbase : f r₀ ≤ B * r₀ ^ d)
    (hstep : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      f (θ * r) ≤ ρ * f r + A * r ^ d) :
    ∀ r : ℝ, 0 < r → r ≤ r₀ →
      f r ≤ ((B + A / (θ ^ d - ρ)) / θ ^ d) * r ^ d := by
  intro r hr hrr₀
  let C := B + A / (θ ^ d - ρ)
  have hC : 0 ≤ C := add_nonneg hB (div_nonneg hA (sub_pos.mpr hρθ).le)
  obtain ⟨k, hLower, hUpper⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr hr₀) ((div_le_one hr₀).mpr hrr₀) hθ hθOne
  have hkr : 0 < θ ^ k * r₀ := mul_pos (pow_pos hθ k) hr₀
  have hrk : r ≤ θ ^ k * r₀ := (div_le_iff₀ hr₀).mp hUpper
  have hk₀ : θ ^ k * r₀ ≤ r₀ :=
    mul_le_of_le_one_left hr₀.le (pow_le_one₀ hθ.le hθOne.le)
  have hbracket : θ * (θ ^ k * r₀) < r := by
    have hl := (lt_div_iff₀ hr₀).mp hLower
    rw [pow_succ] at hl
    nlinarith only [hl]
  have hscale : θ ^ k * r₀ ≤ r / θ :=
    (le_div_iff₀ hθ).mpr (by nlinarith only [hbracket])
  calc
    f r ≤ f (θ ^ k * r₀) := hmono _ _ hr hrk hk₀
    _ ≤ C * (θ ^ k * r₀) ^ d :=
      geometric_radius_power_bound f d hθ hθOne hρ hρθ hA hB hr₀ hbase hstep k
    _ ≤ C * (r / θ) ^ d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hkr.le hscale d) hC
    _ = (C / θ ^ d) * r ^ d := by rw [div_pow]; ring

end StationaryHarmonicMaps
end

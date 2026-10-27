module

public import StationaryHarmonicMaps.Analysis.GeometricIteration

/-! # Equal real-power forcing in geometric radius iteration

Iteration applies to the original unweighted monotone quantity. The all-radius
bound uses a nonnegative exponent; no normalized supremum is assumed finite.
-/

public section

namespace StationaryHarmonicMaps

theorem geometric_radius_rpow_bound (f : ℝ → ℝ) {ν θ ρ A B r₀ : ℝ}
    (hθ : 0<θ) (hθOne : θ<1) (hρ : 0≤ρ) (hρθ : ρ<θ^ν)
    (hA : 0≤A) (hB : 0≤B) (hr₀ : 0<r₀)
    (hbase : f r₀≤B*r₀^ν)
    (hstep : ∀ r : ℝ,0<r → r≤r₀ → f (θ*r)≤ρ*f r+A*r^ν) :
    ∀ k : ℕ,f (θ^k*r₀)≤(B+A/(θ^ν-ρ))*(θ^k*r₀)^ν := by
  let C := B+A/(θ^ν-ρ)
  have hgap : 0<θ^ν-ρ := sub_pos.mpr hρθ
  have hBC : B≤C := le_add_of_nonneg_right (div_nonneg hA hgap.le)
  have hAbsorb : ρ*C+A≤θ^ν*C := by
    have hCancel : (θ^ν-ρ)*(A/(θ^ν-ρ))=A := by field_simp [hgap.ne']
    have hProd : 0≤(θ^ν-ρ)*B := mul_nonneg hgap.le hB
    dsimp only [C]
    nlinarith only [hCancel,hProd]
  intro k
  induction k with
  | zero =>
      simp only [pow_zero,one_mul]
      exact hbase.trans (mul_le_mul_of_nonneg_right hBC (Real.rpow_nonneg hr₀.le _))
  | succ k ih =>
      have hkr : 0<θ^k*r₀ := mul_pos (pow_pos hθ k) hr₀
      have hk₀ : θ^k*r₀≤r₀ := mul_le_of_le_one_left hr₀.le (pow_le_one₀ hθ.le hθOne.le)
      have hNext : θ^(k+1)*r₀=θ*(θ^k*r₀) := by rw [pow_succ];ring
      rw [hNext,Real.mul_rpow hθ.le hkr.le]
      calc
        _ ≤ ρ*f (θ^k*r₀)+A*(θ^k*r₀)^ν := hstep _ hkr hk₀
        _ ≤ ρ*(C*(θ^k*r₀)^ν)+A*(θ^k*r₀)^ν :=
          add_le_add (mul_le_mul_of_nonneg_left ih hρ) le_rfl
        _ = (ρ*C+A)*(θ^k*r₀)^ν := by ring
        _ ≤ (θ^ν*C)*(θ^k*r₀)^ν :=
          mul_le_mul_of_nonneg_right hAbsorb (Real.rpow_nonneg hkr.le _)
        _ = C*(θ^ν*(θ^k*r₀)^ν) := by ring

theorem all_radius_rpow_bound_of_recurrence (f : ℝ → ℝ) {ν θ ρ A B r₀ : ℝ}
    (hν : 0≤ν) (hθ : 0<θ) (hθOne : θ<1) (hρ : 0≤ρ) (hρθ : ρ<θ^ν)
    (hA : 0≤A) (hB : 0≤B) (hr₀ : 0<r₀)
    (hmono : ∀ r s : ℝ,0<r → r≤s → s≤r₀ → f r≤f s)
    (hbase : f r₀≤B*r₀^ν)
    (hstep : ∀ r : ℝ,0<r → r≤r₀ → f (θ*r)≤ρ*f r+A*r^ν) :
    ∀ r : ℝ,0<r → r≤r₀ → f r≤((B+A/(θ^ν-ρ))/θ^ν)*r^ν := by
  intro r hr hrr₀
  let C := B+A/(θ^ν-ρ)
  have hC : 0≤C := add_nonneg hB (div_nonneg hA (sub_pos.mpr hρθ).le)
  obtain ⟨k,hLower,hUpper⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr hr₀) ((div_le_one hr₀).mpr hrr₀) hθ hθOne
  have hkr : 0<θ^k*r₀ := mul_pos (pow_pos hθ k) hr₀
  have hrk : r≤θ^k*r₀ := (div_le_iff₀ hr₀).mp hUpper
  have hk₀ : θ^k*r₀≤r₀ := mul_le_of_le_one_left hr₀.le (pow_le_one₀ hθ.le hθOne.le)
  have hBracket : θ*(θ^k*r₀)<r := by
    have H := (lt_div_iff₀ hr₀).mp hLower
    rw [pow_succ] at H
    nlinarith only [H]
  have hScale : θ^k*r₀≤r/θ := (le_div_iff₀ hθ).mpr (by nlinarith only [hBracket])
  calc
    f r≤f (θ^k*r₀) := hmono _ _ hr hrk hk₀
    _ ≤ C*(θ^k*r₀)^ν := geometric_radius_rpow_bound f hθ hθOne hρ hρθ hA hB hr₀ hbase hstep k
    _ ≤ C*(r/θ)^ν := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hkr.le hScale hν) hC
    _ = (C/θ^ν)*r^ν := by rw [Real.div_rpow hr.le hθ.le];ring

end StationaryHarmonicMaps
end

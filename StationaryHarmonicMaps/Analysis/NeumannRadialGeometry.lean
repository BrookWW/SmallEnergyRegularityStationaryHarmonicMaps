module

public import StationaryHarmonicMaps.Analysis.NeumannKelvinAdjointGeometry

/-!
# Exact radial sample domains for Neumann reflection

The original exterior samples remain in the same sphere-centered ball.
The dilation-variable inequalities give the exact exchanged integration
domain; endpoints are retained explicitly.
-/

public section

open HarmonicMaps Set Metric

namespace StationaryHarmonicMaps.Analysis

/-- A radial sample between the inverse radius and the sphere is no farther from any original sphere center than the exterior point. -/
theorem dist_neumann_reflection_sample_le {n : ℕ}
    (a x : Domain n) (ha : ‖a‖=1) (hx : 1≤‖x‖)
    (t : ℝ) (htLow : (‖x‖^2)⁻¹≤t) (htHigh : t≤‖x‖⁻¹) :
    dist (t • x) a≤dist x a := by
  have hr : 0<‖x‖ := zero_lt_one.trans_le hx
  have ht : 0<t := (inv_pos.mpr (sq_pos_of_pos hr)).trans_le htLow
  have htOne : t≤1 := htHigh.trans ((inv_le_one₀ hr).mpr hx)
  have hθ : ‖‖x‖⁻¹ • x‖=1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),inv_mul_cancel₀ hr.ne']
  have hProd : 1≤(t*‖x‖)*‖x‖ := by
    have H := (div_le_iff₀ (sq_pos_of_pos hr)).mp (show 1/(‖x‖^2)≤t by simpa only [one_div] using htLow)
    nlinarith only [H]
  have H := dist_radial_le_of_radius_product a (‖x‖⁻¹ • x) ha hθ (t*‖x‖) ‖x‖
    (mul_nonneg ht.le hr.le) (by nlinarith only [htOne,hr.le]) hProd
  simpa only [smul_smul,mul_assoc,mul_inv_cancel₀ hr.ne',mul_one,one_smul] using H

/-- Every actual exterior radial sample stays in the original boundary cap. -/
theorem neumann_reflection_sample_mem_boundary_ball {n : ℕ}
    (a x : Domain n) (s : ℝ) (ha : ‖a‖=1) (hx : 1≤‖x‖) (hCap : x∈ball a s)
    (t : ℝ) (htLow : (‖x‖^2)⁻¹≤t) (htHigh : t≤‖x‖⁻¹) : t • x∈ball a s :=
  mem_ball.mpr ((dist_neumann_reflection_sample_le a x ha hx t htLow htHigh).trans_lt hCap)

/-- The positive dilation change of variables gives the exact radial integration window, including its ordered endpoints. -/
theorem neumann_radial_window_swap (r t : ℝ) (hr : 0<r) (ht : 0<t) :
    (1<r ∧ r<2 ∧ (r^2)⁻¹≤t ∧ t≤r⁻¹) ↔
      (t*r/2<t ∧ t<t*r ∧ t≤(t*r)^2 ∧ t*r≤1) := by
  constructor
  · rintro ⟨hrOne,hrTwo,hLow,hHigh⟩
    have hLow' := (div_le_iff₀ (sq_pos_of_pos hr)).mp (show 1/r^2≤t by simpa only [one_div] using hLow)
    have hLowT := mul_le_mul_of_nonneg_left hLow' ht.le
    have hHigh' := (le_div_iff₀ hr).mp (show t≤1/r by simpa only [one_div] using hHigh)
    refine ⟨?_,?_,?_,hHigh'⟩
    · nlinarith only [mul_lt_mul_of_pos_left hrTwo ht]
    · nlinarith only [mul_lt_mul_of_pos_left hrOne ht]
    · nlinarith only [hLowT]
  · rintro ⟨hHalf,hLess,hSquare,hOne⟩
    have hrOne : 1<r := by nlinarith only [hLess,ht]
    have hrTwo : r<2 := by nlinarith only [hHalf,ht]
    refine ⟨hrOne,hrTwo,?_,?_⟩
    · have H : t*1≤t*(t*r^2) := by nlinarith only [hSquare]
      have H1 : 1≤t*r^2 := (mul_le_mul_iff_right₀ ht).mp H
      simpa only [one_div] using (div_le_iff₀ (sq_pos_of_pos hr)).mpr H1
    · simpa only [one_div] using (le_div_iff₀ hr).mpr hOne


/-- Inside the original unit ball the exchanged dilation window is exactly the interval from half the radius to its square. -/
theorem neumann_radial_window_after_dilation {n : ℕ} (y : Domain n) (hy : y≠0)
    (hyOne : ‖y‖<1) (t : ℝ) (ht : 0<t) :
    (1<‖t⁻¹ • y‖ ∧ ‖t⁻¹ • y‖<2 ∧ (‖t⁻¹ • y‖^2)⁻¹≤t ∧ t≤‖t⁻¹ • y‖⁻¹) ↔
      (‖y‖/2<t ∧ t≤‖y‖^2) := by
  have hyPos : 0<‖y‖ := norm_pos_iff.mpr hy
  have hNorm : ‖t⁻¹ • y‖=t⁻¹*‖y‖ := by rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
  have hR : 0<‖t⁻¹ • y‖ := by rw [hNorm];positivity
  have htr : t*‖t⁻¹ • y‖=‖y‖ := by rw [hNorm,← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
  rw [neumann_radial_window_swap _ t hR ht,htr]
  constructor
  · rintro ⟨hHalf,_hLess,hSq,_hOne⟩
    exact ⟨hHalf,hSq⟩
  · rintro ⟨hHalf,hSq⟩
    refine ⟨hHalf,?_,hSq,hyOne.le⟩
    nlinarith only [hSq,mul_lt_mul_of_pos_left hyOne hyPos]

/-- Equal powers in the reflected tangential-gradient weight cancel their dilation factor exactly. -/
theorem neumann_radial_equal_power_weight {n : ℕ} (y : Domain n) (t : ℝ)
    (ht : 0<t) (a : ℕ) : ‖t⁻¹ • y‖^a*t^a=‖y‖^a := by
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ht.le),← mul_pow]
  congr 1
  rw [mul_right_comm,inv_mul_cancel₀ ht.ne',one_mul]

end StationaryHarmonicMaps.Analysis

end

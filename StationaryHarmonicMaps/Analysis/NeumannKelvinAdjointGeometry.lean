module

public import StationaryHarmonicMaps.Analysis.BoundaryInversionGeometry
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Localization of the actual Neumann adjoint radial samples

Every outward sample beyond the inverse radius lies at least as far from
an original unit-sphere center as the original interior point. A compact
test supported in a sphere-centered ball therefore contributes only to
the same interior ball in the Neumann Kelvin adjoint.
-/

public section

open HarmonicMaps MeasureTheory Set Metric

namespace StationaryHarmonicMaps.Analysis

/-- Radial points whose radius product is at least one have the actual distance ordering from each unit-sphere center. -/
theorem dist_radial_le_of_radius_product {n : ℕ}
    (a θ : Domain n) (ha : ‖a‖=1) (hθ : ‖θ‖=1)
    (r t : ℝ) (hr : 0≤r) (hrt : r≤t) (hprod : 1≤r*t) :
    dist (r • θ) a ≤ dist (t • θ) a := by
  have ht : 0≤t := hr.trans hrt
  have hInner : inner ℝ θ a≤1 := by
    simpa only [ha,hθ,one_mul] using real_inner_le_norm θ a
  have hSum : 2≤r+t := by
    nlinarith only [sq_nonneg (r-t),hprod,hr,ht]
  have hFactor : 0≤(t-r)*(t+r-2*inner ℝ θ a) :=
    mul_nonneg (sub_nonneg.mpr hrt) (by linarith only [hInner,hSum])
  have hR : dist (r • θ) a^2=r^2+1-2*r*inner ℝ θ a := by
    rw [dist_eq_norm,norm_sub_sq_real,norm_smul,Real.norm_of_nonneg hr,hθ,ha,
      mul_one,one_pow,real_inner_smul_left]
    ring
  have hT : dist (t • θ) a^2=t^2+1-2*t*inner ℝ θ a := by
    rw [dist_eq_norm,norm_sub_sq_real,norm_smul,Real.norm_of_nonneg ht,hθ,ha,
      mul_one,one_pow,real_inner_smul_left]
    ring
  nlinarith only [hR,hT,hFactor,dist_nonneg (x:=r • θ) (y:=a),dist_nonneg (x:=t • θ) (y:=a)]

/-- Every outward adjoint sample beyond the actual inverse radius retains the original sphere-centered localization. -/
theorem dist_le_neumann_adjoint_radial_sample {n : ℕ}
    (a y : Domain n) (ha : ‖a‖=1) (hy : y≠0) (hyOne : ‖y‖≤1)
    (t : ℝ) (ht : ‖y‖⁻¹≤t) :
    dist y a≤dist (t • (‖y‖⁻¹ • y)) a := by
  have hyPos : 0<‖y‖ := norm_pos_iff.mpr hy
  have hθ : ‖‖y‖⁻¹ • y‖=1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hyPos.le),inv_mul_cancel₀ hyPos.ne']
  have htOne : 1≤t := ((one_le_inv₀ hyPos).mpr hyOne).trans ht
  have hProd : 1≤‖y‖*t := by
    have H := mul_le_mul_of_nonneg_left ht hyPos.le
    rwa [mul_inv_cancel₀ hyPos.ne'] at H
  have H := dist_radial_le_of_radius_product a (‖y‖⁻¹ • y) ha hθ ‖y‖ t
    hyPos.le (hyOne.trans htOne) hProd
  simpa only [smul_smul,mul_inv_cancel₀ hyPos.ne',one_smul] using H

/-- A test supported in an original sphere-centered ball vanishes at every outward adjoint sample from any interior point outside that same ball. -/
theorem neumann_adjoint_radial_test_eq_zero {n q : ℕ}
    (ψ : Domain n → Ambient q) (a : Domain n) (s : ℝ)
    (hSupport : tsupport ψ⊆ball a s) (ha : ‖a‖=1)
    (y : Domain n) (hy : y≠0) (hyOne : ‖y‖≤1) (hyOutside : y∉ball a s)
    (t : ℝ) (ht : ‖y‖⁻¹≤t) : ψ (t • (‖y‖⁻¹ • y))=0 := by
  by_contra hne
  have hInside := hSupport (subset_tsupport ψ hne)
  exact hyOutside (mem_ball.mpr ((dist_le_neumann_adjoint_radial_sample a y ha hy hyOne t ht).trans_lt hInside))

/-- Beyond the actual support radius both terms of the finite-upper Neumann adjoint ray vanish, including a reversed integration interval. -/
theorem neumann_adjoint_ray_eq_zero_of_support_radius {n q : ℕ}
    (ψ : Domain n → Ambient q) (upper : ℝ) (hUpper : 0<upper)
    (hZero : ∀z : Domain n,upper≤‖z‖ → ψ z=0)
    (θ : Domain n) (hθ : ‖θ‖=1) (r : ℝ) (hr : 0<r) (hRange : upper≤r⁻¹) :
    r^(2-(n : ℝ)) • ψ (r⁻¹ • θ)+((n : ℝ)-2) •
      (∫t in r⁻¹..upper,t^((n : ℝ)-3) • ψ (t • θ))=0 := by
  have hFirst : ψ (r⁻¹ • θ)=0 := by
    apply hZero
    rwa [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),hθ,mul_one]
  have hIntegral : (∫t in r⁻¹..upper,t^((n : ℝ)-3) • ψ (t • θ))=0 := by
    calc
      _ = ∫_t in r⁻¹..upper,(0 : Ambient q) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have hInterval : t∈Icc upper r⁻¹ := by simpa only [uIcc_of_ge hRange] using ht
        have htPos : 0≤t := hUpper.le.trans hInterval.1
        have hψ : ψ (t • θ)=0 := hZero _ (by
          rw [norm_smul,Real.norm_of_nonneg htPos,hθ,mul_one]
          exact hInterval.1)
        change t^((n : ℝ)-3) • ψ (t • θ)=0
        rw [hψ,smul_zero]
      _ = 0 := intervalIntegral.integral_zero
  rw [hFirst,hIntegral,smul_zero,smul_zero,zero_add]

/-- The actual finite-upper adjoint expression is zero at every interior point outside the original sphere-centered support ball. -/
theorem neumann_adjoint_expression_eq_zero_off_boundary_ball {n q : ℕ}
    (ψ : Domain n → Ambient q) (upper : ℝ) (hUpper : 0<upper)
    (hZero : ∀z : Domain n,upper≤‖z‖ → ψ z=0)
    (a : Domain n) (s : ℝ) (hSupport : tsupport ψ⊆ball a s) (ha : ‖a‖=1)
    (y : Domain n) (hy : y≠0) (hyOne : ‖y‖≤1) (hyOutside : y∉ball a s) :
    ‖y‖^(2-(n : ℝ)) • ψ (‖y‖⁻¹ • (‖y‖⁻¹ • y))+((n : ℝ)-2) •
      (∫t in ‖y‖⁻¹..upper,t^((n : ℝ)-3) • ψ (t • (‖y‖⁻¹ • y)))=0 := by
  have hyPos : 0<‖y‖ := norm_pos_iff.mpr hy
  have hθ : ‖‖y‖⁻¹ • y‖=1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hyPos.le),inv_mul_cancel₀ hyPos.ne']
  by_cases hRange : upper≤‖y‖⁻¹
  · exact neumann_adjoint_ray_eq_zero_of_support_radius ψ upper hUpper hZero _ hθ _ hyPos hRange
  · have hRange' : ‖y‖⁻¹≤upper := (not_le.mp hRange).le
    have hSample (t : ℝ) (ht : ‖y‖⁻¹≤t) : ψ (t • (‖y‖⁻¹ • y))=0 :=
      neumann_adjoint_radial_test_eq_zero ψ a s hSupport ha y hy hyOne hyOutside t ht
    have hIntegral : (∫t in ‖y‖⁻¹..upper,t^((n : ℝ)-3) • ψ (t • (‖y‖⁻¹ • y)))=0 := by
      calc
        _ = ∫_t in ‖y‖⁻¹..upper,(0 : Ambient q) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have hInterval : t∈Icc ‖y‖⁻¹ upper := by simpa only [uIcc_of_le hRange'] using ht
          change t^((n : ℝ)-3) • ψ (t • (‖y‖⁻¹ • y))=0
          rw [hSample t hInterval.1,smul_zero]
        _ = 0 := intervalIntegral.integral_zero
    rw [hSample _ le_rfl,hIntegral,smul_zero,smul_zero,zero_add]

end StationaryHarmonicMaps.Analysis

end

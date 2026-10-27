module

public import StationaryHarmonicMaps.Analysis.CoexactRangeEulerResolvent
public import StationaryHarmonicMaps.Analysis.WeightedKelvinTestZeroBoundary

/-!
# The actual radial cancellation in Neumann Kelvin reflection

The Kelvin weight and the variable lower endpoint of the radial correction
cancel exactly. The derivative of the original reflected ray therefore
depends only on the original derivative, including in dimension two.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

@[expose] noncomputable def neumannKelvinRay {n q : ℕ} (upper : ℝ)
    (u : Domain n → Ambient q) (θ : Domain n) (r : ℝ) : Ambient q :=
  r ^ (2-(n : ℝ)) • u (r⁻¹ • θ) + ((n : ℝ)-2) •
    ∫ t in r⁻¹..upper, t ^ ((n : ℝ)-3) • u (t • θ)

private theorem radial_integrand_continuousAt {n q : ℕ} (p : ℝ)
    (u : Domain n → Ambient q) (hu : ContDiff ℝ ∞ u) (θ : Domain n)
    (t : ℝ) (ht : 0 < t) : ContinuousAt (fun s : ℝ => s ^ p • u (s • θ)) t :=
  (Real.continuousAt_rpow_const t p (Or.inl ht.ne')).smul
    (hu.continuous.continuousAt.comp (continuousAt_id.smul continuousAt_const))

/-- Positive endpoints give the genuine integrability of each original radial correction. -/
theorem neumannKelvinRay_intervalIntegrable {n q : ℕ} (upper : ℝ) (hUpper : 0 < upper)
    (u : Domain n → Ambient q) (hu : ContDiff ℝ ∞ u) (θ : Domain n)
    (r : ℝ) (hr : 0 < r) :
    IntervalIntegrable (fun t : ℝ => t ^ ((n : ℝ)-3) • u (t • θ)) volume r⁻¹ upper := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have htpos : 0 < t := (lt_min (inv_pos.mpr hr) hUpper).trans_le ht.1
  exact (radial_integrand_continuousAt ((n : ℝ)-3) u hu θ t htpos).continuousWithinAt

/-- The radial derivative of the actual Kelvin-plus-integral expression has no map-value term. -/
theorem neumannKelvinRay_hasDerivAt {n q : ℕ} (upper : ℝ) (hUpper : 0 < upper)
    (u : Domain n → Ambient q) (hu : ContDiff ℝ ∞ u) (θ : Domain n)
    (r : ℝ) (hr : 0 < r) :
    HasDerivAt (neumannKelvinRay upper u θ)
      (-(r ^ (-(n : ℝ))) • fderiv ℝ u (r⁻¹ • θ) θ) r := by
  let f := fun t : ℝ => t ^ ((n : ℝ)-3) • u (t • θ)
  have hInt := neumannKelvinRay_intervalIntegrable upper hUpper u hu θ r hr
  have hFC : ∀ t ∈ Ioi (0 : ℝ), ContinuousAt f t :=
    fun t ht => radial_integrand_continuousAt ((n : ℝ)-3) u hu θ t ht
  have hMeas : StronglyMeasurableAtFilter f (𝓝 r⁻¹) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi hFC r⁻¹ (inv_pos.mpr hr)
  have hIntegral := (intervalIntegral.integral_hasDerivAt_left hInt hMeas
    (hFC r⁻¹ (inv_pos.mpr hr))).scomp r (hasDerivAt_inv hr.ne')
  have hU := ((hu.differentiable (by simp) (r⁻¹ • θ)).hasFDerivAt).comp_hasDerivAt r
    ((hasDerivAt_inv hr.ne').smul_const θ)
  have hPower : HasDerivAt (fun s : ℝ => s ^ (2-(n : ℝ)))
      ((2-(n : ℝ)) * r ^ (2-(n : ℝ)-1)) r :=
    Real.hasDerivAt_rpow_const (Or.inl hr.ne')
  have H := (hPower.smul hU).add (hIntegral.const_smul ((n : ℝ)-2))
  have hInv2 : (r ^ 2)⁻¹ = r ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hr.le, Real.rpow_two]
  have hInvPow : r⁻¹ ^ ((n : ℝ)-3) = r ^ (3-(n : ℝ)) := by
    rw [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
    congr 1
    ring
  have hPow1 : r ^ (2-(n : ℝ)) * r ^ (-2 : ℝ) = r ^ (-(n : ℝ)) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hPow2 : r ^ (-2 : ℝ) * r ^ (3-(n : ℝ)) = r ^ (1-(n : ℝ)) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hExponent : 2-(n : ℝ)-1 = 1-(n : ℝ) := by ring
  have hValue : r ^ (2-(n : ℝ)) • fderiv ℝ u (r⁻¹ • θ) (-(r ^ 2)⁻¹ • θ) +
      ((2-(n : ℝ)) * r ^ (2-(n : ℝ)-1)) • u (r⁻¹ • θ) +
      ((n : ℝ)-2) • (-(r ^ 2)⁻¹ • (-f r⁻¹)) =
        (-(r ^ (-(n : ℝ)))) • fderiv ℝ u (r⁻¹ • θ) θ := by
    rw [map_smul, hInv2, hExponent, show f r⁻¹ = r⁻¹ ^ ((n : ℝ)-3) • u (r⁻¹ • θ) from rfl,
      hInvPow]
    simp only [smul_smul, neg_mul, neg_smul, smul_neg, neg_neg]
    rw [hPow1, hPow2]
    module
  simp only [Function.comp_def] at H
  rw [hValue] at H
  exact H.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.AffineHSMoment
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Exact ball averages and mean oscillation under positive dilation

The affine Jacobian cancels the ball measure in the average. The literal
mean-oscillation bound is therefore unchanged on all centers and scales.
-/

public section

open HarmonicMaps MeasureTheory Set Metric

namespace StationaryHarmonicMaps.Analysis

/-- Positive affine transport preserves the actual average over its image ball. -/
theorem average_affineBall {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a b : Domain n) {t : ℝ} (ht : 0<t) (R : ℝ)
    (f : Domain n → E) :
    (⨍ x in ball b (R/t),f (a+t • (x-b)))=⨍ y in ball a R,f y := by
  have hVolume : volume.real (ball b (R/t)) =
      (t^n)⁻¹ * volume.real (ball a R) := by
    simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one]
      using integral_affineBall a b ht R (fun _ : Domain n => (1 : ℝ))
  simp only [average_eq,measureReal_restrict_apply_univ]
  rw [integral_affineBall a b ht R f,hVolume,mul_inv_rev,smul_smul]
  congr 1
  rw [inv_inv,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ ht.ne'),mul_one]

/-- A centered dilation transports every ball average with no integrability premise. -/
theorem average_dilation_ball {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {t : ℝ} (ht : 0<t) (a : Domain n) (r : ℝ)
    (f : Domain n → E) :
    (⨍ x in ball a r,f (t • x))=⨍ y in ball (t • a) (t*r),f y := by
  have hAffine (x : Domain n) : t • a+t • (x-a)=t • x := by
    rw [smul_sub]
    abel
  simpa only [mul_div_cancel_left₀ r ht.ne',hAffine] using
    average_affineBall (t • a) a ht (t*r) f

/-- All-ball scalar mean oscillation is invariant under positive dilation. -/
theorem meanOscillation_dilation_bound {n : ℕ} (b : Domain n → ℝ) (B : ℝ)
    (hB : ∀ (a : Domain n) (r : ℝ),0<r →
      IntegrableOn b (ball a r) volume ∧
      (⨍ x in ball a r,|b x-(⨍ y in ball a r,b y)|)≤B)
    {t : ℝ} (ht : 0<t) (a : Domain n) (r : ℝ) (hr : 0<r) :
    IntegrableOn (fun x=>b (t • x)) (ball a r) volume ∧
      (⨍ x in ball a r,|b (t • x)-(⨍ y in ball a r,b (t • y))|)≤B := by
  obtain ⟨hI,hOsc⟩ := hB (t • a) (t*r) (mul_pos ht hr)
  have hAffine (x : Domain n) : t • a+t • (x-a)=t • x := by
    rw [smul_sub]
    abel
  have hComp : IntegrableOn (fun x=>b (t • x)) (ball a r) volume := by
    simpa only [mul_div_cancel_left₀ r ht.ne',hAffine] using
      integrable_affineBall (t • a) a ht (t*r) hI
  refine ⟨hComp,?_⟩
  rw [average_dilation_ball ht a r b]
  rw [average_dilation_ball ht a r (fun x=>|b x-(⨍ y in ball (t • a) (t*r),b y)|)]
  exact hOsc

end StationaryHarmonicMaps.Analysis

end

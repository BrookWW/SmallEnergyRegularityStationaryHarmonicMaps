module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Actual L¹ products and Cauchy--Schwarz bounds for HS fields -/

public section

open HarmonicMaps MeasureTheory Filter

namespace StationaryHarmonicMaps.Analysis

/-- Nonnegative real L² functions have an actual L¹ product with its true energy-root bound. -/
theorem integral_mul_le_sqrt_energy_roots {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) :
    Integrable (fun x => f x * g x) μ ∧
      (∫ x, f x * g x ∂μ) ≤
        Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
  have hprod : MemLp (fun x => f x * g x) 1 μ := hg.mul' hf
  refine ⟨memLp_one_iff_integrable.mp hprod, ?_⟩
  have hf' : MemLp f (ENNReal.ofReal 2) μ := by simpa only [ENNReal.ofReal_ofNat] using hf
  have hg' : MemLp g (ENNReal.ofReal 2) μ := by simpa only [ENNReal.ofReal_ofNat] using hg
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hf0 hg0 hf' hg'
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using H

/-- The actual HS square root times a vector norm is integrable with the exact product bound. -/
theorem integral_hs_mul_norm_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {n m q : ℕ}
    (F : X → Gradient n m) (a : X → Ambient q)
    (hF : ∀ i, MemLp (fun x => F x i) 2 μ) (ha : MemLp a 2 μ) :
    Integrable (fun x => Real.sqrt (hsNormSq (F x)) * ‖a x‖) μ ∧
      (∫ x, Real.sqrt (hsNormSq (F x)) * ‖a x‖ ∂μ) ≤
        Real.sqrt (∫ x, hsNormSq (F x) ∂μ) * Real.sqrt (∫ x, ‖a x‖ ^ 2 ∂μ) := by
  have hf : MemLp (fun x => Real.sqrt (hsNormSq (F x))) 2 μ :=
    memLp_sqrt_sum_norm_sq F hF
  have H := integral_mul_le_sqrt_energy_roots hf ha.norm
    (Eventually.of_forall fun x => Real.sqrt_nonneg _) (Eventually.of_forall fun x => norm_nonneg _)
  have hsquare (x : X) : (Real.sqrt (hsNormSq (F x))) ^ 2 = hsNormSq (F x) :=
    Real.sq_sqrt (hsNormSq_nonneg _)
  simpa only [hsquare] using H

/-- Finite measure converts actual HS L² energy into its genuine L¹ norm. -/
theorem integral_hs_le_sqrt_measure_mul_energy {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {n m : ℕ}
    (F : X → Gradient n m) (hF : ∀ i, MemLp (fun x => F x i) 2 μ) :
    Integrable (fun x => Real.sqrt (hsNormSq (F x))) μ ∧
      (∫ x, Real.sqrt (hsNormSq (F x)) ∂μ) ≤
        Real.sqrt (μ.real Set.univ) * Real.sqrt (∫ x, hsNormSq (F x) ∂μ) := by
  have hf : MemLp (fun x => Real.sqrt (hsNormSq (F x))) 2 μ :=
    memLp_sqrt_sum_norm_sq F hF
  have hc : MemLp (fun _ : X => (1 : ℝ)) 2 μ := memLp_const 1
  have H := integral_mul_le_sqrt_energy_roots hc hf
    (Eventually.of_forall fun _ => zero_le_one) (Eventually.of_forall fun x => Real.sqrt_nonneg _)
  have hsquare (x : X) : (Real.sqrt (hsNormSq (F x))) ^ 2 = hsNormSq (F x) :=
    Real.sq_sqrt (hsNormSq_nonneg _)
  simpa only [one_mul, hsquare, one_pow, integral_const, smul_eq_mul, mul_one] using H

end StationaryHarmonicMaps.Analysis

end

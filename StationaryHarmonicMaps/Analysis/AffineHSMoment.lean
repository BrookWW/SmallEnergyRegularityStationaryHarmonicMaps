module

public import HarmonicMaps.Analysis.AffineEnergyScaling

/-!
# Full Hilbert--Schmidt moments under affine ball transport

Every real power of the literal sum of all squared gradient entries has
its exact Jacobian and scalar multiplier. The integral identity holds
without a measurability or finiteness assumption. Actual Lp membership
and integrability transport separately from the original data.
-/

public section

open HarmonicMaps MeasureTheory Set Metric
open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem hs_half_power_smul {n q : ℕ} (c s : ℝ) (A : Gradient n q) :
    (hsNormSq (fun i=>c • A i))^(s/2)=|c|^s*(hsNormSq A)^(s/2) := by
  rw [hsNormSq_const_smul,Real.mul_rpow (sq_nonneg c) (hsNormSq_nonneg A)]
  congr 1
  rw [← sq_abs,← Real.rpow_natCast,← Real.rpow_mul (abs_nonneg c)]
  congr 1
  ring

/-- Positive affine ball pullback preserves actual Lp membership at every exponent. -/
theorem memLp_affineBall_exponent {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (a b : Domain n) {t : ℝ} (ht : 0<t) (R : ℝ) (p : ℝ≥0∞)
    {f : Domain n → E} (hf : MemLp f p (volume.restrict (ball a R))) :
    MemLp (fun x=>f (a+t • (x-b))) p (volume.restrict (ball b (R/t))) := by
  have h := hf.smul_measure (c:=ENNReal.ofReal ((t^n)⁻¹)) ENNReal.ofReal_ne_top
  rw [← affineBall_map_restrict a b ht R] at h
  exact h.comp_of_map (affineBall_measurableEmbedding a b ht.ne').measurable.aemeasurable

/-- Actual integrable data retain integrability on the transported ball. -/
theorem integrable_affineBall {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (a b : Domain n) {t : ℝ} (ht : 0<t) (R : ℝ)
    {f : Domain n → E} (hf : IntegrableOn f (ball a R) volume) :
    IntegrableOn (fun x=>f (a+t • (x-b))) (ball b (R/t)) volume := by
  exact memLp_one_iff_integrable.mp
    (memLp_affineBall_exponent a b ht R 1 (memLp_one_iff_integrable.mpr hf))

/-- The exact full-HS real moment has the affine Jacobian and the absolute scalar power, without measurability or finiteness assumptions. -/
theorem integral_hs_half_power_affineBall {n q : ℕ}
    (a b : Domain n) {t : ℝ} (ht : 0<t) (R c s : ℝ)
    (F : Domain n → Gradient n q) :
    (∫x in ball b (R/t),(hsNormSq (fun i=>c • F (a+t • (x-b)) i))^(s/2))=
      (t^n)⁻¹*|c|^s*(∫x in ball a R,(hsNormSq (F x))^(s/2)) := by
  simp_rw [hs_half_power_smul]
  rw [integral_const_mul,integral_affineBall a b ht R (fun x=>(hsNormSq (F x))^(s/2))]
  simp only [smul_eq_mul]
  ring

end StationaryHarmonicMaps.Analysis

end

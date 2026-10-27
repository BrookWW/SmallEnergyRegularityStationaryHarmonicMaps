module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Actual bounded cancellation atoms paired with mean oscillation

The atom's original support and normalized bound produce both genuine
integrabilities. Its actual zero integral removes the original mean of
the second function. The resulting pairing is bounded by that function's
literal mean oscillation on the original support set.
-/

public section

open MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

/-- A genuine normalized supported cancellation atom has an actual integrable pairing controlled by the original mean oscillation. -/
theorem atom_pairing_le_mean_oscillation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (hS : MeasurableSet S)
    (hS0 : μ S≠0) (hSFin : μ S≠⊤)
    (a b : X → ℝ) (ha : AEStronglyMeasurable a (μ.restrict S))
    (hSupp : Function.support a⊆S)
    (hBound : ∀ᵐ x ∂μ.restrict S,|a x|≤(μ.real S)⁻¹)
    (hCancel : (∫ x,a x ∂μ)=0) (hb : IntegrableOn b S μ) :
    Integrable a μ ∧ Integrable (fun x=>a x*b x) μ ∧
      |∫ x,a x*b x ∂μ|≤⨍ x in S,|b x-(⨍ y in S,b y ∂μ)| ∂μ := by
  let ν := μ.restrict S
  let m := ⨍ y in S,b y ∂μ
  let V := μ.real S
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hSFin
  have hA : ∀ᵐ x ∂ν,‖a x‖≤V⁻¹ := by simpa only [Real.norm_eq_abs] using hBound
  have haLp : MemLp a 1 ν := MemLp.of_bound ha V⁻¹ hA
  have haI : Integrable a μ :=
    (integrableOn_iff_integrable_of_support_subset hSupp).mp (haLp.integrable (by norm_num))
  have hAB : IntegrableOn (fun x=>a x*b x) S μ := hb.bdd_mul ha hA
  have hSuppAB : Function.support (fun x=>a x*b x)⊆S := by
    intro x hx
    apply hSupp
    intro hz
    exact hx (by dsimp only;rw [hz,zero_mul])
  have hABI : Integrable (fun x=>a x*b x) μ :=
    (integrableOn_iff_integrable_of_support_subset hSuppAB).mp hAB
  have hB : IntegrableOn (fun x=>b x-m) S μ := hb.sub (integrable_const m)
  have hError : IntegrableOn (fun x=>a x*(b x-m)) S μ := hB.bdd_mul ha hA
  have hSuppError : Function.support (fun x=>a x*(b x-m))⊆S := by
    intro x hx
    apply hSupp
    intro hz
    exact hx (by dsimp only;rw [hz,zero_mul])
  have hErrorI : Integrable (fun x=>a x*(b x-m)) μ :=
    (integrableOn_iff_integrable_of_support_subset hSuppError).mp hError
  have hIntegral : (∫ x,a x*(b x-m) ∂μ)=(∫ x,a x*b x ∂μ) := by
    have hFun : (fun x=>a x*(b x-m))=(fun x=>a x*b x-a x*m) := by funext x;ring
    rw [hFun,integral_sub hABI (haI.mul_const m),integral_mul_const,hCancel,zero_mul,sub_zero]
  have hSetIntegral : (∫ x,a x*(b x-m) ∂μ)=∫ x in S,a x*(b x-m) ∂μ := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    refine Eventually.of_forall fun x=>?_ 
    dsimp only
    by_cases hx : x∈S
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      have hz : a x=0 := by
        by_contra hn
        exact hx (hSupp hn)
      rw [hz,zero_mul]
  have hVPos : 0<V := ENNReal.toReal_pos hS0 hSFin
  have hV : 0≤V⁻¹ := inv_nonneg.mpr hVPos.le
  refine ⟨haI,hABI,?_⟩
  rw [← hIntegral,hSetIntegral]
  calc
    _ ≤ ∫ x in S,|a x*(b x-m)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x in S,V⁻¹*|b x-m| ∂μ := by
      apply integral_mono_ae hError.abs (hB.abs.const_mul V⁻¹)
      filter_upwards [hBound] with x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ = _ := by rw [integral_const_mul,setAverage_eq,smul_eq_mul]

end StationaryHarmonicMaps.Analysis

end

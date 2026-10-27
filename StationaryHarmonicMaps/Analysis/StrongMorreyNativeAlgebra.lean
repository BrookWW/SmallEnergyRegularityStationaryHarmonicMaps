module

public import StationaryHarmonicMaps.Analysis.StrongerMorreyMeanBound
public import StationaryHarmonicMaps.Analysis.BilinearPowerGrowth

/-!
# Literal bilinear products from original stronger native data

The actual original means and stronger derivative growth supply both
essential bounds internally. The genuine two-map Leibniz theorem then
produces the same bilinear product and its complete stronger power growth.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Original stronger native graphs produce their actual bilinear product
graph and complete growth, with both value bounds supplied by the original
means and growth amplitudes rather than added as premises. -/
theorem exists_stronger_morrey_native_bilinear_product
    (n : ℕ) (hn : 2 ≤ n) (γ : ℝ) (hγ : 0 < γ) (hγTwo : γ < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m k q : ℕ)
      (B : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient q))
      (u : Domain n → Ambient m) (Du : Domain n → Gradient n m) (Ku : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ Ku →
      (∀ a ∈ ball (0 : Domain n) 1, ∀ r : ℝ, 0 < r →
        (∫ x in ball a r ∩ ball (0 : Domain n) 1, hsNormSq (Du x)) ≤
          Ku * r^((n : ℝ)-2+γ)) →
      ∀ (v : Domain n → Ambient k) (Dv : Domain n → Gradient n k) (Kv : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) v Dv → 0 ≤ Kv →
      (∀ a ∈ ball (0 : Domain n) 1, ∀ r : ℝ, 0 < r →
        (∫ x in ball a r ∩ ball (0 : Domain n) 1, hsNormSq (Dv x)) ≤
          Kv * r^((n : ℝ)-2+γ)) →
      let Mu := ‖(⨍ x in ball (0 : Domain n) 1, u x)‖ + C * Real.sqrt Ku
      let Mv := ‖(⨍ x in ball (0 : Domain n) 1, v x)‖ + C * Real.sqrt Kv
      let W := fun x => B (u x) (v x)
      let DW := fun x i => B (Du x i) (v x) + B (u x) (Dv x i)
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ‖u x‖ ≤ Mu) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ‖v x‖ ≤ Mv) ∧
      MemW12 (ballDomain (0 : Domain n) 1) W DW ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ‖W x‖ ≤ ‖B‖ * Mu * Mv) ∧
      0 ≤ 2 * ‖B‖^2 * (Mu^2 * Kv + Mv^2 * Ku) ∧
      ∀ a ∈ ball (0 : Domain n) 1, ∀ r : ℝ, 0 < r →
        IntegrableOn (fun x => hsNormSq (DW x)) (ball a r ∩ ball (0 : Domain n) 1) volume ∧
        (∫ x in ball a r ∩ ball (0 : Domain n) 1, hsNormSq (DW x)) ≤
          (2 * ‖B‖^2 * (Mu^2 * Kv + Mv^2 * Ku)) * r^((n : ℝ)-2+γ) := by
  obtain ⟨C,hC,Hmean⟩ := exists_stronger_morrey_ae_bound_by_mean n hn γ hγ hγTwo
  refine ⟨C,hC,?_⟩
  intro m k q B u Du Ku hu hKu hGrowthU v Dv Kv hv hKv hGrowthV Mu Mv W DW
  obtain ⟨_U,_hU,_hUAE,_hUSup,hUBound⟩ := Hmean m u Du Ku hu hKu hGrowthU
  obtain ⟨_V,_hV,_hVAE,_hVSup,hVBound⟩ := Hmean k v Dv Kv hv hKv hGrowthV
  have hMu : 0 ≤ Mu := add_nonneg (norm_nonneg _) (mul_nonneg hC.le (Real.sqrt_nonneg _))
  have hMv : 0 ≤ Mv := add_nonneg (norm_nonneg _) (mul_nonneg hC.le (Real.sqrt_nonneg _))
  obtain ⟨hProduct,hBound,hCoeff,hGrowth⟩ := bounded_native_bilinear_power_growth_ball
    0 1 (by norm_num) u Du hu Mu hUBound v Dv hv Mv hVBound B
      ((n : ℝ)-2+γ) Ku Kv hKu hKv hGrowthU hGrowthV
  refine ⟨hUBound,hVBound,hProduct,?_,hCoeff,hGrowth⟩
  simpa only [abs_of_nonneg hMu,abs_of_nonneg hMv] using hBound

end StationaryHarmonicMaps.Analysis

end

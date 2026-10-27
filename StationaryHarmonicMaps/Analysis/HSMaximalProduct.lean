module

public import StationaryHarmonicMaps.Analysis.HSMaximalLp
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# A genuine integrable product of the two full-HS maximal fields

The actual maximal moments supplied by the original L2 columns enter
Cauchy--Schwarz with exponent two. The resulting extended measurable
product has a finite integral bounded by the product of the two original
HS energy square roots. No pointwise real conversion is used.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original full-HS L2 fields produce the actual measurable integrable maximal product with the bilinear energy bound. -/
theorem hs_dyadic_maximal_product_control {n q k : ℕ}
    (F : Domain n → Gradient n q) (hF : ∀ i,MemLp (fun x => F x i) 2 volume)
    (G : Domain n → Gradient n k) (hG : ∀ i,MemLp (fun x => G x i) 2 volume)
    {r : ℝ} (hr : 0<r) (hrTwo : r<2) :
    let M := fun x =>
      (dyadicBallMaximal (fun y => ENNReal.ofReal ((Real.sqrt (hsNormSq (F y)))^r)) x)^(1/r) *
      (dyadicBallMaximal (fun y => ENNReal.ofReal ((Real.sqrt (hsNormSq (G y)))^r)) x)^(1/r)
    Measurable M ∧
      (∫⁻ x,M x) ≤ ENNReal.ofReal (((2 : ℝ)^(2/r)*(2/r)/(2/r-1))*(5 : ℝ)^n) *
        (ENNReal.ofReal (∫ x,hsNormSq (F x)))^((1 : ℝ)/2) *
        (ENNReal.ofReal (∫ x,hsNormSq (G x)))^((1 : ℝ)/2) ∧
      (∫⁻ x,M x)<∞ ∧ (∀ᵐ x ∂volume,M x≠∞) := by
  intro M
  let A := dyadicBallMaximal (fun y => ENNReal.ofReal ((Real.sqrt (hsNormSq (F y)))^r))
  let B := dyadicBallMaximal (fun y => ENNReal.ofReal ((Real.sqrt (hsNormSq (G y)))^r))
  let K : ℝ := ((2 : ℝ)^(2/r)*(2/r)/(2/r-1))*(5 : ℝ)^n
  obtain ⟨hA,hABound,_hAI,_hAE,_hBallA⟩ := hs_dyadic_maximal_moment_control F hF hr hrTwo
  obtain ⟨hB,hBBound,_hBI,_hBE,_hBallB⟩ := hs_dyadic_maximal_moment_control G hG hr hrTwo
  have hM : Measurable M := (hA.pow_const (1/r)).mul (hB.pow_const (1/r))
  have hCauchy := ENNReal.lintegral_mul_norm_pow_le (μ := volume)
    ((hA.pow_const (2/r)).aemeasurable) ((hB.pow_const (2/r)).aemeasurable)
    (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1 : ℝ)/2+1/2=1)
  have hExponent : (2/r)*((1 : ℝ)/2)=1/r := by ring
  simp only [← ENNReal.rpow_mul,hExponent] at hCauchy
  have hSquare (v : ℝ≥0∞) : v^((1 : ℝ)/2)*v^((1 : ℝ)/2)=v := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hBound : (∫⁻ x,M x) ≤ ENNReal.ofReal K *
      (ENNReal.ofReal (∫ x,hsNormSq (F x)))^((1 : ℝ)/2) *
      (ENNReal.ofReal (∫ x,hsNormSq (G x)))^((1 : ℝ)/2) := by
    calc
      _ ≤ (∫⁻ x,(A x)^(2/r))^((1 : ℝ)/2)*(∫⁻ x,(B x)^(2/r))^((1 : ℝ)/2) := hCauchy
      _ ≤ (ENNReal.ofReal K*ENNReal.ofReal (∫ x,hsNormSq (F x)))^((1 : ℝ)/2)*
          (ENNReal.ofReal K*ENNReal.ofReal (∫ x,hsNormSq (G x)))^((1 : ℝ)/2) :=
        mul_le_mul (ENNReal.rpow_le_rpow hABound (by norm_num))
          (ENNReal.rpow_le_rpow hBBound (by norm_num)) zero_le zero_le
      _ = _ := by
        simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ)≤1/2)]
        calc
          _ = ((ENNReal.ofReal K)^((1 : ℝ)/2)*(ENNReal.ofReal K)^((1 : ℝ)/2))*
              (ENNReal.ofReal (∫ x,hsNormSq (F x)))^((1 : ℝ)/2)*
              (ENNReal.ofReal (∫ x,hsNormSq (G x)))^((1 : ℝ)/2) := by ac_rfl
          _ = _ := by rw [hSquare]
  have hFinite := hBound.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))
  exact ⟨hM,hBound,hFinite,ae_lt_top' hM.aemeasurable hFinite.ne |>.mono (fun _ hx=>hx.ne)⟩

end StationaryHarmonicMaps.Analysis

end

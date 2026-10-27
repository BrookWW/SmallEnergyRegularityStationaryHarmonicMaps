module

public import StationaryHarmonicMaps.Analysis.DivCurlKernelCancellation
public import StationaryHarmonicMaps.Analysis.LocalSobolevPoincare
public import StationaryHarmonicMaps.Analysis.WeightedColumnBounds
public import HarmonicMaps.SobolevRestriction
public import HolderToCK.Analysis.WeakPoissonLocality

/-!
# Genuine lower-exponent control of rough div--curl kernels

The original rough Sobolev graph on the double ball supplies the higher
oscillation integrability through the proved local Sobolev--Poincare
inequality. The original divergence equation supplies cancellation.
Holder's inequality then gives lower-exponent norms of the original field
and original gradient, without assuming Hardy or BMO estimates.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal NNReal

namespace StationaryHarmonicMaps.Analysis

/-- The coordinate lower-exponent kernel coefficient. -/
@[expose] noncomputable def divcurlLowerExponentConstant (n : ℕ) (p : ℝ≥0) : ℝ :=
  1+localSobolevPoincareConstant n p*Real.sqrt (n:ℝ)

/-- Numeric Sobolev and Holder exponents yield an actual lower-exponent bound for every rough kernel pairing. -/
theorem exists_divcurl_lower_exponent_kernel_bound_explicit (n : ℕ) (hn : 0 < n)
    (p s : ℝ≥0) (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hs : 0 < s)
    (hsp : (s : ℝ)⁻¹=(p : ℝ)⁻¹-(n : ℝ)⁻¹)
    (hpq : Real.HolderConjugate (p : ℝ) (s : ℝ)) :
    ∃ C : ℝ, C=divcurlLowerExponentConstant n p ∧ 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (r : ℝ), 0 < r →
      ∀ (Z : Domain n → Gradient n q),
        (∀ i, MemLp (fun x => Z x i) 2 (volume.restrict (Metric.ball a (2*r)))) →
        HolderToCK.WeakPoissonOn (ballDomain a (2*r)) Z (fun _ => (0 : Ambient q)) →
        ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
          MemW12 (ballDomain a (2*r)) w Dw →
          ∀ (κ : Domain n → ℝ), ContDiff ℝ ∞ κ → HasCompactSupport κ →
          tsupport κ ⊆ Metric.ball a r → ∀ B : ℝ, 0 ≤ B →
          (∀ x ∈ Metric.ball a r,∀ i : Fin n,|fderiv ℝ κ x (EuclideanSpace.single i 1)| ≤ B) →
          IntegrableOn (fun x => κ x * ∑ i : Fin n, inner ℝ (Z x i) (Dw x i))
            (Metric.ball a r) volume ∧
          |∫ x in Metric.ball a r,κ x * ∑ i : Fin n, inner ℝ (Z x i) (Dw x i)| ≤
            C*B*lpNorm (fun x => Real.sqrt (hsNormSq (Z x))) (p : ℝ≥0∞)
              (volume.restrict (Metric.ball a r))*
              lpNorm (fun x => Real.sqrt (hsNormSq (Dw x))) (p : ℝ≥0∞)
                (volume.restrict (Metric.ball a (2*r))) := by
  obtain ⟨S,hSEq,hS,Hsp⟩ := exists_local_sobolev_poincare_bound_explicit n hn p s hp hp₂ hs hsp
  let C : ℝ := 1+S*Real.sqrt (n : ℝ)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,?_,hC,?_⟩
  · change 1+S*Real.sqrt (n:ℝ)=1+localSobolevPoincareConstant n p*Real.sqrt (n:ℝ)
    rw [hSEq]
  intro q a r hr Z hZ hdiv w Dw hw κ hκ hcκ hsκ B hB hDκ
  let μ : Measure (Domain n) := volume.restrict (Metric.ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hsub : Metric.ball a r ⊆ Metric.ball a (2*r) := Metric.ball_subset_ball (by linarith)
  have hμ : μ ≤ volume.restrict (Metric.ball a (2*r)) := Measure.restrict_mono_set volume hsub
  have hZr (i : Fin n) : MemLp (fun x => Z x i) 2 μ := (hZ i).mono_measure hμ
  have hwr : MemW12 (ballDomain a r) w Dw :=
    ⟨hw.1.mono hsub,hw.2.1.mono_measure hμ,fun i => (hw.2.2 i).mono_measure hμ⟩
  let c : Ambient q := ⨍ y in Metric.ball a (2*r),w y
  have HC := divcurl_kernel_cancellation a hr Z hZr (hdiv.mono hsub) hwr c κ hκ hcκ hsκ
  obtain ⟨hucS,hucBound⟩ := Hsp q a r hr w Dw hw
  have huc2 : MemLp (fun x => w x-c) 2 μ := by
    letI : IsFiniteMeasure (volume.restrict (ballDomain a r).val) :=
      isFiniteMeasure_restrict.mpr measure_ball_ne_top
    exact hwr.2.1.sub (memLp_const c)
  have hProd := integral_hs_mul_norm_le Z (fun x => w x-c) hZr huc2
  let G : Domain n → ℝ := fun x => Real.sqrt (hsNormSq (Z x))
  have hG2 : MemLp G 2 μ := memLp_sqrt_sum_norm_sq Z hZr
  have hGp : MemLp G (p : ℝ≥0∞) μ := hG2.mono_exponent (by exact_mod_cast hp₂)
  have hGpR : MemLp G (ENNReal.ofReal (p : ℝ)) μ := by simpa only [ENNReal.ofReal_coe_nnreal] using hGp
  have hucSR : MemLp (fun x => ‖w x-c‖) (ENNReal.ofReal (s : ℝ)) μ := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hucS.norm
  have hHolder := integral_mul_norm_le_Lp_mul_Lq hpq hGpR hucSR
  have hG0 (x : Domain n) : 0 ≤ G x := Real.sqrt_nonneg _
  have hGnorm : lpNorm G (p : ℝ≥0∞) μ=(∫ x,G x^(p : ℝ) ∂μ)^(1/(p : ℝ)) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (show (p : ℝ≥0∞)≠0 by exact_mod_cast hpq.pos.ne') ENNReal.coe_ne_top hGp.aestronglyMeasurable]
    simp only [ENNReal.coe_toReal,Real.norm_of_nonneg (hG0 _),one_div]
  have hUnorm : lpNorm (fun x => w x-c) (s : ℝ≥0∞) μ=
      (∫ x,‖w x-c‖^(s : ℝ) ∂μ)^(1/(s : ℝ)) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (show (s : ℝ≥0∞)≠0 by exact_mod_cast hs.ne') ENNReal.coe_ne_top hucS.aestronglyMeasurable]
    simp only [ENNReal.coe_toReal,one_div,c,μ]
  have hHolder' : (∫ x,G x*‖w x-c‖ ∂μ) ≤
      lpNorm G (p : ℝ≥0∞) μ*lpNorm (fun x => w x-c) (s : ℝ≥0∞) μ := by
    rw [hGnorm,hUnorm]
    simpa only [Real.norm_of_nonneg (hG0 _),Real.norm_of_nonneg (norm_nonneg _)] using hHolder
  have hPoint (x : Domain n) (hx : x ∈ Metric.ball a r) :
      |∑ i : Fin n,fderiv ℝ κ x (EuclideanSpace.single i 1)*inner ℝ (Z x i) (w x-c)| ≤
      (B*Real.sqrt (n : ℝ))*(G x*‖w x-c‖) := by
    have hEq : (∑ i : Fin n,fderiv ℝ κ x (EuclideanSpace.single i 1)*inner ℝ (Z x i) (w x-c))=
        inner ℝ (∑ i : Fin n,fderiv ℝ κ x (EuclideanSpace.single i 1) • Z x i) (w x-c) := by
      simp only [sum_inner,real_inner_smul_left]
    rw [hEq]
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_right
        (norm_sum_smul_le_hs (fun i => fderiv ℝ κ x (EuclideanSpace.single i 1)) (Z x) hB (hDκ x hx))
        (norm_nonneg (w x-c))).trans_eq (by dsimp only [G]; ring))
  refine ⟨HC.1,?_⟩
  rw [HC.2.2,abs_neg]
  calc
    _ ≤ ∫ x in Metric.ball a r,|∑ i : Fin n,
        fderiv ℝ κ x (EuclideanSpace.single i 1)*inner ℝ (Z x i) (w x-c)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x in Metric.ball a r,(B*Real.sqrt (n : ℝ))*(G x*‖w x-c‖) := by
      apply integral_mono_ae HC.2.1.abs (hProd.1.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact hPoint x hx
    _ = (B*Real.sqrt (n : ℝ))*(∫ x,G x*‖w x-c‖ ∂μ) := integral_const_mul _ _
    _ ≤ (B*Real.sqrt (n : ℝ))*(lpNorm G (p : ℝ≥0∞) μ*lpNorm (fun x => w x-c) (s : ℝ≥0∞) μ) :=
      mul_le_mul_of_nonneg_left hHolder' (by positivity)
    _ ≤ (B*Real.sqrt (n : ℝ))*(lpNorm G (p : ℝ≥0∞) μ*
        (S*lpNorm (fun x => Real.sqrt (hsNormSq (Dw x))) (p : ℝ≥0∞)
          (volume.restrict (Metric.ball a (2*r))))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hucBound lpNorm_nonneg) (by positivity)
    _ ≤ _ := by
      have hCoefficient : S*Real.sqrt (n : ℝ) ≤ C := by dsimp only [C]; linarith
      have hNZ : 0 ≤ lpNorm G (p : ℝ≥0∞) μ := lpNorm_nonneg
      have hNW : 0 ≤ lpNorm (fun x => Real.sqrt (hsNormSq (Dw x))) (p : ℝ≥0∞)
          (volume.restrict (Metric.ball a (2*r))) := lpNorm_nonneg
      have H := mul_le_mul_of_nonneg_right hCoefficient (mul_nonneg (mul_nonneg hB hNZ) hNW)
      simpa only [G,μ,mul_assoc,mul_left_comm,mul_comm] using H

theorem exists_divcurl_lower_exponent_kernel_bound (n : ℕ) (hn : 0 < n)
    (p s : ℝ≥0) (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hs : 0 < s)
    (hsp : (s : ℝ)⁻¹=(p : ℝ)⁻¹-(n : ℝ)⁻¹)
    (hpq : Real.HolderConjugate (p : ℝ) (s : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (r : ℝ), 0 < r →
      ∀ (Z : Domain n → Gradient n q),
        (∀ i, MemLp (fun x => Z x i) 2 (volume.restrict (Metric.ball a (2*r)))) →
        HolderToCK.WeakPoissonOn (ballDomain a (2*r)) Z (fun _ => (0 : Ambient q)) →
        ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
          MemW12 (ballDomain a (2*r)) w Dw →
          ∀ (κ : Domain n → ℝ), ContDiff ℝ ∞ κ → HasCompactSupport κ →
          tsupport κ ⊆ Metric.ball a r → ∀ B : ℝ, 0 ≤ B →
          (∀ x ∈ Metric.ball a r,∀ i : Fin n,|fderiv ℝ κ x (EuclideanSpace.single i 1)| ≤ B) →
          IntegrableOn (fun x => κ x * ∑ i : Fin n, inner ℝ (Z x i) (Dw x i))
            (Metric.ball a r) volume ∧
          |∫ x in Metric.ball a r,κ x * ∑ i : Fin n, inner ℝ (Z x i) (Dw x i)| ≤
            C*B*lpNorm (fun x => Real.sqrt (hsNormSq (Z x))) (p : ℝ≥0∞)
              (volume.restrict (Metric.ball a r))*
              lpNorm (fun x => Real.sqrt (hsNormSq (Dw x))) (p : ℝ≥0∞)
                (volume.restrict (Metric.ball a (2*r))) := by
  obtain ⟨C,_hEq,hC,H⟩ := exists_divcurl_lower_exponent_kernel_bound_explicit n hn p s hp hp₂ hs hsp hpq
  exact ⟨C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end

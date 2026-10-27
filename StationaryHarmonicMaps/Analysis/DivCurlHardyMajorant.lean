module

public import StationaryHarmonicMaps.Analysis.DivCurlMaximalPointwise
public import StationaryHarmonicMaps.Analysis.HSMaximalProduct

/-!
# A common integrable majorant for actual rough div--curl kernels

The original globally L2 columns, distributional divergence equation
and native local weak gradient produce every normalized compact kernel
pairing. The same two literal full-HS maximal fields give a measurable
extended common majorant whose integral satisfies the bilinear energy
bound. Neither maximal finiteness nor a kernel estimate is an input.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal NNReal

namespace StationaryHarmonicMaps.Analysis

/-- Genuine rough divergence and native gradient data produce one measurable integrable majorant for every normalized smooth compact kernel at every center and positive scale. -/
theorem exists_divcurl_integrable_kernel_majorant (n : ℕ) (hn : 2≤n) :
    ∃ p : ℝ≥0, (p : ℝ)=2*(n : ℝ)/((n : ℝ)+1) ∧ 1<p ∧ p<2 ∧
      ∃ C K : ℝ, 0<C ∧ 0<K ∧ ∀ (q : ℕ) (Z : Domain n → Gradient n q),
        (∀ i,MemLp (fun x=>Z x i) 2 volume) →
        HolderToCK.WeakPoissonOn (⟨univ,isOpen_univ⟩ : OpenDomain n) Z (fun _=>(0 : Ambient q)) →
        ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
          MemW12Loc (⟨univ,isOpen_univ⟩ : OpenDomain n) w Dw →
          (∀ i,MemLp (fun x=>Dw x i) 2 volume) →
          let M := fun a => ENNReal.ofReal C *
            (dyadicBallMaximal (fun x=>ENNReal.ofReal ((Real.sqrt (hsNormSq (Z x)))^(p : ℝ))) a)^(1/(p : ℝ)) *
            (dyadicBallMaximal (fun x=>ENNReal.ofReal ((Real.sqrt (hsNormSq (Dw x)))^(p : ℝ))) a)^(1/(p : ℝ))
          Measurable M ∧
            (∫⁻ a,M a) ≤ ENNReal.ofReal K *
              (ENNReal.ofReal (∫ x,hsNormSq (Z x)))^((1 : ℝ)/2) *
              (ENNReal.ofReal (∫ x,hsNormSq (Dw x)))^((1 : ℝ)/2) ∧
            (∫⁻ a,M a)<(∞ : ℝ≥0∞) ∧ (∀ᵐ a ∂volume,M a≠(∞ : ℝ≥0∞)) ∧
            ∀ (a : Domain n) (r : ℝ),0<r → ∀ (κ : Domain n → ℝ),
              ContDiff ℝ ∞ κ → HasCompactSupport κ → tsupport κ⊆Metric.ball a r →
              (∀ x∈Metric.ball a r,∀ i : Fin n,
                |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤r^(-(n : ℝ)-1)) →
              Integrable (fun x=>κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i)) volume ∧
                ENNReal.ofReal |∫ x,κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i)|≤M a := by
  obtain ⟨p,hpFormula,hp1,hp2,C,hC,Hkernel⟩ := exists_divcurl_dyadic_maximal_kernel_bound n hn
  have hp0 : 0<(p : ℝ) := by exact_mod_cast (lt_trans zero_lt_one hp1)
  have hp2R : (p : ℝ)<2 := by exact_mod_cast hp2
  let A : ℝ := ((2 : ℝ)^(2/(p : ℝ))*(2/(p : ℝ))/(2/(p : ℝ)-1))*(5 : ℝ)^n
  have hA : 0<A := by
    have hP : 1<(2 : ℝ)/(p : ℝ) := (lt_div_iff₀ hp0).mpr (by simpa using hp2R)
    exact mul_pos (div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (div_pos (by norm_num) hp0)) (sub_pos.mpr hP)) (pow_pos (by norm_num) _)
  refine ⟨p,hpFormula,hp1,hp2,C,C*A,hC,mul_pos hC hA,?_⟩
  intro q Z hZ hdiv w Dw hw hDw M
  let P := fun a =>
    (dyadicBallMaximal (fun x=>ENNReal.ofReal ((Real.sqrt (hsNormSq (Z x)))^(p : ℝ))) a)^(1/(p : ℝ)) *
    (dyadicBallMaximal (fun x=>ENNReal.ofReal ((Real.sqrt (hsNormSq (Dw x)))^(p : ℝ))) a)^(1/(p : ℝ))
  obtain ⟨hP,hBound,hPI,_hPAE⟩ := hs_dyadic_maximal_product_control Z hZ Dw hDw hp0 hp2R
  have hM : Measurable M := by
    have H : Measurable (fun a=>ENNReal.ofReal C*P a) := measurable_const.mul hP
    simpa only [M,P,mul_assoc] using H
  have hIntegral : (∫⁻ a,M a)=ENNReal.ofReal C*∫⁻ a,P a := by
    calc
      _ = ∫⁻ a,ENNReal.ofReal C*P a := lintegral_congr (fun _=>mul_assoc _ _ _)
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hMBound : (∫⁻ a,M a)≤ENNReal.ofReal (C*A)*
      (ENNReal.ofReal (∫ x,hsNormSq (Z x)))^((1 : ℝ)/2)*
      (ENNReal.ofReal (∫ x,hsNormSq (Dw x)))^((1 : ℝ)/2) := by
    rw [hIntegral,ENNReal.ofReal_mul hC.le]
    exact (mul_le_mul_of_nonneg_left hBound zero_le).trans_eq (by dsimp only [A];ac_rfl)
  have hMI : (∫⁻ a,M a)<(∞ : ℝ≥0∞) := by
    rw [hIntegral]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hPI
  refine ⟨hM,hMBound,hMI,(ae_lt_top' hM.aemeasurable hMI.ne).mono (fun _ hx=>hx.ne),?_⟩
  have hZloc (i : Fin n) : LocallyMemL2 (⟨univ,isOpen_univ⟩ : OpenDomain n) (fun x=>Z x i) := by
    intro S _hS _hSub
    exact (hZ i).mono_measure Measure.restrict_le_self
  intro a r hr κ hκ hcκ hsκ hDκ
  exact Hkernel q Z hZloc hdiv w Dw hw a r hr κ hκ hcκ hsκ hDκ

/-- The literal supremum over every admissible compact kernel and every positive scale has a finite extended integral with the same bilinear energy bound. -/
theorem exists_divcurl_grand_kernel_lintegral_bound (n : ℕ) (hn : 2≤n) :
    ∃ K : ℝ, 0<K ∧ ∀ (q : ℕ) (Z : Domain n → Gradient n q),
      (∀ i,MemLp (fun x=>Z x i) 2 volume) →
      HolderToCK.WeakPoissonOn (⟨univ,isOpen_univ⟩ : OpenDomain n) Z (fun _=>(0 : Ambient q)) →
      ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
        MemW12Loc (⟨univ,isOpen_univ⟩ : OpenDomain n) w Dw →
        (∀ i,MemLp (fun x=>Dw x i) 2 volume) →
        let J := fun a => ⨆ r : PositiveRadius, ⨆ κ : Domain n → ℝ,
          ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
          ⨆ (_ : tsupport κ⊆Metric.ball a r.val),
          ⨆ (_ : ∀ x∈Metric.ball a r.val,∀ i : Fin n,
            |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤r.val^(-(n : ℝ)-1)),
            ENNReal.ofReal |∫ x,κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i)|
        (∫⁻ a,J a) ≤ ENNReal.ofReal K *
          (ENNReal.ofReal (∫ x,hsNormSq (Z x)))^((1 : ℝ)/2) *
          (ENNReal.ofReal (∫ x,hsNormSq (Dw x)))^((1 : ℝ)/2) ∧
          (∫⁻ a,J a)<(∞ : ℝ≥0∞) := by
  obtain ⟨p,_hpFormula,_hp1,_hp2,C,K,_hC,hK,H⟩ := exists_divcurl_integrable_kernel_majorant n hn
  refine ⟨K,hK,?_⟩
  intro q Z hZ hdiv w Dw hw hDw J
  obtain ⟨_hM,hBound,hMI,_hMAE,hKernel⟩ := H q Z hZ hdiv w Dw hw hDw
  have hPoint (a : Domain n) : J a≤ENNReal.ofReal C *
      (dyadicBallMaximal (fun x=>ENNReal.ofReal ((Real.sqrt (hsNormSq (Z x)))^(p : ℝ))) a)^(1/(p : ℝ)) *
      (dyadicBallMaximal (fun x=>ENNReal.ofReal ((Real.sqrt (hsNormSq (Dw x)))^(p : ℝ))) a)^(1/(p : ℝ)) := by
    refine iSup_le fun r=>iSup_le fun κ=>iSup_le fun hκ=>iSup_le fun hcκ=>
      iSup_le fun hsκ=>iSup_le fun hDκ=>?_ 
    exact (hKernel a r.val r.property κ hκ hcκ hsκ hDκ).2
  exact ⟨(lintegral_mono hPoint).trans hBound,(lintegral_mono hPoint).trans_lt hMI⟩

end StationaryHarmonicMaps.Analysis

end

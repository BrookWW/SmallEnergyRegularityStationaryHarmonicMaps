/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.HSProductIntegrals
public import StationaryHarmonicMaps.Analysis.HilbertSchmidtLpDecoding
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Ordinary three-factor Holder estimates

Actual L2, Ls and Lr data with reciprocal exponents summing to one
produce an integrable ordinary product and its full moment bound.
-/

public section

open HarmonicMaps MeasureTheory Filter
open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Nonnegative actual L2, Ls and Lr functions have an integrable ordinary
triple product with the exact three energy/moment factors. -/
theorem integral_three_factor_holder {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (r s : ℝ) (hr : 2<r) (hs : 2<s) (hInv : 1/s+1/r=1/2)
    (f g h : X → ℝ) (hf : MemLp f 2 μ)
    (hg : MemLp g (ENNReal.ofReal s) μ) (hh : MemLp h (ENNReal.ofReal r) μ)
    (hf0 : ∀x,0≤f x) (hg0 : ∀x,0≤g x) (hh0 : ∀x,0≤h x) :
    Integrable (fun x=>f x*g x*h x) μ ∧
      (∫x,f x*g x*h x ∂μ)≤Real.sqrt (∫x,(f x)^2 ∂μ)*
        (∫x,(g x)^s ∂μ)^(1/s)*(∫x,(h x)^r ∂μ)^(1/r) := by
  have hr0 : 0<r := lt_trans (by norm_num) hr
  have hs0 : 0<s := lt_trans (by norm_num) hs
  have hTriple : Real.HolderTriple s r 2 :=
    ⟨by simpa only [one_div] using hInv,hs0,hr0⟩
  letI : ENNReal.HolderTriple (ENNReal.ofReal s) (ENNReal.ofReal r) (ENNReal.ofReal 2) :=
    hTriple.ennrealOfReal
  have hgh' : MemLp (fun x=>g x*h x) (ENNReal.ofReal 2) μ := hh.mul' hg
  have hgh : MemLp (fun x=>g x*h x) 2 μ := by simpa only [ENNReal.ofReal_ofNat] using hgh'
  obtain ⟨hI,hCS⟩ := integral_mul_le_sqrt_energy_roots hf hgh
    (Eventually.of_forall hf0) (Eventually.of_forall fun x=>mul_nonneg (hg0 x) (hh0 x))
  have hgSq : MemLp (fun x=>(g x)^2) (ENNReal.ofReal (s/2)) μ := by
    have H := hg.norm_rpow_div 2
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,
      ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),ENNReal.ofReal_ofNat] using H
  have hhSq : MemLp (fun x=>(h x)^2) (ENNReal.ofReal (r/2)) μ := by
    have H := hh.norm_rpow_div 2
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,
      ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),ENNReal.ofReal_ofNat] using H
  have hConj : Real.HolderConjugate (s/2) (r/2) := by
    refine ⟨?_,half_pos hs0,half_pos hr0⟩
    calc
      _=2*(1/s+1/r) := by field_simp
      _=_ := by rw [hInv];norm_num
  have hGH := integral_mul_le_Lp_mul_Lq_of_nonneg hConj
    (Eventually.of_forall fun x=>sq_nonneg (g x))
    (Eventually.of_forall fun x=>sq_nonneg (h x)) hgSq hhSq
  have hGPower (x : X) : ((g x)^2)^(s/2)=(g x)^s := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (hg0 x)]
    congr 1
    ring
  have hHPower (x : X) : ((h x)^2)^(r/2)=(h x)^r := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (hh0 x)]
    congr 1
    ring
  simp only [hGPower,hHPower,←mul_pow] at hGH
  have hRoot : Real.sqrt (∫x,(g x*h x)^2 ∂μ)≤
      (∫x,(g x)^s ∂μ)^(1/s)*(∫x,(h x)^r ∂μ)^(1/r) := by
    have H := Real.sqrt_le_sqrt hGH
    rw [Real.sqrt_mul (Real.rpow_nonneg (integral_nonneg fun x=>Real.rpow_nonneg (hg0 x) s) _)] at H
    simp only [Real.sqrt_eq_rpow,←Real.rpow_mul
      (integral_nonneg fun x=>Real.rpow_nonneg (hg0 x) s),←Real.rpow_mul
      (integral_nonneg fun x=>Real.rpow_nonneg (hh0 x) r)] at H
    have hsScale : 1/(s/2)*(1/2)=1/s := by field_simp
    have hrScale : 1/(r/2)*(1/2)=1/r := by field_simp
    simpa only [Real.sqrt_eq_rpow,hsScale,hrScale] using H
  refine ⟨by simpa only [mul_assoc] using hI,?_⟩
  have H := hCS.trans (mul_le_mul_of_nonneg_left hRoot (Real.sqrt_nonneg _))
  simpa only [mul_assoc] using H

private theorem norm_frame_derivative_pairing_le {n m q : ℕ}
    (L : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (D : Gradient n m) (w : Ambient q) (Q : Gradient n q) :
    ‖∑i : Fin n,inner ℝ (L (D i) w) (Q i)‖≤
      ‖L‖*(Real.sqrt (hsNormSq D)*‖w‖*Real.sqrt (hsNormSq Q)) := by
  let A := fun i=>L (D i) w
  let C := ‖L‖*‖w‖
  have hC : 0≤C := mul_nonneg (norm_nonneg L) (norm_nonneg w)
  have hCol (i : Fin n) : ‖A i‖≤C*‖D i‖ := by
    calc
      _≤‖L (D i)‖*‖w‖ := (L (D i)).le_opNorm w
      _≤(‖L‖*‖D i‖)*‖w‖ := mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)
      _=_ := by dsimp only [C];ring
  have hSq : hsNormSq A≤C^2*hsNormSq D := by
    calc
      _≤∑i : Fin n,(C*‖D i‖)^2 := Finset.sum_le_sum fun i _=>
        pow_le_pow_left₀ (norm_nonneg _) (hCol i) 2
      _=_ := by simp only [mul_pow,hsNormSq,Finset.mul_sum]
  have hRoot : Real.sqrt (hsNormSq A)≤C*Real.sqrt (hsNormSq D) := by
    apply (Real.sqrt_le_sqrt hSq).trans_eq
    rw [Real.sqrt_mul (sq_nonneg C),Real.sqrt_sq hC]
  have hNorm (H : Gradient n q) :
      ‖WithLp.toLp 2 (fun k : Fin (n*q)=>H (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)‖=
        Real.sqrt (hsNormSq H) := by
    rw [←hs_flatten_norm_sq H,Real.sqrt_sq (norm_nonneg _)]
  have H := norm_inner_le_norm (𝕜:=ℝ)
    (WithLp.toLp 2 (fun k : Fin (n*q)=>A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2))
    (WithLp.toLp 2 (fun k : Fin (n*q)=>Q (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2))
  rw [hs_flatten_inner,hNorm,hNorm] at H
  exact H.trans ((mul_le_mul_of_nonneg_right hRoot (Real.sqrt_nonneg _)).trans_eq (by dsimp only [C];ring))

/-- The ordinary frame-derivative contraction is genuinely integrable
and satisfies the complete-HS three-factor Holder bound without a full
tensor-derivative Lr assumption or a dimension-factor loss. -/
theorem integral_frame_derivative_three_factor_holder {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {n m q : ℕ} (r s : ℝ) (hr : 2<r) (hs : 2<s)
    (hInv : 1/s+1/r=1/2)
    (D : X → Gradient n m) (hD : ∀i,MemLp (fun x=>D x i) 2 μ)
    (L : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (w : X → Ambient q) (hw : MemLp w (ENNReal.ofReal s) μ)
    (Q : X → Gradient n q)
    (hQ : MemLp (fun x=>WithLp.toLp 2 (fun k : Fin (n*q)=>
      Q x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) (ENNReal.ofReal r) μ) :
    Integrable (fun x=>∑i : Fin n,inner ℝ (L (D x i) (w x)) (Q x i)) μ ∧
    |∫x,∑i : Fin n,inner ℝ (L (D x i) (w x)) (Q x i) ∂μ|≤
      ‖L‖*Real.sqrt (∫x,hsNormSq (D x) ∂μ)*
        (∫x,‖w x‖^s ∂μ)^(1/s)*(∫x,(hsNormSq (Q x))^(r/2) ∂μ)^(1/r) := by
  have hNorm (H : Gradient n q) :
      ‖WithLp.toLp 2 (fun k : Fin (n*q)=>H (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)‖=
        Real.sqrt (hsNormSq H) := by
    rw [←hs_flatten_norm_sq H,Real.sqrt_sq (norm_nonneg _)]
  have hQNorm : MemLp (fun x=>Real.sqrt (hsNormSq (Q x))) (ENNReal.ofReal r) μ := by
    simpa only [hNorm] using hQ.norm
  obtain ⟨hI,hBound⟩ := integral_three_factor_holder μ r s hr hs hInv
    (fun x=>Real.sqrt (hsNormSq (D x))) (fun x=>‖w x‖) (fun x=>Real.sqrt (hsNormSq (Q x)))
    (memLp_sqrt_sum_norm_sq D hD) hw.norm hQNorm
    (fun _=>Real.sqrt_nonneg _) (fun _=>norm_nonneg _) (fun _=>Real.sqrt_nonneg _)
  have hQCol (i : Fin n) : MemLp (fun x=>Q x i) (ENNReal.ofReal r) μ :=
    (memLp_hs_unflatten_exponent _ (ENNReal.ofReal r) hQ i).ae_eq
      (Eventually.of_forall fun x=>congrFun (hs_unflatten_flatten (Q x)) i)
  have hMeas : AEStronglyMeasurable (fun x=>∑i : Fin n,inner ℝ (L (D x i) (w x)) (Q x i)) μ := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    have hL := L.continuous.comp_aestronglyMeasurable (hD i).aestronglyMeasurable
    exact ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hL.prodMk hw.aestronglyMeasurable)).inner (hQCol i).aestronglyMeasurable
  have hPoint := fun x=>norm_frame_derivative_pairing_le L (D x) (w x) (Q x)
  have hPairI : Integrable (fun x=>∑i : Fin n,inner ℝ (L (D x i) (w x)) (Q x i)) μ :=
    (hI.const_mul ‖L‖).mono' hMeas (Eventually.of_forall hPoint)
  have hQPower (x : X) : (Real.sqrt (hsNormSq (Q x)))^r=(hsNormSq (Q x))^(r/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (hsNormSq_nonneg _)]
    congr 1
    ring
  simp only [Real.sq_sqrt (hsNormSq_nonneg _),hQPower] at hBound
  refine ⟨hPairI,?_⟩
  calc
    _≤∫x,‖∑i : Fin n,inner ℝ (L (D x i) (w x)) (Q x i)‖ ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x=>∑i : Fin n,inner ℝ (L (D x i) (w x)) (Q x i))
    _≤∫x,‖L‖*(Real.sqrt (hsNormSq (D x))*‖w x‖*Real.sqrt (hsNormSq (Q x))) ∂μ :=
      integral_mono hPairI.norm (hI.const_mul ‖L‖) hPoint
    _=‖L‖*(∫x,Real.sqrt (hsNormSq (D x))*‖w x‖*Real.sqrt (hsNormSq (Q x)) ∂μ) := integral_const_mul _ _
    _≤_ := (mul_le_mul_of_nonneg_left hBound (norm_nonneg L)).trans_eq (by ring)

end StationaryHarmonicMaps.Analysis

end

/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.ThreeFactorHolder
public import StationaryHarmonicMaps.Analysis.CoexactNativeDualTestBall
public import StationaryHarmonicMaps.Analysis.CoexactFrameCutoffPairing

/-!
# Compensated low-power control of the same actual relative coexact field

The original native gradient complement identifies the same coexact
field's pairing with the frame-cutoff forcing. Its constructed power
dual has the genuine conjugate moment. Three-factor Holder and power
cancellation give the low-power bound from the actual centered cutoff.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The genuine conjugate exponents for the coexact three-factor pairing. -/
theorem coexact_three_factor_exponents (p : ℝ) (hpOne : 1<p) (hpTwo : p<2) :
    2<p/(p-1) ∧ 2<2*p/(2-p) ∧
      1/(2*p/(2-p))+1/(p/(p-1))=1/2 := by
  have hp : 0<p := zero_lt_one.trans hpOne
  have hm : 0<p-1 := sub_pos.mpr hpOne
  have ht : 0<2-p := sub_pos.mpr hpTwo
  refine ⟨(lt_div_iff₀ hm).mpr (by linarith only [hpTwo]),
    (lt_div_iff₀ ht).mpr (by linarith only [hpOne]),?_⟩
  field_simp
  ring

/-- Every actual relative coexact field of the original native frame-cutoff
forcing has its compensated Lp bound. The power dual, exact pairing and
all pairing integrability are constructed; no high-power full tensor
derivative is assumed. -/
theorem exists_coexact_compensated_lp_bound_ball (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1<p) (hpTwo : p<2) :
    ∃C : ℝ,0<C ∧ ∀m q : ℕ,
      ∀(b : Domain n) (R : ℝ),0<R →
      ∀(U : Domain n → Ambient m) (DU : Domain n → Gradient n m),
      MemW12 (ballDomain b R) U DU →
      ∀M : ℝ,(∀ᵐx∂volume.restrict (ball b R),‖U x‖≤M) →
      ∀L : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q),
      ∀(v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
      HasZeroBoundaryValues (ballDomain b R) v Dv →
      ∀N : ℝ,(∀ᵐx∂volume.restrict (ball b R),‖v x‖≤N) →
      ∀(a : Domain n) (t : ℝ),0<t → ball a t⊆ball b R → ∀z : Ambient q,
      let s := 2*p/(2-p)
      let μ := volume.restrict (ball a t)
      MemLp (fun x=>v x-z) (ENNReal.ofReal s) μ →
      ∀(P : Domain n → Gradient n q) (f : Domain n → Ambient q) (Df : Domain n → Gradient n q),
        MemW12 (ballDomain a t) f Df → (∀i,MemLp (fun x=>P x i) 2 μ) →
        (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain a t) ψ Dψ →
          (∫x,∑i : Fin n,inner ℝ (P x i) (Dψ x i) ∂μ)=0) →
        (∀ᵐx∂μ,∀i,L (U x) (Dv x i)=Df x i+P x i) →
        Integrable (fun x=>(hsNormSq (P x))^(p/2)) μ ∧
        (∫x,(hsNormSq (P x))^(p/2) ∂μ)^(1/p)≤
          C*‖L‖*Real.sqrt (∫x,hsNormSq (DU x) ∂μ)*(∫x,‖v x-z‖^s ∂μ)^(1/s) := by
  have hp : 0<p := zero_lt_one.trans hpOne
  let r := p/(p-1)
  obtain ⟨hr,hs,hInv⟩ := coexact_three_factor_exponents p hpOne hpTwo
  have hr0 : 0<r := lt_trans (by norm_num) hr
  obtain ⟨D,hD,Hdual⟩ := exists_native_coexact_dual_test_ball n hn p hpOne hpTwo
  refine ⟨D^(1/r),Real.rpow_pos_of_pos hD _,?_⟩
  intro m q b R hR U DU hU M hUBound L v Dv hv N hvBound a t ht hSub z s μ hw P f Df hf hP hPN hDecomp
  have hF (i : Fin n) : MemLp (fun x=>L (U x) (Dv x i)) 2 μ :=
    (memLp_bounded_native_frame_columns (ballDomain b R) U DU hU M hUBound L Dv hv.1.2.2 i).mono_measure
      (Measure.restrict_mono_set volume hSub)
  obtain ⟨c,Dc,Q,_hc,hQ,_hSkew,_hClosed,_hDiv,_hNormal,hQN,_hH1,hQr,
    _hPQI,hPI,_hQI,hPower,hMoment⟩ := Hdual q a t ht P hP hPN
  obtain ⟨_hPQI',_hFQI,hPair⟩ := native_coexact_pairing_of_gradient_complement (ballDomain a t)
    _ P f Df hf hF hP hDecomp Q hQ (fun ψ Dψ hψ=>(hQN ψ Dψ hψ).2)
  obtain ⟨_hF',_hA,_hFQI',_hAQI,hComp⟩ :=
    native_frame_cutoff_solenoidal_pairing_ball b R hR U DU hU M hUBound L v Dv hv N hvBound
      a t hSub z Q hQ (fun ψ Dψ hψ=>(hQN ψ Dψ hψ).2)
  have hDU (i : Fin n) : MemLp (fun x=>DU x i) 2 μ :=
    (hU.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)
  obtain ⟨_hTripleI,hTriple⟩ := integral_frame_derivative_three_factor_holder μ r s hr hs hInv
    DU hDU L (fun x=>v x-z) hw Q hQr
  let I := ∫x,(hsNormSq (P x))^(p/2) ∂μ
  have hI0 : 0≤I := integral_nonneg fun x=>Real.rpow_nonneg (hsNormSq_nonneg _) _
  have hExact : I= -(∫x,∑i : Fin n,inner ℝ (L (DU x i) (v x-z)) (Q x i) ∂μ) :=
    hPower.symm.trans (hPair.trans hComp)
  let A := ‖L‖*Real.sqrt (∫x,hsNormSq (DU x) ∂μ)*(∫x,‖v x-z‖^s ∂μ)^(1/s)
  have hA : 0≤A := mul_nonneg (mul_nonneg (norm_nonneg L) (Real.sqrt_nonneg _))
    (Real.rpow_nonneg (integral_nonneg fun _=>Real.rpow_nonneg (norm_nonneg _) _) _)
  have hPairBound : I≤A*(∫x,(hsNormSq (Q x))^(r/2) ∂μ)^(1/r) := by
    have HI : |I|=|∫x,∑i : Fin n,inner ℝ (L (DU x i) (v x-z)) (Q x i) ∂μ| := by
      rw [hExact,abs_neg]
    rw [←HI,abs_of_nonneg hI0] at hTriple
    exact hTriple
  have hStep : I≤(A*D^(1/r))*I^(1/r) := by
    calc
      _≤A*(∫x,(hsNormSq (Q x))^(r/2) ∂μ)^(1/r) := hPairBound
      _≤A*(D*I)^(1/r) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (integral_nonneg fun _=>Real.rpow_nonneg (hsNormSq_nonneg _) _) hMoment
        (one_div_nonneg.mpr hr0.le)) hA
      _=_ := by rw [Real.mul_rpow hD.le hI0];ring
  have hRoot : I^(1/p)≤A*D^(1/r) := by
    by_cases hZero : I=0
    · rw [hZero,Real.zero_rpow (one_div_pos.mpr hp).ne']
      exact mul_nonneg hA (Real.rpow_nonneg hD.le _)
    · have hI : 0<I := lt_of_le_of_ne hI0 (Ne.symm hZero)
      have hConj : p.HolderConjugate r := Real.HolderConjugate.conjExponent hpOne
      have hInvPR : 1/p+1/r=1 := by simpa only [one_div] using hConj.inv_add_inv_eq_one
      have hSplit : I=I^(1/p)*I^(1/r) := by rw [←Real.rpow_add hI,hInvPR,Real.rpow_one]
      exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hI (1/r))).mp
        (by simpa only [mul_comm] using hSplit.symm.trans_le hStep)
  exact ⟨hPI,hRoot.trans_eq (by dsimp only [A];ring)⟩

end StationaryHarmonicMaps.Analysis

end

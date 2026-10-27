module

public import StationaryHarmonicMaps.Analysis.BoundaryCompensatedBilinear
public import StationaryHarmonicMaps.Analysis.CoexactNativeVariationalPairing

/-!
# Actual compensated coexact response of a centered coefficient

The original bounded critical coefficient acts on any actual native test
gradient. The coexact response is constructed from the real L2 product.
Natural cancellation removes its constant coefficient, and the whole-ball
compensated pairing controls the same response energy.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- A centered bounded critical coefficient acting on an arbitrary native
gradient produces a real relative response with the homogeneous compensated
energy bound; the centering vector does not enter the constant. -/
theorem exists_boundary_centered_coexact_compensated_energy (n : ℕ) (hn : 2≤n)
    (m k : ℕ) (B : Ambient m →L[ℝ] (Ambient m →L[ℝ] Ambient k)) :
    ∃C : ℝ,0<C ∧ ∀ (u : Domain n → Ambient m) (Du : Domain n → Gradient n m)
      (η M : ℝ),MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M) →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀ (w : Domain n → Ambient m) (Dw : Domain n → Gradient n m),
        MemW12 (ballDomain (0 : Domain n) 1) w Dw → ∀c : Ambient m,
      ∃ (b : Fin n → Fin n → Domain n → Ambient k)
        (Db : Fin n → Fin n → Domain n → Gradient n k)
        (Q : Domain n → Gradient n k) (v : Domain n → Ambient k)
        (Dv : Domain n → Gradient n k),
        MemW12 (ballDomain (0 : Domain n) 1) v Dv ∧
        (∀i j,MemW12 (ballDomain (0 : Domain n) 1) (b i j) (Db i j)) ∧
        (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i j,b i j x= -b j i x) ∧
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i j l,
          Db i j x l+Db j l x i+Db l i x j=0) ∧
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀j,(∑i : Fin n,Db i j x i)=Q x j) ∧
        (∀(j : Fin n) (ψ : Domain n → Ambient k) (Dψ : Domain n → Gradient n k),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (b i j x) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
          IntegrableOn (fun x=>inner ℝ (Q x j) (ψ x)) (ball (0 : Domain n) 1) volume ∧
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (b i j x) (Dψ x i))=
            -(∫x in ball (0 : Domain n) 1,inner ℝ (Q x j) (ψ x))) ∧
        (∀(ψ : Domain n → Ambient k) (Dψ : Domain n → Gradient n k),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) ∧
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i,
          B (u x-c) (Dw x i)=Dv x i+Q x i) ∧
        (∫x in ball (0 : Domain n) 1,hsNormSq (Q x))≤
          C*η^2*(∫x in ball (0 : Domain n) 1,hsNormSq (Dw x)) := by
  let A : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient m) :=
    (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient m) (F:=Ambient k)).toContinuousLinearMap.comp B
  obtain ⟨D,hD,Hpair⟩ := exists_boundary_bilinear_critical_native_divcurl_bound n hn m k m A
  refine ⟨D^2,sq_pos_of_pos hD,?_⟩
  intro u Du η M hu hη huBound hCritical w Dw hw c
  let μ := volume.restrict (ball (0 : Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have huLp : MemLp u 2 μ := hu.2.1
  let F := fun x i=>B (u x-c) (Dw x i)
  have hF (i : Fin n) : MemLp (fun x=>F x i) 2 μ := by
    have hMeas : AEStronglyMeasurable (fun x=>F x i) μ :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        ((B.continuous.comp_aestronglyMeasurable (huLp.sub (memLp_const c)).aestronglyMeasurable).prodMk
          (hw.2.2 i).aestronglyMeasurable)
    apply (hw.2.2 i).of_le_mul (c:=‖B‖*(|M|+‖c‖)) hMeas
    filter_upwards [huBound] with x hx
    calc
      _≤‖B (u x-c)‖*‖Dw x i‖ := (B (u x-c)).le_opNorm _
      _≤(‖B‖*‖u x-c‖)*‖Dw x i‖ := mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
      _≤(‖B‖*(|M|+‖c‖))*‖Dw x i‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((norm_sub_le (u x) c).trans (add_le_add (hx.trans (le_abs_self M)) (le_refl ‖c‖))) (norm_nonneg B)) (norm_nonneg _)
  obtain ⟨b,Db,Q,v,Dv,hv,hb,hQ,hSkew,hClosed,hDiv,hNormal,hNatural,hDecomp,_hEnergy,hPair⟩ :=
    exists_relative_coexact_native_pairing_unitBall hn F hF
  have hEnergyEq : (∫x,hsNormSq (Q x) ∂μ)=
      ∫x,∑i : Fin n,inner ℝ (F x i) (Q x i) ∂μ := by
    simpa only [real_inner_self_eq_norm_sq,hsNormSq] using
      (hPair Q hQ (fun ψ Dψ hψ=>(hNatural ψ Dψ hψ).2)).2.2
  obtain ⟨_hI,hEstimate⟩ := Hpair u Du η M hu hη huBound hCritical Q hQ
    (fun ψ Dψ hψ=>(hNatural ψ Dψ hψ).2) w Dw hw
  have hConst : MemW12 (ballDomain (0 : Domain n) 1) (fun x=>B c (w x))
      (fun x i=>B c (Dw x i)) :=
    ⟨(memW12Loc_continuousLinearMap hw.to_memW12Loc (B c)).1,
      (B c).lipschitz.comp_memLp (map_zero (B c)) hw.2.1,
      fun i=>(B c).lipschitz.comp_memLp (map_zero (B c)) (hw.2.2 i)⟩
  have hConstI : Integrable (fun x=>∑i : Fin n,inner ℝ (B c (Dw x i)) (Q x i)) μ :=
    integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two
      (hConst.2.2 i) (hQ i))
  have hConstZero : (∫x,∑i : Fin n,inner ℝ (B c (Dw x i)) (Q x i) ∂μ)=0 := by
    simpa only [real_inner_comm] using (hNatural _ _ hConst).2
  have hAdj (x : Domain n) :
      (∑i : Fin n,inner ℝ (A (u x) (Q x i)) (Dw x i))=
        (∑i : Fin n,inner ℝ (F x i) (Q x i))+
          (∑i : Fin n,inner ℝ (B c (Dw x i)) (Q x i)) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℝ ((B (u x)).adjoint (Q x i)) (Dw x i)=_
    rw [ContinuousLinearMap.adjoint_inner_left,real_inner_comm]
    change inner ℝ (B (u x) (Dw x i)) (Q x i)=_
    dsimp only [F]
    rw [map_sub,sub_apply,inner_sub_left]
    ring
  have hFQI : Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Q x i)) μ :=
    integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hF i) (hQ i))
  rw [integral_congr_ae (Eventually.of_forall hAdj),integral_add hFQI hConstI,
    hConstZero,add_zero,←hEnergyEq] at hEstimate
  let X := ∫x,hsNormSq (Q x) ∂μ
  let Y := ∫x,hsNormSq (Dw x) ∂μ
  have hX : 0≤X := integral_nonneg fun _=>hsNormSq_nonneg _
  have hY : 0≤Y := integral_nonneg fun _=>hsNormSq_nonneg _
  have hRoot : Real.sqrt X≤D*η*Real.sqrt Y := by
    by_cases hx : X=0
    · rw [hx,Real.sqrt_zero]
      positivity
    · have hPos : 0<Real.sqrt X := Real.sqrt_pos.mpr (lt_of_le_of_ne hX (Ne.symm hx))
      apply (mul_le_mul_iff_right₀ hPos).mp
      rw [← pow_two,Real.sq_sqrt hX]
      exact ((le_abs_self X).trans hEstimate).trans_eq (by ring)
  have hFinal : X≤D^2*η^2*Y := by
    have H := pow_le_pow_left₀ (Real.sqrt_nonneg X) hRoot 2
    rwa [mul_pow,mul_pow,Real.sq_sqrt hX,Real.sq_sqrt hY] at H
  exact ⟨b,Db,Q,v,Dv,hv,hb,hQ,hSkew,hClosed,hDiv,hNormal,hNatural,hDecomp,hFinal⟩

end StationaryHarmonicMaps.Analysis

end

/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.NaturalCoefficientNeumannKernel
public import StationaryHarmonicMaps.Analysis.StrongerMorreyMeanBound
public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds

/-!
# Actual mean-zero Neumann response of a natural coefficient

The actual original map minus its original mean has a bounded stronger
representative. Its bilinear forcing has a full-ball energy bound using
only the original critical coefficient and stronger derivative growth.
The true native Neumann projection answers the uncentered original
forcing because every constant right mode is genuinely natural.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original natural critical coefficient data and original stronger
native map data produce their actual mean-zero Neumann response and its
full-ball energy bound, with a constant chosen before all field data. -/
theorem exists_natural_coefficient_neumann_initial_response
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃D : ℝ,0<D ∧ ∀(m k q : ℕ)
      (B : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient q))
      (Z : Domain n → Gradient n m) (u : Domain n → Ambient k)
      (Du : Domain n → Gradient n k) (η Ku : ℝ),
      (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      (∀(ψ : Domain n → Ambient m) (Dψ : Domain n → Gradient n m),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) →
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      criticalGradientMorreySquare Z (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) → 0≤Ku →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤Ku*r^((n : ℝ)-2+γ)) →
      ∃(g : Domain n → Ambient q) (Q : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) g Q ∧
        (∫x in ball (0 : Domain n) 1,g x)=0 ∧
        (∀i,MemLp (fun x=>B (Z x i) (u x)) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
        (∫x in ball (0 : Domain n) 1,hsNormSq (Q x))≤D*‖B‖^2*η^2*Ku ∧
        ∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
            ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i) := by
  obtain ⟨H,hH,Hmean⟩ := exists_stronger_morrey_ae_bound_by_mean n hn γ hγ hγTwo
  refine ⟨H^2,sq_pos_of_pos hH,?_⟩
  intro m k q B Z u Du η Ku hZ hNatural hu _hη hCritical hKu hGrowth
  let μ := volume.restrict (ball (0 : Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let c := ⨍x in ball (0 : Domain n) 1,u x
  let w := fun x=>u x-c
  have huLp : MemLp u 2 μ := hu.2.1
  have hwLp : MemLp w 2 μ := huLp.sub (memLp_const c)
  have hw : MemW12 (ballDomain (0 : Domain n) 1) w Du :=
    ⟨(memW12Loc_sub_const hu.to_memW12Loc c).1,hwLp,hu.2.2⟩
  have hMeanZero : (⨍x in ball (0 : Domain n) 1,w x)=0 := by
    have hInt : (∫x,w x ∂μ)=0 := integral_sub_average μ u
    change (⨍x,w x ∂μ)=0
    rw [average_eq,hInt,smul_zero]
  obtain ⟨_V,_hV,_hAE,_hPoint,hWBound⟩ := Hmean k w Du Ku hw hKu hGrowth
  have hBound : ∀ᵐx∂μ,‖w x‖≤H*Real.sqrt Ku := by
    simpa only [hMeanZero,norm_zero,zero_add] using hWBound
  have hM : 0≤H*Real.sqrt Ku := mul_nonneg hH.le (Real.sqrt_nonneg Ku)
  obtain ⟨hF,hFEnergy⟩ := bilinear_hs_energy_of_bounded_right μ B w hw.2.1.aestronglyMeasurable
    (H*Real.sqrt Ku) hBound Z hZ
  let F := fun x i=>B (Z x i) (u x-c)
  have hF' (i : Fin n) : MemLp (fun x=>F x i) 2 μ := hF i
  have hRaw := bilinear_raw_memLp_of_centered_unitBall Z hZ B u c hF'
  obtain ⟨_hCentered,Hcentered⟩ := natural_coefficient_centered_pairing_unitBall Z hZ hNatural B u hRaw c
  have hZTotal : (∫x in ball (0 : Domain n) 1,hsNormSq (Z x))≤η^2 := by
    have HZ := integral_hsNormSq_le_of_criticalMorrey Z
      (mem_ball_self (by norm_num : (0 : ℝ)<1)) (by norm_num : (0 : ℝ)<1) (sq_nonneg η)
      (fun x hx=>⟨hx,hx⟩) hZ hCritical
    simpa only [Real.one_rpow,mul_one] using HZ
  have hFTotal : (∫x in ball (0 : Domain n) 1,hsNormSq (F x))≤H^2*‖B‖^2*η^2*Ku := by
    calc
      _≤(‖B‖*|H*Real.sqrt Ku|)^2*(∫x in ball (0 : Domain n) 1,hsNormSq (Z x)) := hFEnergy
      _≤(‖B‖*|H*Real.sqrt Ku|)^2*η^2 :=
        mul_le_mul_of_nonneg_left hZTotal (sq_nonneg _)
      _=_ := by rw [abs_of_nonneg hM,mul_pow,mul_pow,Real.sq_sqrt hKu];ring
  obtain ⟨g,Q,hg,hMean,hEnergy,hTests⟩ := exists_neumann_gradient_projection (0 : Domain n)
    (by norm_num : (0 : ℝ)<1) F hF'
  refine ⟨g,Q,hg,hMean,hRaw,hEnergy.trans hFTotal,?_⟩
  intro ψ Dψ hψ
  obtain ⟨hQI,_hFI,hEq⟩ := hTests ψ Dψ hψ
  obtain ⟨hRawI,_hCenteredI,hCenterEq⟩ := Hcentered ψ Dψ hψ
  exact ⟨hQI,hRawI,hEq.trans hCenterEq⟩

end StationaryHarmonicMaps.Analysis

end

/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.NaturalCoefficientNeumannKernel
public import StationaryHarmonicMaps.Analysis.BoundaryStrongerMorreyRepresentative
public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds
public import StationaryHarmonicMaps.Analysis.ZeroExtendedHSEnergy

/-!
# Actual localized forcing energy from stronger native oscillation

The original stronger gradient growth constructs the actual closed-ball
Holder representative. Its value at each original center supplies a true
constant. On the localized ball, its Holder difference multiplies the
original critical coefficient energy. The literal indicator forcing is
L2 and has the resulting stronger power energy without a new bound input.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original closed representative and critical coefficient produce
actual centered and localized bilinear forcing fields at every original
center, with a stronger power coefficient depending only on n and γ. -/
theorem exists_natural_coefficient_near_forcing_energy
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃D : ℝ,0<D ∧ ∀(m k q : ℕ)
      (B : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient q))
      (Z : Domain n → Gradient n m) (u : Domain n → Ambient k)
      (Du : Domain n → Gradient n k) (η Ku : ℝ),
      (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      criticalGradientMorreySquare Z (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤Ku →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤Ku*r^((n : ℝ)-2+γ)) →
      ∃V : closedBall (0 : Domain n) 1 → Ambient k,
        Continuous V ∧
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀hx : x∈ball (0 : Domain n) 1,
          V ⟨x,ball_subset_closedBall hx⟩=u x) ∧
        ∀(a : Domain n) (ha : a∈ball (0 : Domain n) 1),
          let c := V ⟨a,ball_subset_closedBall ha⟩
          let F := fun x i=>B (Z x i) (u x-c)
          (∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
          ∀r : ℝ,0<r →
            let Fnear := (ball a r).indicator F
            (∀i,MemLp (fun x=>Fnear x i) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
            (∫x in ball (0 : Domain n) 1,hsNormSq (Fnear x))≤D*‖B‖^2*η^2*Ku*r^((n : ℝ)-2+γ) := by
  obtain ⟨H,hH,Hrep⟩ := existsUnique_closedBall_holder_representative_of_stronger_morrey n hn γ hγ hγTwo
  refine ⟨H^2,sq_pos_of_pos hH,?_⟩
  intro m k q B Z u Du η Ku hZ hCritical hu hKu hGrowth
  obtain ⟨V,⟨hV,hAE,hHolder⟩,_hUnique⟩ := Hrep k u Du Ku hu hKu hGrowth
  refine ⟨V,hV,hAE,?_⟩
  intro a ha c F
  let μ := volume.restrict (ball (0 : Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let w := fun x=>u x-c
  have huLp : MemLp u 2 μ := hu.2.1
  have hw : MemLp w 2 μ := huLp.sub (memLp_const c)
  have hGlobal : ∀ᵐx∂μ,‖w x‖≤H*Real.sqrt Ku*(2 : ℝ)^(γ/2) := by
    filter_upwards [hAE,ae_restrict_mem measurableSet_ball] with x hx hxBall
    have hx0 : dist x (0 : Domain n)≤1 := ball_subset_closedBall hxBall
    have ha0 : dist (0 : Domain n) a≤1 := by rw [dist_comm];exact ball_subset_closedBall ha
    have hDist : dist x a≤2 := (dist_triangle x 0 a).trans (by linarith only [hx0,ha0])
    change ‖u x-c‖≤_
    rw [←hx hxBall]
    exact (hHolder ⟨x,ball_subset_closedBall hxBall⟩ ⟨a,ball_subset_closedBall ha⟩).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hDist (half_pos hγ).le)
        (mul_nonneg hH.le (Real.sqrt_nonneg _)))
  obtain ⟨hF,_hGlobalEnergy⟩ := bilinear_hs_energy_of_bounded_right μ B w hw.aestronglyMeasurable
    (H*Real.sqrt Ku*(2 : ℝ)^(γ/2)) hGlobal Z hZ
  refine ⟨hF,?_⟩
  intro r hr Fnear
  have hNear (i : Fin n) : MemLp (fun x=>Fnear x i) 2 μ := by
    have HI : MemLp ((ball a r).indicator (fun x=>F x i)) 2 μ := (hF i).indicator measurableSet_ball
    apply HI.ae_eq
    exact Eventually.of_forall fun x=>by
      by_cases hx : x∈ball a r
      · simp only [Fnear,indicator_of_mem hx]
      · simp only [Fnear,indicator_of_notMem hx,Pi.zero_apply]
  let S := ball a r∩ball (0 : Domain n) 1
  let μS := volume.restrict S
  have hμ : μS≤μ := Measure.restrict_mono_set volume inter_subset_right
  have hwS : AEStronglyMeasurable w μS := (hw.mono_measure hμ).aestronglyMeasurable
  have hZS (i : Fin n) : MemLp (fun x=>Z x i) 2 μS := (hZ i).mono_measure hμ
  let M := H*Real.sqrt Ku*r^(γ/2)
  have hM : 0≤M := mul_nonneg (mul_nonneg hH.le (Real.sqrt_nonneg _)) (Real.rpow_nonneg hr.le _)
  have hLocal : ∀ᵐx∂μS,‖w x‖≤M := by
    filter_upwards [hAE.filter_mono (ae_mono hμ),
      ae_restrict_mem (measurableSet_ball.inter measurableSet_ball)] with x hx hxS
    change ‖u x-c‖≤_
    rw [←hx hxS.2]
    exact (hHolder ⟨x,ball_subset_closedBall hxS.2⟩ ⟨a,ball_subset_closedBall ha⟩).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hxS.1.le (half_pos hγ).le)
        (mul_nonneg hH.le (Real.sqrt_nonneg _)))
  obtain ⟨_hFS,hEnergy⟩ := bilinear_hs_energy_of_bounded_right μS B w hwS M hLocal Z hZS
  have hZEnergy : (∫x,hsNormSq (Z x) ∂μS)≤η^2*r^((n : ℝ)-2) :=
    integral_hsNormSq_le_of_criticalMorrey Z ha hr (sq_nonneg η) (Subset.refl S) hZS hCritical
  have hSquare : M^2=H^2*Ku*r^γ := by
    have hPower : (r^(γ/2))^2=r^γ := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hr.le]
      congr 1
      ring
    dsimp only [M]
    rw [mul_pow,mul_pow,Real.sq_sqrt hKu,hPower]
  have hCapEnergy : (∫x,hsNormSq (F x) ∂μS)≤H^2*‖B‖^2*η^2*Ku*r^((n : ℝ)-2+γ) := by
    calc
      _≤(‖B‖*|M|)^2*(∫x,hsNormSq (Z x) ∂μS) := hEnergy
      _≤(‖B‖*|M|)^2*(η^2*r^((n : ℝ)-2)) :=
        mul_le_mul_of_nonneg_left hZEnergy (sq_nonneg _)
      _=(H^2*‖B‖^2*η^2*Ku)*(r^γ*r^((n : ℝ)-2)) := by
        rw [abs_of_nonneg hM,mul_pow,hSquare]
        ring
      _=_ := by
        rw [←Real.rpow_add hr,show γ+((n : ℝ)-2)=(n : ℝ)-2+γ by ring]
  refine ⟨hNear,?_⟩
  change (∫x in ball (0 : Domain n) 1,hsNormSq ((ball a r).indicator F x))≤_
  rw [setIntegral_hsNormSq_indicator _ measurableSet_ball,inter_comm]
  exact hCapEnergy

@[expose] def effectiveNaturalNearEnergyConstant (n : ℕ) : ℕ :=
  effectiveBoundaryStrongerConstant n ^ 2

theorem effectiveNaturalNearEnergyConstant_pos (n : ℕ) :
    0 < (effectiveNaturalNearEnergyConstant n : ℝ) := by
  simp only [effectiveNaturalNearEnergyConstant, Nat.cast_pow]
  exact sq_pos_of_pos (effectiveBoundaryStrongerConstant_pos n)

/-- The original closed representative and critical coefficient produce
actual centered and localized bilinear forcing fields at every original
center, with a stronger power coefficient depending only on n and γ. -/
theorem effective_natural_coefficient_near_forcing_energy
    (n : ℕ) (hn : 2≤n) :
    ∀(m k q : ℕ)
      (B : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient q))
      (Z : Domain n → Gradient n m) (u : Domain n → Ambient k)
      (Du : Domain n → Gradient n k) (η Ku : ℝ),
      (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      criticalGradientMorreySquare Z (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤Ku →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤Ku*r^((n : ℝ)-1)) →
      ∃V : closedBall (0 : Domain n) 1 → Ambient k,
        Continuous V ∧
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀hx : x∈ball (0 : Domain n) 1,
          V ⟨x,ball_subset_closedBall hx⟩=u x) ∧
        ∀(a : Domain n) (ha : a∈ball (0 : Domain n) 1),
          let c := V ⟨a,ball_subset_closedBall ha⟩
          let F := fun x i=>B (Z x i) (u x-c)
          (∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
          ∀r : ℝ,0<r →
            let Fnear := (ball a r).indicator F
            (∀i,MemLp (fun x=>Fnear x i) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
            (∫x in ball (0 : Domain n) 1,hsNormSq (Fnear x))≤(effectiveNaturalNearEnergyConstant n : ℝ)*‖B‖^2*η^2*Ku*r^((n : ℝ)-1) := by
  let H : ℝ := effectiveBoundaryStrongerConstant n
  have hH : 0 < H := effectiveBoundaryStrongerConstant_pos n
  have Hrep := effective_closedBall_holder_representative_of_stronger_morrey n hn
  have hConst : (effectiveNaturalNearEnergyConstant n : ℝ) = H ^ 2 := by
    simp only [effectiveNaturalNearEnergyConstant, Nat.cast_pow, H]
  rw [hConst]
  intro m k q B Z u Du η Ku hZ hCritical hu hKu hGrowth
  obtain ⟨V,⟨hV,hAE,hHolder⟩,_hUnique⟩ := Hrep k u Du Ku hu hKu hGrowth
  refine ⟨V,hV,hAE,?_⟩
  intro a ha c F
  let μ := volume.restrict (ball (0 : Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let w := fun x=>u x-c
  have huLp : MemLp u 2 μ := hu.2.1
  have hw : MemLp w 2 μ := huLp.sub (memLp_const c)
  have hGlobal : ∀ᵐx∂μ,‖w x‖≤H*Real.sqrt Ku*(2 : ℝ)^(1/2 : ℝ) := by
    filter_upwards [hAE,ae_restrict_mem measurableSet_ball] with x hx hxBall
    have hx0 : dist x (0 : Domain n)≤1 := ball_subset_closedBall hxBall
    have ha0 : dist (0 : Domain n) a≤1 := by rw [dist_comm];exact ball_subset_closedBall ha
    have hDist : dist x a≤2 := (dist_triangle x 0 a).trans (by linarith only [hx0,ha0])
    change ‖u x-c‖≤_
    rw [←hx hxBall]
    exact (hHolder ⟨x,ball_subset_closedBall hxBall⟩ ⟨a,ball_subset_closedBall ha⟩).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hDist (by norm_num : (0 : ℝ) ≤ 1/2))
        (mul_nonneg hH.le (Real.sqrt_nonneg _)))
  obtain ⟨hF,_hGlobalEnergy⟩ := bilinear_hs_energy_of_bounded_right μ B w hw.aestronglyMeasurable
    (H*Real.sqrt Ku*(2 : ℝ)^(1/2 : ℝ)) hGlobal Z hZ
  refine ⟨hF,?_⟩
  intro r hr Fnear
  have hNear (i : Fin n) : MemLp (fun x=>Fnear x i) 2 μ := by
    have HI : MemLp ((ball a r).indicator (fun x=>F x i)) 2 μ := (hF i).indicator measurableSet_ball
    apply HI.ae_eq
    exact Eventually.of_forall fun x=>by
      by_cases hx : x∈ball a r
      · simp only [Fnear,indicator_of_mem hx]
      · simp only [Fnear,indicator_of_notMem hx,Pi.zero_apply]
  let S := ball a r∩ball (0 : Domain n) 1
  let μS := volume.restrict S
  have hμ : μS≤μ := Measure.restrict_mono_set volume inter_subset_right
  have hwS : AEStronglyMeasurable w μS := (hw.mono_measure hμ).aestronglyMeasurable
  have hZS (i : Fin n) : MemLp (fun x=>Z x i) 2 μS := (hZ i).mono_measure hμ
  let M := H*Real.sqrt Ku*r^(1/2 : ℝ)
  have hM : 0≤M := mul_nonneg (mul_nonneg hH.le (Real.sqrt_nonneg _)) (Real.rpow_nonneg hr.le _)
  have hLocal : ∀ᵐx∂μS,‖w x‖≤M := by
    filter_upwards [hAE.filter_mono (ae_mono hμ),
      ae_restrict_mem (measurableSet_ball.inter measurableSet_ball)] with x hx hxS
    change ‖u x-c‖≤_
    rw [←hx hxS.2]
    exact (hHolder ⟨x,ball_subset_closedBall hxS.2⟩ ⟨a,ball_subset_closedBall ha⟩).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hxS.1.le (by norm_num : (0 : ℝ) ≤ 1/2))
        (mul_nonneg hH.le (Real.sqrt_nonneg _)))
  obtain ⟨_hFS,hEnergy⟩ := bilinear_hs_energy_of_bounded_right μS B w hwS M hLocal Z hZS
  have hZEnergy : (∫x,hsNormSq (Z x) ∂μS)≤η^2*r^((n : ℝ)-2) :=
    integral_hsNormSq_le_of_criticalMorrey Z ha hr (sq_nonneg η) (Subset.refl S) hZS hCritical
  have hSquare : M^2=H^2*Ku*r^(1 : ℝ) := by
    have hPower : (r^(1/2 : ℝ))^2=r^(1 : ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hr.le]
      congr 1
      ring
    dsimp only [M]
    rw [mul_pow,mul_pow,Real.sq_sqrt hKu,hPower]
  have hCapEnergy : (∫x,hsNormSq (F x) ∂μS)≤H^2*‖B‖^2*η^2*Ku*r^((n : ℝ)-1) := by
    calc
      _≤(‖B‖*|M|)^2*(∫x,hsNormSq (Z x) ∂μS) := hEnergy
      _≤(‖B‖*|M|)^2*(η^2*r^((n : ℝ)-2)) :=
        mul_le_mul_of_nonneg_left hZEnergy (sq_nonneg _)
      _=(H^2*‖B‖^2*η^2*Ku)*(r^(1 : ℝ)*r^((n : ℝ)-2)) := by
        rw [abs_of_nonneg hM,mul_pow,hSquare]
        ring
      _=_ := by
        rw [←Real.rpow_add hr,show (1 : ℝ)+((n : ℝ)-2)=(n : ℝ)-1 by ring]
  refine ⟨hNear,?_⟩
  change (∫x in ball (0 : Domain n) 1,hsNormSq ((ball a r).indicator F x))≤_
  rw [setIntegral_hsNormSq_indicator _ measurableSet_ball,inter_comm]
  exact hCapEnergy

end StationaryHarmonicMaps.Analysis

end

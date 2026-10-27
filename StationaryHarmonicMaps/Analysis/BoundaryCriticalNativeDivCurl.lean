module

public import StationaryHarmonicMaps.Analysis.BoundaryCriticalBMOExtension
public import StationaryHarmonicMaps.Analysis.NativeBoundaryTestExtension
public import StationaryHarmonicMaps.Analysis.BoundaryNativeZeroExtension
public import StationaryHarmonicMaps.Analysis.LocalDivCurlContinuousPairing

/-!
# Compensated native pairings up to the sphere

Natural solenoidal fields extend by zero without a boundary divergence.
The actual native test extends to a zero-boundary test on the double ball,
while the original bounded critical coefficient has a whole-space BMO
observable. The resulting ordinary pairing has a homogeneous energy bound.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Full natural boundary cancellation and the original critical graph control
ordinary native div-curl pairings over the entire source ball. -/
theorem exists_boundary_critical_native_divcurl_bound (n : ℕ) (hn : 2≤n) :
    ∃ C : ℝ,0<C ∧ ∀ (m : ℕ) (u : Domain n → Ambient m)
      (Du : Domain n → Gradient n m) (η M : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M) →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀ (L : Ambient m →L[ℝ] ℝ) (q : ℕ) (Z : Domain n → Gradient n q),
        (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
        (∀ (f : Domain n → Ambient q) (Df : Domain n → Gradient n q),
          MemW12 (ballDomain (0 : Domain n) 1) f Df →
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Df x i))=0) →
        ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
          MemW12 (ballDomain (0 : Domain n) 1) w Dw →
          IntegrableOn (fun x=>(∑i : Fin n,inner ℝ (Z x i) (Dw x i))*L (u x))
            (ball (0 : Domain n) 1) volume ∧
          |∫x in ball (0 : Domain n) 1,(∑i : Fin n,inner ℝ (Z x i) (Dw x i))*L (u x)|≤
            C*‖L‖*η*Real.sqrt (∫x in ball (0 : Domain n) 1,hsNormSq (Z x))*
              Real.sqrt (∫x in ball (0 : Domain n) 1,hsNormSq (Dw x)) := by
  obtain ⟨B,hB,HBMO⟩ := exists_boundary_critical_scalar_mean_oscillation_extension n hn
  obtain ⟨K,hK,HExt⟩ := exists_native_boundary_test_extension n hn
  obtain ⟨D,hD,Hpair⟩ := existsUnique_local_divcurl_continuous_pairing n hn
  refine ⟨D*B*Real.sqrt K,mul_pos (mul_pos hD hB) (Real.sqrt_pos.mpr hK),?_⟩
  intro m u Du η M hu hη huBound hCritical L q Z hZ hNatural w Dw hw
  let Ω := ballDomain (0 : Domain n) 1
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let ν := volume.restrict (ball (0 : Domain n) 2)
  let F := fun x=>∑i : Fin n,inner ℝ (Z x i) (Dw x i)
  have hFI : Integrable F μ := integrable_finsetSum _ (fun i _=>
    HolderToCK.integrable_inner_of_memLp_two (hZ i) (hw.2.2 i))
  have hZero : (∫x,F x ∂μ)=0 := hNatural w Dw hw
  have hObsMeas : AEStronglyMeasurable (fun x=>L (u x)) μ :=
    L.continuous.comp_aestronglyMeasurable hu.2.1.aestronglyMeasurable
  have hObsBound : ∀ᵐx∂μ,‖L (u x)‖≤‖L‖*M := by
    filter_upwards [huBound] with x hx
    exact (L.le_opNorm (u x)).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hOriginalI : Integrable (fun x=>F x*L (u x)) μ := hFI.mul_bdd hObsMeas hObsBound
  obtain ⟨c,HB⟩ := HBMO m u Du η hu hη hCritical
  obtain ⟨b,hb,hbInside,hbBMO⟩ := HB L
  have hCenterEq (x : Domain n) : F x*L (u x-c)=F x*L (u x)-F x*L c := by
    rw [map_sub,mul_sub]
  have hCenteredI : Integrable (fun x=>F x*L (u x-c)) μ := by
    simp_rw [hCenterEq]
    exact hOriginalI.sub (hFI.mul_const (L c))
  have hCenteredEq : (∫x,F x*L (u x-c) ∂μ)=(∫x,F x*L (u x) ∂μ) := by
    simp_rw [hCenterEq]
    rw [integral_sub hOriginalI (hFI.mul_const (L c)),integral_mul_const,hZero,zero_mul,sub_zero]
  obtain ⟨_cW,W,DW,hW,hWInside,hDWInside,hWEnergy⟩ := HExt q w Dw hw
  obtain ⟨hG,hGIn,hGOut,hGEnergy,hGDiv⟩ := natural_solenoidal_zeroExtension_unitBall Z hZ hNatural
  let G := (ball (0 : Domain n) 1).indicator Z
  have hGν (i : Fin n) : MemLp (fun x=>G x i) 2 ν := (hG i).mono_measure Measure.restrict_le_self
  have hDiv : HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 2) G
      (fun _=>(0 : Ambient q)) := hGDiv.mono (subset_univ _)
  have hProductEq : (fun x=>(∑i : Fin n,inner ℝ (G x i) (DW x i))*b x)=
      (ball (0 : Domain n) 1).indicator (fun x=>F x*L (u x-c)) := by
    funext x
    by_cases hx : x∈ball (0 : Domain n) 1
    · rw [indicator_of_mem hx]
      simp only [G,indicator_of_mem hx,hDWInside x hx,hbInside x hx,F]
    · simp only [G,indicator_of_notMem hx,Pi.zero_apply,inner_zero_left,
        Finset.sum_const_zero,zero_mul]
  have hProductI : Integrable (fun x=>(∑i : Fin n,inner ℝ (G x i) (DW x i))*b x) ν := by
    rw [hProductEq]
    exact ((integrable_indicator_iff measurableSet_ball).mpr hCenteredI).mono_measure Measure.restrict_le_self
  have hProductIntegral : (∫x,(∑i : Fin n,inner ℝ (G x i) (DW x i))*b x ∂ν)=
      ∫x,F x*L (u x) ∂μ := by
    rw [hProductEq,integral_indicator measurableSet_ball,
      show ν.restrict (ball (0 : Domain n) 1)=μ from by
        rw [Measure.restrict_restrict measurableSet_ball,
          inter_eq_left.mpr (ball_subset_ball (by norm_num : (1 : ℝ)≤2))]]
    exact hCenteredEq
  have hGRestrictedEnergy : (∫x,hsNormSq (G x) ∂ν)=(∫x,hsNormSq (Z x) ∂μ) := by
    change (∫x in ball (0 : Domain n) 2,hsNormSq (G x))=_
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hGEnergy
    · intro x hx
      have hxB : x∉ball (0 : Domain n) 1 := fun h=>hx ((ball_subset_ball (by norm_num : (1 : ℝ)≤2)) h)
      simp only [G,indicator_of_notMem hxB,hsNormSq,Pi.zero_apply,norm_zero,
        zero_pow (by decide : (2 : ℕ)≠0),Finset.sum_const_zero]
  obtain ⟨l,⟨_hAllI,_hLimit,hBound,hAgree⟩,_hUnique⟩ := Hpair q (0 : Domain n) 2
    (by norm_num) G hGν hDiv W DW hW b (B*‖L‖*η) hb (by positivity) hbBMO
  rw [(hAgree hProductI).trans hProductIntegral,hGRestrictedEnergy] at hBound
  have hRoot : Real.sqrt (∫x,hsNormSq (DW x) ∂ν)≤
      Real.sqrt K*Real.sqrt (∫x,hsNormSq (Dw x) ∂μ) := by
    exact (Real.sqrt_le_sqrt hWEnergy).trans_eq (Real.sqrt_mul hK.le _)
  refine ⟨hOriginalI,hBound.trans ?_⟩
  calc
    _≤D*(B*‖L‖*η)*Real.sqrt (∫x,hsNormSq (Z x) ∂μ)*
        (Real.sqrt K*Real.sqrt (∫x,hsNormSq (Dw x) ∂μ)) :=
      mul_le_mul_of_nonneg_left hRoot (by positivity)
    _=_ := by ring

end StationaryHarmonicMaps.Analysis

end

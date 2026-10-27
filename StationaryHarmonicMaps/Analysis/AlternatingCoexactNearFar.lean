module

public import StationaryHarmonicMaps.Analysis.AlternatingBoundaryNearEnergy
public import StationaryHarmonicMaps.Analysis.CoexactAllBallOffSupport
public import StationaryHarmonicMaps.Analysis.ZeroExtendedHSEnergy
public import HarmonicMaps.Analysis.SobolevDifference

/-!
# Same-response near and far splitting of an alternating relative field

Subtracting a constant coefficient changes the forcing by a genuine native
gradient. The localized relative response therefore leaves a far response
with the same natural boundary tests and forcing zero on the query ball.
The true boundary harmonic estimate controls that same far field.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original alternating coexact response has a compensated near field
and an actual harmonic far field on every small query, including boundary caps. -/
theorem exists_alternating_coexact_near_far_density_split (n : ℕ) (hn : 2≤n)
    (m k : ℕ) (B : Ambient m →L[ℝ] (Ambient m →L[ℝ] Ambient k))
    (hAlt : ∀z : Ambient m,B z z=0) (ν : ℝ) :
    ∃C D : ℝ,0<C ∧ 0<D ∧ ∀ (u : Domain n → Ambient m) (Du : Domain n → Gradient n m)
      (η M K : ℝ),MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M) →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) → 0≤K →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤K*r^ν) →
      ∀ (Q : Domain n → Gradient n k) (v : Domain n → Ambient k),
        (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
        MemW12 (ballDomain (0 : Domain n) 1) v (fun x i=>B (u x) (Du x i)-Q x i) →
        (∀ (ψ : Domain n → Ambient k) (Dψ : Domain n → Gradient n k),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) →
        let Q₀ := (ball (0 : Domain n) 1).indicator Q
        ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r → r≤1/8 →
        ∃g h : Domain n → ℝ,(∀x,0≤g x) ∧ (∀x,0≤h x) ∧
          Integrable g volume ∧ Integrable h volume ∧
          (∀x,hsNormSq (Q₀ x)≤2*g x+2*h x) ∧
          (∫x,g x)≤D*η^2*K*r^ν ∧
          ∀ᵐx∂volume.restrict (ball a (r/256)),h x≤
            C*(volume.real (ball a r))⁻¹*
              ((∫y in ball a r,hsNormSq (Q₀ y))+D*η^2*K*r^ν) := by
  obtain ⟨D,hD,Hnear⟩ := exists_alternating_boundary_near_coexact_energy n hn m k B hAlt ν
  obtain ⟨C,hC,Hoff⟩ := exists_native_coexact_all_ball_offSupport_bounds n hn
  refine ⟨2*C,D,by positivity,hD,?_⟩
  intro u Du η M K hu hη hBound hCritical hK hGrowth Q v hQ hv hNatural Q₀ a ha r hr hrCap
  obtain ⟨χ,c,P,w,hχ,hcχ,hsχ,hOne,hBounds,hP,hw,hPN,hPEnergy⟩ :=
    Hnear u Du η M K hu hη hBound hCritical hK hGrowth a ha r hr hrCap
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let F := fun x i=>B (u x) (Du x i)
  let Fnear := fun x i=>χ x • B (u x-c) (Du x i)
  let Ffar := fun x i=>B (u x-c) (Du x i)-Fnear x i
  let H := fun x i=>Q x i-P x i
  let P₀ := (ball (0 : Domain n) 1).indicator P
  let H₀ := (ball (0 : Domain n) 1).indicator H
  have hF (i : Fin n) : MemLp (fun x=>F x i) 2 μ :=
    ((hv.2.2 i).add (hQ i)).ae_eq (Eventually.of_forall fun _=>sub_add_cancel _ _)
  have hFn (i : Fin n) : MemLp (fun x=>Fnear x i) 2 μ :=
    ((hw.2.2 i).add (hP i)).ae_eq (Eventually.of_forall fun _=>sub_add_cancel _ _)
  have hBc : MemW12 (ballDomain (0 : Domain n) 1) (fun x=>B c (u x))
      (fun x i=>B c (Du x i)) :=
    ⟨(memW12Loc_continuousLinearMap hu.to_memW12Loc (B c)).1,
      (B c).lipschitz.comp_memLp (map_zero (B c)) hu.2.1,
      fun i=>(B c).lipschitz.comp_memLp (map_zero (B c)) (hu.2.2 i)⟩
  have hFf (i : Fin n) : MemLp (fun x=>Ffar x i) 2 μ := by
    have hF' := ((hF i).sub (hBc.2.2 i)).sub (hFn i)
    apply hF'.ae_eq
    exact Eventually.of_forall fun x=>by
      simp only [Ffar,F,map_sub,sub_apply,Pi.sub_apply]
  have hH (i : Fin n) : MemLp (fun x=>H x i) 2 μ := (hQ i).sub (hP i)
  have hFarNative : MemW12 (ballDomain (0 : Domain n) 1) ((v-(fun x=>B c (u x)))-w)
      (fun x i=>Ffar x i-H x i) := by
    apply ((hv.sub hBc).sub hw).congr_ae (Eventually.of_forall fun _=>rfl)
    exact Eventually.of_forall fun x=>by
      funext i
      simp only [Ffar,Fnear,H,map_sub,sub_apply]
      abel
  have hFarNatural (ψ : Domain n → Ambient k) (Dψ : Domain n → Gradient n k)
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
      (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (H x i) (Dψ x i))=0 := by
    have hQI : Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ :=
      integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hQ i) (hψ.2.2 i))
    have hPI : Integrable (fun x=>∑i : Fin n,inner ℝ (P x i) (Dψ x i)) μ := (hPN ψ Dψ hψ).1
    simp only [H,inner_sub_left,Finset.sum_sub_distrib]
    rw [integral_sub hQI hPI,hNatural ψ Dψ hψ,(hPN ψ Dψ hψ).2,sub_self]
  have hFarZero : Ffar=ᵐ[volume.restrict (ball (0 : Domain n) 1∩ball a (256*(r/256)))]
      (fun _=>0) := by
    filter_upwards [ae_restrict_mem (measurableSet_ball.inter measurableSet_ball)] with x hx
    have hxBall : x∈ball a r := by simpa only [mul_div_cancel₀ r (by norm_num : (256 : ℝ)≠0)] using hx.2
    funext i
    simp only [Ffar,Fnear,hOne x (ball_subset_closedBall hxBall),one_smul,sub_self,Pi.zero_apply]
  have hFarBound := Hoff k Ffar H _ hFf hH hFarNative hFarNatural a (r/256) (by positivity) hFarZero
  rw [show (256 : ℝ)*(r/256)=r from by ring] at hFarBound
  have hP₀I : Integrable (fun x=>hsNormSq (P₀ x)) volume :=
    integrable_hsNormSq_of_columns _ (memLp_columns_indicator _ measurableSet_ball P hP)
  have hH₀I : Integrable (fun x=>hsNormSq (H₀ x)) volume :=
    integrable_hsNormSq_of_columns _ (memLp_columns_indicator _ measurableSet_ball H hH)
  have hQ₀I : Integrable (fun x=>hsNormSq (Q₀ x)) volume :=
    integrable_hsNormSq_of_columns _ (memLp_columns_indicator _ measurableSet_ball Q hQ)
  have hNearEnergy : (∫x,hsNormSq (P₀ x))≤D*η^2*K*r^ν := by
    rw [integral_hsNormSq_indicator _ measurableSet_ball]
    exact hPEnergy
  have hQSplit (x : Domain n) : Q₀ x=(fun i=>P₀ x i+H₀ x i) := by
    by_cases hx : x∈ball (0 : Domain n) 1
    · simp only [Q₀,P₀,H₀,indicator_of_mem hx,H]
      funext i
      abel
    · simp only [Q₀,P₀,H₀,indicator_of_notMem hx,Pi.zero_apply,add_zero]
      rfl
  have hHSplit (x : Domain n) : H₀ x=(fun i=>Q₀ x i+ -P₀ x i) := by
    by_cases hx : x∈ball (0 : Domain n) 1
    · simp only [Q₀,P₀,H₀,indicator_of_mem hx,H,sub_eq_add_neg]
    · simp only [Q₀,P₀,H₀,indicator_of_notMem hx,Pi.zero_apply,neg_zero,add_zero]
      rfl
  have hDensity (x : Domain n) : hsNormSq (Q₀ x)≤2*hsNormSq (P₀ x)+2*hsNormSq (H₀ x) := by
    rw [hQSplit x]
    exact HolderToCK.hsNormSq_add_le _ _
  have hFarEnergy : (∫x in ball a r,hsNormSq (H₀ x))≤
      2*((∫x in ball a r,hsNormSq (Q₀ x))+D*η^2*K*r^ν) := by
    have hPoint (x : Domain n) : hsNormSq (H₀ x)≤2*hsNormSq (Q₀ x)+2*hsNormSq (P₀ x) := by
      rw [hHSplit x]
      simpa only [hsNormSq,norm_neg,Pi.add_apply] using HolderToCK.hsNormSq_add_le (Q₀ x) (fun i=> -P₀ x i)
    calc
      _≤∫x in ball a r,2*hsNormSq (Q₀ x)+2*hsNormSq (P₀ x) := integral_mono hH₀I.integrableOn
        ((hQ₀I.const_mul 2).add (hP₀I.const_mul 2)).integrableOn hPoint
      _=2*(∫x in ball a r,hsNormSq (Q₀ x))+2*(∫x in ball a r,hsNormSq (P₀ x)) := by
        rw [integral_add (hQ₀I.integrableOn.const_mul 2) (hP₀I.integrableOn.const_mul 2),
          integral_const_mul,integral_const_mul]
      _≤2*(∫x in ball a r,hsNormSq (Q₀ x))+2*(D*η^2*K*r^ν) := by
        have H : (∫x in ball a r,hsNormSq (P₀ x))≤D*η^2*K*r^ν := (integral_mono_measure Measure.restrict_le_self
          (Eventually.of_forall fun _=>hsNormSq_nonneg _) hP₀I).trans hNearEnergy
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left H (by norm_num))
      _=_ := by ring
  refine ⟨fun x=>hsNormSq (P₀ x),fun x=>hsNormSq (H₀ x),fun _=>hsNormSq_nonneg _,
    fun _=>hsNormSq_nonneg _,hP₀I,hH₀I,hDensity,hNearEnergy,?_⟩
  filter_upwards [hFarBound] with x hx
  exact hx.trans ((mul_le_mul_of_nonneg_left hFarEnergy (by positivity :
    0≤C*(volume.real (ball a r))⁻¹)).trans_eq (by ring))

end StationaryHarmonicMaps.Analysis

end

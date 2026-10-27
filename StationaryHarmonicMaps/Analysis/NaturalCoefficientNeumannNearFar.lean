/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.NaturalCoefficientNeumannNearEnergy
public import StationaryHarmonicMaps.Analysis.CoexactAllBallOffSupport
public import HarmonicMaps.Analysis.SobolevDifference

/-!
# The same natural-coefficient Neumann response near and far

The original full natural condition removes the constant value of the
actual closed representative at each center. The localized forcing has
its genuine native Neumann response. Subtraction from the same original
response leaves a far gradient with an actual natural complement and
forcing zero on the parent ball. Boundary off-support bounds therefore
control that same far gradient on every boundary cap.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The same actual native Neumann response has a locally controlled
near gradient and a genuine off-support far gradient. All auxiliary
fields and the full natural far complement are produced internally. -/
theorem exists_natural_coefficient_neumann_near_far_split
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃C D : ℝ,0<C ∧ 0<D ∧ ∀(m k q : ℕ)
      (B : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient q))
      (Z : Domain n → Gradient n m) (u : Domain n → Ambient k)
      (Du : Domain n → Gradient n k) (η Ku : ℝ),
      (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      (∀(ψ : Domain n → Ambient m) (Dψ : Domain n → Gradient n m),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) →
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      criticalGradientMorreySquare Z (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) → 0≤Ku →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤Ku*r^((n : ℝ)-2+γ)) →
      ∀(g : Domain n → Ambient q) (Q : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) g Q →
        (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
            ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) →
        let Q₀ := (ball (0 : Domain n) 1).indicator Q
        ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
          ∃near far : Domain n → ℝ,
            (∀x,0≤near x) ∧ (∀x,0≤far x) ∧ Integrable near volume ∧ Integrable far volume ∧
            (∀x,hsNormSq (Q₀ x)≤2*near x+2*far x) ∧
            (∫x,near x)≤D*‖B‖^2*η^2*Ku*r^((n : ℝ)-2+γ) ∧
            ∀ᵐx∂volume.restrict (ball a (r/256)),far x≤C*(volume.real (ball a r))⁻¹*
              ((∫y in ball a r,hsNormSq (Q₀ y))+D*‖B‖^2*η^2*Ku*r^((n : ℝ)-2+γ)) := by
  obtain ⟨D,hD,Hnear⟩ := exists_natural_coefficient_near_forcing_energy n hn γ hγ hγTwo
  obtain ⟨C,hC,Hoff⟩ := exists_native_coexact_all_ball_offSupport_bounds n hn
  refine ⟨2*C,D,by positivity,hD,?_⟩
  intro m k q B Z u Du η Ku hZ hNatural hu hCritical hKu hGrowth g Q hg hResponse Q₀ a ha r hr
  obtain ⟨V,_hV,_hAE,Hforcing⟩ := Hnear m k q B Z u Du η Ku hZ hCritical hu hKu hGrowth
  let c := V ⟨a,ball_subset_closedBall ha⟩
  let F := fun x i=>B (Z x i) (u x-c)
  let Fnear := (ball a r).indicator F
  obtain ⟨hF,Hlocal⟩ := Hforcing a ha
  obtain ⟨hFn,hFnEnergy⟩ := Hlocal r hr
  change ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1)) at hF
  change ∀i,MemLp (fun x=>Fnear x i) 2 (volume.restrict (ball (0 : Domain n) 1)) at hFn
  change (∫x in ball (0 : Domain n) 1,hsNormSq (Fnear x))≤
    D*‖B‖^2*η^2*Ku*r^((n : ℝ)-2+γ) at hFnEnergy
  let μ := volume.restrict (ball (0 : Domain n) 1)
  have hRaw := bilinear_raw_memLp_of_centered_unitBall Z hZ B u c hF
  obtain ⟨_hF,Hcenter⟩ := natural_coefficient_centered_pairing_unitBall Z hZ hNatural B u hRaw c
  have hCenteredResponse (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q)
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
      (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
        ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (F x i) (Dψ x i) :=
    (hResponse ψ Dψ hψ).trans (Hcenter ψ Dψ hψ).2.2.symm
  obtain ⟨w,P,hw,_hMean,hPEnergy,hPN⟩ := exists_neumann_gradient_projection (0 : Domain n)
    (by norm_num : (0 : ℝ)<1) Fnear hFn
  let Ffar := fun x i=>F x i-Fnear x i
  let H := fun x i=>Q x i-P x i
  let K := fun x i=>Ffar x i-H x i
  let P₀ := (ball (0 : Domain n) 1).indicator P
  let H₀ := (ball (0 : Domain n) 1).indicator H
  let K₀ := (ball (0 : Domain n) 1).indicator K
  have hFf (i : Fin n) : MemLp (fun x=>Ffar x i) 2 μ := (hF i).sub (hFn i)
  have hH (i : Fin n) : MemLp (fun x=>H x i) 2 μ := (hg.2.2 i).sub (hw.2.2 i)
  have hK (i : Fin n) : MemLp (fun x=>K x i) 2 μ := (hFf i).sub (hH i)
  have hFarNative : MemW12 (ballDomain (0 : Domain n) 1) (g-w) (fun x i=>Ffar x i-K x i) := by
    apply (hg.sub hw).congr_ae (Eventually.of_forall fun _=>rfl)
    exact Eventually.of_forall fun x=>by
      funext i
      dsimp only [K,H]
      abel
  have hKNatural (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q)
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
      (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (K x i) (Dψ x i))=0 := by
    have hFI := integrable_column_pairing μ F Dψ hF hψ.2.2
    have hFnI := integrable_column_pairing μ Fnear Dψ hFn hψ.2.2
    have hQI := integrable_column_pairing μ Q Dψ hg.2.2 hψ.2.2
    have hPI := integrable_column_pairing μ P Dψ hw.2.2 hψ.2.2
    have H1 := integral_sub (hFI.sub hFnI) (hQI.sub hPI)
    have H2 := integral_sub hFI hFnI
    have H3 := integral_sub hQI hPI
    simp only [Pi.sub_apply] at H1 H2 H3
    simp only [K,H,Ffar,inner_sub_left,Finset.sum_sub_distrib]
    change (∫x,((∑i : Fin n,inner ℝ (F x i) (Dψ x i))-
      (∑i : Fin n,inner ℝ (Fnear x i) (Dψ x i)))-
      ((∑i : Fin n,inner ℝ (Q x i) (Dψ x i))-
        (∑i : Fin n,inner ℝ (P x i) (Dψ x i))) ∂μ)=0
    rw [H1,H2,H3,←hCenteredResponse ψ Dψ hψ,(hPN ψ Dψ hψ).2.2,sub_self]
  have hFarPoint (x : Domain n) (hx : x∈ball a r) : Ffar x=0 := by
    funext i
    simp only [Ffar,Fnear,indicator_of_mem hx,sub_self,Pi.zero_apply]
  have hFarZero : Ffar=ᵐ[volume.restrict (ball (0 : Domain n) 1∩ball a (256*(r/256)))]
      (fun _=>0) := by
    filter_upwards [ae_restrict_mem (measurableSet_ball.inter measurableSet_ball)] with x hx
    exact hFarPoint x (by simpa only [mul_div_cancel₀ r (by norm_num : (256 : ℝ)≠0)] using hx.2)
  have hHSFar (x : Domain n) (hx : x∈ball a r) : hsNormSq (K₀ x)=hsNormSq (H₀ x) := by
    by_cases hxU : x∈ball (0 : Domain n) 1
    · simp only [K₀,H₀,indicator_of_mem hxU,K,hFarPoint x hx,Pi.zero_apply,zero_sub,hsNormSq,norm_neg]
    · simp only [K₀,H₀,indicator_of_notMem hxU]
  have hFarEnergyEq : (∫x in ball a r,hsNormSq (K₀ x))=(∫x in ball a r,hsNormSq (H₀ x)) :=
    setIntegral_congr_fun measurableSet_ball hHSFar
  have hFarBound := Hoff q Ffar K (g-w) hFf hK hFarNative hKNatural a (r/256) (by positivity) hFarZero
  rw [show (256 : ℝ)*(r/256)=r by ring] at hFarBound
  change ∀ᵐx∂volume.restrict (ball a (r/256)),hsNormSq (K₀ x)≤
    C*(volume.real (ball a r))⁻¹*(∫y in ball a r,hsNormSq (K₀ y)) at hFarBound
  rw [hFarEnergyEq] at hFarBound
  have hFarDensity : ∀ᵐx∂volume.restrict (ball a (r/256)),hsNormSq (H₀ x)≤
      C*(volume.real (ball a r))⁻¹*(∫y in ball a r,hsNormSq (H₀ y)) := by
    filter_upwards [hFarBound,ae_restrict_mem measurableSet_ball] with x hx hxBall
    have hxParent : x∈ball a r := (ball_subset_ball (by linarith only [hr] : r/256≤r)) hxBall
    exact (hHSFar x hxParent).symm.le.trans hx
  have hP₀I : Integrable (fun x=>hsNormSq (P₀ x)) volume :=
    integrable_hsNormSq_of_columns _ (memLp_columns_indicator _ measurableSet_ball P hw.2.2)
  have hH₀I : Integrable (fun x=>hsNormSq (H₀ x)) volume :=
    integrable_hsNormSq_of_columns _ (memLp_columns_indicator _ measurableSet_ball H hH)
  have hQ₀I : Integrable (fun x=>hsNormSq (Q₀ x)) volume :=
    integrable_hsNormSq_of_columns _ (memLp_columns_indicator _ measurableSet_ball Q hg.2.2)
  have hNearEnergy : (∫x,hsNormSq (P₀ x))≤D*‖B‖^2*η^2*Ku*r^((n : ℝ)-2+γ) := by
    rw [integral_hsNormSq_indicator _ measurableSet_ball]
    exact hPEnergy.trans hFnEnergy
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
      2*((∫x in ball a r,hsNormSq (Q₀ x))+D*‖B‖^2*η^2*Ku*r^((n : ℝ)-2+γ)) := by
    have hPoint (x : Domain n) : hsNormSq (H₀ x)≤2*hsNormSq (Q₀ x)+2*hsNormSq (P₀ x) := by
      rw [hHSplit x]
      simpa only [hsNormSq,norm_neg,Pi.add_apply] using
        HolderToCK.hsNormSq_add_le (Q₀ x) (fun i=> -P₀ x i)
    calc
      _≤∫x in ball a r,2*hsNormSq (Q₀ x)+2*hsNormSq (P₀ x) :=
        integral_mono hH₀I.integrableOn ((hQ₀I.const_mul 2).add (hP₀I.const_mul 2)).integrableOn hPoint
      _=2*(∫x in ball a r,hsNormSq (Q₀ x))+2*(∫x in ball a r,hsNormSq (P₀ x)) := by
        rw [integral_add (hQ₀I.integrableOn.const_mul 2) (hP₀I.integrableOn.const_mul 2),
          integral_const_mul,integral_const_mul]
      _≤2*(∫x in ball a r,hsNormSq (Q₀ x))+2*(D*‖B‖^2*η^2*Ku*r^((n : ℝ)-2+γ)) := by
        have HE : (∫x in ball a r,hsNormSq (P₀ x))≤D*‖B‖^2*η^2*Ku*r^((n : ℝ)-2+γ) :=
          (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun _=>hsNormSq_nonneg _) hP₀I).trans hNearEnergy
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left HE (by norm_num))
      _=_ := by ring
  refine ⟨fun x=>hsNormSq (P₀ x),fun x=>hsNormSq (H₀ x),fun _=>hsNormSq_nonneg _,
    fun _=>hsNormSq_nonneg _,hP₀I,hH₀I,hDensity,hNearEnergy,?_⟩
  filter_upwards [hFarDensity] with x hx
  exact hx.trans ((mul_le_mul_of_nonneg_left hFarEnergy (by positivity :
    0≤C*(volume.real (ball a r))⁻¹)).trans_eq (by ring))

end StationaryHarmonicMaps.Analysis

end

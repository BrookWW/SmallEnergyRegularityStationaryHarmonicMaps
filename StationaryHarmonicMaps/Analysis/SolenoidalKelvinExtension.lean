module

public import StationaryHarmonicMaps.Analysis.KelvinPiolaPairing
public import StationaryHarmonicMaps.Analysis.KelvinTestZeroBoundary
public import StationaryHarmonicMaps.Analysis.PhysicalDivergenceTests
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Actual solenoidal L2 extension from the unit ball

The interior original field and its actual exterior Kelvin--Piola field
are joined by indicators, with zero values on the unit sphere. The
exterior test pairing is the negative reflected interior pairing. The
actual smooth zero-boundary difference of each test gives cancellation
from the original divergence equation, without a normal-trace premise.
A genuine measurable representative removes any additional measurability
requirement on the original L2 representative.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem apply_eq_coordinate_sum {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (L : Domain n →L[ℝ] E) (z : Domain n) :
    L z=∑ i : Fin n,z i • L (EuclideanSpace.single i 1) := by
  have hrepr : (∑ i : Fin n,z i • EuclideanSpace.single i 1)=z := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr z
  calc
    _ = L (∑ i : Fin n,z i • EuclideanSpace.single i 1) := congrArg L hrepr.symm
    _ = _ := by simp only [map_sum,map_smul]

private theorem integrable_physical_test {n : ℕ} (S : Set (Domain n))
    (Z : Domain n → Domain n) (hZ : MemLp Z 2 (volume.restrict S))
    (η : Domain n → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) :
    IntegrableOn (fun x => fderiv ℝ η x (Z x)) S volume := by
  have hDη : MemLp (fderiv ℝ η) 2 (volume.restrict S) :=
    (hη.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hcη.fderiv ℝ)
  have hProd : Integrable (fun x => ‖fderiv ℝ η x‖*‖Z x‖) (volume.restrict S) :=
    memLp_one_iff_integrable.mp (hZ.norm.mul' hDη.norm)
  apply hProd.mono' ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (hDη.aestronglyMeasurable.prodMk hZ.aestronglyMeasurable))
  exact Eventually.of_forall fun x => ContinuousLinearMap.le_opNorm _ _

private theorem measurable_solenoidal_kelvin_extension {n : ℕ} (hn : 2≤n)
    (Z : Domain n → Domain n) (hZm : Measurable Z)
    (hZ : MemLp Z 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (hdiv : ∀ (η : Domain n → ℝ),ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Metric.ball (0 : Domain n) 1 →
      (∫ x in Metric.ball (0 : Domain n) 1,fderiv ℝ η x (Z x))=0) :
    ∃ F : Domain n → Domain n,MemLp F 2 volume ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),F x=Z x) ∧
      (∫ x,‖F x‖^2) ≤ 2*(∫ x in Metric.ball (0 : Domain n) 1,‖Z x‖^2) ∧
      ∀ (η : Domain n → ℝ),ContDiff ℝ ∞ η → HasCompactSupport η →
        Integrable (fun x => fderiv ℝ η x (F x)) volume ∧
        (∫ x,fderiv ℝ η x (F x))=0 := by
  letI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  let B : Set (Domain n) := Metric.ball (0 : Domain n) 1
  let O : Set (Domain n) := {x : Domain n | 1<‖x‖}
  let I := inversion (0 : Domain n) 1
  let W : Domain n → Domain n := fun x => -((‖x‖^(2*n-2))⁻¹) •
    (ℝ ∙ x)ᗮ.reflection (Z (I x))
  let F : Domain n → Domain n := B.indicator Z+O.indicator W
  have hBm : MeasurableSet B := measurableSet_ball
  have hOm : MeasurableSet O := (isOpen_lt continuous_const continuous_norm).measurableSet
  obtain ⟨hW,hWEnergy⟩ := kelvin_piola_L2_exterior hn Z hZm hZ
  have hZind : MemLp (B.indicator Z) 2 volume := (memLp_indicator_iff_restrict hBm).mpr hZ
  have hWind : MemLp (O.indicator W) 2 volume := (memLp_indicator_iff_restrict hOm).mpr hW
  have hF : MemLp F 2 volume := hZind.add hWind
  have hDisjoint (x : Domain n) (hx : x∈B) : x∉O := by
    have H : ‖x‖<1 := by simpa only [B,Metric.mem_ball,dist_zero_right] using hx
    change ¬1<‖x‖
    linarith
  have hFPoint (x : Domain n) (hx : x∈B) : F x=Z x := by
    simp only [F,Pi.add_apply,indicator_of_mem hx,indicator_of_notMem (hDisjoint x hx),add_zero]
  have hFInside : ∀ᵐ x ∂volume.restrict B,F x=Z x := by
    filter_upwards [ae_restrict_mem hBm] with x hx
    exact hFPoint x hx
  have hEnergyFun : (fun x => ‖F x‖^2)=(fun x => B.indicator (fun x => ‖Z x‖^2) x+O.indicator (fun x => ‖W x‖^2) x) := by
    funext x
    by_cases hxB : x∈B
    · simp only [F,Pi.add_apply,indicator_of_mem hxB,indicator_of_notMem (hDisjoint x hxB),add_zero]
    · by_cases hxO : x∈O
      · simp only [F,Pi.add_apply,indicator_of_notMem hxB,indicator_of_mem hxO,zero_add]
      · simp only [F,Pi.add_apply,indicator_of_notMem hxB,indicator_of_notMem hxO,zero_add,norm_zero,
          zero_pow (by decide : (2 : ℕ)≠0)]
  have hZI : IntegrableOn (fun x => ‖Z x‖^2) B volume := hZ.integrable_norm_pow (by decide : (2 : ℕ)≠0)
  have hWI : IntegrableOn (fun x => ‖W x‖^2) O volume := hW.integrable_norm_pow (by decide : (2 : ℕ)≠0)
  have hEnergy : (∫ x,‖F x‖^2) ≤ 2*(∫ x in B,‖Z x‖^2) := by
    rw [hEnergyFun,integral_add ((integrable_indicator_iff hBm).mpr hZI)
      ((integrable_indicator_iff hOm).mpr hWI),integral_indicator hBm,integral_indicator hOm]
    linarith
  refine ⟨F,hF,hFInside,hEnergy,?_⟩
  intro η hη hcη
  have hFPair : Integrable (fun x => fderiv ℝ η x (F x)) volume := by
    have HH := integrable_physical_test univ F
      (by simpa only [Measure.restrict_univ] using hF) η hη hcη
    change Integrable (fun x => fderiv ℝ η x (F x)) (volume.restrict univ) at HH
    rw [Measure.restrict_univ] at HH
    exact HH
  have hZPair := integrable_physical_test B Z hZ η hη hcη
  obtain ⟨hWPair,hReflected,hWPairEq⟩ := kelvin_piola_integral_pairing hn Z hZm hZ η hη hcη
  let P : Ambient 1 →L[ℝ] ℝ := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0
  have hP (z : Ambient 1) : P z=z 0 := rfl
  let e : Ambient 1 := EuclideanSpace.single 0 1
  let E : ℝ →L[ℝ] Ambient 1 := (ContinuousLinearMap.id ℝ ℝ).smulRight e
  let ψ : Domain n → Ambient 1 := fun x => E (η x)
  have hPE (t : ℝ) : P (E t)=t := by simp [P,E,e]
  have hψ : ContDiff ℝ ∞ ψ := E.contDiff.comp hη
  have hcψ : HasCompactSupport ψ := hcη.comp_left (map_zero E)
  have hDψ (x z : Domain n) : P (fderiv ℝ ψ x z)=fderiv ℝ η x z := by
    have H := E.hasFDerivAt.comp x (hη.differentiable (by simp) x).hasFDerivAt
    have hFun : ψ=E ∘ η := by funext y; rfl
    rw [hFun,H.fderiv]
    exact hPE _
  obtain ⟨φ,_hφ,hφW,_hφEq,hDφ⟩ := exists_kelvin_test_zeroBoundary hn ψ hψ hcψ
  have hDivSum : ∀ (ζ : Domain n → ℝ),ContDiff ℝ ∞ ζ → HasCompactSupport ζ → tsupport ζ ⊆ B →
      (∫ x in B,∑ i : Fin n,Z x i*fderiv ℝ ζ x (EuclideanSpace.single i 1))=0 := by
    intro ζ hζ hcζ hsζ
    have hPoint (x : Domain n) : (∑ i : Fin n,Z x i*fderiv ℝ ζ x (EuclideanSpace.single i 1))=
        fderiv ℝ ζ x (Z x) := by
      simpa only [smul_eq_mul] using (apply_eq_coordinate_sum (fderiv ℝ ζ x) (Z x)).symm
    rw [integral_congr_ae (Eventually.of_forall hPoint)]
    exact hdiv ζ hζ hcζ hsζ
  have hNative := physical_divergence_free_zeroBoundary_test (ballDomain (0 : Domain n) 1)
    Z hZ hDivSum hφW
  have hPhiSum (x : Domain n) : P (fderiv ℝ φ x (Z x))=
      ∑ i : Fin n,Z x i*(fderiv ℝ φ x (EuclideanSpace.single i 1)) 0 := by
    have H := apply_eq_coordinate_sum (P.comp (fderiv ℝ φ x)) (Z x)
    simpa only [ContinuousLinearMap.comp_apply,smul_eq_mul,hP] using H
  have hPhiPair (x : Domain n) (hx : x≠0) : P (fderiv ℝ φ x (Z x))=
      fderiv ℝ η x (Z x)-fderiv ℝ η (I x) (fderiv ℝ I x (Z x)) := by
    rw [hDφ x hx,sub_apply,ContinuousLinearMap.comp_apply,map_sub,hDψ,hDψ]
  have hAE0 : ∀ᵐ x : Domain n ∂volume,x≠0 := by simp [ae_iff]
  have hPairEq : (fun x => fderiv ℝ η x (Z x)-fderiv ℝ η (I x) (fderiv ℝ I x (Z x))) =ᵐ[volume.restrict B]
      (fun x => ∑ i : Fin n,Z x i*(fderiv ℝ φ x (EuclideanSpace.single i 1)) 0) := by
    filter_upwards [ae_restrict_of_ae hAE0] with x hx
    rw [← hPhiSum x,← hPhiPair x hx]
  have hInsideEq : (∫ x in B,fderiv ℝ η x (Z x))-
      (∫ x in B,fderiv ℝ η (I x) (fderiv ℝ I x (Z x)))=0 := by
    rw [← integral_sub hZPair hReflected,integral_congr_ae hPairEq]
    exact hNative.2
  have hFun : (fun x => fderiv ℝ η x (F x))=
      (fun x => B.indicator (fun x => fderiv ℝ η x (Z x)) x+O.indicator (fun x => fderiv ℝ η x (W x)) x) := by
    funext x
    by_cases hxB : x∈B
    · simp only [F,Pi.add_apply,indicator_of_mem hxB,indicator_of_notMem (hDisjoint x hxB),add_zero]
    · by_cases hxO : x∈O
      · simp only [F,Pi.add_apply,indicator_of_notMem hxB,indicator_of_mem hxO,zero_add]
      · simp only [F,Pi.add_apply,indicator_of_notMem hxB,indicator_of_notMem hxO,zero_add,map_zero]
  refine ⟨hFPair,?_⟩
  rw [hFun,integral_add ((integrable_indicator_iff hBm).mpr hZPair)
    ((integrable_indicator_iff hOm).mpr hWPair),integral_indicator hBm,integral_indicator hOm,hWPairEq]
  exact hInsideEq

/-- Every original L2 solenoidal vector on the unit ball has a genuine full-space L2 solenoidal extension with squared-norm bound two. -/
theorem exists_solenoidal_L2_extension_unitBall {n : ℕ} (hn : 2≤n)
    (Z : Domain n → Domain n)
    (hZ : MemLp Z 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (hdiv : ∀ (η : Domain n → ℝ),ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Metric.ball (0 : Domain n) 1 →
      (∫ x in Metric.ball (0 : Domain n) 1,fderiv ℝ η x (Z x))=0) :
    ∃ F : Domain n → Domain n,MemLp F 2 volume ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),F x=Z x) ∧
      (∫ x,‖F x‖^2) ≤ 2*(∫ x in Metric.ball (0 : Domain n) 1,‖Z x‖^2) ∧
      ∀ (η : Domain n → ℝ),ContDiff ℝ ∞ η → HasCompactSupport η →
        Integrable (fun x => fderiv ℝ η x (F x)) volume ∧
        (∫ x,fderiv ℝ η x (F x))=0 := by
  let Zm := hZ.aestronglyMeasurable.mk Z
  have hZm : Measurable Zm := hZ.aestronglyMeasurable.measurable_mk
  have hEq : Z =ᵐ[volume.restrict (Metric.ball (0 : Domain n) 1)] Zm := hZ.aestronglyMeasurable.ae_eq_mk
  have hZL : MemLp Zm 2 (volume.restrict (Metric.ball (0 : Domain n) 1)) := hZ.ae_eq hEq
  have hDivM : ∀ (η : Domain n → ℝ),ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Metric.ball (0 : Domain n) 1 →
      (∫ x in Metric.ball (0 : Domain n) 1,fderiv ℝ η x (Zm x))=0 := by
    intro η hη hcη hsη
    have H : (fun x => fderiv ℝ η x (Zm x)) =ᵐ[volume.restrict (Metric.ball (0 : Domain n) 1)]
        (fun x => fderiv ℝ η x (Z x)) := hEq.symm.mono fun x hx => congrArg (fderiv ℝ η x) hx
    rw [integral_congr_ae H]
    exact hdiv η hη hcη hsη
  obtain ⟨F,hF,hInside,hEnergy,hGlobal⟩ := measurable_solenoidal_kelvin_extension hn Zm hZm hZL hDivM
  have hEnergyEq : (∫ x in Metric.ball (0 : Domain n) 1,‖Zm x‖^2)=
      ∫ x in Metric.ball (0 : Domain n) 1,‖Z x‖^2 :=
    integral_congr_ae (hEq.symm.mono fun x hx => congrArg (fun z => ‖z‖^2) hx)
  refine ⟨F,hF,?_,by simpa only [hEnergyEq] using hEnergy,hGlobal⟩
  filter_upwards [hInside,hEq] with x hFx hZx
  exact hFx.trans hZx.symm

end StationaryHarmonicMaps.Analysis

end

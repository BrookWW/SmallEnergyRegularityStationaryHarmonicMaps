module

public import StationaryHarmonicMaps.Analysis.MatrixNativeMorreyExponential
public import StationaryHarmonicMaps.Analysis.SkewMeanZeroNativeMorrey
public import StationaryHarmonicMaps.Analysis.MorreyCoefficientExponentInclusion
public import StationaryHarmonicMaps.Analysis.CriticalMorreyPowerGrowth
import HolderToCK.Analysis.Harmonic.GradientVariance

/-!
# Critical control of the actual native matrix perturbation

The actual matrix product, exponential and original gradient are continuous
in the stronger native norm. The contractive exponent inclusion retains
the same original coefficient fields in the critical norm.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

noncomputable section

namespace StationaryHarmonicMaps.Analysis

private theorem actual_right_exp_continuous
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (P : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)) :
    Continuous (fun X=>matrixNativeMorreyMultiplication n hn γ hγ hγTwo q
      e.symm.toContinuousLinearMap e.toContinuousLinearMap P
      (matrixNativeMorreyExp n hn γ hγ hγTwo q e.symm.toContinuousLinearMap e.toContinuousLinearMap
        e.apply_symm_apply e.symm_apply_apply X)) := by
  let S := NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)
  let Exp : S→S := matrixNativeMorreyExp n hn γ hγ hγTwo q
    e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply e.symm_apply_apply
  let L : S→L[ℝ]S := matrixNativeMorreyMultiplication n hn γ hγ hγTwo q
    e.symm.toContinuousLinearMap e.toContinuousLinearMap P
  have hExp : Continuous Exp := continuous_iff_continuousAt.mpr
    (fun X=>(matrixNativeMorreyExp_analytic n hn γ hγ hγTwo q
      e.symm.toContinuousLinearMap e.toContinuousLinearMap
      e.apply_symm_apply e.symm_apply_apply X).continuousAt)
  exact L.continuous.comp hExp

private theorem actual_right_exp_zero
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (P : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)) :
    matrixNativeMorreyMultiplication n hn γ hγ hγTwo q e.symm.toContinuousLinearMap e.toContinuousLinearMap P
      (matrixNativeMorreyExp n hn γ hγ hγTwo q e.symm.toContinuousLinearMap e.toContinuousLinearMap
        e.apply_symm_apply e.symm_apply_apply 0)=P :=
  (congrArg (matrixNativeMorreyMultiplication n hn γ hγ hγTwo q
      e.symm.toContinuousLinearMap e.toContinuousLinearMap P)
    (matrixNativeMorreyExp_zero n hn γ hγ hγTwo q
      e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply e.symm_apply_apply)).trans
    (matrixNativeMorreyMultiplication_unit_right n hn γ hγ hγTwo q
      e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply e.symm_apply_apply P)

private theorem pair_zero_neighborhood
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    (F G : A→B) (hF : Continuous F) (hG : Continuous G) (hF0 : F 0=0) (hG0 : G 0=0)
    (r : ℝ) (hr : 0<r) :
    ∃U : Set A,U∈𝓝 (0 : A) ∧ ∀p∈U,‖F p‖<r ∧ ‖G p‖<r := by
  have hFLimit : Tendsto (fun p=>‖F p‖) (𝓝 0) (𝓝 0) := by
    simpa only [hF0,norm_zero] using (hF.norm.continuousAt (x:=0)).tendsto
  have hGLimit : Tendsto (fun p=>‖G p‖) (𝓝 0) (𝓝 0) := by
    simpa only [hG0,norm_zero] using (hG.norm.continuousAt (x:=0)).tendsto
  have hEvent : ∀ᶠp in 𝓝 (0 : A),‖F p‖<r ∧ ‖G p‖<r :=
    (hFLimit.eventually (gt_mem_nhds hr)).and (hGLimit.eventually (gt_mem_nhds hr))
  exact ⟨{p | ‖F p‖<r ∧ ‖G p‖<r},hEvent,fun _ hp=>hp⟩

private theorem mapped_difference_of_eq
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (I : A→L[ℝ]B) (F G : A) (h : F=G) : I (F-G)=0 :=
  (congrArg (fun W : A=>I (W-G)) h).trans ((congrArg I (sub_self G)).trans I.map_zero)

/-- An analytic given flux and the actual right exponential perturbation
admit a common original parameter neighborhood with arbitrarily small
critical coefficient differences. -/
theorem exists_native_matrix_critical_perturbation_neighborhood
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    let ν := (n : ℝ)-2+γ
    let S := NativeMorreySobolevSpace n (q*q) ν
    let V := SkewMeanZeroNativeMorreySpace n q ν e
    let M := MorreyCoefficientSpace n (q*q) ν
    let C := MorreyCoefficientSpace n (q*q) ((n : ℝ)-2)
    let E := e.symm.toContinuousLinearMap
    let R := e.toContinuousLinearMap
    let D : S→L[ℝ]M := nativeMorreyGradientClass (n:=n) (q:=q*q) ν
    let Exp := matrixNativeMorreyExp n hn γ hγ hγTwo q E R e.apply_symm_apply e.symm_apply_apply
    let mul := matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R
    ∀(P : S) (Z : M) (Φ : S×ℝ→M),
      (∀p,AnalyticAt ℝ Φ p) → Φ (0,0)=Z →
      ∃I : M→L[ℝ]C,‖I‖≤1 ∧
        (∀F,morreyCoefficientRecover (n:=n) (q:=q*q) ((n : ℝ)-2) (I F)=
          morreyCoefficientRecover (n:=n) (q:=q*q) ν F) ∧
        ∀r : ℝ,0<r → ∃U : Set (ℝ×V),U∈𝓝 (0 : ℝ×V) ∧
          ∀p∈U,
            ‖I (D (mul P (Exp p.2.val.val))-D P)‖<r ∧
            ‖I (Φ (p.2.val.val,p.1)-Z)‖<r := by
  intro ν S V M C E R D Exp mul P Z Φ hΦ hBase
  have hCrit : 0≤(n : ℝ)-2 := by
    have hReal : (2 : ℝ)≤n := by exact_mod_cast hn
    linarith
  have hExponents : (n : ℝ)-2≤ν := le_add_of_nonneg_right hγ.le
  let hInclusion := existsUnique_morrey_coefficient_exponent_inclusion n (q*q)
    ((n : ℝ)-2) ν hCrit hExponents
  let I : M→L[ℝ]C := hInclusion.choose
  have hI := hInclusion.choose_spec.1
  refine ⟨I,hI.1,hI.2,?_⟩
  let inc : V→L[ℝ]S := (meanZeroNativeMorreySubmodule n (q*q) ν).subtypeL.comp
    (skewMeanZeroNativeMorreySubmodule n q ν e).subtypeL
  let J : (ℝ×V)→L[ℝ](S×ℝ) :=
    (inc.comp (ContinuousLinearMap.snd ℝ ℝ V)).prod (ContinuousLinearMap.fst ℝ ℝ V)
  have hPhi : Continuous Φ := continuous_iff_continuousAt.mpr fun p=>(hΦ p).continuousAt
  let f : S→S := fun X=>mul P (Exp X)
  have hf : Continuous f := actual_right_exp_continuous n hn γ hγ hγTwo q e P
  have hf0 : f 0=P := actual_right_exp_zero n hn γ hγ hγTwo q e P
  let frame : ℝ×V→S := fun p=>f (inc p.2)
  have hFrame : Continuous frame := hf.comp (inc.comp (ContinuousLinearMap.snd ℝ ℝ V)).continuous
  have hFrame0 : frame 0=P := by
    change f (inc (0 : V))=P
    exact (congrArg f inc.map_zero).trans hf0
  let δFrame : ℝ×V→C := fun p=>I (D (frame p)-D P)
  let δFlux : ℝ×V→C := fun p=>I (Φ (J p)-Z)
  have hFrameDifference : Continuous δFrame := I.continuous.comp
    ((D.continuous.comp hFrame).sub continuous_const)
  have hFluxDifference : Continuous δFlux := I.continuous.comp
    ((hPhi.comp J.continuous).sub continuous_const)
  have hFrameDifference0 : δFrame 0=0 := by
    change I (D (frame 0)-D P)=0
    exact mapped_difference_of_eq I _ _ (congrArg D hFrame0)
  have hFluxDifference0 : δFlux 0=0 := by
    change I (Φ (J 0)-Z)=0
    exact mapped_difference_of_eq I _ _ ((congrArg Φ J.map_zero).trans hBase)
  intro r hr
  exact pair_zero_neighborhood δFrame δFlux hFrameDifference hFluxDifference
    hFrameDifference0 hFluxDifference0 r hr

private theorem raw_coefficient_difference_class {n q : ℕ} (ν : ℝ)
    (F G : MorreyCoefficientSpace n q ν)
    (Fr Gr : Domain n→Gradient n q)
    (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hGr : ∀i,MemLp (fun x=>Gr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hF : morreyCoefficientRecover (n:=n) (q:=q) ν F=hsUnitBallL2Class Fr hFr)
    (hG : morreyCoefficientRecover (n:=n) (q:=q) ν G=hsUnitBallL2Class Gr hGr) :
    morreyCoefficientRecover (n:=n) (q:=q) ν (F-G)=
      hsUnitBallL2Class (fun x i=>Fr x i-Gr x i) (fun i=>(hFr i).sub (hGr i)) := by
  have hClass : hsUnitBallL2Class Fr hFr-hsUnitBallL2Class Gr hGr=
      hsUnitBallL2Class (fun x i=>Fr x i-Gr x i) (fun i=>(hFr i).sub (hGr i)) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (hsUnitBallL2Class Fr hFr) (hsUnitBallL2Class Gr hGr),
      hsUnitBallL2Class_ae Fr hFr,hsUnitBallL2Class_ae Gr hGr,
      hsUnitBallL2Class_ae (fun x i=>Fr x i-Gr x i) (fun i=>(hFr i).sub (hGr i))] with x hSub hFx hGx hDx
    rw [hSub]
    simp only [Pi.sub_apply]
    rw [hFx,hGx,hDx]
    ext k
    rfl
  exact ((morreyCoefficientRecover (n:=n) (q:=q) ν).map_sub F G).trans
    ((congrArg₂ (fun A B : HSUnitBallL2 n q=>A-B) hF hG).trans hClass)

private theorem hs_density_le_base_difference {n q : ℕ} (F G : Gradient n q) :
    hsNormSq F≤2*hsNormSq G+2*hsNormSq (fun i=>F i-G i) := by
  have hSum : G+(fun i=>F i-G i)=F := by
    funext i
    change G i+(F i-G i)=F i
    abel
  simpa only [hSum] using HolderToCK.hsNormSq_add_le G (fun i=>F i-G i)

/-- A small difference in the actual critical coefficient norm preserves
the original raw critical energy with its literal quadratic bound. -/
theorem critical_morrey_bound_of_coefficient_difference {n q : ℕ}
    (F G : MorreyCoefficientSpace n q ((n : ℝ)-2))
    (Fr Gr : Domain n→Gradient n q)
    (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hGr : ∀i,MemLp (fun x=>Gr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hF : morreyCoefficientRecover (n:=n) (q:=q) ((n : ℝ)-2) F=hsUnitBallL2Class Fr hFr)
    (hG : morreyCoefficientRecover (n:=n) (q:=q) ((n : ℝ)-2) G=hsUnitBallL2Class Gr hGr)
    (r M : ℝ) (hr : 0≤r) (hM : 0≤M) (hNorm : ‖F-G‖≤r)
    (hCritical : criticalGradientMorreySquare Gr (ball (0 : Domain n) 1)≤ENNReal.ofReal M) :
    criticalGradientMorreySquare Fr (ball (0 : Domain n) 1)≤ENNReal.ofReal (2*M+2*r^2) := by
  let Dr : Domain n→Gradient n q := fun x i=>Fr x i-Gr x i
  have hDr (i : Fin n) : MemLp (fun x=>Dr x i) 2
      (volume.restrict (ball (0 : Domain n) 1)) := (hFr i).sub (hGr i)
  have hDifference : morreyCoefficientRecover (n:=n) (q:=q) ((n : ℝ)-2) (F-G)=hsUnitBallL2Class Dr hDr :=
    raw_coefficient_difference_class ((n : ℝ)-2) F G Fr Gr hFr hGr hF hG
  have hGrowth := morreyCoefficient_power_growth ((n : ℝ)-2) Dr hDr (F-G) hDifference
  have hNormSquare : ‖F-G‖^2≤r^2 := (sq_le_sq₀ (norm_nonneg _) hr).mpr hNorm
  have hFI : IntegrableOn (fun x=>hsNormSq (Fr x)) (ball (0 : Domain n) 1) volume :=
    integrable_hsNormSq_of_columns Fr hFr
  have hGI : IntegrableOn (fun x=>hsNormSq (Gr x)) (ball (0 : Domain n) 1) volume :=
    integrable_hsNormSq_of_columns Gr hGr
  have hDI : IntegrableOn (fun x=>hsNormSq (Dr x)) (ball (0 : Domain n) 1) volume :=
    integrable_hsNormSq_of_columns Dr hDr
  apply criticalGradientMorreySquare_le_of_truncated_power_growth Fr (ball (0 : Domain n) 1) hFr (2*M+2*r^2)
  intro a ha ρ hρ
  have hGLocal : (∫x in ball a ρ∩ball (0 : Domain n) 1,hsNormSq (Gr x))≤M*ρ^((n : ℝ)-2) :=
    integral_hsNormSq_le_of_criticalMorrey Gr ha hρ hM (Subset.refl _)
      (fun i=>(hGr i).mono_measure (Measure.restrict_mono_set volume inter_subset_right)) hCritical
  have hDLocal : (∫x in ball a ρ∩ball (0 : Domain n) 1,hsNormSq (Dr x))≤r^2*ρ^((n : ℝ)-2) :=
    (hGrowth a ha ρ hρ).trans (mul_le_mul_of_nonneg_right hNormSquare (Real.rpow_nonneg hρ.le _))
  calc
    _≤∫x in ball a ρ∩ball (0 : Domain n) 1,2*hsNormSq (Gr x)+2*hsNormSq (Dr x) :=
      integral_mono (hFI.mono_set inter_subset_right)
        (((hGI.mono_set inter_subset_right).const_mul 2).add ((hDI.mono_set inter_subset_right).const_mul 2))
        (fun x=>hs_density_le_base_difference (Fr x) (Gr x))
    _=2*(∫x in ball a ρ∩ball (0 : Domain n) 1,hsNormSq (Gr x))+
        2*(∫x in ball a ρ∩ball (0 : Domain n) 1,hsNormSq (Dr x)) := by
      rw [integral_add ((hGI.mono_set inter_subset_right).const_mul 2) ((hDI.mono_set inter_subset_right).const_mul 2),
        integral_const_mul,integral_const_mul]
    _≤2*(M*ρ^((n : ℝ)-2))+2*(r^2*ρ^((n : ℝ)-2)) := by linarith
    _=(2*M+2*r^2)*ρ^((n : ℝ)-2) := by ring

end StationaryHarmonicMaps.Analysis

end

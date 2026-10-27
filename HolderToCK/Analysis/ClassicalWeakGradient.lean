module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Native local Sobolev data of C1 maps

Compact tests have support inside the C1 carrier. Integration by parts therefore
uses differentiability only there; no regularity of an ambient extension is
required. The continuous classical columns give local L2 membership on compact
subsets of the same open domain.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace HolderToCK

theorem continuous_smul_of_tsupport_subset {n q : ℕ} {Ω : OpenDomain n}
    {f : Domain n → Ambient q} (hf : ContinuousOn f Ω.val)
    {φ : Domain n → ℝ} (hφ : Continuous φ) (hsφ : tsupport φ ⊆ Ω.val) :
    Continuous (fun x => φ x • f x) := by
  apply continuous_of_tsupport
  intro x hx
  have hxΩ := hsφ (tsupport_smul_subset_left φ f hx)
  exact hφ.continuousAt.smul (hf.continuousAt (Ω.property.mem_nhds hxΩ))

theorem continuousOn_locallyMemL2 {n q : ℕ} {Ω : OpenDomain n}
    {f : Domain n → Ambient q} (hf : ContinuousOn f Ω.val) : LocallyMemL2 Ω f := by
  intro K hK hKΩ
  have hcont := hf.mono hKΩ
  have hI : IntegrableOn f K volume := hcont.integrableOn_compact hK
  have hI2 : IntegrableOn (fun x => ‖f x‖ ^ 2) K volume :=
    (hcont.norm.pow 2).integrableOn_compact hK
  exact (memLp_two_iff_integrable_sq_norm hI.aestronglyMeasurable).mpr hI2

theorem hasWeakGradient_of_contDiffOn_one {n q : ℕ} (Ω : OpenDomain n)
    {f : Domain n → Ambient q} (hf : ContDiffOn ℝ 1 f Ω.val) :
    HasWeakGradient Ω f (fun x i => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  have hDf : ContinuousOn (fderiv ℝ f) Ω.val :=
    hf.continuousOn_fderiv_of_isOpen Ω.property le_rfl
  have hcolumn : ∀ i : Fin n,
      ContinuousOn (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) Ω.val := by
    intro i
    exact hDf.clm_apply continuousOn_const
  refine ⟨hf.continuousOn.locallyIntegrableOn Ω.property.measurableSet,
    (fun i => (hcolumn i).locallyIntegrableOn Ω.property.measurableSet), ?_⟩
  intro i φ hφ hcφ hsφ
  have hdφ : Continuous (coordinateDerivative φ hφ i) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdφ : HasCompactSupport (coordinateDerivative φ hφ i) :=
    hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hsdφ : tsupport (coordinateDerivative φ hφ i) ⊆ Ω.val :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsφ
  have hpair : Integrable (fun x => coordinateDerivative φ hφ i x • f x) volume :=
    (continuous_smul_of_tsupport_subset hf.continuousOn hdφ hsdφ).integrable_of_hasCompactSupport
      hcdφ.smul_right
  have hgrad : Integrable (fun x => φ x • fderiv ℝ f x (EuclideanSpace.single i 1)) volume :=
    (continuous_smul_of_tsupport_subset (hcolumn i) hφ.continuous hsφ).integrable_of_hasCompactSupport
      hcφ.smul_right
  have hprod : Integrable (fun x => φ x • f x) volume :=
    (continuous_smul_of_tsupport_subset hf.continuousOn hφ.continuous hsφ).integrable_of_hasCompactSupport
      hcφ.smul_right
  have hIBP := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (f := φ) (g := f) (v := EuclideanSpace.single i 1)
    hpair hgrad hprod
    (fun _ _ => (hφ.differentiable (by simp)).differentiableAt)
    (fun x hx => (hf.contDiffAt (Ω.property.mem_nhds (hsφ hx))).differentiableAt (by norm_num))
  have hleft : (∫ x in Ω.val, coordinateDerivative φ hφ i x • f x) =
      ∫ x, coordinateDerivative φ hφ i x • f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hnot : x ∉ tsupport (coordinateDerivative φ hφ i) := fun hmem => hx (hsdφ hmem)
    rw [image_eq_zero_of_notMem_tsupport hnot, zero_smul]
  have hright : (∫ x in Ω.val, φ x • fderiv ℝ f x (EuclideanSpace.single i 1)) =
      ∫ x, φ x • fderiv ℝ f x (EuclideanSpace.single i 1) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hnot : x ∉ tsupport φ := fun hmem => hx (hsφ hmem)
    rw [image_eq_zero_of_notMem_tsupport hnot, zero_smul]
  rw [hleft, hright]
  exact neg_eq_iff_eq_neg.mp hIBP.symm

theorem memW12Loc_of_contDiffOn_one {n q : ℕ} (Ω : OpenDomain n)
    {f : Domain n → Ambient q} (hf : ContDiffOn ℝ 1 f Ω.val) :
    MemW12Loc Ω f (fun x i => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  refine ⟨hasWeakGradient_of_contDiffOn_one Ω hf,
    continuousOn_locallyMemL2 hf.continuousOn, ?_⟩
  intro i
  exact continuousOn_locallyMemL2
    ((hf.continuousOn_fderiv_of_isOpen Ω.property le_rfl).clm_apply continuousOn_const)

end HolderToCK
end

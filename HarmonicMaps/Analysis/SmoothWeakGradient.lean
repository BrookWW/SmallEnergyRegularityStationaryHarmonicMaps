module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Weak gradients of globally smooth maps

Compact scalar tests and ordinary integration by parts identify the classical
coordinate derivatives of a smooth map with its distributional derivatives
on every open domain. Finite L2 data then give the literal finite Sobolev
predicate for the same classical derivative columns.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff

namespace HarmonicMaps

noncomputable section

/-- All three compact-test products required by integration by parts are integrable. -/
theorem contDiff_compactTest_pairings_integrable {n q : ℕ}
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f)
    {φ : Domain n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (i : Fin n) :
    Integrable (fun x => φ x • f x) volume ∧
    Integrable (fun x => coordinateDerivative φ hφ i x • f x) volume ∧
    Integrable (fun x => φ x • coordinateDerivative f hf i x) volume := by
  have hdf : Continuous (coordinateDerivative f hf i) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ : Continuous (coordinateDerivative φ hφ i) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdφ : HasCompactSupport (coordinateDerivative φ hφ i) :=
    hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  exact ⟨(hφ.continuous.smul hf.continuous).integrable_of_hasCompactSupport hcφ.smul_right,
    (hdφ.smul hf.continuous).integrable_of_hasCompactSupport hcdφ.smul_right,
    (hφ.continuous.smul hdf).integrable_of_hasCompactSupport hcφ.smul_right⟩

/-- The actual classical coordinate columns of a smooth map are its weak gradient. -/
theorem hasWeakGradient_of_contDiff {n q : ℕ} (Ω : OpenDomain n)
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f) :
    HasWeakGradient Ω f (fun x i => coordinateDerivative f hf i x) := by
  refine ⟨hf.continuous.locallyIntegrable.locallyIntegrableOn Ω.val, ?_, ?_⟩
  · intro i
    have hdi : Continuous (coordinateDerivative f hf i) :=
      (hf.continuous_fderiv (by simp)).clm_apply continuous_const
    exact hdi.locallyIntegrable.locallyIntegrableOn Ω.val
  · intro i φ hφ hcφ hsφ
    have hpair := contDiff_compactTest_pairings_integrable hf hφ hcφ i
    have hIBP := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      (f := φ) (g := f) (v := EuclideanSpace.single i 1)
      hpair.2.1 hpair.2.2 hpair.1
      (fun _ _ => (hφ.differentiable (by simp)).differentiableAt)
      (fun _ _ => (hf.differentiable (by simp)).differentiableAt)
    have hleft : (∫ x in Ω.val, coordinateDerivative φ hφ i x • f x) =
        ∫ x, coordinateDerivative φ hφ i x • f x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hnot : x ∉ tsupport φ := fun hmem => hx (hsφ hmem)
      have hdnot : x ∉ tsupport (coordinateDerivative φ hφ i) :=
        fun hmem => hnot (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) hmem)
      rw [image_eq_zero_of_notMem_tsupport hdnot, zero_smul]
    have hright : (∫ x in Ω.val, φ x • coordinateDerivative f hf i x) =
        ∫ x, φ x • coordinateDerivative f hf i x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hnot : x ∉ tsupport φ := fun hmem => hx (hsφ hmem)
      rw [image_eq_zero_of_notMem_tsupport hnot, zero_smul]
    rw [hleft, hright]
    exact neg_eq_iff_eq_neg.mp hIBP.symm

/-- A globally smooth map with finite map and classical-column L2 data is finite W1,2. -/
theorem memW12_of_contDiff {n q : ℕ} (Ω : OpenDomain n)
    {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f)
    (hF : MemLp f 2 (volume.restrict Ω.val))
    (hDf : ∀ i, MemLp (coordinateDerivative f hf i) 2 (volume.restrict Ω.val)) :
    MemW12 Ω f (fun x i => coordinateDerivative f hf i x) :=
  ⟨hasWeakGradient_of_contDiff Ω hf, hF, hDf⟩

end
end HarmonicMaps

end

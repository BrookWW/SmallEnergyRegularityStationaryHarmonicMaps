module

public import HolderToCK.Analysis.ClassicalWeakGradient
public import HolderToCK.Foundation.WeakPoisson
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-! # Compact Green identities on an open C2 carrier

The map needs regularity only on its open domain. Compact support of the test
provides global integrability of every pairing. The Laplacian is the actual
orthonormal trace of the second derivative, with the native negative weak sign.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff Topology

namespace HolderToCK

theorem compact_inner_integrable {n q : ℕ} {Ω : OpenDomain n}
    {f g : Domain n → Ambient q} (hf : ContinuousOn f Ω.val) (hg : Continuous g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω.val) :
    Integrable (fun x => inner ℝ (f x) (g x)) volume := by
  have hsupport : Function.support (fun x => inner ℝ (f x) (g x)) ⊆ Function.support g := by
    intro x hx
    by_contra hnot
    apply hx
    change inner ℝ (f x) (g x) = 0
    rw [Function.notMem_support.mp hnot, inner_zero_right]
  have htsupport : tsupport (fun x => inner ℝ (f x) (g x)) ⊆ tsupport g :=
    closure_mono hsupport
  have hcont : Continuous (fun x => inner ℝ (f x) (g x)) := by
    apply continuous_of_tsupport
    intro x hx
    exact (hf.continuousAt (Ω.property.mem_nhds (hs (htsupport hx)))).inner hg.continuousAt
  exact hcont.integrable_of_hasCompactSupport
    (hc.isCompact.of_isClosed_subset (isClosed_tsupport _) htsupport)

theorem compact_test_inner_fderiv_integral {n q : ℕ} (Ω : OpenDomain n)
    {f : Domain n → Ambient q} (hf : ContDiffOn ℝ 1 f Ω.val)
    {ψ : Domain n → Ambient q} (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Ω.val) (i : Fin n) :
    IntegrableOn (fun x => inner ℝ (fderiv ℝ f x (EuclideanSpace.single i 1)) (ψ x)) Ω.val ∧
    IntegrableOn (fun x => inner ℝ (f x) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) Ω.val ∧
    (∫ x in Ω.val, inner ℝ (fderiv ℝ f x (EuclideanSpace.single i 1)) (ψ x)) =
      -(∫ x in Ω.val, inner ℝ (f x) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
  have hdf : ContinuousOn (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) Ω.val :=
    (hf.continuousOn_fderiv_of_isOpen Ω.property le_rfl).clm_apply continuousOn_const
  have hdψ : Continuous (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdψ := hcψ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hsdψ := (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsψ
  have hleft := compact_inner_integrable hdf hψ.continuous hcψ hsψ
  have hright := compact_inner_integrable hf.continuousOn hdψ hcdψ hsdψ
  have hprod := compact_inner_integrable hf.continuousOn hψ.continuous hcψ hsψ
  have hi := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (f := f) (g := ψ) (v := EuclideanSpace.single i 1) (B := innerSL ℝ)
    hleft hright hprod
    (fun x hx => (hf.contDiffAt (Ω.property.mem_nhds (hsψ hx))).differentiableAt one_ne_zero)
    (fun _ _ => (hψ.differentiable (by simp)).differentiableAt)
  have hleftΩ : (∫ x in Ω.val, inner ℝ (fderiv ℝ f x (EuclideanSpace.single i 1)) (ψ x)) =
      ∫ x, inner ℝ (fderiv ℝ f x (EuclideanSpace.single i 1)) (ψ x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsψ h)), inner_zero_right]
  have hrightΩ : (∫ x in Ω.val, inner ℝ (f x) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      ∫ x, inner ℝ (f x) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsdψ h)), inner_zero_right]
  refine ⟨hleft.integrableOn, hright.integrableOn, ?_⟩
  rw [hleftΩ, hrightΩ]
  exact neg_eq_iff_eq_neg.mp hi.symm

theorem laplacian_eq_coordinateSum_of_contDiffAt_two {n q : ℕ}
    (f : Domain n → Ambient q) (x : Domain n) (hf : ContDiffAt ℝ 2 f x) :
    Laplacian.laplacian f x = ∑ i : Fin n,
      fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

theorem continuousOn_laplacian_of_contDiffOn_two {n q : ℕ} (Ω : OpenDomain n)
    {f : Domain n → Ambient q} (hf : ContDiffOn ℝ 2 f Ω.val) :
    ContinuousOn (Laplacian.laplacian f) Ω.val := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply continuousOn_finsetSum Finset.univ
  intro i _ x hx
  have hD2 : ContinuousAt (iteratedFDeriv ℝ 2 f) x :=
    (hf.contDiffAt (Ω.property.mem_nhds hx)).continuousAt_iteratedFDeriv le_rfl
  exact ((continuous_eval_const _).continuousAt.comp hD2).continuousWithinAt

theorem weakPoissonOn_of_contDiffOn_two {n q : ℕ} (Ω : OpenDomain n)
    {f : Domain n → Ambient q} (hf : ContDiffOn ℝ 2 f Ω.val) :
    WeakPoissonOn Ω (fun x i => fderiv ℝ f x (EuclideanSpace.single i 1))
      (Laplacian.laplacian f) := by
  have hcolumn (i : Fin n) : ContDiffOn ℝ 1
      (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) Ω.val :=
    (hf.fderiv_of_isOpen Ω.property (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply
      contDiffOn_const
  have hsecond (i : Fin n) : ContinuousOn
      (fun x => fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) Ω.val :=
    ((hcolumn i).continuousOn_fderiv_of_isOpen Ω.property le_rfl).clm_apply continuousOn_const
  have hlap : EqOn (Laplacian.laplacian f)
      (fun x => ∑ i : Fin n, fderiv ℝ
        (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) Ω.val := by
    intro x hx
    exact laplacian_eq_coordinateSum_of_contDiffAt_two f x (hf.contDiffAt (Ω.property.mem_nhds hx))
  have hsum : ContinuousOn (fun x => ∑ i : Fin n, fderiv ℝ
      (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) Ω.val :=
    continuousOn_finsetSum Finset.univ (fun i _ => hsecond i)
  refine ⟨(hsum.congr hlap).locallyIntegrableOn Ω.property.measurableSet, ?_⟩
  intro ψ hψ hcψ hsψ
  have hpair (i : Fin n) := compact_test_inner_fderiv_integral Ω (hcolumn i) hψ hcψ hsψ i
  have hfirst : IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (fderiv ℝ f x (EuclideanSpace.single i 1))
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) Ω.val :=
    integrable_finsetSum Finset.univ (fun i _ => (hpair i).2.1)
  have hforce : IntegrableOn (fun x => inner ℝ (Laplacian.laplacian f x) (ψ x)) Ω.val :=
    (compact_inner_integrable (hsum.congr hlap) hψ.continuous hcψ hsψ).integrableOn
  refine ⟨hfirst, hforce, ?_⟩
  rw [integral_finsetSum _ (fun i _ => (hpair i).2.1)]
  have hsign (i : Fin n) :
      (∫ x in Ω.val, inner ℝ (fderiv ℝ f x (EuclideanSpace.single i 1))
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      -(∫ x in Ω.val, inner ℝ
        (fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) (ψ x)) :=
    neg_eq_iff_eq_neg.mp (hpair i).2.2.symm
  simp_rw [hsign]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => (hpair i).1)]
  apply congrArg Neg.neg
  apply setIntegral_congr_fun Ω.property.measurableSet
  intro x hx
  dsimp only
  rw [hlap hx, sum_inner]

end HolderToCK
end

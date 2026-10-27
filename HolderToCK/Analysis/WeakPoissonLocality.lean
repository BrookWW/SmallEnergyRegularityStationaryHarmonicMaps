module

public import HolderToCK.Foundation.WeakPoisson
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Almost-everywhere forcing and uniqueness for the weak Poisson equation

Smooth compact vector tests identify the forcing without changing the displayed
gradient. Almost-everywhere replacements preserve both integrable pairings and
the signed equation.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ENNReal ContDiff Topology

namespace HolderToCK

theorem locallyIntegrableOn_smul_compactTest_integrable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : OpenDomain n}
    {f : Domain n → E} {φ : Domain n → ℝ}
    (hf : LocallyIntegrableOn f Ω.val volume) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ Ω.val) :
    Integrable (fun x => φ x • f x) volume := by
  have hfK : IntegrableOn f (tsupport φ) volume := hf.integrableOn_compact_subset hsφ hcφ
  have hφK : MemLp φ (⊤ : ℝ≥0∞) (volume.restrict (tsupport φ)) :=
    hφ.memLp_top_of_hasCompactSupport hcφ _
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp (hfK.smul_of_top_right hφK)
  intro x hx
  by_contra hnot
  apply hx
  change φ x • f x = 0
  rw [image_eq_zero_of_notMem_tsupport hnot, zero_smul]

theorem WeakPoissonOn.congr {n q : ℕ} {Ω : OpenDomain n}
    {Du Dv : Domain n → Gradient n q} {F G : Domain n → Ambient q}
    (hEq : WeakPoissonOn Ω Du F)
    (hDu : Du =ᵐ[volume.restrict Ω.val] Dv) (hF : F =ᵐ[volume.restrict Ω.val] G) :
    WeakPoissonOn Ω Dv G := by
  refine ⟨LocallyIntegrableOn.congr hF hEq.1, ?_⟩
  intro ψ hψ hcψ hsψ
  obtain ⟨hleft, hright, heq⟩ := hEq.2 ψ hψ hcψ hsψ
  have hleftEq : (fun x => ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =ᵐ[volume.restrict Ω.val]
      (fun x => ∑ i : Fin n,
        inner ℝ (Dv x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
    filter_upwards [hDu] with x hx
    rw [hx]
  have hrightEq : (fun x => inner ℝ (F x) (ψ x)) =ᵐ[volume.restrict Ω.val]
      (fun x => inner ℝ (G x) (ψ x)) := by
    filter_upwards [hF] with x hx
    rw [hx]
  refine ⟨hleft.congr hleftEq, hright.congr hrightEq, ?_⟩
  calc
    _ = ∫ x in Ω.val, ∑ i : Fin n,
        inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) :=
      (integral_congr_ae hleftEq).symm
    _ = -(∫ x in Ω.val, inner ℝ (F x) (ψ x)) := heq
    _ = _ := congrArg Neg.neg (integral_congr_ae hrightEq)

theorem WeakPoissonOn.mono {n q : ℕ} {Ω Ω' : OpenDomain n}
    {Du : Domain n → Gradient n q} {F : Domain n → Ambient q}
    (hEq : WeakPoissonOn Ω Du F) (hsub : Ω'.val ⊆ Ω.val) :
    WeakPoissonOn Ω' Du F := by
  refine ⟨hEq.1.mono_set hsub, ?_⟩
  intro ψ hψ hcψ hsψ
  obtain ⟨hleft, hright, heq⟩ := hEq.2 ψ hψ hcψ (hsψ.trans hsub)
  have hleftWhole (s : Set (Domain n)) (hs : tsupport ψ ⊆ s) :
      (∫ x in s, ∑ i : Fin n,
        inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      ∫ x, ∑ i : Fin n, inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hd (i : Fin n) : fderiv ℝ ψ x (EuclideanSpace.single i 1) = 0 := by
      have hnot : x ∉ tsupport (fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1)) :=
        fun h => hx (hs (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) h))
      exact image_eq_zero_of_notMem_tsupport
        (f := fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1)) hnot
    simp only [hd, inner_zero_right, Finset.sum_const_zero]
  have hrightWhole (s : Set (Domain n)) (hs : tsupport ψ ⊆ s) :
      (∫ x in s, inner ℝ (F x) (ψ x)) = ∫ x, inner ℝ (F x) (ψ x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), inner_zero_right]
  refine ⟨hleft.mono_set hsub, hright.mono_set hsub, ?_⟩
  rw [hleftWhole Ω'.val hsψ, hrightWhole Ω'.val hsψ]
  rwa [hleftWhole Ω.val (hsψ.trans hsub), hrightWhole Ω.val (hsψ.trans hsub)] at heq

theorem WeakPoissonOn.sub {n q : ℕ} {Ω : OpenDomain n}
    {Du Dv : Domain n → Gradient n q} {F G : Domain n → Ambient q}
    (hF : WeakPoissonOn Ω Du F) (hG : WeakPoissonOn Ω Dv G) :
    WeakPoissonOn Ω (fun x i => Du x i - Dv x i) (fun x => F x - G x) := by
  refine ⟨hF.1.sub hG.1, ?_⟩
  intro ψ hψ hcψ hsψ
  have hWeakF := hF.2 ψ hψ hcψ hsψ
  have hWeakG := hG.2 ψ hψ hcψ hsψ
  have hleft (x : Domain n) :
      (∑ i : Fin n, inner ℝ (Du x i - Dv x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      (∑ i : Fin n, inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) -
        (∑ i : Fin n, inner ℝ (Dv x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
    simp only [inner_sub_left, Finset.sum_sub_distrib]
  have hright (x : Domain n) : inner ℝ (F x - G x) (ψ x) =
      inner ℝ (F x) (ψ x) - inner ℝ (G x) (ψ x) := inner_sub_left _ _ _
  refine ⟨(hWeakF.1.sub hWeakG.1).congr (Eventually.of_forall fun x => (hleft x).symm),
    (hWeakF.2.1.sub hWeakG.2.1).congr (Eventually.of_forall fun x => (hright x).symm), ?_⟩
  rw [setIntegral_congr_fun Ω.property.measurableSet (fun x _ => hleft x),
    integral_sub hWeakF.1 hWeakG.1,
    setIntegral_congr_fun Ω.property.measurableSet (fun x _ => hright x),
    integral_sub hWeakF.2.1 hWeakG.2.1, hWeakF.2.2, hWeakG.2.2]
  ring

theorem WeakPoissonOn.ae_eq_forcing {n q : ℕ} {Ω : OpenDomain n}
    {Du : Domain n → Gradient n q} {F G : Domain n → Ambient q}
    (hF : WeakPoissonOn Ω Du F) (hG : WeakPoissonOn Ω Du G) :
    F =ᵐ[volume.restrict Ω.val] G := by
  have hlocal := hF.1.sub hG.1
  have hzero : ∀ᵐ x ∂volume, x ∈ Ω.val → F x - G x = 0 := by
    apply Ω.property.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal
    intro φ hφ hcφ hsφ
    have hI := locallyIntegrableOn_smul_compactTest_integrable hlocal hφ.continuous hcφ hsφ
    change (∫ x, φ x • (F x - G x)) = 0
    have hwhole : (∫ x, φ x • (F x - G x)) = ∫ x in Ω.val, φ x • (F x - G x) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsφ h)), zero_smul]
    rw [hwhole]
    apply ext_inner_left ℝ
    intro v
    have hIΩ : IntegrableOn (fun x => φ x • (F x - G x)) Ω.val := hI.integrableOn
    rw [← integral_inner hIΩ v, inner_zero_right]
    let ψ : Domain n → Ambient q := fun x => φ x • v
    have hψ : ContDiff ℝ ∞ ψ := hφ.smul contDiff_const
    have hcψ : HasCompactSupport ψ := hcφ.smul_right
    have hsψ : tsupport ψ ⊆ Ω.val := (tsupport_smul_subset_left _ _).trans hsφ
    have hWeakF := hF.2 ψ hψ hcψ hsψ
    have hWeakG := hG.2 ψ hψ hcψ hsψ
    have hpair : (∫ x in Ω.val, inner ℝ (F x) (ψ x)) =
        ∫ x in Ω.val, inner ℝ (G x) (ψ x) :=
      neg_injective (hWeakF.2.2.symm.trans hWeakG.2.2)
    have htest (x : Domain n) : inner ℝ v (φ x • (F x - G x)) =
        inner ℝ (F x) (ψ x) - inner ℝ (G x) (ψ x) := by
      simp only [ψ, inner_smul_right, inner_sub_right]
      rw [real_inner_comm v (F x), real_inner_comm v (G x)]
      ring
    rw [setIntegral_congr_fun Ω.property.measurableSet (fun x _ => htest x),
      integral_sub hWeakF.2.1 hWeakG.2.1, hpair, sub_self]
  apply (ae_restrict_iff' Ω.property.measurableSet).2
  filter_upwards [hzero] with x hx hxΩ
  exact sub_eq_zero.mp (hx hxΩ)

end HolderToCK
end

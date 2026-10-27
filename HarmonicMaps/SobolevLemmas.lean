module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Integrable weak pairings and uniqueness of weak gradients

The weak derivative identities in `Sobolev` have integrable pairings, and
their gradient fields are unique almost everywhere on the open domain.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace HarmonicMaps

private theorem integrable_smul_compactTest {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : OpenDomain n} {f : Domain n → E} {φ : Domain n → ℝ}
    (hf : LocallyIntegrableOn f Ω.val volume)
    (hφ : Continuous φ) (hcompact : HasCompactSupport φ)
    (hsupport : tsupport φ ⊆ Ω.val) :
    Integrable (fun x => φ x • f x) volume := by
  have hfK : IntegrableOn f (tsupport φ) volume :=
    hf.integrableOn_compact_subset hsupport hcompact
  have hφK : MemLp φ ∞ (volume.restrict (tsupport φ)) :=
    hφ.memLp_top_of_hasCompactSupport hcompact _
  have hpairK : IntegrableOn (fun x => φ x • f x) (tsupport φ) volume :=
    hfK.smul_of_top_right hφK
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hpairK
  intro x hx
  by_contra hnot
  have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport hnot
  simp [Function.mem_support, hzero] at hx

/-- A test function paired with any coordinate of a weak gradient is integrable. -/
theorem HasWeakGradient.integrable_test_gradient {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hDu : HasWeakGradient Ω u Du)
    (i : Fin n) {φ : Domain n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ)
    (hsupport : tsupport φ ⊆ Ω.val) :
    IntegrableOn (fun x => φ x • Du x i) Ω.val volume :=
  (integrable_smul_compactTest (hDu.2.1 i) hφ.continuous hcompact hsupport).integrableOn

/-- The coordinate derivative of a test function paired with the map is integrable. -/
theorem HasWeakGradient.integrable_test_derivative {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hDu : HasWeakGradient Ω u Du)
    (i : Fin n) {φ : Domain n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ)
    (hsupport : tsupport φ ⊆ Ω.val) :
    IntegrableOn (fun x => coordinateDerivative φ hφ i x • u x) Ω.val volume := by
  have hderiv_cont : Continuous (coordinateDerivative φ hφ i) := by
    unfold coordinateDerivative
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hderiv_compact : HasCompactSupport (coordinateDerivative φ hφ i) := by
    change HasCompactSupport
      (fun x : Domain n => fderiv ℝ φ x (EuclideanSpace.single i 1))
    exact hcompact.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hderiv_support : tsupport (coordinateDerivative φ hφ i) ⊆ Ω.val := by
    exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsupport
  exact (integrable_smul_compactTest hDu.1 hderiv_cont hderiv_compact
    hderiv_support).integrableOn

/-- Any two weak gradients of the same map have equal coordinate columns almost everywhere. -/
theorem HasWeakGradient.ae_eq_coordinate {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q}
    {Du Dv : Domain n → Gradient n q}
    (hDu : HasWeakGradient Ω u Du) (hDv : HasWeakGradient Ω u Dv)
    (i : Fin n) :
    (fun x => Du x i) =ᵐ[volume.restrict Ω.val] (fun x => Dv x i) := by
  have hlocal : LocallyIntegrableOn (fun x => Du x i - Dv x i) Ω.val volume :=
    (hDu.2.1 i).sub (hDv.2.1 i)
  have hzero : ∀ᵐ x ∂volume, x ∈ Ω.val → Du x i - Dv x i = 0 := by
    apply Ω.property.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal
    intro φ hφ hcompact hsupport
    have hpair : (∫ x in Ω.val, φ x • Du x i) =
        ∫ x in Ω.val, φ x • Dv x i := by
      apply neg_injective
      exact (hDu.2.2 i φ hφ hcompact hsupport).symm.trans
        (hDv.2.2 i φ hφ hcompact hsupport)
    have hzero_on : (∫ x in Ω.val, φ x • (Du x i - Dv x i)) = 0 := by
      simp_rw [smul_sub]
      rw [integral_sub
        (hDu.integrable_test_gradient i hφ hcompact hsupport)
        (hDv.integrable_test_gradient i hφ hcompact hsupport), hpair, sub_self]
    have hwhole : (∫ x in Ω.val, φ x • (Du x i - Dv x i)) =
        ∫ x, φ x • (Du x i - Dv x i) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hnot : x ∉ tsupport φ := fun hmem => hx (hsupport hmem)
      simp [image_eq_zero_of_notMem_tsupport hnot]
    exact hwhole.symm.trans hzero_on
  apply (ae_restrict_iff' Ω.property.measurableSet).2
  filter_upwards [hzero] with x hx hxΩ
  exact sub_eq_zero.mp (hx hxΩ)

/-- The displayed weak gradient is unique almost everywhere on its open domain. -/
theorem HasWeakGradient.ae_eq {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q}
    {Du Dv : Domain n → Gradient n q}
    (hDu : HasWeakGradient Ω u Du) (hDv : HasWeakGradient Ω u Dv) :
    Du =ᵐ[volume.restrict Ω.val] Dv := by
  have hcolumns : ∀ i : Fin n,
      ∀ᵐ x ∂volume.restrict Ω.val, Du x i = Dv x i :=
    fun i => hDu.ae_eq_coordinate hDv i
  filter_upwards [ae_all_iff.2 hcolumns] with x hx
  funext i
  exact hx i

end HarmonicMaps

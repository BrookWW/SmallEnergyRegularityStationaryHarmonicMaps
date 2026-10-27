module

public import StationaryHarmonicMaps.Analysis.OperatorFluxIntegrability
public import StationaryHarmonicMaps.Analysis.SmoothTestLocalization
public import StationaryHarmonicMaps.Analysis.WeakPoissonBoundedTest
public import HolderToCK.Analysis.WeakPoissonLocality

/-!
# The actual weak operator-flux transformation

The original signed Poisson equation is tested with the actual bounded
zero-boundary product Pψ. A finite interior-ball localization gives the
transformation on arbitrary open domains with only local Sobolev data.
This is an operator product rule and assumes no gauge construction or identity.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem inner_apply_eq_star_inner {q : ℕ}
    (A : Ambient q →L[ℝ] Ambient q) (v w : Ambient q) :
    inner ℝ v (A w) = inner ℝ (star A v) w :=
  (ContinuousLinearMap.adjoint_inner_left A w v).symm

/-- The actual bounded Sobolev product gives the flux identity for a test in one interior ball. -/
theorem weak_operator_flux_transform_local {n m q : ℕ} {Ω : OpenDomain n}
    {p : Domain n → Ambient m} {Dp : Domain n → Gradient n m}
    (hp : MemW12Loc Ω p Dp) {M : ℝ}
    (hb : ∀ᵐ x ∂volume.restrict Ω.val, ‖p x‖ ≤ M)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {F : Domain n → Ambient q}
    (hP : HolderToCK.WeakPoissonOn Ω Du F)
    {a : Domain n} {r : ℝ} (hr : 0 < r) (hclosed : Metric.closedBall a r ⊆ Ω.val)
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Metric.ball a r) :
    (∫ x, ∑ i : Fin n, inner ℝ (star (R (p x)) (Du x i))
      (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      -(∫ x, inner ℝ (star (R (p x)) (F x) +
        ∑ i : Fin n, star (R (Dp x i)) (Du x i)) (ψ x)) := by
  let E (x : Domain n) (i : Fin n) := star (R (p x)) (Du x i)
  let J (x : Domain n) := star (R (p x)) (F x) + ∑ i : Fin n, star (R (Dp x i)) (Du x i)
  have hball : Metric.ball a r ⊆ Ω.val := Metric.ball_subset_closedBall.trans hclosed
  have hsΩ := hsψ.trans hball
  have hEL := locallyMemL2_operator_flux hp hb R hu
  have hJL := locallyIntegrableOn_operator_flux_rhs hp hb R hu hP.1
  have hLI := integrable_locallyL2_vector_test E hEL ψ hψ hcψ hsΩ
  have hJI := integrable_locallyL1_vector_test hJL ψ hψ.continuous hcψ hsΩ
  obtain ⟨hw, C, _hC, hbound⟩ := operator_test_zeroBoundary_ball hp hb R hr hclosed ψ hψ hcψ hsψ
  have hFB : IntegrableOn F (Metric.ball a r) volume :=
    (hP.1.integrableOn_compact_subset hclosed (isCompact_closedBall a r)).mono_set
      Metric.ball_subset_closedBall
  have H := weakPoissonOn_bounded_zeroBoundary_test (hP.mono hball)
    (hu.memW12_ball hclosed).2.2 hFB hw hbound
  have hpoint (x : Domain n) :
      (∑ i : Fin n, inner ℝ (Du x i)
        (R (Dp x i) (ψ x) + R (p x) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))) +
          inner ℝ (F x) (R (p x) (ψ x)) =
      (∑ i : Fin n, inner ℝ (E x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) +
        inner ℝ (J x) (ψ x) := by
    simp only [inner_add_right, Finset.sum_add_distrib, E, J, inner_add_left, sum_inner]
    simp_rw [inner_apply_eq_star_inner]
    ring
  have hzero : (∫ x in Metric.ball a r,
      (∑ i : Fin n, inner ℝ (Du x i)
        (R (Dp x i) (ψ x) + R (p x) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))) +
          inner ℝ (F x) (R (p x) (ψ x))) = 0 := by
    have hAint : IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (Du x i)
        (R (Dp x i) (ψ x) + R (p x) (fderiv ℝ ψ x (EuclideanSpace.single i 1))))
        (Metric.ball a r) volume := H.1
    have hBint : IntegrableOn (fun x => inner ℝ (F x) (R (p x) (ψ x)))
        (Metric.ball a r) volume := H.2.1
    have heq : (∫ x in Metric.ball a r, ∑ i : Fin n, inner ℝ (Du x i)
        (R (Dp x i) (ψ x) + R (p x) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))) =
        -(∫ x in Metric.ball a r, inner ℝ (F x) (R (p x) (ψ x))) := H.2.2
    rw [integral_add hAint hBint, heq]
    ring
  have hsumzero : (∫ x in Metric.ball a r,
      (∑ i : Fin n, inner ℝ (E x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) +
        inner ℝ (J x) (ψ x)) = 0 :=
    (integral_congr_ae (Eventually.of_forall hpoint)).symm.trans hzero
  rw [integral_add hLI.integrableOn hJI.integrableOn] at hsumzero
  have hlocal : (∫ x in Metric.ball a r, ∑ i : Fin n,
      inner ℝ (E x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      -(∫ x in Metric.ball a r, inner ℝ (J x) (ψ x)) :=
    eq_neg_iff_add_eq_zero.mpr hsumzero
  have hzL (x : Domain n) (hx : x ∉ Metric.ball a r) :
      (∑ i : Fin n, inner ℝ (E x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) = 0 := by
    have hnot : x ∉ tsupport ψ := fun h => hx (hsψ h)
    simp only [fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot, zero_apply,
      inner_zero_right, Finset.sum_const_zero]
  have hzJ (x : Domain n) (hx : x ∉ Metric.ball a r) : inner ℝ (J x) (ψ x) = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsψ h)), inner_zero_right]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzL,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzJ] at hlocal
  exact hlocal

/-- Bounded Sobolev operator fields transform the actual weak equation on every open domain. -/
theorem weak_operator_flux_transform {n m q : ℕ} {Ω : OpenDomain n}
    {p : Domain n → Ambient m} {Dp : Domain n → Gradient n m}
    (hp : MemW12Loc Ω p Dp) {M : ℝ}
    (hb : ∀ᵐ x ∂volume.restrict Ω.val, ‖p x‖ ≤ M)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {F : Domain n → Ambient q}
    (hP : HolderToCK.WeakPoissonOn Ω Du F) :
    LocallyIntegrableOn (fun x => star (R (p x)) (F x) +
      ∑ i : Fin n, star (R (Dp x i)) (Du x i)) Ω.val volume ∧
    ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Ω.val →
      IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (star (R (p x)) (Du x i))
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) Ω.val volume ∧
      IntegrableOn (fun x => inner ℝ (star (R (p x)) (F x) +
        ∑ i : Fin n, star (R (Dp x i)) (Du x i)) (ψ x)) Ω.val volume ∧
      (∫ x in Ω.val, ∑ i : Fin n, inner ℝ (star (R (p x)) (Du x i))
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
        -(∫ x in Ω.val, inner ℝ (star (R (p x)) (F x) +
          ∑ i : Fin n, star (R (Dp x i)) (Du x i)) (ψ x)) := by
  let E (x : Domain n) (i : Fin n) := star (R (p x)) (Du x i)
  let J (x : Domain n) := star (R (p x)) (F x) + ∑ i : Fin n, star (R (Dp x i)) (Du x i)
  have hEL := locallyMemL2_operator_flux hp hb R hu
  have hJL := locallyIntegrableOn_operator_flux_rhs hp hb R hu hP.1
  refine ⟨hJL, ?_⟩
  intro ψ hψ hcψ hsψ
  have hLI := integrable_locallyL2_vector_test E hEL ψ hψ hcψ hsψ
  have hJI := integrable_locallyL1_vector_test hJL ψ hψ.continuous hcψ hsψ
  obtain ⟨r, t, φ, hballs, hφ, hsum⟩ :=
    exists_finite_ball_smooth_test_localization Ω ψ hψ hcψ hsψ
  have hsφ (j : t) : tsupport (φ j) ⊆ Ω.val :=
    (hφ j).2.2.trans (Metric.ball_subset_closedBall.trans (hballs j.val).2)
  have hLIφ (j : t) := integrable_locallyL2_vector_test E hEL (φ j) (hφ j).1 (hφ j).2.1 (hsφ j)
  have hJIφ (j : t) := integrable_locallyL1_vector_test hJL (φ j) (hφ j).1.continuous
    (hφ j).2.1 (hsφ j)
  have hzero (j : t) := weak_operator_flux_transform_local hp hb R hu hP
    (hballs j.val).1 (hballs j.val).2 (φ j) (hφ j).1 (hφ j).2.1 (hφ j).2.2
  have hDsum (x : Domain n) : fderiv ℝ ψ x = ∑ j : t, fderiv ℝ (φ j) x := by
    have H := fderiv_sum (u := Finset.univ) (A := φ) (x := x)
      (fun j _ => ((hφ j).1.differentiable (by simp) x))
    exact (congrArg (fun f : Domain n → Ambient q => fderiv ℝ f x) hsum).symm.trans H
  have hleft (x : Domain n) :
      (∑ i : Fin n, inner ℝ (E x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      ∑ j : t, ∑ i : Fin n, inner ℝ (E x i) (fderiv ℝ (φ j) x (EuclideanSpace.single i 1)) := by
    simp only [hDsum, sum_apply, inner_sum]
    exact Finset.sum_comm
  have hright (x : Domain n) : inner ℝ (J x) (ψ x) = ∑ j : t, inner ℝ (J x) (φ j x) := by
    have H := congrFun hsum x
    simp only [Finset.sum_apply] at H
    rw [← H, inner_sum]
  have hwhole : (∫ x, ∑ i : Fin n, inner ℝ (E x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      -(∫ x, inner ℝ (J x) (ψ x)) := by
    calc
      _ = ∫ x, ∑ j : t, ∑ i : Fin n,
          inner ℝ (E x i) (fderiv ℝ (φ j) x (EuclideanSpace.single i 1)) :=
        integral_congr_ae (Eventually.of_forall hleft)
      _ = ∑ j : t, ∫ x, ∑ i : Fin n,
          inner ℝ (E x i) (fderiv ℝ (φ j) x (EuclideanSpace.single i 1)) :=
        integral_finsetSum _ (fun j _ => hLIφ j)
      _ = ∑ j : t, -(∫ x, inner ℝ (J x) (φ j x)) :=
        Finset.sum_congr rfl (fun j _ => hzero j)
      _ = -(∑ j : t, ∫ x, inner ℝ (J x) (φ j x)) :=
        Finset.sum_neg_distrib (fun j : t => ∫ x, inner ℝ (J x) (φ j x))
      _ = -(∫ x, ∑ j : t, inner ℝ (J x) (φ j x)) :=
        congrArg Neg.neg (integral_finsetSum _ (fun j _ => hJIφ j)).symm
      _ = _ := congrArg Neg.neg (integral_congr_ae
        (Eventually.of_forall fun x => (hright x).symm))
  refine ⟨hLI.integrableOn, hJI.integrableOn, ?_⟩
  have hzL (x : Domain n) (hx : x ∉ Ω.val) :
      (∑ i : Fin n, inner ℝ (E x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) = 0 := by
    have hnot : x ∉ tsupport ψ := fun h => hx (hsψ h)
    simp only [fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot, zero_apply,
      inner_zero_right, Finset.sum_const_zero]
  have hzJ (x : Domain n) (hx : x ∉ Ω.val) : inner ℝ (J x) (ψ x) = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsψ h)), inner_zero_right]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzL,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzJ]
  exact hwhole

end StationaryHarmonicMaps.Analysis

end

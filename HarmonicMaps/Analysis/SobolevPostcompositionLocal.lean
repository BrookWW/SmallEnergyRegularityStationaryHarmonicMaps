module

public import HarmonicMaps.Analysis.SobolevPostcomposition
import HarmonicMaps.SobolevRestriction
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Weak target chain rule on arbitrary open domains

The finite-ball chain rule gives local distributional identities. A finite
smooth partition of unity on each compact test support combines those
identities on the original open domain. L2 and integrability conditions are
established on compact subsets, so the domain need not have finite volume.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff Manifold

namespace HarmonicMaps

private theorem postcomposition_pairing_integrable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : OpenDomain n} {f : Domain n → E} {φ : Domain n → ℝ}
    (hf : LocallyIntegrableOn f Ω.val volume) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω.val) :
    Integrable (fun x => φ x • f x) volume := by
  have hfK : IntegrableOn f (tsupport φ) volume := hf.integrableOn_compact_subset hs hc
  have hφK := hφ.memLp_top_of_hasCompactSupport hc (volume.restrict (tsupport φ))
  have hpair := hfK.smul_of_top_right hφK
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hpair
  intro x hx
  by_contra hnot
  have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport hnot
  change φ x • f x ≠ 0 at hx
  exact hx (by rw [hz, zero_smul])

private theorem postcomposition_setIntegral_eq_integral {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set (Domain n)} {φ : Domain n → ℝ} (f : Domain n → E)
    (hs : tsupport φ ⊆ s) :
    (∫ x in s, φ x • f x) = ∫ x, φ x • f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
  simp only [hz, zero_smul]

/-- Smooth target maps with globally bounded derivative preserve the literal
local Sobolev predicate on every open domain. -/
theorem MemW12Loc.postcompose {n q k : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (F : Ambient q → Ambient k) (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) :
    MemW12Loc Ω (F ∘ u) (fun x i => fderiv ℝ F (u x) (Du x i)) := by
  classical
  let v := F ∘ u
  let Dv : Domain n → Gradient n k := fun x i => fderiv ℝ F (u x) (Du x i)
  have hvL : LocallyMemL2 Ω v := by
    intro K hK hs
    letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    exact memLp_postcomposition (hu.2.1 K hK hs) hF hDF
  have hDvL (i : Fin n) : LocallyMemL2 Ω (fun x => Dv x i) := by
    intro K hK hs
    exact memLp_postcomposition_column (hu.2.1 K hK hs).aestronglyMeasurable
      (hu.2.2 i K hK hs) hF hDF
  have hvI : LocallyIntegrableOn v Ω.val volume := by
    apply (locallyIntegrableOn_iff Ω.property.isLocallyClosed).mpr
    intro K hs hK
    letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    exact (hvL K hK hs).integrable (by norm_num)
  have hDvI (i : Fin n) : LocallyIntegrableOn (fun x => Dv x i) Ω.val volume := by
    apply (locallyIntegrableOn_iff Ω.property.isLocallyClosed).mpr
    intro K hs hK
    letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    exact (hDvL i K hK hs).integrable (by norm_num)
  refine ⟨⟨hvI, hDvI, ?_⟩, hvL, hDvL⟩
  intro i φ hφ hcφ hsφ
  have hballs (x : tsupport φ) : ∃ r : ℝ, 0 < r ∧ Metric.closedBall x.val r ⊆ Ω.val := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Ω.property x.val (hsφ x.property)
    exact ⟨ε / 2, by positivity,
      (Metric.closedBall_subset_ball (by linarith only [hε])).trans hball⟩
  choose r hr hclosed using hballs
  obtain ⟨t, ht⟩ := hcφ.elim_finite_subcover
    (fun x : tsupport φ => Metric.ball x.val (r x)) (fun _ => Metric.isOpen_ball)
    (fun x hx => mem_iUnion_of_mem ⟨x, hx⟩ (Metric.mem_ball_self (hr ⟨x, hx⟩)))
  let U : t → Set (Domain n) := fun j => Metric.ball j.val.val (r j.val)
  have hcover : tsupport φ ⊆ ⋃ j : t, U j := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion_of_mem ⟨j, hj⟩ hxj
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, Domain n) (isClosed_tsupport φ) U (fun _ => Metric.isOpen_ball) hcover
  let ψ : t → Domain n → ℝ := fun j x => φ x * ρ j x
  have hψ (j : t) : ContDiff ℝ ∞ (ψ j) := hφ.mul (ρ j).contMDiff.contDiff
  have hcψ (j : t) : HasCompactSupport (ψ j) := hcφ.mul_right
  have hsψ (j : t) : tsupport (ψ j) ⊆ U j := tsupport_mul_subset_right.trans (hρ j)
  have hsψΩ (j : t) : tsupport (ψ j) ⊆ Ω.val :=
    (hsψ j).trans (Metric.ball_subset_closedBall.trans (hclosed j.val))
  have hsum : (∑ j : t, ψ j) = φ := by
    funext x
    simp only [Finset.sum_apply, ψ]
    rw [← Finset.mul_sum]
    by_cases hx : x ∈ tsupport φ
    · have H := ρ.sum_eq_one hx
      rw [finsum_eq_sum_of_fintype] at H
      rw [H, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hDsum (x : Domain n) :
      (∑ j : t, coordinateDerivative (ψ j) (hψ j) i x) = coordinateDerivative φ hφ i x := by
    have H := fderiv_sum (u := Finset.univ) (A := ψ) (x := x)
      (fun j _ => (hψ j).differentiable (by simp) x)
    rw [hsum] at H
    simp only [coordinateDerivative, H, sum_apply]
  have hidentity (j : t) :
      (∫ x, coordinateDerivative (ψ j) (hψ j) i x • v x) =
        -(∫ x, ψ j x • Dv x i) := by
    have hw := (hu.memW12_ball (hclosed j.val)).postcompose (hr j.val) F hF L hDF
    have H := hw.1.2.2 i (ψ j) (hψ j) (hcψ j) (hsψ j)
    change (∫ x in U j, coordinateDerivative (ψ j) (hψ j) i x • v x) =
      -(∫ x in U j, ψ j x • Dv x i) at H
    rw [postcomposition_setIntegral_eq_integral (φ := coordinateDerivative (ψ j) (hψ j) i) v
      ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans (hsψ j)),
      postcomposition_setIntegral_eq_integral (fun x => Dv x i) (hsψ j)] at H
    exact H
  have hleft (j : t) : Integrable
      (fun x => coordinateDerivative (ψ j) (hψ j) i x • v x) volume :=
    postcomposition_pairing_integrable hvI
      ((hψ j).continuous_fderiv (by simp) |>.clm_apply continuous_const)
      ((hcψ j).fderiv_apply ℝ (EuclideanSpace.single i 1))
      ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans (hsψΩ j))
  have hright (j : t) : Integrable (fun x => ψ j x • Dv x i) volume :=
    postcomposition_pairing_integrable (hDvI i) (hψ j).continuous (hcψ j) (hsψΩ j)
  change (∫ x in Ω.val, coordinateDerivative φ hφ i x • v x) =
    -(∫ x in Ω.val, φ x • Dv x i)
  rw [postcomposition_setIntegral_eq_integral (φ := coordinateDerivative φ hφ i) v
    ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsφ),
    postcomposition_setIntegral_eq_integral (fun x => Dv x i) hsφ]
  calc
    (∫ x, coordinateDerivative φ hφ i x • v x) =
        ∫ x, ∑ j : t, coordinateDerivative (ψ j) (hψ j) i x • v x := by
      congr 1
      funext x
      rw [← Finset.sum_smul, hDsum x]
    _ = ∑ j : t, ∫ x, coordinateDerivative (ψ j) (hψ j) i x • v x :=
      integral_finsetSum _ (fun j _ => hleft j)
    _ = ∑ j : t, -(∫ x, ψ j x • Dv x i) := Finset.sum_congr rfl (fun j _ => hidentity j)
    _ = -(∫ x, ∑ j : t, ψ j x • Dv x i) := by
      rw [Finset.sum_neg_distrib, integral_finsetSum _ (fun j _ => hright j)]
    _ = -(∫ x, φ x • Dv x i) := by
      congr 1
      congr 1
      funext x
      rw [← Finset.sum_smul]
      have H := congrFun hsum x
      simpa only [Finset.sum_apply] using congrArg (fun c : ℝ => c • Dv x i) H

end HarmonicMaps

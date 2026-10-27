module

public import HarmonicMaps.Geometry.TargetChartGram

/-!
# Smooth local normal families

The actual inclusion differential determines the normal space at the base
point. The inverse Gram family transports this space smoothly to the normal
spaces in one target chart. The tangent and transported normal sum is genuinely
invertible on a smaller open chart neighborhood.
-/

public section

open Filter Topology
open scoped Manifold ContDiff

namespace HarmonicMaps.CompactSmoothEmbeddedTarget

set_option backward.isDefEq.respectTransparency false in
/-- Actual target geometry produces a smooth local family of full normal-space parametrizations. -/
theorem exists_smooth_normal_family {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (p : N.Carrier) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) p
    let a := e p
    let gamma : EuclideanSpace ℝ (Fin N.dimension) → EuclideanSpace ℝ (Fin q) :=
      Subtype.val ∘ e.symm
    let A := fun t => fderiv ℝ gamma t
    let A0 : EuclideanSpace ℝ (Fin N.dimension) →L[ℝ] EuclideanSpace ℝ (Fin q) :=
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
        𝓘(ℝ, EuclideanSpace ℝ (Fin q))
        (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) p
    let K := A0.rangeᗮ
    ∃ V : Set (EuclideanSpace ℝ (Fin N.dimension)),
      IsOpen V ∧ a ∈ V ∧ V ⊆ e.target ∧
      ContDiffOn ℝ ∞ gamma V ∧
      ∃ L : EuclideanSpace ℝ (Fin N.dimension) → (K →L[ℝ] EuclideanSpace ℝ (Fin q)),
        ContDiffOn ℝ ∞ L V ∧ L a = K.subtypeL ∧
        ∀ t ∈ V,
          Function.Injective (A t) ∧ Function.Injective (L t) ∧
          (L t).range = (A t).rangeᗮ ∧ ((A t).coprod (L t)).IsInvertible := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin q))
  let e := extChartAt I p
  let a := e p
  let gamma : EuclideanSpace ℝ (Fin N.dimension) → EuclideanSpace ℝ (Fin q) :=
    Subtype.val ∘ e.symm
  let A := fun t => fderiv ℝ gamma t
  let G := fun t => (A t).adjoint.comp (A t)
  let A0 : EuclideanSpace ℝ (Fin N.dimension) →L[ℝ] EuclideanSpace ℝ (Fin q) :=
    mfderiv I J (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) p
  let K := A0.rangeᗮ
  obtain ⟨W, hWo, haW, hWe, hgamma, hA, hG, hGi, _⟩ :=
    N.exists_smooth_chart_gram_inverse p
  have hAa : A a = A0 := by
    have hi : MDifferentiableAt I J
        (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) p :=
      N.isSmoothEmbedding.contMDiff.mdifferentiableAt (by simp)
    have hg : HasFDerivAt gamma A0 a := by
      simpa only [I, J, gamma, A0, a, e, writtenInExtChartAt, mfld_simps,
        hasFDerivWithinAt_univ, Function.comp_def] using hi.hasMFDerivAt.2
    exact hg.fderiv
  let B := fun t => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin q)) -
    (A t).comp ((G t).inverse.comp (A t).adjoint)
  let L : EuclideanSpace ℝ (Fin N.dimension) → (K →L[ℝ] EuclideanSpace ℝ (Fin q)) :=
    fun t => (B t).comp K.subtypeL
  have hAd : ContDiffOn ℝ ∞ A W := hgamma.fderiv_of_isOpen hWo (by simp)
  have hAdj : ContDiffOn ℝ ∞ (fun t => (A t).adjoint) W :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin N.dimension))
      (F := EuclideanSpace ℝ (Fin q))).contDiff.comp_contDiffOn hAd
  have hLd : ContDiffOn ℝ ∞ L W :=
    (contDiffOn_const.sub (hAd.clm_comp (hGi.clm_comp hAdj))).clm_comp contDiffOn_const
  have hnormal : ∀ t ∈ W, (A t).adjoint.comp (L t) = 0 := by
    intro t ht
    ext w : 1
    change (A t).adjoint
      (w.val - A t ((G t).inverse ((A t).adjoint w.val))) = 0
    rw [map_sub]
    change (A t).adjoint w.val - G t ((G t).inverse ((A t).adjoint w.val)) = 0
    rw [(hG t ht).self_apply_inverse, sub_self]
  have hLa : L a = K.subtypeL := by
    ext w : 1
    have hw : A0.adjoint w.val = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← A0.orthogonal_range]
      exact w.property
    change w.val - A a ((G a).inverse ((A a).adjoint w.val)) = w.val
    rw [hAa, hw, map_zero, map_zero, sub_zero]
  let S := fun t => (A t).coprod (L t)
  obtain ⟨e0, he0⟩ :
      ∃ e0 : (EuclideanSpace ℝ (Fin N.dimension) × K) ≃L[ℝ]
        EuclideanSpace ℝ (Fin q),
        ∀ (v : EuclideanSpace ℝ (Fin N.dimension)) (w : K),
          e0 (v, w) = A0 v + w.val := N.exists_tangent_normal_equiv p
  have hSa : S a = (e0 : (EuclideanSpace ℝ (Fin N.dimension) × K) →L[ℝ]
      EuclideanSpace ℝ (Fin q)) := by
    apply ContinuousLinearMap.ext
    intro x
    change A a x.1 + L a x.2 = e0 x
    rw [hAa, hLa]
    exact (he0 x.1 x.2).symm
  have hSc : ContinuousOn S W :=
    hAd.continuousOn.continuousLinearMapCoprod hLd.continuousOn
  let H := fun t => e0.symm.toContinuousLinearMap.comp (S t)
  have hHc : ContinuousOn H W := continuousOn_const.clm_comp hSc
  have hHa : H a = 1 := by
    dsimp only [H]
    rw [hSa]
    apply ContinuousLinearMap.ext
    intro x
    exact e0.symm_apply_apply x
  have hHu : IsUnit (H a) := by rw [hHa]; exact isUnit_one
  have hUnits : {T : (EuclideanSpace ℝ (Fin N.dimension) × K) →L[ℝ]
      (EuclideanSpace ℝ (Fin N.dimension) × K) | IsUnit T} ∈ 𝓝 (H a) :=
    (Units.isOpen (R := (EuclideanSpace ℝ (Fin N.dimension) × K) →L[ℝ]
      (EuclideanSpace ℝ (Fin N.dimension) × K))).mem_nhds hHu
  have hHnhds : {t | IsUnit (H t)} ∈ 𝓝 a :=
    (hHc.continuousAt (hWo.mem_nhds haW)).preimage_mem_nhds hUnits
  obtain ⟨O, hOH, hOo, haO⟩ := mem_nhds_iff.mp hHnhds
  let V := W ∩ O
  have hVinv : ∀ t ∈ V, (S t).IsInvertible := by
    intro t ht
    obtain ⟨u, hu⟩ := hOH ht.2
    have hHinv : (H t).IsInvertible := by
      rw [← hu]
      exact ⟨ContinuousLinearEquiv.ofUnit u, rfl⟩
    have hSinv := (ContinuousLinearMap.isInvertible_equiv
      (f := e0)).comp hHinv
    have hEq : e0.toContinuousLinearMap.comp (H t) = S t := by
      apply ContinuousLinearMap.ext
      intro x
      change e0 (e0.symm (S t x)) = S t x
      exact e0.apply_symm_apply _
    exact hEq ▸ hSinv
  refine ⟨V, hWo.inter hOo, ⟨haW, haO⟩, fun t ht => hWe ht.1,
    hgamma.mono Set.inter_subset_left, L, hLd.mono Set.inter_subset_left, hLa, ?_⟩
  intro t ht
  have hSj := (hVinv t ht).injective
  have hLj : Function.Injective (L t) := by
    intro v w hvw
    have heq : S t (0, v) = S t (0, w) := by
      change A t 0 + L t v = A t 0 + L t w
      rw [hvw]
    exact congrArg Prod.snd (hSj heq)
  have hLrange : (L t).range ≤ (A t).rangeᗮ := by
    intro z hz
    obtain ⟨w, rfl⟩ := hz
    rw [(A t).orthogonal_range]
    apply LinearMap.mem_ker.mpr
    exact congrArg (fun T => T w) (hnormal t ht.1)
  have hRange : (L t).range = (A t).rangeᗮ := by
    apply le_antisymm hLrange
    intro z hz
    obtain ⟨⟨v, w⟩, heq⟩ := (hVinv t ht).surjective z
    have hAv : A t v ∈ (A t).rangeᗮ := by
      have hLw : L t w ∈ (A t).rangeᗮ := hLrange ⟨w, rfl⟩
      have hEq : A t v = z - L t w := by
        change A t v + L t w = z at heq
        exact eq_sub_of_add_eq heq
      rw [hEq]
      exact Submodule.sub_mem _ hz hLw
    have hzero : A t v = 0 :=
      (Submodule.disjoint_def.mp (A t).range.orthogonal_disjoint) (A t v) ⟨v, rfl⟩ hAv
    refine ⟨w, ?_⟩
    change A t v + L t w = z at heq
    simpa only [ContinuousLinearMap.coe_coe, hzero, zero_add] using heq
  exact ⟨hA t ht.1, hLj, hRange, hVinv t ht⟩

end HarmonicMaps.CompactSmoothEmbeddedTarget

end

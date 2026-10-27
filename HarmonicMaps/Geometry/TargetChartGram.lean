module

public import HarmonicMaps.Geometry.TargetTangentNormal
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth Gram inverses in actual target charts

The literal chart parametrization has an injective derivative on its open
chart domain. Its Gram operator is invertible there, and the same inverse
family is smooth and satisfies both inverse identities on that domain.
-/

public section

open scoped Manifold ContDiff

namespace HarmonicMaps.CompactSmoothEmbeddedTarget

/-- A genuine target chart has smooth invertible Gram operators and smooth actual inverses. -/
theorem exists_smooth_chart_gram_inverse {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (p : N.Carrier) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) p
    let a := e p
    let gamma : EuclideanSpace ℝ (Fin N.dimension) → EuclideanSpace ℝ (Fin q) :=
      Subtype.val ∘ e.symm
    let A := fun t => fderiv ℝ gamma t
    let G := fun t => (A t).adjoint.comp (A t)
    ∃ V : Set (EuclideanSpace ℝ (Fin N.dimension)),
      IsOpen V ∧ a ∈ V ∧ V ⊆ e.target ∧
      ContDiffOn ℝ ∞ gamma V ∧
      (∀ t ∈ V, Function.Injective (A t)) ∧
      (∀ t ∈ V, (G t).IsInvertible) ∧
      ContDiffOn ℝ ∞ (fun t => (G t).inverse) V ∧
      ∀ t ∈ V,
        (G t).inverse.comp (G t) = ContinuousLinearMap.id ℝ _ ∧
        (G t).comp (G t).inverse = ContinuousLinearMap.id ℝ _ := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin q))
  let e := extChartAt I p
  let a := e p
  let gamma : EuclideanSpace ℝ (Fin N.dimension) → EuclideanSpace ℝ (Fin q) :=
    Subtype.val ∘ e.symm
  let A := fun t => fderiv ℝ gamma t
  let G := fun t => (A t).adjoint.comp (A t)
  let phi := chartAt (EuclideanSpace ℝ (Fin N.dimension)) p
  have he : e.target = phi.target := by simp only [e, I, phi, mfld_simps]
  have hgamma : gamma = Subtype.val ∘ phi.symm := by
    simp only [gamma, e, I, phi, mfld_simps]
  have hOpen : IsOpen e.target := by rw [he]; exact phi.open_target
  have ha : a ∈ e.target := mem_extChartAt_target p
  have hg : ContDiffOn ℝ ∞ gamma e.target := by
    rw [he, hgamma]
    exact (N.isSmoothEmbedding.contMDiff.comp_contMDiffOn
      (contMDiffOn_chart_symm (I := I) (x := p))).contDiffOn
  have hd : phi.MDifferentiable I I := mdifferentiable_chart p
  have hA : ∀ t ∈ e.target, Function.Injective (A t) := by
    intro t ht
    have hphi : t ∈ phi.target := he ▸ ht
    have hi : MDifferentiableAt I J
        (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) (phi.symm t) :=
      N.isSmoothEmbedding.contMDiff.mdifferentiableAt (by simp)
    change Function.Injective (fderiv ℝ gamma t)
    rw [hgamma, ← mfderiv_eq_fderiv,
      mfderiv_comp t hi (hd.mdifferentiableAt_symm hphi)]
    exact (N.embedding_mfderiv_injective (phi.symm t)).comp
      (hd.symm.mfderiv_injective hphi)
  have hG : ∀ t ∈ e.target, (G t).IsInvertible := by
    intro t ht
    have hGj : Function.Injective (G t) :=
      (A t).adjoint_comp_self_injective_iff.mpr (hA t ht)
    have hker : (G t).ker = ⊥ := LinearMap.ker_eq_bot.mpr hGj
    have hrange : (G t).range = ⊤ :=
      LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hGj)
    exact ⟨ContinuousLinearEquiv.ofBijective (G t) hker hrange,
      ContinuousLinearEquiv.coe_ofBijective (G t) hker hrange⟩
  have hAd : ContDiffOn ℝ ∞ A e.target :=
    hg.fderiv_of_isOpen hOpen (by simp)
  have hAdj : ContDiff ℝ ∞
      (fun B : EuclideanSpace ℝ (Fin N.dimension) →L[ℝ] EuclideanSpace ℝ (Fin q) =>
        B.adjoint) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin N.dimension))
      (F := EuclideanSpace ℝ (Fin q))).contDiff
  have hGd : ContDiffOn ℝ ∞ G e.target :=
    (hAdj.comp_contDiffOn hAd).clm_comp hAd
  have hGinv : ContDiffOn ℝ ∞ (fun t => (G t).inverse) e.target := by
    intro t ht
    exact (hG t ht).contDiffAt_map_inverse.comp_contDiffWithinAt t (hGd t ht)
  refine ⟨e.target, hOpen, ha, Set.Subset.rfl, hg, hA, hG, hGinv, ?_⟩
  intro t ht
  exact ⟨(hG t ht).inverse_comp_self, (hG t ht).self_comp_inverse⟩

end HarmonicMaps.CompactSmoothEmbeddedTarget

end

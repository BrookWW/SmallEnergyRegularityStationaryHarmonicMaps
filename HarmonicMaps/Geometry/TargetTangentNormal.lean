module

public import HarmonicMaps.Geometry.TargetNearestNormal
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The pointwise tangent and normal linear decomposition

The actual immersion chart presentation makes the inclusion differential
injective. Its range and the orthogonal complement therefore give an invertible
linear sum map at each target point. This is a pointwise linear statement; it
does not assert the existence of a smooth moving normal coordinate map.
-/

public section

open Filter Topology
open scoped Manifold ContDiff

namespace HarmonicMaps.CompactSmoothEmbeddedTarget

/-- The differential of the literal target inclusion is injective. -/
theorem embedding_mfderiv_injective {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (p : N.Carrier) :
    Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
        𝓘(ℝ, EuclideanSpace ℝ (Fin q))
        (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) p) := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin q))
  let h := N.isSmoothEmbedding.isImmersion.isImmersionOfComplement_complement p
  let F := N.isSmoothEmbedding.isImmersion.complement
  let L : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin N.dimension) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin N.dimension)) F).comp
      h.equiv.symm.toContinuousLinearMap
  let r : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin N.dimension) :=
    L ∘ h.codChart
  have hd : h.domChart.MDifferentiable I I :=
    ⟨(contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
        (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
        (by simp)⟩
  have hc : MDifferentiableAt J J h.codChart p.val :=
    (contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
      h.mem_codChart_source).mdifferentiableAt (by simp)
  have hr : MDifferentiableAt J I r p.val :=
    ((L.contMDiff (n := ∞)).mdifferentiableAt (by simp)).comp p.val hc
  have hi : MDifferentiableAt I J
      (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) p :=
    N.isSmoothEmbedding.contMDiff.mdifferentiableAt (by simp)
  have heq : (r ∘ (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)))
      =ᶠ[𝓝 p] h.domChart := by
    filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with x hx
    have hy : (h.domChart.extend I) x ∈ (h.domChart.extend I).target :=
      (h.domChart.extend I).map_source
        (by simpa only [OpenPartialHomeomorph.extend_source] using hx)
    have hw : h.codChart x.val = h.equiv (h.domChart x, 0) := by
      simpa only [I, J, mfld_simps, hx] using h.writtenInCharts hy
    change L (h.codChart x.val) = h.domChart x
    rw [hw]
    change (h.equiv.symm (h.equiv (h.domChart x, 0))).1 = h.domChart x
    rw [h.equiv.symm_apply_apply]
  have hderiv :
      (mfderiv J I r p.val).comp
          (mfderiv I J (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) p) =
        mfderiv I I h.domChart p :=
    (mfderiv_comp p hr hi).symm.trans heq.mfderiv_eq
  intro v w hvw
  apply hd.mfderiv_injective h.mem_domChart_source
  rw [← hderiv]
  exact congrArg (mfderiv J I r p.val) hvw

/-- The actual tangent differential and its orthogonal normal space form a linear equivalence. -/
theorem exists_tangent_normal_equiv {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (p : N.Carrier) :
    let A : EuclideanSpace ℝ (Fin N.dimension) →L[ℝ] EuclideanSpace ℝ (Fin q) :=
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
        𝓘(ℝ, EuclideanSpace ℝ (Fin q))
        (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) p
    ∃ e : (EuclideanSpace ℝ (Fin N.dimension) × ↥(A.rangeᗮ))
        ≃L[ℝ] EuclideanSpace ℝ (Fin q),
      ∀ (v : EuclideanSpace ℝ (Fin N.dimension)) (w : A.rangeᗮ),
        e (v, w) = A v + w.val := by
  let A : EuclideanSpace ℝ (Fin N.dimension) →L[ℝ] EuclideanSpace ℝ (Fin q) :=
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
      𝓘(ℝ, EuclideanSpace ℝ (Fin q))
      (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) p
  have hker : A.ker = ⊥ := LinearMap.ker_eq_bot.mpr (N.embedding_mfderiv_injective p)
  refine ⟨A.coprodSubtypeLEquivOfIsCompl A.range.isCompl_orthogonal hker, ?_⟩
  intro v w
  rfl

end HarmonicMaps.CompactSmoothEmbeddedTarget

end

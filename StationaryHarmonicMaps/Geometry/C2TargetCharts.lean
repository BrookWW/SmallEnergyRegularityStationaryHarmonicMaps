module

public import StationaryHarmonicMaps.Foundation.TangentImage
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Actual charts of compact C² embedded targets

The inclusion differential is injective. In each actual target chart the
ambient parametrization is C², its derivative is C¹ and injective, and its
range is the ambient tangent subspace at the parametrized point.
-/

public section

open Filter Topology
open scoped Manifold ContDiff

namespace StationaryHarmonicMaps.CompactC2EmbeddedTarget

/-- The actual C² embedded inclusion has an injective differential. -/
theorem embedding_mfderiv_injective {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) :
    Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
        𝓘(ℝ, EuclideanSpace ℝ (Fin q)) N.embedding p) := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin q))
  let h := N.isC2Embedding.isImmersion.isImmersionOfComplement_complement p
  let F := N.isC2Embedding.isImmersion.complement
  let L : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin N.dimension) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin N.dimension)) F).comp
      h.equiv.symm.toContinuousLinearMap
  let r : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin N.dimension) :=
    L ∘ h.codChart
  have hd : h.domChart.MDifferentiable I I :=
    ⟨(contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
        two_ne_zero,
      (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
        two_ne_zero⟩
  have hc : MDifferentiableAt J J h.codChart p.val :=
    (contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
      h.mem_codChart_source).mdifferentiableAt two_ne_zero
  have hr : MDifferentiableAt J I r p.val :=
    ((L.contMDiff (n := 2)).mdifferentiableAt two_ne_zero).comp p.val hc
  have hi : MDifferentiableAt I J N.embedding p := N.embedding_mdifferentiable p
  have heq : r ∘ N.embedding =ᶠ[𝓝 p] h.domChart := by
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
      (mfderiv J I r p.val).comp (mfderiv I J N.embedding p) =
        mfderiv I I h.domChart p :=
    (mfderiv_comp p hr hi).symm.trans heq.mfderiv_eq
  intro v w hvw
  apply hd.mfderiv_injective h.mem_domChart_source
  rw [← hderiv]
  exact congrArg (mfderiv J I r p.val) hvw

/-- The ambient parametrization of each actual chart is C² on its open target. -/
theorem chart_parametrization_contDiff {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) p
    ContDiffOn ℝ 2 (N.embedding ∘ e.symm) e.target := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let e := extChartAt I p
  let phi := chartAt (EuclideanSpace ℝ (Fin N.dimension)) p
  have he : e.target = phi.target := by simp only [e, I, phi, mfld_simps]
  have hgamma : N.embedding ∘ e.symm = N.embedding ∘ phi.symm := by
    simp only [e, I, phi, mfld_simps]
  change ContDiffOn ℝ 2 (N.embedding ∘ e.symm) e.target
  rw [he, hgamma]
  exact (N.isC2Embedding.contMDiff.comp_contMDiffOn
    (contMDiffOn_chart_symm (I := I) (x := p))).contDiffOn

/-- The derivative family of a C² target chart is C¹. -/
theorem chart_parametrization_fderiv_contDiff {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) p
    ContDiffOn ℝ 1 (fderiv ℝ (N.embedding ∘ e.symm)) e.target := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let e := extChartAt I p
  have hOpen : IsOpen e.target := by
    simp only [e, I, mfld_simps]
    exact (chartAt (EuclideanSpace ℝ (Fin N.dimension)) p).open_target
  exact (N.chart_parametrization_contDiff p).fderiv_of_isOpen hOpen (by norm_num)

/-- Each actual chart parametrization has an injective derivative on its chart domain. -/
theorem chart_parametrization_fderiv_injective {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) p
    ∀ t ∈ e.target, Function.Injective (fderiv ℝ (N.embedding ∘ e.symm) t) := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin q))
  let e := extChartAt I p
  let phi := chartAt (EuclideanSpace ℝ (Fin N.dimension)) p
  have he : e.target = phi.target := by simp only [e, I, phi, mfld_simps]
  have hgamma : N.embedding ∘ e.symm = N.embedding ∘ phi.symm := by
    simp only [e, I, phi, mfld_simps]
  have hd : phi.MDifferentiable I I := mdifferentiable_chart p
  change ∀ t ∈ e.target, Function.Injective (fderiv ℝ (N.embedding ∘ e.symm) t)
  intro t ht
  have hphi : t ∈ phi.target := he ▸ ht
  have hi : MDifferentiableAt I J N.embedding (phi.symm t) :=
    N.embedding_mdifferentiable (phi.symm t)
  change Function.Injective (fderiv ℝ (N.embedding ∘ e.symm) t)
  rw [hgamma, ← mfderiv_eq_fderiv,
    mfderiv_comp t hi (hd.mdifferentiableAt_symm hphi)]
  exact (N.embedding_mfderiv_injective (phi.symm t)).comp
    (hd.symm.mfderiv_injective hphi)

/-- The derivative range in an actual chart is the source ambient tangent subspace. -/
theorem chart_parametrization_tangentImage {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) p
    ∀ t ∈ e.target,
      N.tangentImage (e.symm t) = (fderiv ℝ (N.embedding ∘ e.symm) t).range := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin q))
  let e := extChartAt I p
  let phi := chartAt (EuclideanSpace ℝ (Fin N.dimension)) p
  have he : e.target = phi.target := by simp only [e, I, phi, mfld_simps]
  have hesymm : (e.symm : EuclideanSpace ℝ (Fin N.dimension) → N.Carrier) =
      phi.symm := by simp only [e, I, phi, mfld_simps]
  have hd : phi.MDifferentiable I I := mdifferentiable_chart p
  change ∀ t ∈ e.target,
    N.tangentImage (e.symm t) = (fderiv ℝ (N.embedding ∘ e.symm) t).range
  intro t ht
  have hphi : t ∈ phi.target := he ▸ ht
  have hi : MDifferentiableAt I J N.embedding (phi.symm t) :=
    N.embedding_mdifferentiable (phi.symm t)
  change N.tangentImage (e.symm t) = (fderiv ℝ (N.embedding ∘ e.symm) t).range
  rw [hesymm, ← mfderiv_eq_fderiv,
    mfderiv_comp t hi (hd.mdifferentiableAt_symm hphi)]
  change (mfderiv I J N.embedding (phi.symm t)).range =
    ((mfderiv I J N.embedding (phi.symm t)).comp (mfderiv I I phi.symm t)).range
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨z, hz⟩ := hd.symm.mfderiv_surjective hphi v
    exact ⟨z, congrArg (mfderiv I J N.embedding (phi.symm t)) hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨mfderiv I I phi.symm t z, rfl⟩

end StationaryHarmonicMaps.CompactC2EmbeddedTarget

end

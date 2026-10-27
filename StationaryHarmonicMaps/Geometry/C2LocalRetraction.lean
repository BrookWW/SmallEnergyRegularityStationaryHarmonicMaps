module

public import StationaryHarmonicMaps.Geometry.C2TargetCharts
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Local C² retractions onto the actual target

The immersion normal form produces a C² map from an ambient neighborhood to
the target carrier. It fixes the target there. Composing with the actual
inclusion gives an ambient retraction whose derivative at a target point has
range in the ambient tangent subspace.
-/

public section

open Filter Set Topology
open scoped Manifold ContDiff

namespace StationaryHarmonicMaps.CompactC2EmbeddedTarget

/-- Each actual C² embedded target point has a local C² carrier-valued retraction. -/
theorem exists_local_c2_retraction_to_carrier {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) :
    ∃ (V : Set (EuclideanSpace ℝ (Fin q)))
      (ρ : EuclideanSpace ℝ (Fin q) → N.Carrier),
      IsOpen V ∧ p.val ∈ V ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin q))
        𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) 2 ρ V ∧
      ∀ y : N.Carrier, y.val ∈ V → ρ y.val = y := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin q))
  let h := N.isC2Embedding.isImmersion.isImmersionOfComplement_complement p
  let F := N.isC2Embedding.isImmersion.complement
  let L : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin N.dimension) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin N.dimension)) F).comp
      h.equiv.symm.toContinuousLinearMap
  let r : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin N.dimension) :=
    L ∘ h.codChart
  let ρ : EuclideanSpace ℝ (Fin q) → N.Carrier := h.domChart.symm ∘ r
  have hrN (y : N.Carrier) (hy : y ∈ h.domChart.source) :
      r y.val = h.domChart y := by
    have hz : (h.domChart.extend I) y ∈ (h.domChart.extend I).target :=
      (h.domChart.extend I).map_source
        (by simpa only [OpenPartialHomeomorph.extend_source] using hy)
    have hw : h.codChart y.val = h.equiv (h.domChart y, 0) := by
      simpa only [I, J, mfld_simps, hy] using h.writtenInCharts hz
    change L (h.codChart y.val) = h.domChart y
    rw [hw]
    change (h.equiv.symm (h.equiv (h.domChart y, 0))).1 = h.domChart y
    rw [h.equiv.symm_apply_apply]
  have hcod : ContDiffAt ℝ 2 h.codChart p.val :=
    (contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
      h.mem_codChart_source).contDiffAt
  have hr : ContDiffAt ℝ 2 r p.val :=
    ((L.contDiff (n := 2)).contDiffAt).comp p.val hcod
  have hchartInv : ContMDiffOn I I 2 h.domChart.symm h.domChart.target :=
    contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
  have hbase : h.domChart p ∈ h.domChart.target :=
    h.domChart.map_source h.mem_domChart_source
  have hinv : ContMDiffAt I I 2 h.domChart.symm (r p.val) := by
    rw [hrN p h.mem_domChart_source]
    exact hchartInv.contMDiffAt (h.domChart.open_target.mem_nhds hbase)
  have hρ : ContMDiffAt J I 2 ρ p.val := hinv.comp p.val hr.contMDiffAt
  obtain ⟨U, hU, hρU⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (by simp : (2 : ℕ∞ω) ≠ ∞)).mp hρ
  obtain ⟨V, hVU, hVo, hpV⟩ := mem_nhds_iff.mp hU
  obtain ⟨W, hWo, hWpre⟩ :=
    N.isC2Embedding.isEmbedding.isInducing.isOpen_iff.mp h.domChart.open_source
  have hpW : p.val ∈ W := by
    change p ∈ N.embedding ⁻¹' W
    rw [hWpre]
    exact h.mem_domChart_source
  refine ⟨V ∩ W, ρ, hVo.inter hWo, ⟨hpV, hpW⟩,
    hρU.mono (fun _ hy => hVU hy.1), ?_⟩
  intro y hy
  have hydom : y ∈ h.domChart.source := by
    rw [← hWpre]
    exact hy.2
  change h.domChart.symm (r y.val) = y
  rw [hrN y hydom, h.domChart.left_inv hydom]

/-- The actual ambient derivative of the local retraction takes values in the target tangent. -/
theorem exists_local_c2_ambient_retraction {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) :
    ∃ (V : Set (EuclideanSpace ℝ (Fin q)))
      (R : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin q)),
      IsOpen V ∧ p.val ∈ V ∧ ContDiffOn ℝ 2 R V ∧
      (∀ z, R z ∈ N.carrierSet) ∧
      (∀ y : N.Carrier, y.val ∈ V → R y.val = y.val) ∧
      ∀ y : N.Carrier, y.val ∈ V → ∀ v : EuclideanSpace ℝ (Fin q),
        fderiv ℝ R y.val v ∈ N.tangentImage y := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin q))
  obtain ⟨V, ρ, hVo, hpV, hρ, hfix⟩ := N.exists_local_c2_retraction_to_carrier p
  have hR : ContDiffOn ℝ 2 (N.embedding ∘ ρ) V :=
    (N.isC2Embedding.contMDiff.comp_contMDiffOn hρ).contDiffOn
  refine ⟨V, N.embedding ∘ ρ, hVo, hpV, hR, fun z => (ρ z).property,
    (fun y hy => congrArg N.embedding (hfix y hy)), ?_⟩
  intro y hy v
  have hρd : MDifferentiableAt J I ρ y.val :=
    (hρ.contMDiffAt (hVo.mem_nhds hy)).mdifferentiableAt two_ne_zero
  have hderiv : fderiv ℝ (N.embedding ∘ ρ) y.val =
      (mfderiv I J N.embedding y).comp (mfderiv J I ρ y.val) := by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp y.val (N.embedding_mdifferentiable (ρ y.val)) hρd, hfix y hy]
  change fderiv ℝ (N.embedding ∘ ρ) y.val v ∈ (mfderiv I J N.embedding y).range
  rw [hderiv]
  exact ⟨mfderiv J I ρ y.val v, rfl⟩

end StationaryHarmonicMaps.CompactC2EmbeddedTarget

end

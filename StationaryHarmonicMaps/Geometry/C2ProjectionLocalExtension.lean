module

public import StationaryHarmonicMaps.Geometry.C2NormalProjection
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Local ambient extensions of the C² target normal projection

The actual immersion normal form gives a local ambient coordinate retraction.
Composing it with the C¹ chart expression of the target projection gives a C¹
ambient extension near each target point. No canonical extension is selected.
-/

public section

open Filter Set Topology
open scoped Manifold ContDiff

namespace StationaryHarmonicMaps.CompactC2EmbeddedTarget

/-- Near each genuine target point, its normal projection has a C¹ ambient extension. -/
theorem exists_local_ambient_normal_projection_extension {q : ℕ}
    (N : CompactC2EmbeddedTarget q) (p : N.Carrier) :
    ∃ (V : Set (EuclideanSpace ℝ (Fin q)))
      (Qext : EuclideanSpace ℝ (Fin q) →
        EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q)),
      IsOpen V ∧ p.val ∈ V ∧ ContDiffOn ℝ 1 Qext V ∧
      ∀ y : N.Carrier, y.val ∈ V → Qext y.val = (N.tangentImage y)ᗮ.starProjection := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin q))
  let h := N.isC2Embedding.isImmersion.isImmersionOfComplement_complement p
  let F := N.isC2Embedding.isImmersion.complement
  let L : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin N.dimension) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin N.dimension)) F).comp
      h.equiv.symm.toContinuousLinearMap
  let r : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin N.dimension) :=
    L ∘ h.codChart
  let Q : N.Carrier → EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q) :=
    fun y => (N.tangentImage y)ᗮ.starProjection
  let Qext : EuclideanSpace ℝ (Fin q) →
      EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q) :=
    fun y => Q (h.domChart.symm (r y))
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
  have hr : ContDiffAt ℝ 1 r p.val :=
    (((L.contDiff (n := 2)).contDiffAt).comp p.val hcod).of_le one_le_two
  have hchartInv : ContMDiffOn I I 1 h.domChart.symm h.domChart.target :=
    (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).of_le one_le_two
  have hQchart : ContDiffOn ℝ 1 (Q ∘ h.domChart.symm) h.domChart.target :=
    (N.normal_projection_contMDiff.comp_contMDiffOn hchartInv).contDiffOn
  have hbase : h.domChart p ∈ h.domChart.target :=
    h.domChart.map_source h.mem_domChart_source
  have hQat : ContDiffAt ℝ 1 (Q ∘ h.domChart.symm) (r p.val) := by
    rw [hrN p h.mem_domChart_source]
    exact hQchart.contDiffAt (h.domChart.open_target.mem_nhds hbase)
  have hext : ContDiffAt ℝ 1 Qext p.val := hQat.comp p.val hr
  obtain ⟨U, hU, hextU⟩ := hext.contDiffOn le_rfl (by simp)
  obtain ⟨V, hVU, hVo, hpV⟩ := mem_nhds_iff.mp hU
  obtain ⟨W, hWo, hWpre⟩ :=
    N.isC2Embedding.isEmbedding.isInducing.isOpen_iff.mp h.domChart.open_source
  have hpW : p.val ∈ W := by
    change p ∈ N.embedding ⁻¹' W
    rw [hWpre]
    exact h.mem_domChart_source
  refine ⟨V ∩ W, Qext, hVo.inter hWo, ⟨hpV, hpW⟩,
    hextU.mono (fun _ hy => hVU hy.1), ?_⟩
  intro y hy
  have hydom : y ∈ h.domChart.source := by
    rw [← hWpre]
    exact hy.2
  change Q (h.domChart.symm (r y.val)) = Q y
  rw [hrN y hydom, h.domChart.left_inv hydom]

end StationaryHarmonicMaps.CompactC2EmbeddedTarget

end

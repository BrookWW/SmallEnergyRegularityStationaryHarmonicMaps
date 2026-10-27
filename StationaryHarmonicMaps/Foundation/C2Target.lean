module

public import HarmonicMaps.Target

/-!
# Compact C² embedded targets

The carrier is an actual compact Euclidean subset with a C² manifold structure
and C² embedded inclusion. Smooth targets retain their subset and charts under
the proved change of regularity.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace StationaryHarmonicMaps

/-- A nonempty compact embedded C² submanifold of Euclidean space, without boundary. -/
structure CompactC2EmbeddedTarget (q : ℕ) where
  dimension : ℕ
  carrierSet : Set (EuclideanSpace ℝ (Fin q))
  nonempty : carrierSet.Nonempty
  isCompact : IsCompact carrierSet
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin dimension)) carrierSet]
  [isManifold : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin dimension)) 2 carrierSet]
  isC2Embedding :
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, EuclideanSpace ℝ (Fin dimension)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) 2
      (Subtype.val : carrierSet → EuclideanSpace ℝ (Fin q))

namespace CompactC2EmbeddedTarget

variable {q : ℕ}

abbrev Carrier (N : CompactC2EmbeddedTarget q) : Type := N.carrierSet

instance instChartedSpace (N : CompactC2EmbeddedTarget q) :
    ChartedSpace (EuclideanSpace ℝ (Fin N.dimension)) N.Carrier := N.chartedSpace

instance instIsManifold (N : CompactC2EmbeddedTarget q) :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) 2 N.Carrier := N.isManifold

instance instNonempty (N : CompactC2EmbeddedTarget q) : Nonempty N.Carrier :=
  N.nonempty.to_subtype

instance instCompactSpace (N : CompactC2EmbeddedTarget q) : CompactSpace N.Carrier :=
  isCompact_iff_compactSpace.mp N.isCompact

abbrev embedding (N : CompactC2EmbeddedTarget q) :
    N.Carrier → EuclideanSpace ℝ (Fin q) := Subtype.val

theorem boundaryless (N : CompactC2EmbeddedTarget q) :
    BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) N.Carrier :=
  inferInstance

theorem isClosed (N : CompactC2EmbeddedTarget q) : IsClosed N.carrierSet :=
  N.isCompact.isClosed

@[simp] theorem range_embedding (N : CompactC2EmbeddedTarget q) :
    Set.range N.embedding = N.carrierSet := Subtype.range_val

theorem embedding_mem (N : CompactC2EmbeddedTarget q) (p : N.Carrier) :
    N.embedding p ∈ N.carrierSet := p.property

theorem embedding_mdifferentiable (N : CompactC2EmbeddedTarget q) :
    MDifferentiable
      𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q))
      N.embedding :=
  N.isC2Embedding.contMDiff.mdifferentiable two_ne_zero


end CompactC2EmbeddedTarget

namespace SmoothTarget

theorem isC2Embedding {q : ℕ} (N : HarmonicMaps.CompactSmoothEmbeddedTarget q) :
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) 2
      (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) := by
  refine ⟨?_, N.isSmoothEmbedding.isEmbedding⟩
  let hI := N.isSmoothEmbedding.isImmersion
  have hF : Manifold.IsImmersionOfComplement hI.complement
      𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) 2
      (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) := by
    intro p
    let h := hI.isImmersionOfComplement_complement p
    apply Manifold.IsImmersionAtOfComplement.mk_of_charts h.equiv h.domChart h.codChart
      h.mem_domChart_source h.mem_codChart_source
    · exact IsManifold.maximalAtlas_subset_of_le
        (show (2 : ℕ∞ω) ≤ ∞ from ENat.LEInfty.out) h.domChart_mem_maximalAtlas
    · exact IsManifold.maximalAtlas_subset_of_le
        (show (2 : ℕ∞ω) ≤ ∞ from ENat.LEInfty.out) h.codChart_mem_maximalAtlas
    · exact h.source_subset_preimage_source
    · exact h.writtenInCharts
  exact hF.isImmersion

/-- A smooth target retains exactly its actual subset and charts as a C² target. -/
def toC2 {q : ℕ} (N : HarmonicMaps.CompactSmoothEmbeddedTarget q) :
    CompactC2EmbeddedTarget q where
  dimension := N.dimension
  carrierSet := N.carrierSet
  nonempty := N.nonempty
  isCompact := N.isCompact
  chartedSpace := N.chartedSpace
  isManifold := inferInstance
  isC2Embedding := isC2Embedding N

@[simp] theorem toC2_carrierSet {q : ℕ}
    (N : HarmonicMaps.CompactSmoothEmbeddedTarget q) :
    (toC2 N).carrierSet = N.carrierSet := rfl

@[simp] theorem toC2_dimension {q : ℕ}
    (N : HarmonicMaps.CompactSmoothEmbeddedTarget q) :
    (toC2 N).dimension = N.dimension := rfl

end SmoothTarget


end StationaryHarmonicMaps

end

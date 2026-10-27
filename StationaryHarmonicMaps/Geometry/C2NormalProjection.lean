module

public import StationaryHarmonicMaps.Geometry.C2TargetCharts
public import StationaryHarmonicMaps.Geometry.GramProjection
public import StationaryHarmonicMaps.Geometry.ProjectionDifferential

/-!
# C¹ normal projections along actual C² targets

The orthogonal projection onto the normal subspace varies C¹ in every actual
target chart. Its regularity follows from the C¹ derivative family of a C²
chart and the Gram formula for its actual tangent range.
Its actual chart derivatives are self-adjoint and satisfy differentiated
idempotence.
-/

public section

open Filter Topology
open scoped Manifold ContDiff

namespace StationaryHarmonicMaps.CompactC2EmbeddedTarget

/-- Actual orthogonal normal projections are C¹ in each C² target chart. -/
theorem normal_projection_chart_contDiff {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) p
    ContDiffOn ℝ 1 (fun t => (N.tangentImage (e.symm t))ᗮ.starProjection) e.target := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let e := extChartAt I p
  have hProjection := Geometry.contDiffOn_normal_starProjection_of_injective
    (N.chart_parametrization_fderiv_contDiff p)
    (N.chart_parametrization_fderiv_injective p)
  change ContDiffOn ℝ 1 (fun t => (N.tangentImage (e.symm t))ᗮ.starProjection) e.target
  exact hProjection.congr fun t ht => by rw [N.chart_parametrization_tangentImage p t ht]

/-- The actual normal projection field on a C² target is a C¹ manifold map. -/
theorem normal_projection_contMDiff {q : ℕ} (N : CompactC2EmbeddedTarget q) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
      𝓘(ℝ, EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q)) 1
      (fun p : N.Carrier => (N.tangentImage p)ᗮ.starProjection) := by
  intro p
  rw [contMDiffAt_iff_source]
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let e := extChartAt I p
  have hOpen : IsOpen e.target := by
    simp only [e, I, mfld_simps]
    exact (chartAt (EuclideanSpace ℝ (Fin N.dimension)) p).open_target
  have hbase : e p ∈ e.target := mem_extChartAt_target p
  exact ((N.normal_projection_chart_contDiff p).contDiffAt
    (hOpen.mem_nhds hbase)).contMDiffAt.contMDiffWithinAt

/-- The chart field has its actual Fréchet derivative at every point of its chart domain. -/
theorem normal_projection_chart_hasFDerivAt {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) p
    let Q := fun t => (N.tangentImage (e.symm t))ᗮ.starProjection
    ∀ t ∈ e.target, HasFDerivAt Q (fderiv ℝ Q t) t := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let e := extChartAt I p
  have hOpen : IsOpen e.target := by
    simp only [e, I, mfld_simps]
    exact (chartAt (EuclideanSpace ℝ (Fin N.dimension)) p).open_target
  change ∀ t ∈ e.target, HasFDerivAt
    (fun s => (N.tangentImage (e.symm s))ᗮ.starProjection)
    (fderiv ℝ (fun s => (N.tangentImage (e.symm s))ᗮ.starProjection) t) t
  intro t ht
  exact ((N.normal_projection_chart_contDiff p).contDiffAt
    (hOpen.mem_nhds ht)).differentiableAt one_ne_zero |>.hasFDerivAt

/-- Directional derivatives of the actual chart normal projection are self-adjoint. -/
theorem normal_projection_chart_derivative_isSelfAdjoint {q : ℕ}
    (N : CompactC2EmbeddedTarget q) (p : N.Carrier) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) p
    let Q := fun t => (N.tangentImage (e.symm t))ᗮ.starProjection
    ∀ t ∈ e.target, ∀ v : EuclideanSpace ℝ (Fin N.dimension),
      IsSelfAdjoint (fderiv ℝ Q t v) := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let e := extChartAt I p
  let Q := fun t => (N.tangentImage (e.symm t))ᗮ.starProjection
  change ∀ t ∈ e.target, ∀ v : EuclideanSpace ℝ (Fin N.dimension),
    IsSelfAdjoint (fderiv ℝ Q t v)
  intro t ht v
  exact Geometry.projection_derivative_isSelfAdjoint
    (N.normal_projection_chart_hasFDerivAt p t ht)
    (Filter.Eventually.of_forall fun s => isSelfAdjoint_starProjection
      (N.tangentImage (e.symm s))ᗮ) v

/-- The actual chart normal-projection derivative satisfies the mixed composition identity. -/
theorem normal_projection_chart_derivative_idempotence {q : ℕ}
    (N : CompactC2EmbeddedTarget q) (p : N.Carrier) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) p
    let Q := fun t => (N.tangentImage (e.symm t))ᗮ.starProjection
    ∀ t ∈ e.target, ∀ v : EuclideanSpace ℝ (Fin N.dimension),
      fderiv ℝ Q t v * Q t + Q t * fderiv ℝ Q t v = fderiv ℝ Q t v := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let e := extChartAt I p
  let Q := fun t => (N.tangentImage (e.symm t))ᗮ.starProjection
  change ∀ t ∈ e.target, ∀ v : EuclideanSpace ℝ (Fin N.dimension),
    fderiv ℝ Q t v * Q t + Q t * fderiv ℝ Q t v = fderiv ℝ Q t v
  intro t ht v
  exact Geometry.projection_derivative_idempotence
    (N.normal_projection_chart_hasFDerivAt p t ht)
    (Filter.Eventually.of_forall fun s =>
      (N.tangentImage (e.symm s))ᗮ.isIdempotentElem_starProjection) v

end StationaryHarmonicMaps.CompactC2EmbeddedTarget

end

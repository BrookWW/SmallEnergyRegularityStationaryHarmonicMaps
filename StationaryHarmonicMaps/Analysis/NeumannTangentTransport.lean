module

public import StationaryHarmonicMaps.Analysis.NeumannRadialL2Strong
public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds
public import StationaryHarmonicMaps.Analysis.L2FiniteLinearLimits
public import HarmonicMaps.Analysis.VariableMollificationMatrix
public import HarmonicMaps.Analysis.SobolevCutoffBoundary
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Actual tangential-column transport in the Neumann reflection

The genuine orthogonal projection onto the radial orthogonal complement
has measurable coefficients bounded by one. Its full HS composition bound
controls the same radial averages, and the same coefficients preserve their
strong L2 convergence.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The true radial tangential projection has its literal coordinate formula on the entire carrier. -/
theorem neumann_tangent_projection_apply {n : ℕ} (x v : Domain n) :
    (ℝ ∙ x)ᗮ.starProjection v=v-(inner ℝ x v/‖x‖^2) • x := by
  rw [Submodule.starProjection_orthogonal_val,Submodule.starProjection_singleton]
  simp only [RCLike.ofReal_real_eq_id,id_eq]

private theorem tangent_coefficient_memLp_top {n : ℕ} (μ : Measure (Domain n)) (i j : Fin n) :
    MemLp (fun x : Domain n=>((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j) ∞ μ := by
  have hForm : (fun x : Domain n=>((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j)=
      (fun x=>(EuclideanSpace.single i (1 : ℝ)) j-(inner ℝ x (EuclideanSpace.single i 1)/‖x‖^2)*x j) := by
    funext x
    rw [neumann_tangent_projection_apply]
    rfl
  have hMeas : Measurable (fun x : Domain n=>((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j) := by
    rw [hForm]
    exact measurable_const.sub (((continuous_id.inner continuous_const).measurable.div
      (measurable_norm.pow_const 2)).mul (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n=>ℝ) j).continuous.measurable)
  apply memLp_top_of_bound hMeas.aestronglyMeasurable 1
  exact Eventually.of_forall fun x=>(PiLp.norm_apply_le ((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j).trans
    (((ℝ ∙ x)ᗮ.norm_starProjection_apply_le (EuclideanSpace.single i (1 : ℝ))).trans_eq (by simp))

/-- The actual projected radial columns retain the full original HS L2 bound, with no target-dimension factor. -/
theorem neumann_radial_tangent_columns_L2 {n q : ℕ} (a : ℕ)
    (D : Domain n → Gradient n q)
    (hD : ∀j,MemLp (fun x=>D x j) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    let A := {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}
    let V := fun x j=>‖x‖^a • (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^a • D (t • x) j)
    let T := fun x i=>∑j : Fin n,((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j • V x j
    (∀i,MemLp (fun x=>T x i) 2 (volume.restrict A)) ∧
      (∫x in A,hsNormSq (T x))≤(2 : ℝ)^(2*a)*(4 : ℝ)^n*(∫x in ball (0 : Domain n) 1,hsNormSq (D x)) := by
  intro A V T
  let μ := volume.restrict A
  have hV (j : Fin n) : MemLp (fun x=>V x j) 2 μ :=
    (neumann_radial_interval_L2 a a (fun x=>D x j) (hD j)).2.2.2.2.1
  have hT (i : Fin n) : MemLp (fun x=>T x i) 2 μ :=
    memLp_finsetSum _ (fun j _=>(hV j).smul (r := (2 : ℝ≥0∞)) (tangent_coefficient_memLp_top μ i j))
  have hPoint (x : Domain n) : hsNormSq (T x)≤hsNormSq (V x) := by
    have H := hsNormSq_right_comp_le_of_norm_le (V x) ((ℝ ∙ x)ᗮ.starProjection)
      ((ℝ ∙ x)ᗮ.starProjection_norm_le)
    simpa only [one_pow,one_mul] using H
  have hVI : Integrable (fun x=>hsNormSq (V x)) μ := integrable_hsNormSq_of_columns V hV
  refine ⟨hT,?_⟩
  calc
    _≤∫x,hsNormSq (V x) ∂μ := integral_mono (integrable_hsNormSq_of_columns T hT) hVI hPoint
    _=∑j : Fin n,∫x,‖V x j‖^2 ∂μ := integral_finsetSum _ fun j _=>(hV j).integrable_norm_pow (by decide : (2 : ℕ)≠0)
    _≤∑j : Fin n,(2 : ℝ)^(2*a)*(4 : ℝ)^n*(∫x in ball (0 : Domain n) 1,‖D x j‖^2) :=
      Finset.sum_le_sum fun j _=>(neumann_radial_interval_L2 a a (fun x=>D x j) (hD j)).2.2.2.2.2
    _=_ := by
      rw [← Finset.mul_sum,← integral_finsetSum _ (fun j _=>(hD j).integrable_norm_pow (by decide : (2 : ℕ)≠0))]
      rfl

/-- The same genuine tangential radial columns preserve strong L2 convergence of the original columns. -/
theorem neumann_radial_tangent_columns_strong_L2 {n q : ℕ} (a : ℕ)
    (D : ℕ → Domain n → Gradient n q) (F : Domain n → Gradient n q)
    (hD : ∀k j,MemLp (fun x=>D k x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hF : ∀j,MemLp (fun x=>F x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hConv : ∀j,Tendsto (fun k=>eLpNorm (fun x=>D k x j-F x j) 2
      (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0)) :
    let A := {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}
    let V := fun (G : Domain n → Gradient n q) x j=>‖x‖^a •
      (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^a • G (t • x) j)
    let T := fun (G : Domain n → Gradient n q) x i=>
      ∑j : Fin n,((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j • V G x j
    ∀i,Tendsto (fun k=>eLpNorm (fun x=>T (D k) x i-T F x i) 2 (volume.restrict A)) atTop (𝓝 0) := by
  intro A V T i
  let μ := volume.restrict A
  let c := fun (j : Fin n) (x : Domain n)=>((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j
  have hc (j : Fin n) : MemLp (c j) ∞ μ := tangent_coefficient_memLp_top μ i j
  have hVD (k : ℕ) (j : Fin n) : MemLp (fun x=>V (D k) x j) 2 μ :=
    (neumann_radial_interval_L2 a a (fun x=>D k x j) (hD k j)).2.2.2.2.1
  have hVF (j : Fin n) : MemLp (fun x=>V F x j) 2 μ :=
    (neumann_radial_interval_L2 a a (fun x=>F x j) (hF j)).2.2.2.2.1
  have hVL (j : Fin n) : Tendsto (fun k=>eLpNorm (fun x=>V (D k) x j-V F x j) 2 μ) atTop (𝓝 0) :=
    (neumann_radial_interval_strong_L2 a a (fun k x=>D k x j) (fun x=>F x j)
      (fun k=>hD k j) (hF j) (hConv j)).2
  apply tendsto_L2_finset_sum μ (fun k j x=>c j x • V (D k) x j) (fun j x=>c j x • V F x j)
    (fun k j=>(hVD k j).smul (r := (2 : ℝ≥0∞)) (hc j))
    (fun j=>(hVF j).smul (r := (2 : ℝ≥0∞)) (hc j))
  intro j
  have H := tendsto_eLpNorm_smul_of_top (hc j)
    (fun k=>((hVD k j).sub (hVF j)).aestronglyMeasurable) (hVL j)
  simpa only [Pi.sub_apply,smul_sub] using H

end StationaryHarmonicMaps.Analysis

end

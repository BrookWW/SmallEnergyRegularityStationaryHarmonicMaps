module

public import StationaryHarmonicMaps.Analysis.NeumannTangentTransport
public import StationaryHarmonicMaps.Analysis.AnnularInversionGradientTransport

/-!
# Actual L2 data for the Neumann Kelvin outer formula

Original ball data supply the weighted inversion and radial averages on
the exterior annulus. The tangential part uses the true radial orthogonal
projection. No reflected weak-gradient or boundary equation is assumed.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set Metric
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem annulus_image_subset_unit {n : ℕ} :
    inversion (0 : Domain n) 1 '' {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}⊆ball (0 : Domain n) 1 := by
  rintro _ ⟨x,hx,rfl⟩
  rw [mem_ball_zero_iff,norm_unit_inversion]
  exact (inv_lt_one₀ (zero_lt_one.trans hx.1)).mpr hx.1

private theorem annulus_weight_memLp_top {n : ℕ} (hn : 2≤n) :
    MemLp (fun x : Domain n=>‖x‖^(2-(n : ℝ))) ∞
      (volume.restrict {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}) := by
  have hA : MeasurableSet {x : Domain n | 1<‖x‖ ∧ ‖x‖<2} :=
    (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)
  apply memLp_top_of_bound (measurable_norm.pow_const _).aestronglyMeasurable 1
  filter_upwards [ae_restrict_mem hA] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos hx.1.le (sub_nonpos.mpr (by exact_mod_cast hn))

/-- The complete literal exterior value and derivative-column formulas have actual L2 membership from the original raw ball data. -/
theorem neumann_kelvin_outer_memLp {n q : ℕ} (hn : 2≤n)
    (u : Domain n → Ambient q) (D : Domain n → Gradient n q)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hD : ∀j,MemLp (fun x=>D x j) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    let A := {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}
    let I := inversion (0 : Domain n) 1
    let V := fun x=>‖x‖^(n-2) • (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^(n-3) • u (t • x))
    let B := fun x j=>‖x‖^(n-2) • (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^(n-2) • D (t • x) j)
    let U := fun x=>‖x‖^(2-(n : ℝ)) • u (I x)+((n : ℝ)-2) • V x
    let DU := fun x i=>‖x‖^(2-(n : ℝ)) •
      (∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • D (I x) j)+
        ((n : ℝ)-2) • (∑j : Fin n,((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j • B x j)
    MemLp U 2 (volume.restrict A) ∧ ∀i,MemLp (fun x=>DU x i) 2 (volume.restrict A) := by
  intro A I V B U DU
  let μ := volume.restrict A
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hA0 (x : Domain n) (hx : x∈A) : x≠0 := norm_pos_iff.mp (zero_lt_one.trans hx.1)
  have hImage := annulus_image_subset_unit (n := n)
  have huImage : MemLp u 2 (volume.restrict (I '' A)) :=
    hu.mono_measure (Measure.restrict_mono_set volume hImage)
  have hDImage (j : Fin n) : MemLp (fun x=>D x j) 2 (volume.restrict (I '' A)) :=
    (hD j).mono_measure (Measure.restrict_mono_set volume hImage)
  have hPull := (unit_inversion_L2_transport_bounded_set A hA hA0 2 (by norm_num)
    (fun _ hx=>hx.2.le) u huImage).1
  have hColumns := (unit_inversion_L2_gradient_columns_transport A hA 1 2 (by norm_num) (by norm_num)
    (fun _ hx=>hx.1.le) (fun _ hx=>hx.2.le) D hDImage).1
  have hW := annulus_weight_memLp_top hn
  have hV : MemLp V 2 μ := (neumann_radial_interval_L2 (n-2) (n-3) u hu).2.2.2.2.1
  have hT := (neumann_radial_tangent_columns_L2 (n-2) D hD).1
  exact ⟨(hPull.smul (r := (2 : ℝ≥0∞)) hW).add (hV.const_smul ((n : ℝ)-2)),fun i=>
    ((hColumns i).smul (r := (2 : ℝ≥0∞)) hW).add ((hT i).const_smul ((n : ℝ)-2))⟩

private theorem strong_add {X : Type*} [MeasurableSpace X] {q : ℕ} (μ : Measure X)
    (f g : ℕ → X → Ambient q) (v w : X → Ambient q)
    (hf : ∀k,MemLp (f k) 2 μ) (hg : ∀k,MemLp (g k) 2 μ)
    (hv : MemLp v 2 μ) (hw : MemLp w 2 μ)
    (hF : Tendsto (fun k=>eLpNorm (f k-v) 2 μ) atTop (𝓝 0))
    (hG : Tendsto (fun k=>eLpNorm (g k-w) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k=>eLpNorm ((f k+g k)-(v+w)) 2 μ) atTop (𝓝 0) := by
  have hUpper : Tendsto (fun k=>eLpNorm (f k-v) 2 μ+eLpNorm (g k-w) 2 μ) atTop (𝓝 0) := by
    simpa only [add_zero] using hF.add hG
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper (fun _=>zero_le)
  intro k
  have heq : (f k+g k)-(v+w)=(f k-v)+(g k-w) := by funext x;simp only [Pi.add_apply,Pi.sub_apply];abel
  change eLpNorm ((f k+g k)-(v+w)) 2 μ≤eLpNorm (f k-v) 2 μ+eLpNorm (g k-w) 2 μ
  rw [heq]
  exact eLpNorm_add_le ((hf k).sub hv).aestronglyMeasurable ((hg k).sub hw).aestronglyMeasurable (by norm_num)

/-- The same complete exterior formulas preserve the actual strong L2 convergence of the original maps and columns. -/
theorem neumann_kelvin_outer_strong_L2 {n q : ℕ} (hn : 2≤n)
    (u : ℕ → Domain n → Ambient q) (D : ℕ → Domain n → Gradient n q)
    (v : Domain n → Ambient q) (F : Domain n → Gradient n q)
    (hu : ∀k,MemLp (u k) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hD : ∀k j,MemLp (fun x=>D k x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hv : MemLp v 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hF : ∀j,MemLp (fun x=>F x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hMap : Tendsto (fun k=>eLpNorm (u k-v) 2 (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0))
    (hColumns : ∀j,Tendsto (fun k=>eLpNorm (fun x=>D k x j-F x j) 2
      (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0)) :
    let A := {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}
    let I := inversion (0 : Domain n) 1
    let V := fun (f : Domain n → Ambient q) x=>‖x‖^(n-2) •
      (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^(n-3) • f (t • x))
    let B := fun (G : Domain n → Gradient n q) x j=>‖x‖^(n-2) •
      (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^(n-2) • G (t • x) j)
    let U := fun (f : Domain n → Ambient q) x=>‖x‖^(2-(n : ℝ)) • f (I x)+((n : ℝ)-2) • V f x
    let DU := fun (G : Domain n → Gradient n q) x i=>‖x‖^(2-(n : ℝ)) •
      (∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • G (I x) j)+
        ((n : ℝ)-2) • (∑j : Fin n,((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j • B G x j)
    Tendsto (fun k=>eLpNorm (U (u k)-U v) 2 (volume.restrict A)) atTop (𝓝 0) ∧
      ∀i,Tendsto (fun k=>eLpNorm (fun x=>DU (D k) x i-DU F x i) 2 (volume.restrict A)) atTop (𝓝 0) := by
  intro A I V B U DU
  let μ := volume.restrict A
  let ν := volume.restrict (I '' A)
  let w := fun x : Domain n=>‖x‖^(2-(n : ℝ))
  let c := (n : ℝ)-2
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hA0 (x : Domain n) (hx : x∈A) : x≠0 := norm_pos_iff.mp (zero_lt_one.trans hx.1)
  have hν : ν≤volume.restrict (ball (0 : Domain n) 1) := Measure.restrict_mono_set volume annulus_image_subset_unit
  have hUImage k := (hu k).mono_measure hν
  have hVImage := hv.mono_measure hν
  have hDImage k j := (hD k j).mono_measure hν
  have hFImage j := (hF j).mono_measure hν
  have hMapImage : Tendsto (fun k=>eLpNorm (u k-v) 2 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hMap (fun _=>zero_le) (fun k=>eLpNorm_mono_measure _ hν)
  have hColumnsImage j : Tendsto (fun k=>eLpNorm (fun x=>D k x j-F x j) 2 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hColumns j) (fun _=>zero_le)
      (fun k=>eLpNorm_mono_measure _ hν)
  let P := fun (f : Domain n → Ambient q) x=>f (I x)
  let Q := fun (G : Domain n → Gradient n q) x i=>∑j : Fin n,
    (fderiv ℝ I x (EuclideanSpace.single i 1)) j • G (I x) j
  let T := fun (G : Domain n → Gradient n q) x i=>∑j : Fin n,
    ((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j • B G x j
  have hPU k := (unit_inversion_L2_transport_bounded_set A hA hA0 2 (by norm_num) (fun _ hx=>hx.2.le) (u k) (hUImage k)).1
  have hPV := (unit_inversion_L2_transport_bounded_set A hA hA0 2 (by norm_num) (fun _ hx=>hx.2.le) v hVImage).1
  have hPUConv := tendsto_unit_inversion_L2_transport A hA hA0 2 (by norm_num) (fun _ hx=>hx.2.le)
    u v hUImage hVImage hMapImage
  have hQD k := (unit_inversion_L2_gradient_columns_transport A hA 1 2 (by norm_num) (by norm_num)
    (fun _ hx=>hx.1.le) (fun _ hx=>hx.2.le) (D k) (hDImage k)).1
  have hQF := (unit_inversion_L2_gradient_columns_transport A hA 1 2 (by norm_num) (by norm_num)
    (fun _ hx=>hx.1.le) (fun _ hx=>hx.2.le) F hFImage).1
  have hQConv := tendsto_unit_inversion_L2_gradient_columns A hA 1 2 (by norm_num) (by norm_num)
    (fun _ hx=>hx.1.le) (fun _ hx=>hx.2.le) D F hDImage hFImage hColumnsImage
  have hW : MemLp w ∞ μ := annulus_weight_memLp_top hn
  have hC : MemLp (fun _ : Domain n=>c) ∞ μ := memLp_top_of_bound aestronglyMeasurable_const ‖c‖ (Eventually.of_forall fun _=>le_rfl)
  have hVU k : MemLp (V (u k)) 2 μ := (neumann_radial_interval_L2 (n-2) (n-3) (u k) (hu k)).2.2.2.2.1
  have hVV : MemLp (V v) 2 μ := (neumann_radial_interval_L2 (n-2) (n-3) v hv).2.2.2.2.1
  have hVConv := (neumann_radial_interval_strong_L2 (n-2) (n-3) u v hu hv hMap).2
  have hTD k := (neumann_radial_tangent_columns_L2 (n-2) (D k) (hD k)).1
  have hTF := (neumann_radial_tangent_columns_L2 (n-2) F hF).1
  have hTConv := neumann_radial_tangent_columns_strong_L2 (n-2) D F hD hF hColumns
  have hMult (a : Domain n → ℝ) (ha : MemLp a ∞ μ)
      (f : ℕ → Domain n → Ambient q) (g : Domain n → Ambient q)
      (hf : ∀k,MemLp (f k) 2 μ) (hg : MemLp g 2 μ)
      (hLim : Tendsto (fun k=>eLpNorm (f k-g) 2 μ) atTop (𝓝 0)) :
      Tendsto (fun k=>eLpNorm ((fun x=>a x • f k x)-(fun x=>a x • g x)) 2 μ) atTop (𝓝 0) := by
    have H := tendsto_eLpNorm_smul_of_top ha (fun k=>((hf k).sub hg).aestronglyMeasurable) hLim
    change Tendsto (fun k=>eLpNorm (fun x=>a x • f k x-a x • g x) 2 μ) atTop (𝓝 0)
    simpa only [Pi.sub_apply,smul_sub] using H
  constructor
  · exact strong_add μ (fun k x=>w x • P (u k) x) (fun k x=>c • V (u k) x)
      (fun x=>w x • P v x) (fun x=>c • V v x)
      (fun k=>(hPU k).smul (r := (2 : ℝ≥0∞)) hW) (fun k=>(hVU k).const_smul c)
      (hPV.smul (r := (2 : ℝ≥0∞)) hW) (hVV.const_smul c)
      (hMult w hW (fun k=>P (u k)) (P v) hPU hPV hPUConv)
      (hMult (fun _=>c) hC (fun k=>V (u k)) (V v) hVU hVV hVConv)
  · intro i
    exact strong_add μ (fun k x=>w x • Q (D k) x i) (fun k x=>c • T (D k) x i)
      (fun x=>w x • Q F x i) (fun x=>c • T F x i)
      (fun k=>(hQD k i).smul (r := (2 : ℝ≥0∞)) hW) (fun k=>(hTD k i).const_smul c)
      ((hQF i).smul (r := (2 : ℝ≥0∞)) hW) ((hTF i).const_smul c)
      (hMult w hW (fun k x=>Q (D k) x i) (fun x=>Q F x i) (fun k=>hQD k i) (hQF i) (hQConv i))
      (hMult (fun _=>c) hC (fun k x=>T (D k) x i) (fun x=>T F x i) (fun k=>hTD k i) (hTF i) (hTConv i))

end StationaryHarmonicMaps.Analysis

end

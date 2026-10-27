module

public import StationaryHarmonicMaps.Analysis.AnnularInversionGradientTransport

/-!
# Strong transport of the even inversion graph

The annular value and derivative formulas preserve the original strong L2
convergence. All columns are the literal chain columns under inversion.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set Metric
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem even_annulus_image_subset {n : ℕ} :
    inversion (0 : Domain n) 1 '' {x : Domain n | 1 < ‖x‖ ∧ ‖x‖ < 2} ⊆
      ball (0 : Domain n) 1 := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_ball_zero_iff, norm_unit_inversion]
  exact (inv_lt_one₀ (zero_lt_one.trans hx.1)).mpr hx.1

/-- The raw original L2 graph gives actual L2 data for the even annular formula. -/
theorem even_inversion_outer_memLp {n q : ℕ}
    (u : Domain n → Ambient q) (D : Domain n → Gradient n q)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hD : ∀ j, MemLp (fun x => D x j) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    let A := {x : Domain n | 1 < ‖x‖ ∧ ‖x‖ < 2}
    let I := inversion (0 : Domain n) 1
    MemLp (fun x => u (I x)) 2 (volume.restrict A) ∧
      ∀ i, MemLp (fun x => ∑ j : Fin n,
        (fderiv ℝ I x (EuclideanSpace.single i 1)) j • D (I x) j) 2 (volume.restrict A) := by
  intro A I
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hA0 (x : Domain n) (hx : x ∈ A) : x ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hx.1)
  have hU := hu.mono_measure (Measure.restrict_mono_set volume even_annulus_image_subset)
  have hF (j : Fin n) := (hD j).mono_measure
    (Measure.restrict_mono_set volume even_annulus_image_subset)
  exact ⟨(unit_inversion_L2_transport_bounded_set A hA hA0 2 (by norm_num)
    (fun _ hx => hx.2.le) u hU).1,
    (unit_inversion_L2_gradient_columns_transport A hA 1 2 (by norm_num) (by norm_num)
      (fun _ hx => hx.1.le) (fun _ hx => hx.2.le) D hF).1⟩

/-- Both literal even inversion formulas preserve strong L2 convergence of the original data. -/
theorem even_inversion_outer_strong_L2 {n q : ℕ}
    (u : ℕ → Domain n → Ambient q) (D : ℕ → Domain n → Gradient n q)
    (v : Domain n → Ambient q) (F : Domain n → Gradient n q)
    (hu : ∀ k, MemLp (u k) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hD : ∀ k j, MemLp (fun x => D k x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hv : MemLp v 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hF : ∀ j, MemLp (fun x => F x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hMap : Tendsto (fun k => eLpNorm (u k - v) 2
      (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0))
    (hColumns : ∀ j, Tendsto (fun k => eLpNorm (fun x => D k x j - F x j) 2
      (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0)) :
    let A := {x : Domain n | 1 < ‖x‖ ∧ ‖x‖ < 2}
    let I := inversion (0 : Domain n) 1
    Tendsto (fun k => eLpNorm (fun x => u k (I x) - v (I x)) 2
      (volume.restrict A)) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun k => eLpNorm (fun x =>
        (∑ j : Fin n, (fderiv ℝ I x (EuclideanSpace.single i 1)) j • D k (I x) j) -
          ∑ j : Fin n, (fderiv ℝ I x (EuclideanSpace.single i 1)) j • F (I x) j) 2
            (volume.restrict A)) atTop (𝓝 0) := by
  intro A I
  let ν := volume.restrict (I '' A)
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hA0 (x : Domain n) (hx : x ∈ A) : x ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hx.1)
  have hν : ν ≤ volume.restrict (ball (0 : Domain n) 1) :=
    Measure.restrict_mono_set volume even_annulus_image_subset
  have hMap' : Tendsto (fun k => eLpNorm (u k - v) 2 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hMap (fun _ => zero_le)
      (fun _ => eLpNorm_mono_measure _ hν)
  have hColumns' (j : Fin n) : Tendsto (fun k => eLpNorm (fun x => D k x j - F x j) 2 ν)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hColumns j)
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ hν)
  exact ⟨tendsto_unit_inversion_L2_transport A hA hA0 2 (by norm_num) (fun _ hx => hx.2.le)
      u v (fun k => (hu k).mono_measure hν) (hv.mono_measure hν) hMap',
    tendsto_unit_inversion_L2_gradient_columns A hA 1 2 (by norm_num) (by norm_num)
      (fun _ hx => hx.1.le) (fun _ hx => hx.2.le) D F
      (fun k j => (hD k j).mono_measure hν) (fun j => (hF j).mono_measure hν) hColumns'⟩

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.WhitneyPartitionQuantitative

/-!
# Genuine nested Whitney scales and cutoff products

Distance-to-complement radii on nested bad sets are compared at actual
intersections of their tenfold balls. The resulting factor three gives
the derivative bound for the actual low/high cutoff product.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Nested actual distance radii and intersecting tenfold balls give the high-to-low scale bound and the actual enlarged-ball inclusion. -/
theorem nested_whitney_tenfold_geometry {n : ℕ} (Slo Shi : Set (Domain n))
    (hNested : Shi⊆Slo) (hComp : Sloᶜ.Nonempty) (a b : Domain n)
    (hOverlap : (Metric.ball a (10*(Metric.infDist a Sloᶜ/20))∩
      Metric.ball b (10*(Metric.infDist b Shiᶜ/20))).Nonempty) :
    let rlo := Metric.infDist a Sloᶜ/20
    let rhi := Metric.infDist b Shiᶜ/20
    0<rlo ∧ 0<rhi ∧ rhi≤3*rlo ∧ dist a b<40*rlo ∧
      Metric.ball b (10*rhi)⊆Metric.ball a (70*rlo) := by
  intro rlo rhi
  obtain ⟨x,hxa,hxb⟩ := hOverlap
  have hax : dist a x<10*rlo := by simpa only [Metric.mem_ball,dist_comm] using hxa
  have hxb' : dist x b<10*rhi := hxb
  have hrlo : 0<rlo := by linarith only [dist_nonneg (x := a) (y := x),hax]
  have hrhi : 0<rhi := by linarith only [dist_nonneg (x := x) (y := b),hxb']
  have hAB : dist a b<10*rlo+10*rhi :=
    (dist_triangle a x b).trans_lt (add_lt_add hax hxb')
  have hMono : Metric.infDist b Shiᶜ≤Metric.infDist b Sloᶜ :=
    Metric.infDist_le_infDist_of_subset (compl_subset_compl.mpr hNested) hComp
  have hLip := Metric.infDist_le_infDist_add_dist (x := b) (y := a) (s := Sloᶜ)
  have hRa : Metric.infDist a Sloᶜ=20*rlo := by dsimp only [rlo];ring
  have hRb : Metric.infDist b Shiᶜ=20*rhi := by dsimp only [rhi];ring
  have hDist : 20*rhi≤20*rlo+dist a b := by
    rw [hRb] at hMono
    rw [hRa,dist_comm] at hLip
    exact hMono.trans hLip
  have hRatio : rhi≤3*rlo := by linarith only [hDist,hAB]
  have hCenter : dist a b<40*rlo := by linarith only [hAB,hRatio]
  refine ⟨hrlo,hrhi,hRatio,hCenter,?_⟩
  intro z hz
  have hzb : dist z b<10*rhi := hz
  have H := dist_triangle z b a
  rw [dist_comm b a] at H
  change dist z a<70*rlo
  linarith only [H,hzb,hCenter,hRatio]

/-- Actual smooth cutoffs bounded between zero and one have a true product derivative bound at the high radius once the genuine geometric scale comparison is available. -/
theorem norm_fderiv_nested_cutoff_product_le {n : ℕ}
    (θlo θhi : Domain n → ℝ) (hLo : ContDiff ℝ ∞ θlo) (hHi : ContDiff ℝ ∞ θhi)
    (hLoBound : ∀ x,0≤θlo x ∧ θlo x≤1) (hHiBound : ∀ x,0≤θhi x ∧ θhi x≤1)
    (B rlo rhi : ℝ) (hB : 0<B) (hrlo : 0<rlo) (hrhi : 0<rhi)
    (hRatio : rhi≤3*rlo)
    (hDLo : ∀ x,‖fderiv ℝ θlo x‖≤B/rlo)
    (hDHi : ∀ x,‖fderiv ℝ θhi x‖≤B/rhi) :
    ∀ x,‖fderiv ℝ (fun y => θlo y*θhi y) x‖≤4*B/rhi := by
  have hScale : B/rlo≤3*B/rhi := by
    apply (div_le_div_iff₀ hrlo hrhi).mpr
    have H := mul_le_mul_of_nonneg_left hRatio hB.le
    nlinarith only [H]
  intro x
  rw [fderiv_fun_mul (hLo.differentiable (by simp) x) (hHi.differentiable (by simp) x)]
  calc
    _ ≤ ‖θlo x • fderiv ℝ θhi x‖+‖θhi x • fderiv ℝ θlo x‖ := norm_add_le _ _
    _ = |θlo x| * ‖fderiv ℝ θhi x‖+|θhi x| * ‖fderiv ℝ θlo x‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
    _ ≤ ‖fderiv ℝ θhi x‖+‖fderiv ℝ θlo x‖ := by
      apply add_le_add
      · exact mul_le_of_le_one_left (norm_nonneg _)
          (by rw [abs_of_nonneg (hLoBound x).1];exact (hLoBound x).2)
      · exact mul_le_of_le_one_left (norm_nonneg _)
          (by rw [abs_of_nonneg (hHiBound x).1];exact (hHiBound x).2)
    _ ≤ B/rhi+3*B/rhi := add_le_add (hDHi x) ((hDLo x).trans hScale)
    _ = _ := by ring

end StationaryHarmonicMaps.Analysis

end

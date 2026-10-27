module

public import StationaryHarmonicMaps.Analysis.WhitneyNestedScales
public import StationaryHarmonicMaps.Analysis.CorrectedPiecePointwise

/-!
# Literal support of the actual corrected Whitney piece

A nonzero original compensation coefficient forces an actual overlap
of the original low and high support balls. The proved nested distance
geometry places that entire high ball in the seventyfold low ball.
Outside this low ball, both original rows vanish term by term, so the
actual corrected series has literal support in that ball.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original nested support geometry and actual integral-defined coefficients produce literal seventyfold support for the original corrected piece. -/
theorem support_corrected_whitney_piece_subset {n : ℕ} {I : Type*}
    (Slo Shi : Set (Domain n)) (hNested : Shi⊆Slo) (hComp : Sloᶜ.Nonempty)
    (a : Domain n) (p : I → Domain n) (φ : Domain n → ℝ) (ψ : I → Domain n → ℝ)
    (hφ : tsupport φ⊆Metric.ball a (10*(Metric.infDist a Sloᶜ/20)))
    (hψ : ∀ j,tsupport (ψ j)⊆Metric.ball (p j) (10*(Metric.infDist (p j) Shiᶜ/20)))
    (f : Domain n → ℝ) (ci : ℝ) (c : I → ℝ) :
    let d := fun j=>(∫ x,φ x*(ψ j x*(f x-c j)))/(∫ x,ψ j x)
    let A := fun x=>φ x*(f x-ci)-(∑' j,φ x*(ψ j x*(f x-c j)))+(∑' j,d j*ψ j x)
    Function.support A⊆Metric.ball a (70*(Metric.infDist a Sloᶜ/20)) := by
  intro d A
  let rlo := Metric.infDist a Sloᶜ/20
  let rhi := fun j=>Metric.infDist (p j) Shiᶜ/20
  have hrlo : 0≤rlo := div_nonneg Metric.infDist_nonneg (by norm_num)
  have hLowSub : Metric.ball a (10*rlo)⊆Metric.ball a (70*rlo) := Metric.ball_subset_ball (by linarith only [hrlo])
  have hNonzeroOverlap (j : I) (hj : d j≠0) :
      (Metric.ball a (10*rlo)∩Metric.ball (p j) (10*rhi j)).Nonempty := by
    by_contra hNo
    have hZero : (fun x=>φ x*(ψ j x*(f x-c j)))=fun _=>0 := by
      funext x
      by_cases hxφ : φ x=0
      · rw [hxφ,zero_mul]
      · by_cases hxψ : ψ j x=0
        · rw [hxψ,zero_mul,mul_zero]
        · exact False.elim (hNo ⟨x,hφ (subset_tsupport φ hxφ),hψ j (subset_tsupport (ψ j) hxψ)⟩)
    apply hj
    dsimp only [d]
    rw [hZero,integral_zero,zero_div]
  intro x hx
  by_contra hOutside
  have hφZero : φ x=0 := image_eq_zero_of_notMem_tsupport (fun H=>hOutside (hLowSub (hφ H)))
  have hCorrectionsZero (j : I) : d j*ψ j x=0 := by
    by_cases hj : d j=0
    · rw [hj,zero_mul]
    · obtain ⟨_hrlo,_hrhi,_hRatio,_hCenter,hBall⟩ :=
        nested_whitney_tenfold_geometry Slo Shi hNested hComp a (p j) (hNonzeroOverlap j hj)
      have hxψ : x∉tsupport (ψ j) := fun H=>hOutside (hBall (hψ j H))
      rw [image_eq_zero_of_notMem_tsupport hxψ,mul_zero]
  exact hx (by
    change φ x*(f x-ci)-(∑' j,φ x*(ψ j x*(f x-c j)))+(∑' j,d j*ψ j x)=0
    simp only [hφZero,zero_mul,tsum_zero,hCorrectionsZero,sub_self,add_zero])

end StationaryHarmonicMaps.Analysis

end

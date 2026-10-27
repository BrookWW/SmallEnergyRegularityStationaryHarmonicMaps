module

public import StationaryHarmonicMaps.Geometry.OneFormGaffneyIdentity
public import StationaryHarmonicMaps.Analysis.BallDivergenceIntegral

/-!
# Normal one-form Gaffney estimate on the actual Euclidean ball

The coefficient gradient, exterior derivative and divergence use their
literal finite sums. The actual sphere contraction gives the nonpositive
boundary contribution through the ball divergence inequality.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual smooth normal one-forms satisfy the full coefficient Gaffney inequality, with all energy integrability produced. -/
theorem smooth_normal_oneForm_gaffney {n q : ℕ}
    (A : Fin n → Domain n → Ambient q) (hA : ∀ i, ContDiff ℝ ∞ (A i))
    (hNormal : ∀ y : Domain n, ‖y‖=1 → (∑ i : Fin n, y i • A i y)=0) :
    let g := fun x : Domain n => ∑ i : Fin n, ∑ j : Fin n,
      ‖fderiv ℝ (A j) x (EuclideanSpace.single i 1)‖^2
    let c := fun x : Domain n => ∑ i : Fin n, ∑ j : Fin n,
      ‖fderiv ℝ (A j) x (EuclideanSpace.single i 1)-
        fderiv ℝ (A i) x (EuclideanSpace.single j 1)‖^2
    let d := fun x : Domain n => ‖∑ i : Fin n,
      fderiv ℝ (A i) x (EuclideanSpace.single i 1)‖^2
    IntegrableOn g (ball (0 : Domain n) 1) volume ∧
      IntegrableOn c (ball (0 : Domain n) 1) volume ∧
      IntegrableOn d (ball (0 : Domain n) 1) volume ∧
      (∫ x in ball (0 : Domain n) 1, g x) ≤
        (1/2:ℝ)*(∫ x in ball (0 : Domain n) 1, c x) +
          ∫ x in ball (0 : Domain n) 1, d x := by
  intro g c d
  let V := fun x : Domain n => WithLp.toLp 2 (fun i : Fin n => ∑ j : Fin n,
    (inner ℝ (A j x) (fderiv ℝ (A i) x (EuclideanSpace.single j 1)) -
      inner ℝ (A i x) (fderiv ℝ (A j) x (EuclideanSpace.single j 1))))
  obtain ⟨hV,hIdentity⟩ := oneForm_gaffney_divergence_identity A hA
  have hCol (i j : Fin n) : Continuous (fun x=>fderiv ℝ (A j) x (EuclideanSpace.single i 1)) :=
    (((hA j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hg : Continuous g := continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => (hCol i j).norm.pow 2
  have hc : Continuous c := continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ((hCol i j).sub (hCol j i)).norm.pow 2
  have hd : Continuous d := (continuous_finsetSum _ fun i _ => hCol i i).norm.pow 2
  have hgI : IntegrableOn g (ball (0 : Domain n) 1) volume :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Domain n) 1)).mono_set ball_subset_closedBall
  have hcI : IntegrableOn c (ball (0 : Domain n) 1) volume :=
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Domain n) 1)).mono_set ball_subset_closedBall
  have hdI : IntegrableOn d (ball (0 : Domain n) 1) volume :=
    (hd.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Domain n) 1)).mono_set ball_subset_closedBall
  have hFlux (x : Domain n) (hx : ‖x‖=1) : inner ℝ x (V x) ≤ 0 := by
    have H := normal_oneForm_sphere_flux A hNormal x hx
      (fun i => (hA i).differentiable (by simp) x)
    have hp : inner ℝ x (V x) = ∑ i : Fin n, x i * ∑ j : Fin n,
        (inner ℝ (A j x) (fderiv ℝ (A i) x (EuclideanSpace.single j 1)) -
          inner ℝ (A i x) (fderiv ℝ (A j) x (EuclideanSpace.single j 1))) := by
      simp only [PiLp.inner_apply,Real.inner_apply,V]
    rw [hp,H]
    exact neg_nonpos.mpr (Finset.sum_nonneg fun i _=>sq_nonneg _)
  have hDiv := (unitBall_integral_divergence_nonpos V (hV.of_le (by simp)) hFlux).2
  have hInt : (∫ x in ball (0 : Domain n) 1, ∑ i : Fin n,
      (fderiv ℝ V x (EuclideanSpace.single i 1)) i) =
      (∫ x in ball (0 : Domain n) 1, g x) -
        (1/2:ℝ)*(∫ x in ball (0 : Domain n) 1, c x) -
          ∫ x in ball (0 : Domain n) 1, d x := by
    rw [integral_congr_ae (Eventually.of_forall hIdentity)]
    have H1 : (∫ x in ball (0 : Domain n) 1, (g x-(1/2:ℝ)*c x)-d x) =
        (∫ x in ball (0 : Domain n) 1, g x-(1/2:ℝ)*c x) -
          ∫ x in ball (0 : Domain n) 1, d x := by
      simpa only [Pi.sub_apply] using integral_sub (hgI.sub (hcI.const_mul (1/2:ℝ))) hdI
    have H2 : (∫ x in ball (0 : Domain n) 1, g x-(1/2:ℝ)*c x) =
        (∫ x in ball (0 : Domain n) 1, g x) -
          ∫ x in ball (0 : Domain n) 1, (1/2:ℝ)*c x := by
      simpa only [Pi.sub_apply] using integral_sub hgI (hcI.const_mul (1/2:ℝ))
    exact H1.trans (congrArg (fun t : ℝ => t-(∫ x in ball (0 : Domain n) 1, d x))
      (H2.trans (by rw [integral_const_mul])))
  refine ⟨hgI,hcI,hdI,?_⟩
  rw [hInt] at hDiv
  linarith only [hDiv]

end StationaryHarmonicMaps.Analysis

end

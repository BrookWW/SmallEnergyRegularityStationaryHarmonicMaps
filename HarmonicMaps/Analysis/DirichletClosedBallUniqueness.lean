module

public import HarmonicMaps.Analysis.SmoothBallZeroBoundary
public import HarmonicMaps.Analysis.DirichletZeroBoundaryGreen
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniqueness of smooth harmonic candidates on a closed ball

The actual sphere-zero boundary condition produces the existing graph-closure
W0 test. Its signed Green pairing forces the original classical columns to
vanish. The conclusion concerns the source closed ball only.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace HarmonicMaps

/-- A smooth harmonic candidate with actual zero sphere data vanishes on the
source closed ball. -/
theorem dirichlet_harmonic_zero_closedBall {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (f : Domain n → Ambient q) (hf : ContDiffOn ℝ ∞ f U)
    (hboundary : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, f x = 0)
    (hharmonic : ∀ x ∈ Metric.ball (0 : Domain n) R.val,
      Laplacian.laplacian f x = 0) :
    ∀ x ∈ Metric.closedBall (0 : Domain n) R.val, f x = 0 := by
  classical
  have hW0 := smooth_zeroBoundary_ball hn R U hU hclosed f hf hboundary
  obtain ⟨hInt, _, hGreen⟩ := dirichlet_zeroBoundary_green_laplacian R U hU hclosed
    f hf f (fun x i => fderiv ℝ f x (EuclideanSpace.single i 1)) hW0
  simp only [real_inner_self_eq_norm_sq] at hInt hGreen
  let e : Domain n → ℝ := fun x => ∑ i : Fin n,
    ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2
  have hLapZero : (∫ x in Metric.ball (0 : Domain n) R.val,
      inner ℝ (Laplacian.laplacian f x) (f x)) = 0 := by
    calc
      _ = ∫ x in Metric.ball (0 : Domain n) R.val, (0 : ℝ) :=
        setIntegral_congr_fun measurableSet_ball (fun x hx => by simp [hharmonic x hx])
      _ = 0 := by simp
  have hEnergyZero : (∫ x in Metric.ball (0 : Domain n) R.val, e x) = 0 := by
    simpa only [hLapZero, neg_zero] using hGreen
  have hNonneg : 0 ≤ e := fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hAE : e =ᵐ[volume.restrict (Metric.ball (0 : Domain n) R.val)] 0 :=
    (integral_eq_zero_iff_of_nonneg hNonneg hInt).mp hEnergyZero
  have hCols (i : Fin n) : ContDiffOn ℝ ∞
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) U :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hEcont : ContinuousOn e U := by
    apply continuousOn_finsetSum
    intro i _
    exact (hCols i).continuousOn.norm.pow 2
  have hEvery : EqOn e (fun _ => 0) (Metric.ball (0 : Domain n) R.val) :=
    (volume : Measure (Domain n)).eqOn_open_of_ae_eq hAE Metric.isOpen_ball
      (hEcont.mono (Metric.ball_subset_closedBall.trans hclosed)) continuousOn_const
  have hColumnZero (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val)
      (i : Fin n) : fderiv ℝ f x (EuclideanSpace.single i 1) = 0 := by
    have H := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) =>
      sq_nonneg ‖fderiv ℝ f x (EuclideanSpace.single j 1)‖)).mp (hEvery hx)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (H i (Finset.mem_univ i)))
  have hDerivativeZero (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
      fderiv ℝ f x = 0 := by
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
    intro i
    simpa [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using hColumnZero x hx i
  have hDiff : DifferentiableOn ℝ f (Metric.ball (0 : Domain n) R.val) :=
    (hf.differentiableOn (by simp)).mono (Metric.ball_subset_closedBall.trans hclosed)
  have hConst : EqOn f (fun _ => f 0) (Metric.ball (0 : Domain n) R.val) := by
    intro x hx
    apply (convex_ball (0 : Domain n) R.val).is_const_of_fderivWithin_eq_zero hDiff
      (fun z hz => by rw [fderivWithin_of_isOpen Metric.isOpen_ball hz, hDerivativeZero z hz])
      hx (Metric.mem_ball_self R.property)
  have hConstClosed : EqOn f (fun _ => f 0) (Metric.closedBall (0 : Domain n) R.val) :=
    hConst.of_subset_closure (hf.continuousOn.mono hclosed) continuousOn_const
      Metric.ball_subset_closedBall (by rw [closure_ball 0 (ne_of_gt R.property)])
  let i : Fin n := ⟨0, by omega⟩
  let p : Domain n := R.val • EuclideanSpace.single i 1
  have hp : p ∈ Metric.sphere (0 : Domain n) R.val := by
    simp only [p, Metric.mem_sphere, dist_zero_right, norm_smul,
      Real.norm_of_nonneg R.property.le, PiLp.norm_single, norm_one, mul_one]
  have hAtZero : f 0 = 0 := (hConstClosed (Metric.sphere_subset_closedBall hp)).symm.trans
    (hboundary p hp)
  intro x hx
  exact (hConstClosed hx).trans hAtZero

/-- Arbitrary smooth harmonic candidates agreeing on the sphere agree on the
source closed ball; their off-carrier extensions are unrestricted. -/
theorem dirichlet_harmonic_unique_closedBall {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (f g : Domain n → Ambient q) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g U)
    (hboundary : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, f x = g x)
    (hfHarmonic : ∀ x ∈ Metric.ball (0 : Domain n) R.val,
      Laplacian.laplacian f x = 0)
    (hgHarmonic : ∀ x ∈ Metric.ball (0 : Domain n) R.val,
      Laplacian.laplacian g x = 0) :
    Set.EqOn f g (Metric.closedBall (0 : Domain n) R.val) := by
  have hZero := dirichlet_harmonic_zero_closedBall hn R U hU hclosed (f - g) (hf.sub hg)
    (fun x hx => sub_eq_zero.mpr (hboundary x hx)) (fun x hx => by
      rw [((hf.contDiffAt (hU.mem_nhds (hclosed (Metric.ball_subset_closedBall hx)))).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).laplacian_sub
        ((hg.contDiffAt (hU.mem_nhds (hclosed (Metric.ball_subset_closedBall hx)))).of_le
          (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))),
        hfHarmonic x hx, hgHarmonic x hx, sub_self])
  intro x hx
  exact sub_eq_zero.mp (hZero x hx)

end HarmonicMaps

end

module

public import HarmonicMaps.Analysis.PoissonClosedBallSmooth
public import HarmonicMaps.Analysis.DirichletClosedSmoothData
public import HarmonicMaps.Analysis.DirichletSmoothData
public import HarmonicMaps.Analysis.SobolevDifference

/-!
# Canonical Poisson Dirichlet assembly

Smooth neighborhood data determine a smooth harmonic replacement on the closed
ball, uniquely on that carrier. The same ambient representative has finite
Sobolev data with its native derivative columns, and its difference from the
datum belongs to the actual zero-boundary graph closure. The integral uses the
canonical radius-weighted radial pushforward of volume.toSphere.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

/-- The canonical closed-ball Dirichlet solution, its finite Sobolev data,
zero-boundary difference and uniqueness share the same actual witnesses. -/
theorem poisson_scaledPolar_dirichlet_assembly {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U) :
    ∃ v : Metric.closedBall (0 : Domain n) R.val → Ambient q,
      Continuous v ∧
      (∀ b : Metric.sphere (0 : Domain n) R.val,
        v ⟨b.val, Metric.sphere_subset_closedBall b.property⟩ = m b.val) ∧
      ∃ w : Domain n → Ambient q,
        (∀ x : Metric.closedBall (0 : Domain n) R.val, w x.val = v x) ∧
        ContDiffOn ℝ ∞ w (Metric.closedBall (0 : Domain n) R.val) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian w x = 0) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) R.val,
          w x = ((R.val ^ 2 - ‖x‖ ^ 2) /
            ((n : ℝ) * (volume : Measure (Domain n)).real
              (Metric.ball 0 1) * R.val)) •
            (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m y
              ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
                (ENNReal.ofReal (R.val ^ (n - 1)) •
                  (volume : Measure (Domain n)).toSphere))) ∧
        MemW12 (ballDomain (0 : Domain n) R.val) w
          (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
        HasZeroBoundaryValues (ballDomain (0 : Domain n) R.val) (m - w)
          (fun x i => fderiv ℝ m x (EuclideanSpace.single i 1) -
            fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
        (∀ z : Domain n → Ambient q,
          ContDiffOn ℝ ∞ z (Metric.closedBall (0 : Domain n) R.val) →
          (∀ x ∈ Metric.sphere (0 : Domain n) R.val, z x = m x) →
          (∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian z x = 0) →
          EqOn z w (Metric.closedBall (0 : Domain n) R.val)) ∧
        (∀ v' : Metric.closedBall (0 : Domain n) R.val → Ambient q,
          (∃ z : Domain n → Ambient q,
            (∀ x : Metric.closedBall (0 : Domain n) R.val, z x.val = v' x) ∧
            ContDiffOn ℝ ∞ z (Metric.closedBall (0 : Domain n) R.val) ∧
            (∀ x ∈ Metric.sphere (0 : Domain n) R.val, z x = m x) ∧
            (∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian z x = 0)) →
          v' = v) := by
  obtain ⟨v, hv, hb, w, hwv, hws, hwh, hwformula⟩ :=
    poisson_scaledPolar_closedBall_smooth hn R U hU hclosed m hm
  have hwb (x : Domain n) (hx : x ∈ Metric.sphere (0 : Domain n) R.val) : w x = m x :=
    (hwv ⟨x, Metric.sphere_subset_closedBall hx⟩).trans (hb ⟨x, hx⟩)
  have hdiff := closed_smooth_zeroBoundaryDifference hn R m w (hm.mono hclosed) hws
    (fun x hx => (hwb x hx).symm)
  have hmW := dirichlet_smoothData_memW12 R U hU hclosed m hm
  have hwW : MemW12 (ballDomain (0 : Domain n) R.val) w
      (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) := by
    simpa only [sub_sub_cancel] using hmW.sub hdiff.1
  have huniq (z : Domain n → Ambient q)
      (hzs : ContDiffOn ℝ ∞ z (Metric.closedBall (0 : Domain n) R.val))
      (hzb : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, z x = m x)
      (hzh : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian z x = 0) :
      EqOn z w (Metric.closedBall (0 : Domain n) R.val) :=
    closed_dirichlet_harmonic_unique_closedBall hn R z w hzs hws
      (fun x hx => (hzb x hx).trans (hwb x hx).symm) hzh hwh
  refine ⟨v, hv, hb, w, hwv, hws, hwh, hwformula, hwW, hdiff, huniq, ?_⟩
  rintro v' ⟨z, hzv, hzs, hzb, hzh⟩
  funext x
  exact (hzv x).symm.trans ((huniq z hzs hzb hzh x.property).trans (hwv x))

end HarmonicMaps
end

module

public import HarmonicMaps.Analysis.PoissonCoordinateWords
public import HarmonicMaps.Analysis.PoissonAngularEulerFields
public import HarmonicMaps.Analysis.PoissonAngularEulerSmooth

/-!
# Closed-ball smoothness of the canonical Poisson solution

Smooth data on a neighborhood of the closed ball determine a continuous
closed-ball solution with a smooth ambient representative on that ball.
The same representative is harmonic inside and equals the literal canonical
scaled-polar Poisson integral there. The measure remains the radius-weighted
radial pushforward of volume.toSphere.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

/-- The canonical Poisson solution is smooth up to the entire closed-ball
boundary for actual smooth neighborhood data, in every source dimension. -/
theorem poisson_scaledPolar_closedBall_smooth {n q : ℕ} (hn : 2 ≤ n)
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
                  (volume : Measure (Domain n)).toSphere))) := by
  obtain ⟨A, hA⟩ := poisson_coordinateSkewGenerators n
  obtain ⟨F, hFc, hFs, hFh, hFi, hFb, hFa⟩ :=
    poisson_coordinateAngular_continuous_family hn R U hU hclosed m hm A
      (fun i j => (hA i j).1)
  obtain ⟨E, hEc, hEs, hFr, hEa, hEr⟩ :=
    poisson_angular_family_euler_fields R A (fun i j => (hA i j).2) F hFc hFs hFh hFa
  have hSmooth := poisson_angular_euler_closed_smooth R A (fun i j => (hA i j).2)
    F E hFc hEc hFs hEs hFr hFa hEa hEr
  refine ⟨fun x => F [] x.val, (hFc []).restrict, ?_, F [], fun _ => rfl,
    (hSmooth []).1, hFh [], ?_⟩
  · intro b
    simpa only [List.map_nil, List.foldr_nil] using hFb [] b
  · intro x hx
    simpa only [List.map_nil, List.foldr_nil] using hFi [] x hx

end HarmonicMaps
end

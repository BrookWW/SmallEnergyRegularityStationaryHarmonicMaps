module

public import HarmonicMaps.Analysis.PoissonAngularWords
public import HarmonicMaps.Analysis.PoissonAngularGeometry

/-!
# Continuous coordinate-angular Poisson fields

All finite coordinate-angular words have continuous representatives on the
closed ball. Their interior derivatives retain the actual angular-word action,
and every word remains harmonic in the open ball. Ambient representatives are
existential auxiliary functions; only their closed-ball values are specified.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace HarmonicMaps

/-- Continuous closed-ball representatives for the entire coordinate-angular
family, with the actual first-order angular recurrence in the interior. -/
theorem poisson_coordinateAngular_continuous_family {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (A : Fin n → Fin n → (Domain n →L[ℝ] Domain n))
    (hA : ∀ i j, star (A i j) = -A i j) :
    let P : Domain n → Ambient q := fun z =>
      ((R.val ^ 2 - ‖z‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
        (∫ y : Domain n, (‖z - y‖ ^ n)⁻¹ • m y
          ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
            (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere))
    let L : (Domain n →L[ℝ] Domain n) → (Domain n → Ambient q) → Domain n → Ambient q :=
      fun B f x => fderiv ℝ f x (B x)
    ∃ F : List (Fin n × Fin n) → Domain n → Ambient q,
      (∀ w, ContinuousOn (F w) (Metric.closedBall (0 : Domain n) R.val)) ∧
      (∀ w, ContDiffOn ℝ ∞ (F w) (Metric.ball (0 : Domain n) R.val)) ∧
      (∀ w x, x ∈ Metric.ball (0 : Domain n) R.val → Laplacian.laplacian (F w) x = 0) ∧
      (∀ w x, x ∈ Metric.ball (0 : Domain n) R.val →
        F w x = (w.map (fun ij => A ij.1 ij.2)).foldr L P x) ∧
      (∀ w (b : Metric.sphere (0 : Domain n) R.val),
        F w b.val = (w.map (fun ij => A ij.1 ij.2)).foldr L m b.val) ∧
      ∀ w i j x, x ∈ Metric.ball (0 : Domain n) R.val →
        fderiv ℝ (F w) x (A i j x) = F ((i, j) :: w) x := by
  classical
  let P : Domain n → Ambient q := fun z =>
    ((R.val ^ 2 - ‖z‖ ^ 2) /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
      (∫ y : Domain n, (‖z - y‖ ^ n)⁻¹ • m y
        ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
          (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere))
  let L : (Domain n →L[ℝ] Domain n) → (Domain n → Ambient q) → Domain n → Ambient q :=
    fun B f x => fderiv ℝ f x (B x)
  let W : List (Fin n × Fin n) → Domain n → Ambient q := fun w =>
    (w.map (fun ij => A ij.1 ij.2)).foldr L P
  have hWords (w : List (Fin n × Fin n)) :=
    poisson_scaledPolar_angularWords hn R U hU hclosed m hm
      (w.map (fun ij => A ij.1 ij.2)) (by
        intro B hB
        obtain ⟨⟨i, j⟩, _, rfl⟩ := List.mem_map.mp hB
        exact hA i j)
  have hCompletion (w : List (Fin n × Fin n)) :
      ∃ v : Metric.closedBall (0 : Domain n) R.val → Ambient q,
        Continuous v ∧
        (∀ x : Metric.ball (0 : Domain n) R.val,
          v ⟨x.val, Metric.ball_subset_closedBall x.property⟩ = W w x.val) ∧
        ∀ b : Metric.sphere (0 : Domain n) R.val,
          v ⟨b.val, Metric.sphere_subset_closedBall b.property⟩ =
            (w.map (fun ij => A ij.1 ij.2)).foldr L m b.val :=
    (hWords w).2.2.2.2.2.exists
  choose V hV using hCompletion
  let F : List (Fin n × Fin n) → Domain n → Ambient q := fun w =>
    Function.extend Subtype.val (V w) (fun _ => 0)
  have hF (w : List (Fin n × Fin n)) (x : Metric.closedBall (0 : Domain n) R.val) :
      F w x.val = V w x := Subtype.val_injective.extend_apply _ _ x
  have hInterior (w : List (Fin n × Fin n)) (x : Domain n)
      (hx : x ∈ Metric.ball (0 : Domain n) R.val) : F w x = W w x :=
    (hF w ⟨x, Metric.ball_subset_closedBall hx⟩).trans ((hV w).2.1 ⟨x, hx⟩)
  have hLocal (w : List (Fin n × Fin n)) (x : Domain n)
      (hx : x ∈ Metric.ball (0 : Domain n) R.val) : F w =ᶠ[nhds x] W w := by
    filter_upwards [Metric.isOpen_ball.eventually_mem hx] with y hy
    exact hInterior w y hy
  refine ⟨F, ?_, ?_, ?_, hInterior, ?_, ?_⟩
  · intro w
    apply continuousOn_iff_continuous_restrict.mpr
    exact (hV w).1.congr (fun x => (hF w x).symm)
  · intro w
    exact (hWords w).2.1.congr (fun x hx => hInterior w x hx)
  · intro w x hx
    rw [(InnerProductSpace.laplacian_congr_nhds (hLocal w x hx)).eq_of_nhds]
    exact (hWords w).2.2.1 x hx
  · intro w b
    exact (hF w ⟨b.val, Metric.sphere_subset_closedBall b.property⟩).trans ((hV w).2.2 b)
  · intro w i j x hx
    rw [(hLocal w x hx).fderiv_eq, hInterior ((i, j) :: w) x hx]
    rfl

end HarmonicMaps
end

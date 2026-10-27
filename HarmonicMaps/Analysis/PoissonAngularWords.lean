module

public import HarmonicMaps.Analysis.PoissonAngularDerivative

/-!
# All angular words of the canonical Poisson integral

Every finite word of real skew-rotation derivatives is the same canonical
integral applied to the corresponding smooth boundary datum. It is harmonic
inside the ball and has a unique continuous completion with all boundary values.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace HarmonicMaps

/-- Every finite angular word has the canonical integral identity, actual
interior smoothness/harmonicity, all-path boundary limits and a unique
continuous completion on the true closed-ball subtype. -/
theorem poisson_scaledPolar_angularWords {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (As : List (Domain n →L[ℝ] Domain n))
    (hAs : ∀ A ∈ As, star A = -A) :
    let P : (Domain n → Ambient q) → Domain n → Ambient q := fun f z =>
      ((R.val ^ 2 - ‖z‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
        (∫ y : Domain n, (‖z - y‖ ^ n)⁻¹ • f y
          ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
            (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere))
    let L : (Domain n →L[ℝ] Domain n) → (Domain n → Ambient q) → Domain n → Ambient q :=
      fun A f x => fderiv ℝ f x (A x)
    let g := As.foldr L m
    let v := As.foldr L (P m)
    ContDiffOn ℝ ∞ g U ∧
    ContDiffOn ℝ ∞ v (Metric.ball (0 : Domain n) R.val) ∧
    (∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian v x = 0) ∧
    (∀ x ∈ Metric.ball (0 : Domain n) R.val, v x = P g x) ∧
    (∀ b ∈ Metric.sphere (0 : Domain n) R.val,
      Tendsto v (nhdsWithin b (Metric.ball (0 : Domain n) R.val)) (nhds (g b))) ∧
    ∃! w : Metric.closedBall (0 : Domain n) R.val → Ambient q,
      Continuous w ∧
      (∀ x : Metric.ball (0 : Domain n) R.val,
        w ⟨x.val, Metric.ball_subset_closedBall x.property⟩ = v x.val) ∧
      ∀ b : Metric.sphere (0 : Domain n) R.val,
        w ⟨b.val, Metric.sphere_subset_closedBall b.property⟩ = g b.val := by
  let P : (Domain n → Ambient q) → Domain n → Ambient q := fun f z =>
    ((R.val ^ 2 - ‖z‖ ^ 2) /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
      (∫ y : Domain n, (‖z - y‖ ^ n)⁻¹ • f y
        ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
          (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere))
  let L : (Domain n →L[ℝ] Domain n) → (Domain n → Ambient q) → Domain n → Ambient q :=
    fun A f x => fderiv ℝ f x (A x)
  have hWords : ∀ Bs : List (Domain n →L[ℝ] Domain n),
      (∀ A ∈ Bs, star A = -A) →
      ContDiffOn ℝ ∞ (Bs.foldr L m) U ∧
      EqOn (Bs.foldr L (P m)) (P (Bs.foldr L m)) (Metric.ball (0 : Domain n) R.val) := by
    intro Bs
    induction Bs with
    | nil =>
      intro _
      exact ⟨hm, fun _ _ => rfl⟩
    | cons A Bs ih =>
      intro hBs
      have hA : star A = -A := hBs A (List.mem_cons_self ..)
      have hTail : ∀ B ∈ Bs, star B = -B :=
        fun B hB => hBs B (List.mem_cons_of_mem _ hB)
      obtain ⟨hg, hEq⟩ := ih hTail
      have hAngular := poisson_scaledPolar_angularDerivative hn R U hU hclosed
        (Bs.foldr L m) hg A hA
      refine ⟨hAngular.1, ?_⟩
      intro x hx
      have hLocal : Bs.foldr L (P m) =ᶠ[nhds x] P (Bs.foldr L m) := by
        filter_upwards [Metric.isOpen_ball.eventually_mem hx] with z hz
        exact hEq hz
      change fderiv ℝ (Bs.foldr L (P m)) x (A x) = P (L A (Bs.foldr L m)) x
      rw [hLocal.fderiv_eq]
      exact hAngular.2.1 x hx
  obtain ⟨hg, hEq⟩ := hWords As hAs
  let g := As.foldr L m
  let v := As.foldr L (P m)
  have hSmoothHarmonic := poisson_scaledPolar_integral_smooth_harmonic hn R U hU hclosed g hg
  have hSmooth : ContDiffOn ℝ ∞ v (Metric.ball (0 : Domain n) R.val) :=
    hSmoothHarmonic.1.congr hEq
  have hHarmonic : ∀ x ∈ Metric.ball (0 : Domain n) R.val,
      Laplacian.laplacian v x = 0 := by
    intro x hx
    have hLocal : v =ᶠ[nhds x] P g := by
      filter_upwards [Metric.isOpen_ball.eventually_mem hx] with z hz
      exact hEq hz
    rw [(InnerProductSpace.laplacian_congr_nhds hLocal).eq_of_nhds]
    exact hSmoothHarmonic.2 x hx
  have hBoundary : ∀ b ∈ Metric.sphere (0 : Domain n) R.val,
      Tendsto v (nhdsWithin b (Metric.ball (0 : Domain n) R.val)) (nhds (g b)) := by
    intro b hb
    apply (poisson_scaledPolar_boundary_tendsto hn R U hU hclosed g hg b hb).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hEq hx).symm
  obtain ⟨w, ⟨hw, hwi, hwb⟩, hwu⟩ :=
    poisson_scaledPolar_continuousClosedBall_existsUnique hn R U hU hclosed g hg
  refine ⟨hg, hSmooth, hHarmonic, hEq, hBoundary, w, ⟨hw, ?_, hwb⟩, ?_⟩
  · intro x
    exact (hwi x).trans (hEq x.property).symm
  · rintro w' ⟨hw', hw'i, hw'b⟩
    apply hwu w'
    refine ⟨hw', ?_, hw'b⟩
    intro x
    exact (hw'i x).trans (hEq x.property)

end HarmonicMaps
end

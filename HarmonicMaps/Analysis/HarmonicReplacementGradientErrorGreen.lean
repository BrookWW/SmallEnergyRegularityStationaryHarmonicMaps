module

public import HarmonicMaps.Analysis.HarmonicReplacementEnergyOrthogonality
public import HarmonicMaps.Analysis.HarmonicGradientErrorGreen

/-!
# Exact Green formula for the actual replacement error

The fixed-scale Poisson witness retains its full source boundary, energy and
uniqueness conclusions. Applying the signed Green identity to that same
witness gives the exact gradient-error formula with coefficient one.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

/-- The actual source replacement keeps orthogonality and obtains the signed
error identity from the same zero-boundary difference and native columns. -/
theorem harmonicReplacement_gradientErrorGreen {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc (ballDomain (0 : Domain n) 1) u Du)
    (hN : TakesValuesIn N (ballDomain (0 : Domain n) 1) u)
    (η : ℝ) (hη : 0 < η) (hηscale : η ^ (1 / 4 : ℝ) ≤ 1 / 4)
    (hsmall : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal η) :
    let m : Domain n → Ambient q := fun x =>
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - η ^ (1 / 4 : ℝ) • y)
    ∃ v : Metric.closedBall (0 : Domain n) (1 / 2 : ℝ) → Ambient q,
      Continuous v ∧
      (∀ b : Metric.sphere (0 : Domain n) (1 / 2 : ℝ),
        v ⟨b.val, Metric.sphere_subset_closedBall b.property⟩ = m b.val) ∧
      ∃ w : Domain n → Ambient q,
        (∀ x : Metric.closedBall (0 : Domain n) (1 / 2 : ℝ), w x.val = v x) ∧
        ContDiffOn ℝ ∞ w (Metric.closedBall (0 : Domain n) (1 / 2 : ℝ)) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ), Laplacian.laplacian w x = 0) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ),
          w x = (((1 / 2 : ℝ) ^ 2 - ‖x‖ ^ 2) /
            ((n : ℝ) * (volume : Measure (Domain n)).real
              (Metric.ball 0 1) * (1 / 2 : ℝ))) •
            (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m y
              ∂((Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict
                (Metric.sphere (0 : Domain n) (1 / 2 : ℝ))))) ∧
        MemW12 (ballDomain (0 : Domain n) (1 / 2 : ℝ)) w
          (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
        HasZeroBoundaryValues (ballDomain (0 : Domain n) (1 / 2 : ℝ)) (m - w)
          (fun x i => fderiv ℝ m x (EuclideanSpace.single i 1) -
            fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
        (∀ z : Domain n → Ambient q,
          ContDiffOn ℝ ∞ z (Metric.closedBall (0 : Domain n) (1 / 2 : ℝ)) →
          (∀ x ∈ Metric.sphere (0 : Domain n) (1 / 2 : ℝ), z x = m x) →
          (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ), Laplacian.laplacian z x = 0) →
          EqOn z w (Metric.closedBall (0 : Domain n) (1 / 2 : ℝ))) ∧
        (∀ v' : Metric.closedBall (0 : Domain n) (1 / 2 : ℝ) → Ambient q,
          (∃ z : Domain n → Ambient q,
            (∀ x : Metric.closedBall (0 : Domain n) (1 / 2 : ℝ), z x.val = v' x) ∧
            ContDiffOn ℝ ∞ z (Metric.closedBall (0 : Domain n) (1 / 2 : ℝ)) ∧
            (∀ x ∈ Metric.sphere (0 : Domain n) (1 / 2 : ℝ), z x = m x) ∧
            (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ), Laplacian.laplacian z x = 0)) →
          v' = v) ∧
        (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
          hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1))) =
          (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
            hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1))) +
          (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
            hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1) -
              fderiv ℝ w x (EuclideanSpace.single i 1))) ∧
        (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
          hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1))) ≤
          ∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x) ∧
        (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
          hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1) -
            fderiv ℝ w x (EuclideanSpace.single i 1))) =
          -(∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
            inner ℝ (Laplacian.laplacian m x) ((m - w) x)) := by
  let m : Domain n → Ambient q := fun x =>
    ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (x - η ^ (1 / 4 : ℝ) • y)
  let R : PositiveRadius := ⟨1 / 2, by norm_num⟩
  let h : PositiveRadius := ⟨η ^ (1 / 4 : ℝ), Real.rpow_pos_of_pos hη _⟩
  have hfinite : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsmall
  obtain ⟨_, _, hm, hclosed, _⟩ := hu.interiorMollification_spec N hN hfinite h hηscale
  obtain ⟨v, hv, hb, w, hwv, hws, hwh, hformula, hwW, hdiff, huniq, hvuniq,
    hidentity, hbound⟩ :=
    harmonicReplacement_energyOrthogonality hn N u Du hu hN η hη hηscale hsmall
  have hgreen := harmonic_gradientError_green R (Metric.ball 0 (3 / 4))
    Metric.isOpen_ball hclosed m w hm hws hwh hdiff
  exact ⟨v, hv, hb, w, hwv, hws, hwh, hformula, hwW, hdiff, huniq, hvuniq,
    hidentity, hbound, hgreen⟩

end HarmonicMaps
end

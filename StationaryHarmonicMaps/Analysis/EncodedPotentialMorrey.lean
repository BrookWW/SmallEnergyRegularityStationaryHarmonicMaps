module

public import StationaryHarmonicMaps.Analysis.OperatorCoefficientEncoding
public import StationaryHarmonicMaps.Analysis.NormalProjectionPotentialBounds

/-!
# The matrix one-form Morrey square in actual Euclidean coefficients

A fixed continuous linear coefficient encoding realizes exactly the sum over
all matrix entries. The extended energy and every truncated-ball supremum
therefore have the source Hilbert--Schmidt meaning.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The encoded one-form's literal gradient-shaped energy equals its true coefficient energy. -/
theorem encoded_operator_field_energy {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (A : Domain n → Fin n → Ambient q →L[ℝ] Ambient q) (S : Set (Domain n)) :
    dirichletEnergy (fun x i => E (A x i)) S =
      ∫⁻ x in S, ENNReal.ofReal (∑ i : Fin n, ∑ j : Fin q,
        ‖A x i (EuclideanSpace.single j 1)‖ ^ 2) := by
  simp only [dirichletEnergy, hsNormSq, hE]

/-- The potential Morrey square is bounded by a target coefficient times the gradient square. -/
theorem encoded_normal_potential_morrey_le {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    {G : Ambient q → Ambient q →L[ℝ] Ambient q} (hG : ContDiff ℝ 1 G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    {D : Set (Domain n)} (hD : D ⊆ Ω.val) :
    criticalGradientMorreySquare (fun x i => E (projectionCommutator
      (G (u x)) (fderiv ℝ G (u x) (Du x i)))) D ≤
      ENNReal.ofReal ((q : ℝ) * (2 * L) ^ 2) * criticalGradientMorreySquare Du D := by
  refine iSup_le fun x => iSup_le fun r => ?_
  change ENNReal.ofReal (r.val ^ (2 - (n : ℤ))) *
    dirichletEnergy (fun x i => E (projectionCommutator
      (G (u x)) (fderiv ℝ G (u x) (Du x i)))) (Metric.ball x.val r.val ∩ D) ≤ _
  rw [encoded_operator_field_energy E hE]
  exact normal_projection_potential_truncated_morrey_le N (Du := Du)
    hN hG hGN hL hDG hD x.property r

/-- A single stationary ball controls the sum of both complete critical Morrey squares. -/
theorem stationary_joint_morrey_square_bound {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hstationary : IsDomainStationary Ω Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    {G : Ambient q → Ambient q →L[ℝ] Ambient q} (hG : ContDiff ℝ 1 G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val) :
    criticalGradientMorreySquare Du (Metric.ball a (3 * R / 4)) +
      criticalGradientMorreySquare (fun x i => E (projectionCommutator
        (G (u x)) (fderiv ℝ G (u x) (Du x i)))) (Metric.ball a (3 * R / 4)) ≤
      (1 + ENNReal.ofReal ((q : ℝ) * (2 * L) ^ 2)) *
        ENNReal.ofReal ((4 : ℝ) ^ (n - 2)) * normalizedEnergy Du a ⟨R, hR⟩ := by
  have hD : Metric.ball a (3 * R / 4) ⊆ Ω.val :=
    (Metric.ball_subset_ball (by linarith only [hR])).trans
      (Metric.ball_subset_closedBall.trans hball)
  have hM := stationary_morrey_bound hn hstationary hu hR hball
  have hA := encoded_normal_potential_morrey_le N (Du := Du) hN hG hGN hL hDG E hE hD
  calc
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ (n - 2)) * normalizedEnergy Du a ⟨R, hR⟩ +
        ENNReal.ofReal ((q : ℝ) * (2 * L) ^ 2) *
          (ENNReal.ofReal ((4 : ℝ) ^ (n - 2)) * normalizedEnergy Du a ⟨R, hR⟩) :=
      add_le_add hM (hA.trans (mul_le_mul_right hM _))
    _ = _ := by ring

end StationaryHarmonicMaps.Analysis

end

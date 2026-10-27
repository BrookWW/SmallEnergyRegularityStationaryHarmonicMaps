module

public import StationaryHarmonicMaps.Frozen.VariationalWeakPoissonEquivalence
public import StationaryHarmonicMaps.Analysis.EncodedPotentialMorrey
public import HolderToCK.Analysis.WeakPoissonLocality

/-!
# Uniform antisymmetric system data from one stationary energy bound

For any prescribed positive system threshold, one epsilon is chosen from
n and the actual target before all maps and balls. The same constructed
potential is skew, locally L² in its true coefficients, satisfies the signed
weak equation and has the required joint critical Morrey smallness.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual target geometry and stationarity produce the complete small system data uniformly. -/
theorem exists_stationary_small_system_data {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactC2EmbeddedTarget q) {η : ℝ} (hη : 0 < η) :
    ∃ (G : Ambient q → Ambient q →L[ℝ] Ambient q) (L : ℝ)
      (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q)) (ε : ℝ),
      0 < ε ∧ ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      (∀ p : N.Carrier, G p.val = N.normalProjection p) ∧ 0 ≤ L ∧
      (∀ y : Ambient q, ‖fderiv ℝ G y‖ ≤ L) ∧
      (∀ (T : Ambient q →L[ℝ] Ambient q) (k : Fin (q * q)),
        E T k = T (EuclideanSpace.single
          ((finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm k).1 1)
          ((finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm k).2) ∧
      (∀ T : Ambient q →L[ℝ] Ambient q,
        ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2) ∧
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
        MemW12Loc Ω u Du →
        (∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet) →
        IsWeaklyHarmonicByTangentVariations N Ω u Du → IsDomainStationary Ω Du →
        ∀ (a : Domain n) (R : ℝ) (hR : 0 < R), Metric.closedBall a R ⊆ Ω.val →
          normalizedEnergy Du a ⟨R, hR⟩ ≤ ENNReal.ofReal ε →
          let A : Domain n → Fin n → Ambient q →L[ℝ] Ambient q :=
            fun x i => projectionCommutator (G (u x)) (fderiv ℝ G (u x) (Du x i))
          (∀ᵐ x ∂volume.restrict Ω.val, ∀ i : Fin n,
            A x i ∈ skewAdjoint (Ambient q →L[ℝ] Ambient q)) ∧
          (∀ i : Fin n, LocallyMemL2 Ω (fun x => E (A x i))) ∧
          HolderToCK.WeakPoissonOn Ω Du (fun x => -(∑ i : Fin n, A x i (Du x i))) ∧
          criticalGradientMorreySquare Du (Metric.ball a (3 * R / 4)) +
            criticalGradientMorreySquare (fun x i => E (A x i))
              (Metric.ball a (3 * R / 4)) ≤ ENNReal.ofReal (η ^ 2) := by
  obtain ⟨G, L, hG, hcG, hGN, hL, hDG, hiff⟩ := N.variational_weakPoisson_equivalence
  obtain ⟨E, hEntries, hEnorm⟩ := exists_operator_coefficient_encoding q
  let M : ℝ := (1 + (q : ℝ) * (2 * L) ^ 2) * (4 : ℝ) ^ (n - 2)
  have hM : 0 < M := by dsimp only [M]; positivity
  let ε : ℝ := η ^ 2 / M
  have hε : 0 < ε := div_pos (pow_pos hη 2) hM
  have hcancel : M * ε = η ^ 2 := by dsimp only [ε]; field_simp [hM.ne']
  have hCoefficient : (1 + ENNReal.ofReal ((q : ℝ) * (2 * L) ^ 2)) *
      ENNReal.ofReal ((4 : ℝ) ^ (n - 2)) = ENNReal.ofReal M := by
    dsimp only [M]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 1 + (q : ℝ) * (2 * L) ^ 2),
      ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : 0 ≤ (q : ℝ) * (2 * L) ^ 2), ENNReal.ofReal_one]
  refine ⟨G, L, E, ε, hε, hG, hcG, hGN, hL, hDG, hEntries, hEnorm, ?_⟩
  intro Ω u Du hu hN hweak hstationary a R hR hball hsmall
  have hproperties := normal_projection_commutator_properties N hu hN hG hcG hGN hL hDG
  have hpde := (hiff hu hN).mp hweak
  have hforcing : (fun x => -(∑ i : Fin n, fderiv ℝ G (u x) (Du x i) (Du x i)))
      =ᵐ[volume.restrict Ω.val]
      (fun x => -(∑ i : Fin n, projectionCommutator (G (u x))
        (fderiv ℝ G (u x) (Du x i)) (Du x i))) := by
    filter_upwards [hproperties] with x hx
    exact congrArg Neg.neg (Finset.sum_congr rfl (fun i _ => (hx i).2.1.symm))
  refine ⟨hproperties.mono (fun x hx i => (hx i).1), ?_,
    hpde.congr (Filter.EventuallyEq.refl _ _) hforcing, ?_⟩
  · intro i K hK hs
    have hA := locallyMemL2_projectionCommutator N hu hN hG hcG hGN hL hDG i K hK hs
    apply hA.of_le_mul (E.continuous.comp_aestronglyMeasurable hA.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun x => E.le_opNorm _)
  · have hJoint := stationary_joint_morrey_square_bound hn N hu hstationary hN hG hGN
      hL hDG E hEnorm hR hball
    rw [hCoefficient] at hJoint
    calc
      _ ≤ ENNReal.ofReal M * normalizedEnergy Du a ⟨R, hR⟩ := hJoint
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal ε := mul_le_mul_right hsmall _
      _ = ENNReal.ofReal (M * ε) := (ENNReal.ofReal_mul hM.le).symm
      _ = ENNReal.ofReal (η ^ 2) := by rw [hcancel]

end StationaryHarmonicMaps.Analysis

end

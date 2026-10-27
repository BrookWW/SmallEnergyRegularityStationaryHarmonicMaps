module

public import StationaryHarmonicMaps.Analysis.AffineMorreyScaling
public import StationaryHarmonicMaps.Geometry.ProjectionCommutator
public import HolderToCK.Analysis.WeakPoissonAffine

/-!
# Positive affine transport of the actual skew weak system

The transported potential has one factor of the dilation, and its forcing
has two. The same pullback carries the explicit weak gradient, every signed
vector test and both complete critical Morrey suprema.
-/

public section

open HarmonicMaps MeasureTheory Set

namespace StationaryHarmonicMaps.Analysis

/-- A columnwise operator estimate gives the real quadratic system forcing bound. -/
theorem system_forcing_norm_le {n q : ℕ}
    (A : Fin n → Ambient q →L[ℝ] Ambient q) (v : Gradient n q) {K : ℝ}
    (hA : ∀ i, ‖A i‖ ≤ K * ‖v i‖) :
    ‖∑ i : Fin n, A i (v i)‖ ≤ K * hsNormSq v := by
  calc
    _ ≤ ∑ i : Fin n, ‖A i (v i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, K * ‖v i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖A i‖ * ‖v i‖ := (A i).le_opNorm _
        _ ≤ (K * ‖v i‖) * ‖v i‖ := mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _)
        _ = K * ‖v i‖ ^ 2 := by ring
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Dilation gives the square factor in the signed weak forcing exactly. -/
theorem system_forcing_smul {n q : ℕ}
    (t : ℝ) (A : Fin n → Ambient q →L[ℝ] Ambient q) (v : Gradient n q) :
    t ^ 2 • (-(∑ i : Fin n, A i (v i))) =
      -(∑ i : Fin n, (t • A i) (t • v i)) := by
  simp only [smul_neg, smul_apply, map_smul,
    smul_smul, ← Finset.smul_sum, pow_two]

/-- The actual Sobolev system and both full Morrey suprema use the same affine pullback. -/
theorem antisymmetric_system_affineBall {n q : ℕ}
    (a b : Domain n) {R t K : ℝ} (ht : 0 < t)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (A : Domain n → Fin n → Ambient q →L[ℝ] Ambient q)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q))
    (hu : MemW12 (ballDomain a R) u Du)
    (hEq : HolderToCK.WeakPoissonOn (ballDomain a R) Du
      (fun x => -(∑ i : Fin n, A x i (Du x i))))
    (hA : ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      ∀ i, ‖A x i‖ ≤ K * ‖Du x i‖)
    (hskew : ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      ∀ i, A x i ∈ skewAdjoint (Ambient q →L[ℝ] Ambient q)) :
    MemW12 (ballDomain b (R / t)) (fun z => u (a + t • (z - b)))
      (fun z i => t • Du (a + t • (z - b)) i) ∧
    HolderToCK.WeakPoissonOn (ballDomain b (R / t))
      (fun z i => t • Du (a + t • (z - b)) i)
      (fun z => -(∑ i : Fin n,
        (t • A (a + t • (z - b)) i) (t • Du (a + t • (z - b)) i))) ∧
    (∀ᵐ z ∂volume.restrict (Metric.ball b (R / t)),
      ∀ i, t • A (a + t • (z - b)) i ∈ skewAdjoint (Ambient q →L[ℝ] Ambient q)) ∧
    criticalGradientMorreySquare (fun z i => t • Du (a + t • (z - b)) i)
        (Metric.ball b (R / t)) +
      criticalGradientMorreySquare (fun z i => E (t • A (a + t • (z - b)) i))
        (Metric.ball b (R / t)) =
      criticalGradientMorreySquare Du (Metric.ball a R) +
        criticalGradientMorreySquare (fun x i => E (A x i)) (Metric.ball a R) := by
  have hBound : ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      ‖-(∑ i : Fin n, A x i (Du x i))‖ ≤ K * hsNormSq (Du x) := by
    filter_upwards [hA] with x hx
    simpa only [norm_neg] using system_forcing_norm_le (A x) (Du x) hx
  have hEq' := hEq.affineBall_pullback hu K hBound b ht
  refine ⟨hu.affineBall_pullback b ht, ?_, ?_, ?_⟩
  · exact hEq'.congr (Filter.EventuallyEq.refl _ _)
      (Filter.Eventually.of_forall fun z => system_forcing_smul t (A (a + t • (z - b)))
        (Du (a + t • (z - b))))
  · filter_upwards [ae_affineBall a b ht R hskew] with z hz i
    have hi := skewAdjoint.mem_iff.mp (hz i)
    apply skewAdjoint.mem_iff.mpr
    simp only [star_smul, star_trivial, hi, smul_neg]
  · rw [criticalGradientMorreySquare_affineBall a b ht R Du,
      criticalGradientMorreySquare_affineBall_encoded_operator E A a b ht R]

end StationaryHarmonicMaps.Analysis

end

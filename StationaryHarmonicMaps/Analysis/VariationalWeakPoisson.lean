module

public import StationaryHarmonicMaps.Analysis.ScalarVectorWeakEquation
public import StationaryHarmonicMaps.Analysis.VariationalVectorEquation
public import HarmonicMaps.EnergyLemmas

/-!
# The signed weak Poisson equation from actual target variations

The normal-extension forcing has a genuine local L¹ bound by the quadratic
Hilbert--Schmidt gradient density. The original tangent-variation predicate
then gives every compact smooth vector test, with the sign `Δu = -B`.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The actual extension derivative forcing is bounded by the same gradient's square density. -/
theorem normal_extension_forcing_norm_le {n q : ℕ}
    (G : Ambient q → Ambient q →L[ℝ] Ambient q) (_hG : ContDiff ℝ 1 G)
    {L : ℝ} (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L)
    (y : Ambient q) (v : Fin n → Ambient q) :
    ‖∑ i : Fin n, fderiv ℝ G y (v i) (v i)‖ ≤ L * hsNormSq v := by
  calc
    _ ≤ ∑ i : Fin n, ‖fderiv ℝ G y (v i) (v i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, L * ‖v i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      calc
        _ ≤ ‖fderiv ℝ G y (v i)‖ * ‖v i‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (L * ‖v i‖) * ‖v i‖ := mul_le_mul_of_nonneg_right
          ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (hDG y) (norm_nonneg _))) (norm_nonneg _)
        _ = L * ‖v i‖ ^ 2 := by ring
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Local Sobolev L² columns produce actual local L¹ forcing, without target-valued assumptions. -/
theorem locallyIntegrableOn_normal_extension_forcing {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (G : Ambient q → Ambient q →L[ℝ] Ambient q) (hG : ContDiff ℝ 1 G)
    {L : ℝ} (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L) :
    LocallyIntegrableOn (fun x => ∑ i : Fin n,
      fderiv ℝ G (u x) (Du x i) (Du x i)) Ω.val volume := by
  apply (locallyIntegrableOn_iff Ω.property.isLocallyClosed).mpr
  intro K hs hK
  have hmu := (hu.2.1 K hK hs).aestronglyMeasurable
  have hDGmeas := (hG.continuous_fderiv (by simp)).comp_aestronglyMeasurable hmu
  have hDi (i : Fin n) := (hu.2.2 i K hK hs).aestronglyMeasurable
  have hAi (i : Fin n) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hDGmeas.prodMk (hDi i))
  have hBi (i : Fin n) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((hAi i).prodMk (hDi i))
  have hBmeas : AEStronglyMeasurable (fun x => ∑ i : Fin n,
      fderiv ℝ G (u x) (Du x i) (Du x i)) (volume.restrict K) :=
    Finset.aestronglyMeasurable_fun_sum _ (fun i _ => hBi i)
  have henergy : Integrable (fun x => ∑ i : Fin n, ‖Du x i‖ ^ 2)
      (volume.restrict K) :=
    integrable_finsetSum _ (fun i _ =>
      (hu.2.2 i K hK hs).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  apply (henergy.const_mul L).mono' hBmeas
  exact Eventually.of_forall (fun x => normal_extension_forcing_norm_le G hG hDG (u x) (Du x))

/-- The actual map variation implies the full signed weak Poisson equation. -/
theorem variational_weakPoissonOn {n q : ℕ} (N : CompactC2EmbeddedTarget q)
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    (hweak : IsWeaklyHarmonicByTangentVariations N Ω u Du)
    (G : Ambient q → Ambient q →L[ℝ] Ambient q) (hG : ContDiff ℝ 1 G)
    (hcG : HasCompactSupport G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p)
    {L : ℝ} (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L) :
    HolderToCK.WeakPoissonOn Ω Du (fun x => -(∑ i : Fin n,
      fderiv ℝ G (u x) (Du x i) (Du x i))) := by
  apply weakPoissonOn_neg_of_separated Ω Du
    (fun x => ∑ i : Fin n, fderiv ℝ G (u x) (Du x i) (Du x i))
    (locallyIntegrableOn_normal_extension_forcing hu G hG hDG)
  intro η hη hcη hsη v
  exact variational_weak_vector_equation N hu hN hweak G hG hcG hGN η hη hcη hsη v

/-- One target-dependent extension and derivative bound give the signed equation for every map. -/
theorem exists_normal_extension_weakPoissonOn {q : ℕ} (N : CompactC2EmbeddedTarget q) :
    ∃ (G : Ambient q → Ambient q →L[ℝ] Ambient q) (L : ℝ),
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      (∀ p : N.Carrier, G p.val = N.normalProjection p) ∧ 0 ≤ L ∧
      (∀ y : Ambient q, ‖fderiv ℝ G y‖ ≤ L) ∧
      ∀ {n : ℕ} {Ω : OpenDomain n} {u : Domain n → Ambient q}
        {Du : Domain n → Gradient n q}, MemW12Loc Ω u Du →
        (∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet) →
        IsWeaklyHarmonicByTangentVariations N Ω u Du →
        HolderToCK.WeakPoissonOn Ω Du (fun x => -(∑ i : Fin n,
          fderiv ℝ G (u x) (Du x i) (Du x i))) := by
  obtain ⟨G, L, hG, hcG, hraw, hL, hDG⟩ :=
    N.exists_global_ambient_normal_projection_extension_bounded_derivative
  have hGN (p : N.Carrier) : G p.val = N.normalProjection p :=
    (hraw p).trans (N.normalProjection_eq_starProjection p).symm
  refine ⟨G, L, hG, hcG, hGN, hL, hDG, ?_⟩
  intro n Ω u Du hu hN hweak
  exact variational_weakPoissonOn N hu hN hweak G hG hcG hGN hDG

end StationaryHarmonicMaps.Analysis

end

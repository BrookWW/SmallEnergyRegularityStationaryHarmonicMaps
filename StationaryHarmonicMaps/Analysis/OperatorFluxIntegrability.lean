module

public import StationaryHarmonicMaps.Analysis.SobolevOperatorTest
public import HolderToCK.Analysis.L2PairingContinuity
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Integrability of actual operator fluxes

An essentially bounded operator coefficient multiplies local L² columns.
The transformed forcing is locally L¹: its first term uses the coefficient
bound and the original L¹ forcing; its remaining terms use L² times L².
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem operator_star_continuous {q : ℕ} : Continuous
    (star : (Ambient q →L[ℝ] Ambient q) → (Ambient q →L[ℝ] Ambient q)) :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Ambient q) (F := Ambient q)).continuous

private theorem operator_norm_star {q : ℕ} (A : Ambient q →L[ℝ] Ambient q) :
    ‖star A‖ = ‖A‖ :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Ambient q) (F := Ambient q)).norm_map A

/-- The actual adjoint operator flux has genuine local L² columns. -/
theorem locallyMemL2_operator_flux {n m q : ℕ} {Ω : OpenDomain n}
    {p : Domain n → Ambient m} {Dp : Domain n → Gradient n m}
    (hp : MemW12Loc Ω p Dp) {M : ℝ}
    (hb : ∀ᵐ x ∂volume.restrict Ω.val, ‖p x‖ ≤ M)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (i : Fin n) :
    LocallyMemL2 Ω (fun x => star (R (p x)) (Du x i)) := by
  intro K hK hsK
  have hP := R.continuous.comp_aestronglyMeasurable (hp.2.1 K hK hsK).aestronglyMeasurable
  have hstarP := (operator_star_continuous (q := q)).comp_aestronglyMeasurable hP
  have hE := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (hstarP.prodMk (hu.2.2 i K hK hsK).aestronglyMeasurable)
  apply (hu.2.2 i K hK hsK).of_le_mul (c := ‖R‖ * |M|) hE
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsK hb] with x hx
  calc
    _ ≤ ‖star (R (p x))‖ * ‖Du x i‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖R (p x)‖ * ‖Du x i‖ := by rw [operator_norm_star]
    _ ≤ (‖R‖ * |M|) * ‖Du x i‖ := by
      gcongr
      exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (hx.trans (le_abs_self M)) (norm_nonneg _))

/-- The actual transformed right side is locally L¹ without an integrability assumption on products. -/
theorem locallyIntegrableOn_operator_flux_rhs {n m q : ℕ} {Ω : OpenDomain n}
    {p : Domain n → Ambient m} {Dp : Domain n → Gradient n m}
    (hp : MemW12Loc Ω p Dp) {M : ℝ}
    (hb : ∀ᵐ x ∂volume.restrict Ω.val, ‖p x‖ ≤ M)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {F : Domain n → Ambient q}
    (hF : LocallyIntegrableOn F Ω.val volume) :
    LocallyIntegrableOn (fun x => star (R (p x)) (F x) +
      ∑ i : Fin n, star (R (Dp x i)) (Du x i)) Ω.val volume := by
  apply (locallyIntegrableOn_iff Ω.property.isLocallyClosed).mpr
  intro K hsK hK
  let μ := volume.restrict K
  have hFK : Integrable F μ := hF.integrableOn_compact_subset hsK hK
  have hP := R.continuous.comp_aestronglyMeasurable (hp.2.1 K hK hsK).aestronglyMeasurable
  have hstarP := (operator_star_continuous (q := q)).comp_aestronglyMeasurable hP
  have hPFmeas := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (hstarP.prodMk hFK.aestronglyMeasurable)
  have hPF : Integrable (fun x => star (R (p x)) (F x)) μ := by
    apply (hFK.norm.const_mul (‖R‖ * |M|)).mono' hPFmeas
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsK hb] with x hx
    calc
      _ ≤ ‖star (R (p x))‖ * ‖F x‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖R (p x)‖ * ‖F x‖ := by rw [operator_norm_star]
      _ ≤ _ := by
        gcongr
        exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (hx.trans (le_abs_self M)) (norm_nonneg _))
  have hterm (i : Fin n) : Integrable (fun x => star (R (Dp x i)) (Du x i)) μ := by
    have hDP : MemLp (fun x => R (Dp x i)) 2 μ :=
      R.lipschitz.comp_memLp (map_zero R) (hp.2.2 i K hK hsK)
    have hstarDP := (operator_star_continuous (q := q)).comp_aestronglyMeasurable
        hDP.aestronglyMeasurable
    have hmeas := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hstarDP.prodMk (hu.2.2 i K hK hsK).aestronglyMeasurable)
    have hprod : MemLp (fun x => ‖R (Dp x i)‖ * ‖Du x i‖) 1 μ :=
      (hu.2.2 i K hK hsK).norm.mul' hDP.norm
    apply (memLp_one_iff_integrable.mp hprod).mono' hmeas
    exact Eventually.of_forall (fun x => by
      calc
        _ ≤ ‖star (R (Dp x i))‖ * ‖Du x i‖ := ContinuousLinearMap.le_opNorm _ _
        _ = _ := by rw [operator_norm_star])
  exact hPF.add (integrable_finsetSum _ (fun i _ => hterm i))

/-- Local L² columns have a genuine whole-space compact derivative pairing. -/
theorem integrable_locallyL2_vector_test {n q : ℕ} {Ω : OpenDomain n}
    (E : Domain n → Gradient n q) (hE : ∀ i : Fin n, LocallyMemL2 Ω (fun x => E x i))
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Ω.val) :
    Integrable (fun x => ∑ i : Fin n,
      inner ℝ (E x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) volume := by
  have hI : IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (E x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) (tsupport ψ) volume := by
    apply integrable_finsetSum
    intro i _hi
    exact HolderToCK.integrable_inner_of_memLp_two (hE i (tsupport ψ) hcψ hsψ)
      (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hcψ.fderiv_apply ℝ (EuclideanSpace.single i 1)))
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hI
  intro x hx
  by_contra hnot
  apply hx
  simp only [fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot, zero_apply,
    inner_zero_right, Finset.sum_const_zero]

/-- A local L¹ vector field has a genuine whole-space compact vector-test pairing. -/
theorem integrable_locallyL1_vector_test {n q : ℕ} {Ω : OpenDomain n}
    {J : Domain n → Ambient q} (hJ : LocallyIntegrableOn J Ω.val volume)
    (ψ : Domain n → Ambient q) (hψ : Continuous ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Ω.val) :
    Integrable (fun x => inner ℝ (J x) (ψ x)) volume := by
  have hJK := hJ.integrableOn_compact_subset hsψ hcψ
  obtain ⟨C, hC⟩ := hcψ.exists_bound_of_continuous hψ
  have hI : IntegrableOn (fun x => inner ℝ (J x) (ψ x)) (tsupport ψ) volume := by
    apply (hJK.norm.mul_const C).mono' (hJK.aestronglyMeasurable.inner hψ.aestronglyMeasurable)
    exact Eventually.of_forall fun x => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _))
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hI
  intro x hx
  by_contra hnot
  apply hx
  change inner ℝ (J x) (ψ x) = 0
  rw [image_eq_zero_of_notMem_tsupport hnot, inner_zero_right]

end StationaryHarmonicMaps.Analysis

end

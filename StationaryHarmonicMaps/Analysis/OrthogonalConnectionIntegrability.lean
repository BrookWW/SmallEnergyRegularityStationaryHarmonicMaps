module

public import StationaryHarmonicMaps.Analysis.OrthogonalCoordinateSystem
public import Mathlib.Analysis.CStarAlgebra.Basic
public import StationaryHarmonicMaps.Analysis.BoundedOperatorProducts

/-!
# Actual integrability of transformed connections

Bounded Sobolev frame coordinates and local L² potential coefficients give
local L² for `P* dP + P* A P`. Its contraction against an actual local L²
one-form is locally L¹ by finite sums of genuine L² products.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

/-- The actual connection has locally L² operator coefficients. -/
theorem locallyMemL2_frame_connection {n m q : ℕ} {Ω : OpenDomain n}
    {p : Domain n → Ambient m} {Dp : Domain n → Gradient n m}
    (hp : MemW12Loc Ω p Dp) {M : ℝ}
    (hb : ∀ᵐ x ∂volume.restrict Ω.val, ‖p x‖ ≤ M)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (A : Domain n → Fin n → Ambient q →L[ℝ] Ambient q)
    (hA : ∀ i, LocallyMemL2 Ω (fun x => A x i)) (i : Fin n) :
    LocallyMemL2 Ω (fun x =>
      star (R (p x)) * R (Dp x i) + star (R (p x)) * A x i * R (p x)) := by
  intro K hK hsK
  let μ := volume.restrict K
  let C := ‖R‖ * |M|
  have hP := R.continuous.comp_aestronglyMeasurable (hp.2.1 K hK hsK).aestronglyMeasurable
  have hstarP : AEStronglyMeasurable (fun x => star (R (p x))) μ :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Ambient q)
      (F := Ambient q)).continuous.comp_aestronglyMeasurable hP
  have hPb : ∀ᵐ x ∂μ, ‖R (p x)‖ ≤ C := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsK hb] with x hx
    exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (hx.trans (le_abs_self M)) (norm_nonneg _))
  have hstarNorm (T : Ambient q →L[ℝ] Ambient q) : ‖star T‖ = ‖T‖ :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Ambient q) (F := Ambient q)).norm_map T
  have hD : MemLp (fun x => R (Dp x i)) 2 μ :=
    R.lipschitz.comp_memLp (map_zero R) (hp.2.2 i K hK hsK)
  have hstarPb : ∀ᵐ x ∂μ, ‖star (R (p x))‖ ≤ C := by
    filter_upwards [hPb] with x hx
    rw [hstarNorm]
    exact hx
  exact memLp_two_bounded_connection hP hPb hstarP hstarPb hD (hA i K hK hsK)

/-- A true local L² operator one-form contracts with local L² columns to a local L¹ field. -/
theorem locallyIntegrableOn_operator_contraction {n q : ℕ} {Ω : OpenDomain n}
    (Z : Domain n → Fin n → Ambient q →L[ℝ] Ambient q)
    (hZ : ∀ i, LocallyMemL2 Ω (fun x => Z x i))
    (F : Domain n → Gradient n q)
    (hF : ∀ i, LocallyMemL2 Ω (fun x => F x i)) :
    LocallyIntegrableOn (fun x => ∑ i : Fin n, Z x i (F x i)) Ω.val volume := by
  apply (locallyIntegrableOn_iff Ω.property.isLocallyClosed).mpr
  intro K hsK hK
  apply integrable_finsetSum
  intro i _
  have hZi := hZ i K hK hsK
  have hFi := hF i K hK hsK
  have hmeas := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (hZi.aestronglyMeasurable.prodMk hFi.aestronglyMeasurable)
  have hprod : MemLp (fun x => ‖Z x i‖ * ‖F x i‖) 1 (volume.restrict K) :=
    hFi.norm.mul' hZi.norm
  apply (memLp_one_iff_integrable.mp hprod).mono' hmeas
  exact Eventually.of_forall fun x => (Z x i).le_opNorm _

end StationaryHarmonicMaps.Analysis

end

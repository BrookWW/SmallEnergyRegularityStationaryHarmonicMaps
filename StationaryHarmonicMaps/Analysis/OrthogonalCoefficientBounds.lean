module

public import StationaryHarmonicMaps.Analysis.OperatorCoefficientCoordinates
public import StationaryHarmonicMaps.Geometry.OrthogonalFluxAlgebra

/-! # Exact coefficient size of an orthogonal frame -/

public section

open HarmonicMaps

namespace StationaryHarmonicMaps.Analysis

/-- Every orthogonal operator preserves the square norm, using its actual adjoint identity. -/
theorem norm_sq_apply_orthogonal {q : ℕ} (P : Ambient q →L[ℝ] Ambient q)
    (hP : star P * P = 1) (v : Ambient q) : ‖P v‖ ^ 2 = ‖v‖ ^ 2 := by
  have hinv : star P (P v) = v :=
    congrArg (fun T : Ambient q →L[ℝ] Ambient q => T v) hP
  calc
    _ = inner ℝ (P v) (P v) := (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ (star P (P v)) v :=
      (ContinuousLinearMap.adjoint_inner_left P v (P v)).symm
    _ = _ := by rw [hinv, real_inner_self_eq_norm_sq]

/-- Genuine HS coordinates of an orthogonal frame have norm exactly sqrt(q). -/
theorem encoded_orthogonal_frame_norm {q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (P : Ambient q →L[ℝ] Ambient q) (hP : star P * P = 1) :
    ‖E P‖ = Real.sqrt (q : ℝ) := by
  have hsq : ‖E P‖ ^ 2 = (q : ℝ) := by
    rw [hE]
    simp_rw [norm_sq_apply_orthogonal P hP]
    simp only [PiLp.norm_single, norm_one, one_pow, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  calc
    ‖E P‖ = Real.sqrt (‖E P‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = _ := congrArg Real.sqrt hsq

/-- Orthogonality gives the actual essential bound required by the Sobolev product rule. -/
theorem ae_orthogonal_coordinates_bound {n q : ℕ} {Ω : OpenDomain n}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q))
    (R : Ambient (q * q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀ z, E (R z) = z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (p : Domain n → Ambient (q * q))
    (horth : ∀ᵐ x ∂MeasureTheory.volume.restrict Ω.val, star (R (p x)) * R (p x) = 1) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict Ω.val, ‖p x‖ ≤ Real.sqrt (q : ℝ) := by
  filter_upwards [horth] with x hx
  exact le_of_eq ((congrArg norm (hER (p x))).symm.trans
    (encoded_orthogonal_frame_norm E hE (R (p x)) hx))

end StationaryHarmonicMaps.Analysis

end

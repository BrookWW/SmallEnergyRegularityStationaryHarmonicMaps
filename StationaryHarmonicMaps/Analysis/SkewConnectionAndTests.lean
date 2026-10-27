module

public import StationaryHarmonicMaps.Analysis.SobolevOrthogonalFrame
public import StationaryHarmonicMaps.Analysis.OrthogonalCoefficientBounds
public import StationaryHarmonicMaps.Analysis.OrthogonalOperatorBounds
public import StationaryHarmonicMaps.Analysis.BoundedOperatorProducts
public import StationaryHarmonicMaps.Geometry.SkewMatrixPairing

/-!
# Actual skew L2 connections from native orthogonal Sobolev frames

The differentiated orthogonality equation comes from the original native
weak columns. Actual bounded operator products give L2 coefficients before
any connection pairing or divergence test is formed.
-/

public section

open HarmonicMaps MeasureTheory Filter

namespace StationaryHarmonicMaps.Analysis

/-- The genuine transformed connection has actual L2 columns and is skew almost everywhere. -/
theorem frame_connection_memLp_and_skew {n q : ℕ} {Ω : OpenDomain n}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀ z, E (R z) = z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
    (hp : MemW12 Ω p Dp)
    (horth : ∀ᵐ x ∂volume.restrict Ω.val, star (R (p x)) * R (p x) = 1)
    (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q))
    (hA : ∀ i, MemLp (fun x => A x i) 2 (volume.restrict Ω.val))
    (hAskew : ∀ i, ∀ᵐ x ∂volume.restrict Ω.val, star (A x i) = -A x i) :
    (∀ i, MemLp (fun x => star (R (p x)) * R (Dp x i) +
      star (R (p x)) * A x i * R (p x)) 2 (volume.restrict Ω.val)) ∧
    (∀ i, MemLp (fun x => E (star (R (p x)) * R (Dp x i) +
      star (R (p x)) * A x i * R (p x))) 2 (volume.restrict Ω.val)) ∧
    ∀ᵐ x ∂volume.restrict Ω.val, ∀ i,
      star (star (R (p x)) * R (Dp x i) + star (R (p x)) * A x i * R (p x)) =
        -(star (R (p x)) * R (Dp x i) + star (R (p x)) * A x i * R (p x)) := by
  let μ := volume.restrict Ω.val
  have hP := R.continuous.comp_aestronglyMeasurable hp.2.1.aestronglyMeasurable
  have hPb : ∀ᵐ x ∂μ, ‖R (p x)‖ ≤ (1 : ℝ) :=
    horth.mono fun x hx => orthogonal_opNorm_le_one _ hx
  have hstarP : AEStronglyMeasurable (fun x => star (R (p x))) μ :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Ambient q) (F := Ambient q)).continuous.comp_aestronglyMeasurable hP
  have hstarPb : ∀ᵐ x ∂μ, ‖star (R (p x))‖ ≤ (1 : ℝ) := by
    filter_upwards [hPb] with x hx
    have heq : ‖star (R (p x))‖ = ‖R (p x)‖ :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Ambient q) (F := Ambient q)).norm_map _
    rw [heq]
    exact hx
  have hZ (i : Fin n) : MemLp (fun x => star (R (p x)) * R (Dp x i) +
      star (R (p x)) * A x i * R (p x)) 2 μ :=
    memLp_two_bounded_connection hP hPb hstarP hstarPb
      (R.lipschitz.comp_memLp (map_zero R) (hp.2.2 i)) (hA i)
  refine ⟨hZ, fun i => E.lipschitz.comp_memLp (map_zero E) (hZ i), ?_⟩
  have hb := ae_orthogonal_coordinates_bound (Ω := Ω) E R hER hE p horth
  have hD := ae_orthogonal_frame_derivative hp.to_memW12Loc R _ hb horth
  filter_upwards [hD, ae_all_iff.2 hAskew] with x hx hAx i
  have hd : star (star (R (p x)) * R (Dp x i)) = -(star (R (p x)) * R (Dp x i)) := by
    rw [star_mul, star_star]
    exact eq_neg_of_add_eq_zero_left (hx i)
  have ha : star (star (R (p x)) * A x i * R (p x)) =
      -(star (R (p x)) * A x i * R (p x)) := by
    rw [star_mul, star_mul, star_star, hAx i]
    apply ContinuousLinearMap.ext
    intro v
    change star (R (p x)) ((-A x i) (R (p x) v)) =
      -(star (R (p x)) (A x i (R (p x) v)))
    rw [neg_apply, map_neg]
  change ContinuousLinearMap.adjoint _ = _
  rw [map_add]
  change star (star (R (p x)) * R (Dp x i)) +
    star (star (R (p x)) * A x i * R (p x)) = _
  rw [hd, ha]
  abel

end StationaryHarmonicMaps.Analysis

end

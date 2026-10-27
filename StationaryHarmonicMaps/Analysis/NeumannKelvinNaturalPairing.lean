module

public import StationaryHarmonicMaps.Analysis.NeumannKelvinRadialPairing
public import StationaryHarmonicMaps.Analysis.NeumannKelvinGradientPairing
public import StationaryHarmonicMaps.Analysis.NeumannKelvinAdjointLambda
import HarmonicMaps.Analysis.BallAverageDifferentiation

/-!
# The actual full natural test pairing for Neumann reflection

The inversion and radial ordinary pairings combine on the original raw
columns. Their actual smooth adjoint is added to the original test; no
zero trace is imposed on this native whole-ball test.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Set Filter Metric
open StationaryHarmonicMaps.Geometry
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Every original compact smooth double-ball test has an actual native natural adjoint giving the full reflected gradient pairing and preserving each original boundary-cap support. -/
theorem exists_neumann_kelvin_natural_pairing {n q : ℕ} (hn : 2 ≤ n)
    (D : Domain n → Gradient n q)
    (hD : ∀ j, MemLp (fun x => D x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ ball (0 : Domain n) 2) :
    let I := inversion (0 : Domain n) 1
    let B := fun x j => ‖x‖^(n-2) •
      (∫ t in (‖x‖⁻¹)^2..‖x‖⁻¹, t^(n-2) • D (t • x) j)
    let DO := fun x i => ‖x‖^(2-(n : ℝ)) •
      (∑ j : Fin n, (fderiv ℝ I x (EuclideanSpace.single i 1)) j • D (I x) j) +
      ((n : ℝ)-2) • (∑ j : Fin n,
        ((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j • B x j)
    let DU := fun x i => if ‖x‖ ≤ 1 then D x i else DO x i
    ∃ φ : Domain n → Ambient q,
      ContDiff ℝ ∞ φ ∧
      MemW12 (ballDomain (0 : Domain n) 1) φ
        (fun x i => fderiv ℝ φ x (EuclideanSpace.single i 1)) ∧
      (∀ (a : Domain n) (s : ℝ), ‖a‖ = 1 → tsupport ψ ⊆ ball a s →
        ∀ y : Domain n, ‖y‖ < 1 → s < dist y a → fderiv ℝ φ y = 0) ∧
      IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (DU x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) (ball (0 : Domain n) 2) volume ∧
      (∫ x in ball (0 : Domain n) 2, ∑ i : Fin n, inner ℝ (DU x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      ∫ x in ball (0 : Domain n) 1, ∑ i : Fin n, inner ℝ (D x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1) + fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
  classical
  intro I B DO DU
  let ν := volume.restrict (ball (0 : Domain n) 1)
  let μ := volume.restrict (ball (0 : Domain n) 2)
  let A := {x : Domain n | 1 < ‖x‖ ∧ ‖x‖ < 2}
  let S := {x : Domain n | (1/2 : ℝ) < ‖x‖ ∧ ‖x‖ < 1}
  let σ := volume.restrict A
  let W := fun x i => ‖x‖^(2-(n : ℝ)) •
    (∑ j : Fin n, (fderiv ℝ I x (EuclideanSpace.single i 1)) j • D (I x) j)
  let T := fun x i => ∑ j : Fin n,
    ((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j • B x j
  let L := fun y i => ‖y‖^(2-(n : ℝ)) •
    fderiv ℝ ψ (I y) (fderiv ℝ I y (EuclideanSpace.single i 1))
  let R := fun y i => ‖y‖^(n-2) •
    (∫ t in ‖y‖/2..‖y‖^2, t^(-(n : ℝ)) •
      fderiv ℝ ψ (t⁻¹ • y) ((ℝ ∙ y)ᗮ.starProjection (EuclideanSpace.single i 1)))
  let fIn := fun x => ∑ i : Fin n, inner ℝ (D x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))
  let fW := fun x => ∑ i : Fin n, inner ℝ (W x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))
  let fT := fun x => ∑ i : Fin n, inner ℝ (T x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))
  let fL := fun x => ∑ i : Fin n, inner ℝ (D x i) (L x i)
  let fR := fun x => ∑ i : Fin n, inner ℝ (D x i) (R x i)
  have hZeroψ (z : Domain n) (hz : 2 ≤ ‖z‖) : ψ z = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    exact (not_lt_of_ge hz) (mem_ball_zero_iff.mp (hsψ hs))
  obtain ⟨φ, hφ, hφW, _hφEq, _hφNear, hφD, _hφSupport, hφGradSupport⟩ :=
    exists_neumann_kelvin_adjoint_with_reciprocal_gradient 2 (by norm_num : (0 : ℝ)<2) ψ hψ hZeroψ
  obtain ⟨hWI, hLI, hWPair⟩ := neumann_kelvin_inversion_integral_pairing hn D hD ψ hψ
  obtain ⟨hTI, hRI, hTPair⟩ := neumann_kelvin_radial_integral_pairing hn D hD ψ hψ hcψ hsψ
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hAE0 : ∀ᵐ x : Domain n ∂volume, x ≠ 0 := by simp [ae_iff]
  have hLZero : ∀ᵐ y : Domain n ∂volume, y ∈ ball (0 : Domain n) 1 \ S → fL y = 0 := by
    filter_upwards [hAE0] with y hy hyS
    have hyOne : ‖y‖ < 1 := mem_ball_zero_iff.mp hyS.1
    have hyHalf : ‖y‖ ≤ 1/2 := le_of_not_gt (fun h => hyS.2 ⟨h,hyOne⟩)
    have hInv : 2 ≤ ‖I y‖ := by
      rw [show ‖I y‖ = ‖y‖⁻¹ from norm_unit_inversion y]
      have H := one_div_le_one_div_of_le (norm_pos_iff.mpr hy) hyHalf
      norm_num only [one_div, inv_div, div_one] at H
      exact H
    have hNot : I y ∉ tsupport ψ := fun h => (not_lt_of_ge hInv) (mem_ball_zero_iff.mp (hsψ h))
    have hDψ0 : fderiv ℝ ψ (I y) = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hNot
    simp only [fL, L, hDψ0, zero_apply, smul_zero, inner_zero_right, Finset.sum_const_zero]
  have hLFull : Integrable fL ν :=
    hLI.of_ae_sdiff_eq_zero measurableSet_ball.nullMeasurableSet hLZero
  have hSSub : S ⊆ ball (0 : Domain n) 1 := fun y hy => mem_ball_zero_iff.mpr hy.2
  have hLEq : (∫ y, fL y ∂ν) = ∫ y in S, fL y :=
    setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_ball.nullMeasurableSet hSSub hLZero
  have hNat2 : (n : ℝ)-2 = ((n-2 : ℕ) : ℝ) := (Nat.cast_sub hn).symm
  have hφPoint : (fun y => ∑ i : Fin n, inner ℝ (D y i)
      (fderiv ℝ φ y (EuclideanSpace.single i 1))) =ᵐ[ν]
      (fun y => fL y + ((n : ℝ)-2) * fR y) := by
    filter_upwards [hAE0.filter_mono (ae_mono Measure.restrict_le_self)] with y hy
    have hDj (i : Fin n) : fderiv ℝ φ y (EuclideanSpace.single i 1) =
        L y i + ((n : ℝ)-2) • R y i := by
      simpa only [L, R, I, hNat2, Real.rpow_natCast, neumann_tangent_projection_apply] using
        hφD y (EuclideanSpace.single i 1) hy
    simp only [hDj, inner_add_right, real_inner_smul_right, Finset.sum_add_distrib, ← Finset.mul_sum]
    rfl
  have hψW := memW12_ball_of_ambient_c1 (0 : Domain n) 1 ψ (hψ.of_le (by simp))
  have hInI : Integrable fIn ν := integrable_finsetSum _ (fun i _ =>
    HolderToCK.integrable_inner_of_memLp_two (hD i) (hψW.2.2 i))
  have hφI : Integrable (fun y => ∑ i : Fin n, inner ℝ (D y i)
      (fderiv ℝ φ y (EuclideanSpace.single i 1))) ν :=
    integrable_finsetSum _ (fun i _ => HolderToCK.integrable_inner_of_memLp_two (hD i) (hφW.2.2 i))
  have hRadI : Integrable (fun y => ((n : ℝ)-2) * fR y) ν := hRI.const_mul _
  have hOuterEq : (∫ x, fW x + ((n : ℝ)-2) * fT x ∂σ) =
      ∫ y, ∑ i : Fin n, inner ℝ (D y i) (fderiv ℝ φ y (EuclideanSpace.single i 1)) ∂ν := by
    rw [integral_add hWI (hTI.const_mul _), integral_const_mul, hWPair, hTPair, ← hLEq]
    rw [integral_congr_ae hφPoint, integral_add hLFull hRadI, integral_const_mul]
  let C := closedBall (0 : Domain n) 1
  have hInner : μ.restrict C = ν := by
    have hSub : C ⊆ ball (0 : Domain n) 2 := closedBall_subset_ball (by norm_num)
    rw [show μ.restrict C = volume.restrict (C ∩ ball (0 : Domain n) 2) from
      Measure.restrict_restrict measurableSet_closedBall, inter_eq_left.mpr hSub]
    exact (Measure.restrict_congr_set (HarmonicMaps.ball_ae_eq_closedBall (0 : Domain n)
      (by norm_num : (0 : ℝ)<1))).symm
  have hOuter : μ.restrict Cᶜ = σ := by
    rw [show μ.restrict Cᶜ = volume.restrict (Cᶜ ∩ ball (0 : Domain n) 2) from
      Measure.restrict_restrict measurableSet_closedBall.compl]
    congr 1
    ext x
    simp only [C, A, mem_inter_iff, mem_compl_iff, mem_closedBall, mem_ball, dist_zero_right, mem_setOf_eq, not_le]
  have hOutsideI : Integrable (fun x => fW x + ((n : ℝ)-2) * fT x) σ :=
    hWI.add (hTI.const_mul _)
  have hPiece : (fun x => ∑ i : Fin n, inner ℝ (DU x i)
      (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      C.piecewise fIn (fun x => fW x + ((n : ℝ)-2) * fT x) := by
    funext x
    by_cases hx : ‖x‖ ≤ 1
    · simp only [DU, if_pos hx, C, piecewise, mem_closedBall, dist_zero_right, hx, if_true, fIn]
    · simp only [DU, if_neg hx, C, piecewise, mem_closedBall, dist_zero_right, hx, if_false,
        DO, inner_add_left, real_inner_smul_left, Finset.sum_add_distrib, ← Finset.mul_sum, fW, fT, W, T]
  have hGlobal : Integrable (fun x => ∑ i : Fin n, inner ℝ (DU x i)
      (fderiv ℝ ψ x (EuclideanSpace.single i 1))) μ := by
    rw [hPiece]
    apply Integrable.piecewise measurableSet_closedBall
    · change Integrable fIn (μ.restrict C)
      rw [hInner]
      exact hInI
    · change Integrable (fun x => fW x + ((n : ℝ)-2) * fT x) (μ.restrict Cᶜ)
      rw [hOuter]
      exact hOutsideI
  refine ⟨φ, hφ, hφW, hφGradSupport, hGlobal, ?_⟩
  rw [hPiece, integral_piecewise measurableSet_closedBall
    (by change Integrable fIn (μ.restrict C); rw [hInner]; exact hInI)
    (by change Integrable (fun x => fW x + ((n : ℝ)-2) * fT x) (μ.restrict Cᶜ); rw [hOuter]; exact hOutsideI)]
  change (∫ x, fIn x ∂μ.restrict C) +
    (∫ x, fW x + ((n : ℝ)-2) * fT x ∂μ.restrict Cᶜ) = _
  rw [hInner, hOuter, hOuterEq, ← integral_add hInI hφI]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [fIn, inner_add_right, Finset.sum_add_distrib]

end StationaryHarmonicMaps.Analysis

end

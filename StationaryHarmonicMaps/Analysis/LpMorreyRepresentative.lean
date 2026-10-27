module

public import StationaryHarmonicMaps.Analysis.SobolevLpOscillation
public import StationaryHarmonicMaps.Analysis.CampanatoRepresentative
public import HarmonicMaps.SobolevRestriction
public import HolderToCK.Foundation.BallVolume

/-!
# Continuous representatives from actual Lp gradient growth

The Sobolev L1 Poincare estimate converts the displayed HS-gradient Lp growth
to the literal mean-oscillation bound. Exact ball volumes and real-power
identities retain the gradient amplitude, including zero amplitude.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology

namespace StationaryHarmonicMaps

private theorem lp_morrey_radius_scale {n : ℕ} {p α K r V : ℝ}
    (hp : 0 < p) (hK : 0 ≤ K) (hr : 0 < r) (hV : 0 < V) :
    r * (((r ^ n * V)⁻¹ * (K ^ p * r ^ ((n : ℝ) - p + p * α))) ^ (1 / p)) =
      V ^ (-(1 / p)) * K * r ^ α := by
  have hradius : (r ^ n)⁻¹ * r ^ ((n : ℝ) - p + p * α) =
      r ^ (p * (α - 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hr.le, ← Real.rpow_add hr]
    congr 1
    ring
  have hfactor : (r ^ n * V)⁻¹ * (K ^ p * r ^ ((n : ℝ) - p + p * α)) =
      V⁻¹ * K ^ p * r ^ (p * (α - 1)) := by
    calc
      _ = V⁻¹ * K ^ p * ((r ^ n)⁻¹ * r ^ ((n : ℝ) - p + p * α)) := by
        rw [mul_inv_rev]
        ring
      _ = _ := by rw [hradius]
  have hradiusRoot : r * (r ^ (p * (α - 1))) ^ (1 / p) = r ^ α := by
    calc
      _ = r ^ (1 : ℝ) * r ^ ((p * (α - 1)) * (1 / p)) := by
        rw [← Real.rpow_mul hr.le, Real.rpow_one]
      _ = r ^ (1 + (p * (α - 1)) * (1 / p)) := (Real.rpow_add hr _ _).symm
      _ = _ := by
        congr 1
        field_simp [hp.ne']
        ring
  calc
    _ = (V⁻¹) ^ (1 / p) * (K ^ p) ^ (1 / p) *
        (r * (r ^ (p * (α - 1))) ^ (1 / p)) := by
      rw [hfactor, Real.mul_rpow
        (mul_nonneg (inv_nonneg.mpr hV.le) (Real.rpow_nonneg hK _))
        (Real.rpow_nonneg hr.le _),
        Real.mul_rpow (inv_nonneg.mpr hV.le) (Real.rpow_nonneg hK _)]
      ring
    _ = _ := by
      rw [hradiusRoot, one_div, Real.rpow_rpow_inv hK hp.ne',
        ← Real.rpow_neg_eq_inv_rpow]

/-- A genuine one-ball Lp gradient growth bound supplies mean oscillation. -/
theorem sobolev_meanOscillation_of_lp_growth {n q : ℕ} (a : Domain n)
    {r p α K : ℝ} (hr : 0 < r) (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2) (hK : 0 ≤ K)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a r) u Du)
    (hgrowth : (∫ x in Metric.ball a r, (Real.sqrt (hsNormSq (Du x))) ^ p) ≤
      K ^ p * r ^ ((n : ℝ) - p + p * α)) :
    (⨍ x in Metric.ball a r, ‖u x - (⨍ y in Metric.ball a r, u y)‖) ≤
      (((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) *
        (volume.real (Metric.ball (0 : Domain n) 1)) ^ (-(1 / p))) * K * r ^ α := by
  have hp : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp₁
  have hV : 0 < volume.real (Metric.ball (0 : Domain n) 1) :=
    HolderToCK.ball_volume_real_pos (0 : Domain n) (by norm_num)
  have hmeanNonneg :
      0 ≤ (⨍ x in Metric.ball a r, (Real.sqrt (hsNormSq (Du x))) ^ p) := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun _x => Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hmean : (⨍ x in Metric.ball a r, (Real.sqrt (hsNormSq (Du x))) ^ p) ≤
      (volume.real (Metric.ball a r))⁻¹ *
        (K ^ p * r ^ ((n : ℝ) - p + p * α)) := by
    simpa only [setAverage_eq, smul_eq_mul] using
      mul_le_mul_of_nonneg_left hgrowth
        (inv_nonneg.mpr (show 0 ≤ volume.real (Metric.ball a r) from ENNReal.toReal_nonneg))
  have hroot := Real.rpow_le_rpow hmeanNonneg hmean (one_div_nonneg.mpr hp.le)
  have hconstant : 0 ≤ (2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ) := by positivity
  calc
    _ ≤ ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) * r *
        (⨍ x in Metric.ball a r, (Real.sqrt (hsNormSq (Du x))) ^ p) ^ (1 / p) :=
      sobolev_ballAverage_oscillation_le_lp_hs a hr hp₁ hp₂ hu
    _ ≤ ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) *
        (r * (((volume.real (Metric.ball a r))⁻¹ *
          (K ^ p * r ^ ((n : ℝ) - p + p * α))) ^ (1 / p))) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hroot (mul_nonneg hconstant hr.le)
    _ = _ := by
      rw [HolderToCK.ball_volume_real a hr, lp_morrey_radius_scale hp hK hr hV]
      ring

/-- Actual all-center Lp gradient growth gives the unique continuous representative.
The constant is chosen before the map, its amplitude and the reference radius. -/
theorem existsUnique_continuous_representative_of_lp_gradient_growth
    (n : ℕ) (p α : ℝ) (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2)
    (hα : 0 < α) (_hαOne : α < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
        (K r₀ : ℝ),
        MemW12Loc (⟨Set.univ, isOpen_univ⟩ : OpenDomain n) u Du →
        0 ≤ K → 0 < r₀ →
        (∀ (x : Domain n) (r : ℝ), 0 < r → r ≤ r₀ →
          (∫ y in Metric.ball x r, (Real.sqrt (hsNormSq (Du y))) ^ p) ≤
            K ^ p * r ^ ((n : ℝ) - p + p * α)) →
        ∃! w : Domain n → Ambient q,
          Continuous w ∧ w =ᵐ[volume] u ∧
          (∀ x, Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, u y)
            (𝓝[>] (0 : ℝ)) (𝓝 (w x))) ∧
          (∀ (x : Domain n) (r : ℝ), 0 < r → r ≤ r₀ →
            ‖(⨍ y in Metric.ball x r, u y) - w x‖ ≤ C * K * r ^ α) ∧
          (∀ x y : Domain n, dist x y ≤ r₀ / 4 →
            ‖w x - w y‖ ≤ C * K * (dist x y) ^ α) := by
  let D : ℝ := ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) *
    (volume.real (Metric.ball (0 : Domain n) 1)) ^ (-(1 / p))
  let T : ℝ := (2 : ℝ) ^ n / (1 - (1 / 2 : ℝ) ^ α)
  let H : ℝ := meanOscillationHolderConstant n α
  let C : ℝ := 1 + (1 + |T| + |H|) * D
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hTD : T * D ≤ C := by
    have hle : T ≤ 1 + |T| + |H| := by
      have hT := le_abs_self T
      have hH := abs_nonneg H
      linarith
    have hm := mul_le_mul_of_nonneg_right hle hD
    dsimp only [C]
    linarith
  have hHD : H * D ≤ C := by
    have hle : H ≤ 1 + |T| + |H| := by
      have hH := le_abs_self H
      have hT := abs_nonneg T
      linarith
    have hm := mul_le_mul_of_nonneg_right hle hD
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro q u Du K r₀ hu hK hr₀ hgrowth
  have hlocal : LocallyIntegrable u volume :=
    locallyIntegrableOn_univ.mp hu.1.1
  have hosc : ∀ (x : Domain n) (r : ℝ), 0 < r → r ≤ r₀ →
      (⨍ y in Metric.ball x r, ‖u y - (⨍ z in Metric.ball x r, u z)‖) ≤
        (D * K) * r ^ α := by
    intro x r hr hrr₀
    have hW : MemW12 (ballDomain x r) u Du := hu.memW12_ball (subset_univ _)
    exact sobolev_meanOscillation_of_lp_growth x hr hp₁ hp₂ hK hW (hgrowth x r hr hrr₀)
  obtain ⟨w, hw, _⟩ := existsUnique_continuous_representative_of_meanOscillation
    u hlocal hα (mul_nonneg hD hK) hr₀ hosc
  refine ⟨w, ⟨hw.1, hw.2.1, hw.2.2.1, ?_, ?_⟩, ?_⟩
  · intro x r hr hrr₀
    calc
      ‖(⨍ y in Metric.ball x r, u y) - w x‖ ≤
          ((2 : ℝ) ^ n * (D * K)) * r ^ α / (1 - (1 / 2 : ℝ) ^ α) :=
        hw.2.2.2.1 x r hr hrr₀
      _ = (T * D) * K * r ^ α := by dsimp only [T]; ring
      _ ≤ C * K * r ^ α := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hTD hK) (Real.rpow_nonneg hr.le _)
  · intro x y hdist
    calc
      ‖w x - w y‖ ≤ H * (D * K) * (dist x y) ^ α :=
        hw.2.2.2.2 x y hdist
      _ = (H * D) * K * (dist x y) ^ α := by ring
      _ ≤ C * K * (dist x y) ^ α := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hHD hK) (Real.rpow_nonneg dist_nonneg _)
  · intro v hv
    exact MeasureTheory.Measure.eq_of_ae_eq (hv.2.1.trans hw.2.1.symm) hv.1 hw.1

end StationaryHarmonicMaps

end

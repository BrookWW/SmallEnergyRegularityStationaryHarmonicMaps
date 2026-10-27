module

public import StationaryHarmonicMaps.Analysis.HardyLittlewoodLp
public import StationaryHarmonicMaps.Analysis.HilbertSchmidtEncoding
public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds

/-!
# Genuine maximal moments of complete Hilbert--Schmidt fields

All original L2 columns supply the full HS square. The actual lower-power
density has its 2/r moment equal to the original HS energy, before the
proved strong maximal estimate is applied. No maximal integrability or
pointwise finiteness is assumed.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original genuine L2 columns produce the actual maximal 2/r moment, AE finiteness and all-radius average domination. -/
theorem hs_dyadic_maximal_moment_control {n m : ℕ}
    (F : Domain n → Gradient n m) (hF : ∀ i, MemLp (fun x => F x i) 2 volume)
    {r : ℝ} (hr : 0 < r) (hrTwo : r < 2) :
    let d := fun x => ENNReal.ofReal ((Real.sqrt (hsNormSq (F x)))^r)
    let M := dyadicBallMaximal d
    Measurable M ∧
      (∫⁻ x, (M x)^((2 : ℝ)/r)) ≤
        ENNReal.ofReal (((2 : ℝ)^((2 : ℝ)/r)*((2 : ℝ)/r)/((2 : ℝ)/r-1))*(5 : ℝ)^n) *
          ENNReal.ofReal (∫ x, hsNormSq (F x)) ∧
      (∫⁻ x, (M x)^((2 : ℝ)/r)) < ∞ ∧
      (∀ᵐ x ∂volume, M x ≠ ∞) ∧
      ∀ (x : Domain n) (R : PositiveRadius), centeredBallAverageENN d x R ≤
        ENNReal.ofReal ((2 : ℝ)^n)*M x := by
  intro d M
  have hFlat := memLp_hs_flatten F hF
  have hSqrt (x : Domain n) : Real.sqrt (hsNormSq (F x)) =
      ‖WithLp.toLp 2 (fun k : Fin (n*m) => F x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)‖ := by
    rw [← hs_flatten_norm_sq (F x),Real.sqrt_sq (norm_nonneg _)]
  have hd : AEMeasurable d volume := by
    have H := (hFlat.aestronglyMeasurable.norm.aemeasurable.pow_const r).ennreal_ofReal
    simpa only [d,hSqrt] using H
  have hPower (x : Domain n) : (d x)^((2 : ℝ)/r)=ENNReal.ofReal (hsNormSq (F x)) := by
    dsimp only [d]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      (div_nonneg (by norm_num : (0 : ℝ)≤2) hr.le),
      ← Real.rpow_mul (Real.sqrt_nonneg _),show r*((2 : ℝ)/r)=2 by field_simp,
      Real.rpow_two,Real.sq_sqrt (hsNormSq_nonneg _)]
  have hI := integrable_hsNormSq_of_columns F hF
  have hMoment : (∫⁻ x, (d x)^((2 : ℝ)/r)) = ENNReal.ofReal (∫ x, hsNormSq (F x)) := by
    simp_rw [hPower]
    exact (ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun x => hsNormSq_nonneg _)).symm
  have hFinite : (∫⁻ x, (d x)^((2 : ℝ)/r)) < ∞ := by
    rw [hMoment]
    exact ENNReal.ofReal_lt_top
  have hp : 1 < (2 : ℝ)/r := (lt_div_iff₀ hr).mpr (by simpa only [one_mul] using hrTwo)
  obtain ⟨hM,hBound,hMI,hAE,hBall⟩ := dyadicBallMaximal_strongLp_control d hd hp hFinite
  rw [hMoment] at hBound
  exact ⟨hM,hBound,hMI,hAE,hBall⟩

end StationaryHarmonicMaps.Analysis

end

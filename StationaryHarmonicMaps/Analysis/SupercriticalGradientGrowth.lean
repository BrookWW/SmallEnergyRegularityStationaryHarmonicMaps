module

public import StationaryHarmonicMaps.Analysis.HilbertSchmidtEncoding
public import StationaryHarmonicMaps.Analysis.LpPowerComparison
public import HolderToCK.Foundation.BallVolume

/-!
# Actual higher-Lp Hilbert--Schmidt gradient growth

Every original column contributes to the actual Euclidean full-entry
encoding. Columnwise Lp membership therefore supplies membership for the
full HS norm without identifying it with a Pi or operator norm. Genuine
higher-to-lower Holder comparison gives the precise all-ball quadratic
growth, with the original global s-moment as its amplitude.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual columnwise Lp data give membership for the same complete HS norm at any extended exponent. -/
theorem memLp_hsNorm_of_columns {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {n q : ℕ} (F : X → Gradient n q) (p : ℝ≥0∞)
    (hF : ∀ i,MemLp (fun x=>F x i) p μ) :
    MemLp (fun x=>Real.sqrt (hsNormSq (F x))) p μ := by
  let L : Gradient n q →ₗ[ℝ] Ambient (n*q) :=
    { toFun := fun A=>WithLp.toLp 2 (fun k : Fin (n*q)=>
        A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      map_add' := fun A B=>by ext k;rfl
      map_smul' := fun c A=>by ext k;rfl }
  have hFlat := L.toContinuousLinearMap.lipschitz.comp_memLp (map_zero L) (MemLp.of_eval hF)
  have hNorm (x : X) : Real.sqrt (hsNormSq (F x))=‖L (F x)‖ := by
    rw [← hs_flatten_norm_sq (F x),Real.sqrt_sq (norm_nonneg _)]
    rfl
  simpa only [hNorm,Function.comp_apply,LinearMap.coe_toContinuousLinearMap'] using hFlat.norm

/-- The actual global higher HS moment produces the literal all-center quadratic Morrey growth with the full HS amplitude. -/
theorem global_hs_supercritical_quadratic_growth {n q : ℕ}
    (F : Domain n → Gradient n q) (s : ℝ) (hs : 2≤s)
    (hF : MemLp (fun x=>Real.sqrt (hsNormSq (F x))) (ENNReal.ofReal s) volume) :
    let J := ∫ y,(Real.sqrt (hsNormSq (F y)))^s
    let K := (volume.real (Metric.ball (0 : Domain n) 1))^((1/2 : ℝ)-1/s)*J^(1/s)
    Integrable (fun y=>(Real.sqrt (hsNormSq (F y)))^s) volume ∧
      ∀ (x : Domain n) (r : ℝ),0<r →
        (∫ y in Metric.ball x r,(Real.sqrt (hsNormSq (F y)))^(2 : ℝ))≤
          K^2*r^((n : ℝ)-2+2*(1-(n : ℝ)/s)) := by
  intro J K
  let G := fun x=>Real.sqrt (hsNormSq (F x))
  have hs0 : 0<s := lt_of_lt_of_le (by norm_num : (0 : ℝ)<2) hs
  have hNorm (x : Domain n) : ‖G x‖=G x := Real.norm_of_nonneg (Real.sqrt_nonneg _)
  have hMoment : Integrable (fun x=>(G x)^s) volume := by
    have H := hF.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hs0).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hs0.le,Real.norm_of_nonneg (Real.sqrt_nonneg _)] using H
  refine ⟨hMoment,?_⟩
  intro x r hr
  let μ := volume.restrict (Metric.ball x r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hBall : MemLp G (ENNReal.ofReal s) μ := hF.mono_measure Measure.restrict_le_self
  have hHolder := integral_norm_rpow_le_of_exponent_le G (μ:=μ) (by norm_num : (0 : ℝ)<2) hs hBall
  have hLocalMoment : (∫ y in Metric.ball x r,(G y)^s)≤J :=
    setIntegral_le_integral hMoment (Eventually.of_forall fun y=>Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hJ : 0≤J := integral_nonneg fun y=>Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hV : 0<volume.real (Metric.ball (0 : Domain n) 1) := HolderToCK.ball_volume_real_pos 0 (by norm_num)
  have hMass : μ.real univ=r^n*volume.real (Metric.ball (0 : Domain n) 1) := by
    rw [measureReal_restrict_apply_univ,HolderToCK.ball_volume_real x hr]
  have hK : K^2=(volume.real (Metric.ball (0 : Domain n) 1))^(1-2/s)*J^(2/s) := by
    dsimp only [K]
    rw [mul_pow,← Real.rpow_two,← Real.rpow_mul hV.le,← Real.rpow_two,← Real.rpow_mul hJ]
    congr 2 <;> ring
  have hRadius : (r^n)^(1-2/s)=r^((n : ℝ)-2+2*(1-(n : ℝ)/s)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hr.le]
    congr 1
    ring
  calc
    _ ≤ (μ.real univ)^(1-2/s)*(∫ y in Metric.ball x r,(G y)^s)^(2/s) := by
      simpa only [hNorm] using hHolder
    _ ≤ (μ.real univ)^(1-2/s)*J^(2/s) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (integral_nonneg fun y=>Real.rpow_nonneg (Real.sqrt_nonneg _) _) hLocalMoment (by positivity))
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    _ = _ := by
      rw [hMass,Real.mul_rpow (pow_nonneg hr.le n) hV.le,hRadius,hK]
      ring

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.CriticalLpMorreyPointwise
public import StationaryHarmonicMaps.Analysis.InteriorAverageDifferentiation
public import StationaryHarmonicMaps.Analysis.BallSuperlevelMeasure

/-!
# Geometric value tails from actual lower-power critical growth

The same original values are identified at Lebesgue points. A large value
forces an actual lower-power energy-average superlevel. The real Lp
energy of the original graph controls that superlevel's measure.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem dyadic_lp_energy_level_ratio (n m : ℕ) (p : ℝ) (hp : 0<p)
    {η : ℝ} (hη : 0<η) :
    ((5 : ℝ)^n/(16*η*(2 : ℝ)^m)^p)*η^p≤
      (5 : ℝ)^n*((1/2 : ℝ)^p)^m := by
  let L := (16*η*(2 : ℝ)^m)^p
  have hL : 0<L := Real.rpow_pos_of_pos (by positivity) _
  have hPow : ((1/2 : ℝ)^p)^m*((2 : ℝ)^m)^p=1 := by
    rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ)≤1/2) p m,
      ←Real.mul_rpow (pow_nonneg (by norm_num : (0 : ℝ)≤1/2) m) (pow_nonneg (by norm_num : (0 : ℝ)≤2) m),←mul_pow]
    norm_num
  have hProd : L*((1/2 : ℝ)^p)^m=(16 : ℝ)^p*η^p := by
    dsimp only [L]
    rw [Real.mul_rpow (by positivity : 0≤16*η) (by positivity : 0≤(2 : ℝ)^m),
      Real.mul_rpow (by norm_num : (0 : ℝ)≤16) hη.le]
    calc
      _=(16 : ℝ)^p*η^p*(((1/2 : ℝ)^p)^m*((2 : ℝ)^m)^p) := by ring
      _=_ := by rw [hPow,mul_one]
  have hSixteen : 1≤(16 : ℝ)^p := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ)≤1)
      (by norm_num : (1 : ℝ)≤16) hp.le
  have hScale : η^p≤L*((1/2 : ℝ)^p)^m := by
    rw [hProd]
    exact le_mul_of_one_le_left (Real.rpow_nonneg hη.le _) hSixteen
  change ((5 : ℝ)^n/L)*η^p≤_
  calc
    _≤((5 : ℝ)^n/L)*(L*((1/2 : ℝ)^p)^m) :=
      mul_le_mul_of_nonneg_left hScale (by positivity)
    _=_ := by field_simp

/-- Critical Lp growth of the actual native gradient gives a genuine
geometric outer-measure tail for the same original centered map. -/
theorem exists_distribution_tail_of_criticalLp_growth (n : ℕ)
    (p : ℝ) (hpOne : 1≤p) (hpTwo : p≤2) :
    ∃C : ℝ,0<C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0<η →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫y in ball a r∩ball (0 : Domain n) 1,(Real.sqrt (hsNormSq (Du y)))^p)≤η^p*r^((n : ℝ)-p)) →
      ∀m : ℕ,volume {x | x∈ball (0 : Domain n) (7/8 : ℝ) ∧
        C*η*((m : ℝ)+1)<‖u x-(⨍y in ball (0 : Domain n) 1,u y)‖}≤
        ENNReal.ofReal ((5 : ℝ)^n*((1/2 : ℝ)^p)^m) := by
  classical
  have hp : 0<p := zero_lt_one.trans_le hpOne
  obtain ⟨C,hC,Hpoint⟩ := exists_pointwise_bound_of_criticalLp_growth n p hpOne hpTwo
  refine ⟨C,hC,?_⟩
  intro q u Du η hu hη hGrowth m
  let B := ball (0 : Domain n) 1
  let μ := volume.restrict B
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let G := fun x=>Real.sqrt (hsNormSq (Du x))
  let f := B.indicator (fun x=>ENNReal.ofReal ((G x)^p))
  let L := (16*η*(2 : ℝ)^m)^p
  have hL : 0<L := Real.rpow_pos_of_pos (by positivity) _
  have hG2 : MemLp G 2 μ := memLp_sqrt_sum_norm_sq Du hu.2.2
  have hGp := memLp_real_of_memL2 G hpTwo hG2
  have hGI : Integrable (fun x=>(G x)^p) μ := by
    simpa only [G,Real.norm_of_nonneg (Real.sqrt_nonneg _)] using
      integrable_norm_rpow_of_memLp_real G hp.le hGp
  let S := {x : Domain n | ∃r : ℝ,0<r ∧ r≤1/16 ∧
    ENNReal.ofReal L*volume (ball x r)≤∫⁻y in ball x r,f y}
  have hMeasure : volume S≤ENNReal.ofReal ((5 : ℝ)^n/L)*∫⁻y,f y :=
    centered_ball_superlevel_measure_le f S (1/16) L hL (fun _ hx=>hx)
  have hTotal : (∫⁻y,f y)≤ENNReal.ofReal (η^p) := by
    rw [lintegral_indicator measurableSet_ball,
      ←ofReal_integral_eq_lintegral_ofReal hGI (Eventually.of_forall fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _)]
    apply ENNReal.ofReal_le_ofReal
    have H := hGrowth 0 (mem_ball_self (by norm_num : (0 : ℝ)<1)) 1 (by norm_num)
    simpa only [inter_self,Real.one_rpow,mul_one] using H
  have huLp : MemLp u 2 μ := hu.2.1
  have hLDT := integrableOn_ae_tendsto_ballAverage_interior u (0 : Domain n)
    (s:=(7/8 : ℝ)) (by norm_num : (0 : ℝ)<1) (by norm_num) (huLp.integrable (by norm_num))
  have hTail : volume {x | x∈ball (0 : Domain n) (7/8 : ℝ) ∧
      C*η*((m : ℝ)+1)<‖u x-(⨍y in ball (0 : Domain n) 1,u y)‖}≤volume S := by
    apply measure_mono_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hLDT] with x hx
    intro hValue
    have hLebesgue : Tendsto (fun r : ℝ=>⨍y in ball x r,u y) (𝓝[>] (0 : ℝ)) (𝓝 (u x)) := by
      simpa only [setAverage_eq,measureReal_def] using hx hValue.1
    have hNot : ¬(∀r : ℝ,0<r → r≤1/16 →
      (∫y in ball x r,(Real.sqrt (hsNormSq (Du y)))^p)≤L*volume.real (ball x r)) := by
      intro hEnergy
      exact (not_le_of_gt hValue.2) (Hpoint q u Du η hu hη.le hGrowth x hValue.1 hLebesgue m hEnergy)
    push Not at hNot
    obtain ⟨r,hr,hrCap,hBad⟩ := hNot
    refine ⟨r,hr,hrCap,?_⟩
    have hSub : ball x r⊆B := by
      intro y hy
      have H := dist_triangle y x (0 : Domain n)
      have hyx : dist y x<r := hy
      have hx0 : dist x (0 : Domain n)<7/8 := hValue.1
      change dist y (0 : Domain n)<1
      linarith only [H,hyx,hx0,hrCap]
    have hLocalI : IntegrableOn (fun y=>(G y)^p) (ball x r) volume :=
      hGI.mono_measure (Measure.restrict_mono_set volume hSub)
    have hEnergyEq : (∫⁻y in ball x r,f y)=ENNReal.ofReal (∫y in ball x r,(G y)^p) := by
      rw [lintegral_indicator measurableSet_ball,Measure.restrict_restrict measurableSet_ball,
        inter_eq_right.mpr hSub]
      exact (ofReal_integral_eq_lintegral_ofReal hLocalI
        (Eventually.of_forall fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _)).symm
    have hProd : ENNReal.ofReal L*volume (ball x r)=ENNReal.ofReal (L*volume.real (ball x r)) := by
      rw [ENNReal.ofReal_mul hL.le,measureReal_def,ENNReal.ofReal_toReal measure_ball_ne_top]
    rw [hProd,hEnergyEq]
    exact ENNReal.ofReal_le_ofReal hBad.le
  calc
    _≤volume S := hTail
    _≤ENNReal.ofReal ((5 : ℝ)^n/L)*∫⁻y,f y := hMeasure
    _≤ENNReal.ofReal ((5 : ℝ)^n/L)*ENNReal.ofReal (η^p) := mul_le_mul_right hTotal _
    _=ENNReal.ofReal (((5 : ℝ)^n/L)*η^p) := (ENNReal.ofReal_mul (by positivity)).symm
    _≤_ := ENNReal.ofReal_le_ofReal (dyadic_lp_energy_level_ratio n m p hp hη)

end StationaryHarmonicMaps.Analysis

end

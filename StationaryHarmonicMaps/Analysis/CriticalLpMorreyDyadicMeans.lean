module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyDyadicMeans
public import StationaryHarmonicMaps.Analysis.LpMorreyRepresentative

/-!
# Actual dyadic means under critical lower-power gradient growth

The original native graph restricts to each contained ball. Its actual
critical Lp gradient growth controls mean oscillation and therefore the
finite sequence of dyadic means, with no reverse Lp-to-L2 estimate.
-/

public section

open HarmonicMaps MeasureTheory Set Metric

namespace StationaryHarmonicMaps.Analysis

/-- Original critical Lp gradient growth controls every contained-ball mean
oscillation uniformly before the map and its amplitude are chosen. -/
theorem meanOscillation_le_of_criticalLp_growth {n q : ℕ}
    (p : ℝ) (hpOne : 1≤p) (hpTwo : p≤2)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (K : ℝ)
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du) (hK : 0≤K)
    (hGrowth : ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,(Real.sqrt (hsNormSq (Du x)))^p)≤K^p*r^((n : ℝ)-p))
    (a : Domain n) (r : ℝ) (hr : 0<r) (hSub : ball a r⊆ball (0 : Domain n) 1) :
    (⨍x in ball a r,‖u x-(⨍y in ball a r,u y)‖)≤
      (((2 : ℝ)^(n+1)*Real.sqrt (n : ℝ))*(volume.real (ball (0 : Domain n) 1))^(-(1/p)))*K := by
  have hLocal : MemW12 (ballDomain a r) u Du := memW12_of_openDomain_subset hu hSub
  have H := hGrowth a (hSub (mem_ball_self hr)) r hr
  rw [inter_eq_left.mpr hSub] at H
  have H' := sobolev_meanOscillation_of_lp_growth (α:=0) a hr hpOne hpTwo hK hLocal
    (by simpa only [mul_zero,add_zero] using H)
  simpa only [Real.rpow_zero,mul_one] using H'

/-- The original lower-power critical graph controls the same actual
means linearly in the number of dyadic scales. -/
theorem exists_dyadic_mean_bound_of_criticalLp_growth (n : ℕ)
    (p : ℝ) (hpOne : 1≤p) (hpTwo : p≤2) :
    ∃C : ℝ,0<C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (K : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤K →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,(Real.sqrt (hsNormSq (Du x)))^p)≤K^p*r^((n : ℝ)-p)) →
      ∀x∈ball (0 : Domain n) (7/8 : ℝ),∀m : ℕ,
        ‖(⨍y in ball x ((1/16 : ℝ)*(1/2 : ℝ)^m),u y)-(⨍y in ball (0 : Domain n) 1,u y)‖≤
          C*K*((m : ℝ)+1) := by
  let B := ((2 : ℝ)^(n+1)*Real.sqrt (n : ℝ))*(volume.real (ball (0 : Domain n) 1))^(-(1/p))
  let H := (2 : ℝ)^n*B
  let J := (16 : ℝ)^n*B
  let C := 1+H+J
  have hH : 0≤H := by dsimp only [H,B];positivity
  have hJ : 0≤J := by dsimp only [J,B];positivity
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro q u Du K hu hK hGrowth x hx m
  let μ := volume.restrict (ball (0 : Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have huLp : MemLp u 2 μ := hu.2.1
  have huI : IntegrableOn u (ball (0 : Domain n) 1) volume := huLp.integrable (by norm_num)
  have hOsc (a : Domain n) (r : ℝ) (hr : 0<r) (hSub : ball a r⊆ball (0 : Domain n) 1) :
      (⨍y in ball a r,‖u y-(⨍z in ball a r,u z)‖)≤B*K :=
    meanOscillation_le_of_criticalLp_growth p hpOne hpTwo u Du K hu hK hGrowth a r hr hSub
  have hSub : ball x (1/16 : ℝ)⊆ball (0 : Domain n) 1 :=
    ball_subset_closedBall.trans (closedBall_sixteenth_subset_unit hx)
  have hHead := ballMean_dyadic_difference_bound u x (by norm_num : (0 : ℝ)<1/16)
    (huI.mono_set hSub) (fun r hr hcap=>hOsc x r hr ((ball_subset_ball hcap).trans hSub)) m
  have hMass : volume.real (ball (0 : Domain n) 1)≤(16 : ℝ)^n*volume.real (ball x (1/16 : ℝ)) := by
    rw [HolderToCK.ball_volume_real 0 (by norm_num : (0 : ℝ)<1),
      HolderToCK.ball_volume_real x (by norm_num : (0 : ℝ)<1/16)]
    rw [one_pow,one_mul,←mul_assoc,←mul_pow]
    norm_num
  have hBase := norm_setAverage_sub_le_mul_meanOscillation u
    (Metric.measure_ball_pos volume x (by norm_num : (0 : ℝ)<1/16)).ne'
    measure_ball_ne_top measure_ball_ne_top hSub huI hMass
  have hBase' : ‖(⨍y in ball x (1/16 : ℝ),u y)-(⨍y in ball (0 : Domain n) 1,u y)‖≤J*K :=
    (hBase.trans (mul_le_mul_of_nonneg_left (hOsc 0 1 (by norm_num) (Subset.refl _))
      (by positivity))).trans_eq (by dsimp only [J];ring)
  have hScalar : (m : ℝ)*H+J≤C*((m : ℝ)+1) := by
    have hm : 0≤(m : ℝ) := Nat.cast_nonneg m
    have hJm := mul_nonneg hJ hm
    dsimp only [C]
    nlinarith only [hm,hH,hJm]
  calc
    _≤‖(⨍y in ball x ((1/16 : ℝ)*(1/2 : ℝ)^m),u y)-(⨍y in ball x (1/16 : ℝ),u y)‖+
        ‖(⨍y in ball x (1/16 : ℝ),u y)-(⨍y in ball (0 : Domain n) 1,u y)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤(m : ℝ)*(2 : ℝ)^n*(B*K)+J*K := add_le_add hHead hBase'
    _=((m : ℝ)*H+J)*K := by dsimp only [H];ring
    _≤(C*((m : ℝ)+1))*K := mul_le_mul_of_nonneg_right hScalar hK
    _=_ := by ring

end StationaryHarmonicMaps.Analysis

end

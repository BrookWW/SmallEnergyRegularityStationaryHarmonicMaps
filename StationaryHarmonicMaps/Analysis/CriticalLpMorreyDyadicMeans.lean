module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyDyadicMeans
public import StationaryHarmonicMaps.Analysis.LpMorreyRepresentative
public import StationaryHarmonicMaps.Analysis.EffectiveEuclideanVolume

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

@[expose] def criticalLpMeanOscillationMajorant (n : ℕ) : ℕ :=
  2^(n+1) * (n+1) * (1 + (n+1)^n)

@[expose] def criticalLpDyadicMeanMajorant (n : ℕ) : ℕ :=
  1 + (2^n + 16^n) * criticalLpMeanOscillationMajorant n

theorem criticalLpMeanOscillationCoefficient_le (n : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    ((2 : ℝ)^(n+1)*Real.sqrt (n : ℝ)) *
      (volume.real (ball (0 : Domain n) 1))^(-(1/p)) ≤
        (criticalLpMeanOscillationMajorant n : ℝ) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpPos : 0 < p := zero_lt_one.trans_le hp
  have hpower := euclidean_unit_ball_inverse_rpow_le n (1/p)
    (div_nonneg zero_le_one hpPos.le) ((div_le_one hpPos).mpr hp)
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ)+1 := by
    have Hsq := Real.sq_sqrt hn
    have Hnonneg := Real.sqrt_nonneg (n : ℝ)
    nlinarith only [Hsq, Hnonneg, hn, sq_nonneg (n : ℝ)]
  have H := mul_le_mul (mul_le_mul_of_nonneg_left hsqrt
    (show 0 ≤ (2 : ℝ)^(n+1) by positivity)) hpower
    (Real.rpow_nonneg ENNReal.toReal_nonneg _) (by positivity)
  simpa only [criticalLpMeanOscillationMajorant, Nat.cast_mul, Nat.cast_add,
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using H

theorem exists_dyadic_mean_bound_of_criticalLp_growth_explicit (n : ℕ)
    (p : ℝ) (hpOne : 1≤p) (hpTwo : p≤2) :
    ∃C : ℝ,0<C ∧ C = (criticalLpDyadicMeanMajorant n : ℝ) ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
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
  let C : ℝ := criticalLpDyadicMeanMajorant n
  have hH : 0≤H := by dsimp only [H,B];positivity
  have hJ : 0≤J := by dsimp only [J,B];positivity
  have hC : 0<C := by dsimp only [C, criticalLpDyadicMeanMajorant]; positivity
  have hBBound : B ≤ (criticalLpMeanOscillationMajorant n : ℝ) :=
    criticalLpMeanOscillationCoefficient_le n p hpOne
  have hCBound : 1+H+J ≤ C := by
    have HH := mul_le_mul_of_nonneg_left hBBound (show 0 ≤ (2 : ℝ)^n+(16 : ℝ)^n by positivity)
    have HF : C = 1+((2 : ℝ)^n+(16 : ℝ)^n)*(criticalLpMeanOscillationMajorant n : ℝ) := by
      simp only [C, criticalLpDyadicMeanMajorant, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    rw [HF]
    calc
      1+H+J = 1+((2 : ℝ)^n+(16 : ℝ)^n)*B := by dsimp only [H,J]; ring
      _ ≤ _ := add_le_add_right HH 1
  refine ⟨C,hC,rfl,?_⟩
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
    have hHle : H ≤ C := by linarith only [hCBound, hJ]
    have hJle : J ≤ C := by linarith only [hCBound, hH]
    calc
      _ ≤ (m : ℝ)*C+C := add_le_add (mul_le_mul_of_nonneg_left hHle hm) hJle
      _ = _ := by ring
  calc
    _≤‖(⨍y in ball x ((1/16 : ℝ)*(1/2 : ℝ)^m),u y)-(⨍y in ball x (1/16 : ℝ),u y)‖+
        ‖(⨍y in ball x (1/16 : ℝ),u y)-(⨍y in ball (0 : Domain n) 1,u y)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤(m : ℝ)*(2 : ℝ)^n*(B*K)+J*K := add_le_add hHead hBase'
    _=((m : ℝ)*H+J)*K := by dsimp only [H];ring
    _≤(C*((m : ℝ)+1))*K := mul_le_mul_of_nonneg_right hScalar hK
    _=_ := by ring

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
  obtain ⟨C,hC,_hFormula,H⟩ := exists_dyadic_mean_bound_of_criticalLp_growth_explicit n p hpOne hpTwo
  exact ⟨C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end

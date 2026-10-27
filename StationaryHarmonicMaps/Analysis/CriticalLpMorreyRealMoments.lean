module

public import StationaryHarmonicMaps.Analysis.CriticalLpMorreyIntegerMoments
public import StationaryHarmonicMaps.Analysis.LpPowerComparison

/-!
# All finite real value moments from actual critical Lp growth

One larger positive integer moment is produced from the original graph.
Forward finite-measure Holder comparison gives the desired real moment,
with the same original amplitude, including zero amplitude.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Every positive real interior value moment is genuinely finite and
controlled by the original lower-power critical gradient amplitude. -/
theorem exists_real_moment_bound_of_criticalLp_growth (n : ℕ)
    (p : ℝ) (hpOne : 1≤p) (hpTwo : p≤2) (s : ℝ) (hs : 0<s) :
    ∃C : ℝ,0<C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫y in ball a r∩ball (0 : Domain n) 1,(Real.sqrt (hsNormSq (Du y)))^p)≤η^p*r^((n : ℝ)-p)) →
      MemLp (fun x=>u x-(⨍y in ball (0 : Domain n) 1,u y)) (ENNReal.ofReal s)
        (volume.restrict (ball (0 : Domain n) (7/8 : ℝ))) ∧
      IntegrableOn (fun x=>‖u x-(⨍y in ball (0 : Domain n) 1,u y)‖^s)
        (ball (0 : Domain n) (7/8 : ℝ)) volume ∧
      (∫x in ball (0 : Domain n) (7/8 : ℝ),‖u x-(⨍y in ball (0 : Domain n) 1,u y)‖^s)≤C*η^s := by
  obtain ⟨k,hk⟩ := exists_nat_ge (max s 1)
  have hsk : s≤(k : ℝ) := (le_max_left s 1).trans hk
  have hkOne : 1≤k := by exact_mod_cast (le_max_right s 1).trans hk
  have hkPos : 0<(k : ℝ) := hs.trans_le hsk
  obtain ⟨D,hD,HD⟩ := exists_integer_moment_bound_of_criticalLp_growth n p hpOne hpTwo k hkOne
  let V := volume.real (ball (0 : Domain n) (7/8 : ℝ))
  let C := V^(1-s/k)*D^(s/k)
  have hV : 0<V := HolderToCK.ball_volume_real_pos _ (by norm_num)
  have hC : 0<C := mul_pos (Real.rpow_pos_of_pos hV _) (Real.rpow_pos_of_pos hD _)
  refine ⟨C,hC,?_⟩
  intro q u Du η hu hη hGrowth
  let μ := volume.restrict (ball (0 : Domain n) (7/8 : ℝ))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let f := fun x=>u x-(⨍y in ball (0 : Domain n) 1,u y)
  obtain ⟨hfN,_hIN,hBoundN⟩ := HD q u Du η hu hη hGrowth
  have hf : MemLp f (ENNReal.ofReal (k : ℝ)) μ := by
    simpa only [ENNReal.ofReal_natCast] using hfN
  have hBound : (∫x,‖f x‖^(k : ℝ) ∂μ)≤D*η^(k : ℝ) := by
    simpa only [Real.rpow_natCast] using hBoundN
  have hfs : MemLp f (ENNReal.ofReal s) μ := hf.mono_exponent (ENNReal.ofReal_le_ofReal hsk)
  have hI := integrable_norm_rpow_of_memLp_real f hs.le hfs
  have H := integral_norm_rpow_le_of_exponent_le f hs hsk hf
  have hRoot := Real.rpow_le_rpow (integral_nonneg fun _=>Real.rpow_nonneg (norm_nonneg _) _) hBound
    (div_nonneg hs.le hkPos.le)
  refine ⟨hfs,hI,H.trans ((mul_le_mul_of_nonneg_left hRoot (Real.rpow_nonneg ENNReal.toReal_nonneg _)).trans_eq ?_)⟩
  have hMass : (μ univ).toReal=V := by
    simp only [μ,Measure.restrict_apply_univ,V,measureReal_def]
  rw [hMass,Real.mul_rpow hD.le (Real.rpow_nonneg hη _),←Real.rpow_mul hη]
  have hPower : (k : ℝ)*(s/k)=s := by field_simp
  rw [hPower]
  dsimp only [C,V]
  ring

@[expose] def criticalLpFourMomentMajorant (n : ℕ) : ℕ :=
  (1 + criticalLpIntegerMomentMajorant n 4) * (1 + 2^n)

theorem exists_real_moment_bound_of_criticalLp_growth_four_explicit (n : ℕ)
    (p : ℝ) (hpOne : 1≤p) (hpTwo : p≤2) (s : ℝ) (hs : 0<s) (hsFour : s ≤ 4) :
    ∃C : ℝ,0<C ∧ C = (criticalLpFourMomentMajorant n : ℝ) ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫y in ball a r∩ball (0 : Domain n) 1,(Real.sqrt (hsNormSq (Du y)))^p)≤η^p*r^((n : ℝ)-p)) →
      MemLp (fun x=>u x-(⨍y in ball (0 : Domain n) 1,u y)) (ENNReal.ofReal s)
        (volume.restrict (ball (0 : Domain n) (7/8 : ℝ))) ∧
      IntegrableOn (fun x=>‖u x-(⨍y in ball (0 : Domain n) 1,u y)‖^s)
        (ball (0 : Domain n) (7/8 : ℝ)) volume ∧
      (∫x in ball (0 : Domain n) (7/8 : ℝ),‖u x-(⨍y in ball (0 : Domain n) 1,u y)‖^s)≤C*η^s := by
  let k : ℕ := 4
  have hsk : s ≤ (k : ℝ) := hsFour
  have hkOne : 1 ≤ k := by norm_num [k]
  have hkPos : 0 < (k : ℝ) := by norm_num [k]
  obtain ⟨D,hD,hDFormula,HD⟩ := exists_integer_moment_bound_of_criticalLp_growth_explicit n p hpOne hpTwo k hkOne
  let V := volume.real (ball (0 : Domain n) (7/8 : ℝ))
  let C : ℝ := criticalLpFourMomentMajorant n
  have hV : 0<V := HolderToCK.ball_volume_real_pos _ (by norm_num)
  have hC : 0<C := by dsimp only [C, criticalLpFourMomentMajorant]; positivity
  have hVUpper : V ≤ (2 : ℝ)^n := by
    have hsub : ball (0 : Domain n) (7/8 : ℝ) ⊆ ball (0 : Domain n) 1 := ball_subset_ball (by norm_num)
    exact (ENNReal.toReal_mono measure_ball_ne_top (measure_mono hsub (μ := volume))).trans
      (euclidean_unit_ball_volume_upper_bound n)
  have hpower (x t : ℝ) (hx : 0 ≤ x) (ht : 0 ≤ t) (htOne : t ≤ 1) : x^t ≤ 1+x := by
    by_cases hxOne : x ≤ 1
    · exact (Real.rpow_le_one hx hxOne ht).trans (le_add_of_nonneg_right hx)
    · exact (Real.rpow_le_self_of_one_le (not_le.mp hxOne).le htOne).trans
        (le_add_of_nonneg_left zero_le_one)
  have hsRatio : 0 ≤ s/k := div_nonneg hs.le hkPos.le
  have hsRatioOne : s/k ≤ 1 := (div_le_one hkPos).mpr hsk
  have hVPower : V^(1-s/k) ≤ 1+(2 : ℝ)^n :=
    (hpower V (1-s/k) hV.le (by linarith only [hsRatioOne]) (by linarith only [hsRatio])).trans
      (add_le_add_right hVUpper 1)
  have hDPower : D^(s/k) ≤ 1+D := hpower D (s/k) hD.le hsRatio hsRatioOne
  have hCoeff : V^(1-s/k)*D^(s/k) ≤ C := by
    have H := mul_le_mul hVPower hDPower (Real.rpow_nonneg hD.le _) (by positivity)
    exact H.trans_eq (by
      rw [hDFormula]
      simp only [C, criticalLpFourMomentMajorant, k, Nat.cast_mul,
        Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat]
      ring)
  refine ⟨C,hC,rfl,?_⟩
  intro q u Du η hu hη hGrowth
  let μ := volume.restrict (ball (0 : Domain n) (7/8 : ℝ))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let f := fun x=>u x-(⨍y in ball (0 : Domain n) 1,u y)
  obtain ⟨hfN,_hIN,hBoundN⟩ := HD q u Du η hu hη hGrowth
  have hf : MemLp f (ENNReal.ofReal (k : ℝ)) μ := by
    simpa only [ENNReal.ofReal_natCast] using hfN
  have hBound : (∫x,‖f x‖^(k : ℝ) ∂μ)≤D*η^(k : ℝ) := by
    simpa only [Real.rpow_natCast] using hBoundN
  have hfs : MemLp f (ENNReal.ofReal s) μ := hf.mono_exponent (ENNReal.ofReal_le_ofReal hsk)
  have hI := integrable_norm_rpow_of_memLp_real f hs.le hfs
  have H := integral_norm_rpow_le_of_exponent_le f hs hsk hf
  have hRoot := Real.rpow_le_rpow (integral_nonneg fun _=>Real.rpow_nonneg (norm_nonneg _) _) hBound
    (div_nonneg hs.le hkPos.le)
  refine ⟨hfs,hI,H.trans ((mul_le_mul_of_nonneg_left hRoot (Real.rpow_nonneg ENNReal.toReal_nonneg _)).trans ?_)⟩
  have hMass : (μ univ).toReal=V := by
    simp only [μ,Measure.restrict_apply_univ,V,measureReal_def]
  rw [hMass,Real.mul_rpow hD.le (Real.rpow_nonneg hη _),←Real.rpow_mul hη]
  have hPower : (k : ℝ)*(s/k)=s := by field_simp
  rw [hPower]
  calc
    V^(1-s/k)*(D^(s/k)*η^s) = (V^(1-s/k)*D^(s/k))*η^s := by ring
    _ ≤ C*η^s := mul_le_mul_of_nonneg_right hCoeff (Real.rpow_nonneg hη _)

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.AffineHSMoment
public import StationaryHarmonicMaps.Analysis.LpPowerComparison
public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds
public import StationaryHarmonicMaps.Analysis.CriticalMorreyMeanOscillation
public import HarmonicMaps.SobolevRestriction

/-!
# Actual critical Lp gradient growth under positive affine pullback

The literal HS-gradient norm has its true multiplier and Jacobian. Growth
on all ambient balls up to twice a reference radius gives all truncated
queries of the same pulled-back unit-ball graph; large queries use its
actual total energy and the nonnegative critical radius exponent.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric

namespace StationaryHarmonicMaps.Analysis

/-- Positive affine pullback has the exact norm-power gradient integral. -/
theorem integral_lp_gradient_affineBall {n q : ℕ} (a b : Domain n) {t : ℝ}
    (ht : 0<t) (R p : ℝ) (F : Domain n → Gradient n q) :
    (∫x in ball b (R/t),(Real.sqrt (hsNormSq (fun i=>t • F (a+t • (x-b)) i)))^p)=
      (t^n)⁻¹*t^p*(∫x in ball a R,(Real.sqrt (hsNormSq (F x)))^p) := by
  have hPoint (A : Gradient n q) : (Real.sqrt (hsNormSq (fun i=>t • A i)))^p=
      t^p*(Real.sqrt (hsNormSq A))^p := by
    rw [hsNormSq_const_smul,Real.sqrt_mul (sq_nonneg t),Real.sqrt_sq ht.le,
      Real.mul_rpow ht.le (Real.sqrt_nonneg _)]
  simp_rw [hPoint]
  rw [integral_const_mul,integral_affineBall a b ht R (fun x=>(Real.sqrt (hsNormSq (F x)))^p)]
  simp only [smul_eq_mul]
  ring

/-- Original all-center local critical Lp growth gives complete truncated
critical growth of the actual rescaled native unit-ball gradient. -/
theorem affine_unit_truncated_criticalLp_growth {n q : ℕ} (hn : 2≤n)
    (p : ℝ) (hpOne : 1≤p) (hpTwo : p≤2)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc (⟨univ,isOpen_univ⟩ : OpenDomain n) u Du)
    (a : Domain n) (R η : ℝ) (hR : 0<R) (hη : 0≤η)
    (hGrowth : ∀ (b : Domain n) (r : ℝ),0<r → r≤2*R →
      (∫x in ball b r,(Real.sqrt (hsNormSq (Du x)))^p)≤η^p*r^((n : ℝ)-p)) :
    let U := fun x=>u (a+R • x)
    let DU := fun x i=>R • Du (a+R • x) i
    MemW12 (ballDomain (0 : Domain n) 1) U DU ∧
      ∀b∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball b r∩ball (0 : Domain n) 1,(Real.sqrt (hsNormSq (DU x)))^p)≤η^p*r^((n : ℝ)-p) := by
  intro U DU
  have hp : 0<p := zero_lt_one.trans_le hpOne
  have hnp : 0≤(n : ℝ)-p := by
    have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
    linarith only [hnR,hpTwo]
  have hNative : MemW12 (ballDomain (0 : Domain n) 1) U DU := by
    simpa only [sub_zero,div_self hR.ne'] using
      (hu.memW12_ball (subset_univ (closedBall a R))).affineBall_pullback (0 : Domain n) hR
  have hIntegral (b : Domain n) (r : ℝ) :
      (∫x in ball b r,(Real.sqrt (hsNormSq (DU x)))^p)=
        (R^n)⁻¹*R^p*(∫x in ball (a+R • b) (R*r),(Real.sqrt (hsNormSq (Du x)))^p) := by
    have hArg (x : Domain n) : a+R • b+R • (x-b)=a+R • x := by rw [smul_sub];abel
    simpa only [mul_div_cancel_left₀ r hR.ne',hArg] using
      integral_lp_gradient_affineBall (a+R • b) b hR (R*r) p Du
  have hFactor : (R^n)⁻¹*R^p*R^((n : ℝ)-p)=1 := by
    rw [←Real.rpow_natCast,←Real.rpow_neg hR.le,←Real.rpow_add hR,←Real.rpow_add hR]
    have hExponent : -(n : ℝ)+p+((n : ℝ)-p)=0 := by ring
    rw [hExponent,Real.rpow_zero]
  have hBound (b : Domain n) (r : ℝ) (hr : 0<r) (hCap : r≤2) :
      (∫x in ball b r,(Real.sqrt (hsNormSq (DU x)))^p)≤η^p*r^((n : ℝ)-p) := by
    rw [hIntegral]
    have H := hGrowth (a+R • b) (R*r) (mul_pos hR hr) (by nlinarith only [hCap,hR])
    have H' := mul_le_mul_of_nonneg_left H (show 0≤(R^n)⁻¹*R^p by positivity)
    exact H'.trans_eq (by
      rw [Real.mul_rpow hR.le hr.le]
      calc
        _=((R^n)⁻¹*R^p*R^((n : ℝ)-p))*(η^p*r^((n : ℝ)-p)) := by ring
        _=_ := by rw [hFactor,one_mul])
  have hLp (b : Domain n) (r : ℝ) :
      IntegrableOn (fun x=>(Real.sqrt (hsNormSq (DU x)))^p) (ball b r) volume := by
    have hF := hu.memW12_ball (subset_univ (closedBall (a+R • b) (R*r)))
    have hPull := hF.affineBall_pullback b hR
    have hArg (x : Domain n) : a+R • b+R • (x-b)=a+R • x := by rw [smul_sub];abel
    have hLocal : MemW12 (ballDomain b r) U DU := by
      simpa only [mul_div_cancel_left₀ r hR.ne',hArg] using hPull
    let μ := volume.restrict (ball b r)
    letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
    have hG : MemLp (fun x=>Real.sqrt (hsNormSq (DU x))) 2 μ := memLp_sqrt_sum_norm_sq DU hLocal.2.2
    change Integrable (fun x=>(Real.sqrt (hsNormSq (DU x)))^p) μ
    simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _)] using
      integrable_norm_rpow_of_memL2 _ hp.le hpTwo hG
  refine ⟨hNative,?_⟩
  intro b _hb r hr
  by_cases hSmall : r≤2
  · exact (setIntegral_mono_set (hLp b r)
      (Eventually.of_forall fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      (Eventually.of_forall fun _ hx=>hx.1)).trans (hBound b r hr hSmall)
  · have hTotal : (∫x in ball (0 : Domain n) 1,(Real.sqrt (hsNormSq (DU x)))^p)≤η^p := by
      simpa only [Real.one_rpow,mul_one] using hBound 0 1 (by norm_num) (by norm_num)
    have hPow : 1≤r^((n : ℝ)-p) := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ)≤1)
        (by linarith only [not_le.mp hSmall] : 1≤r) hnp
    exact (setIntegral_mono_set (hLp 0 1)
      (Eventually.of_forall fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      (Eventually.of_forall fun _ hx=>hx.2)).trans (hTotal.trans
        (le_mul_of_one_le_right (Real.rpow_nonneg hη _) hPow))

end StationaryHarmonicMaps.Analysis

end

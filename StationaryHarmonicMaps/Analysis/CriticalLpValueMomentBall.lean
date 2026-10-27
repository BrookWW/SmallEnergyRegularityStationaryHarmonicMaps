module

public import StationaryHarmonicMaps.Analysis.AffineLpGradientGrowth
public import StationaryHarmonicMaps.Analysis.CriticalLpMorreyRealMoments
public import StationaryHarmonicMaps.Analysis.AffineMeanOscillation

/-!
# Actual lower-power critical value moments on arbitrary balls

The original global native graph is rescaled to a true unit-ball graph.
Its local all-center critical gradient growth supplies every truncated
unit query. Exact ball averages and the true affine Jacobian return the
same original centered values and their scale-correct real moments.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Local critical Lp gradient growth of the original native graph gives
all positive real value moments with the genuine radius-to-dimension factor. -/
theorem exists_local_real_moment_bound_of_criticalLp_growth (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1≤p) (hpTwo : p≤2) (s : ℝ) (hs : 0<s) :
    ∃C : ℝ,0<C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ) (a : Domain n) (R : ℝ),
      MemW12Loc (⟨univ,isOpen_univ⟩ : OpenDomain n) u Du → 0≤η → 0<R →
      (∀ (b : Domain n) (r : ℝ),0<r → r≤2*R →
        (∫x in ball b r,(Real.sqrt (hsNormSq (Du x)))^p)≤η^p*r^((n : ℝ)-p)) →
      let c := ⨍x in ball a R,u x
      MemLp (fun x=>u x-c) (ENNReal.ofReal s) (volume.restrict (ball a ((7/8 : ℝ)*R))) ∧
      IntegrableOn (fun x=>‖u x-c‖^s) (ball a ((7/8 : ℝ)*R)) volume ∧
      (∫x in ball a ((7/8 : ℝ)*R),‖u x-c‖^s)≤C*η^s*R^n := by
  obtain ⟨C,hC,HC⟩ := exists_real_moment_bound_of_criticalLp_growth n p hpOne hpTwo s hs
  refine ⟨C,hC,?_⟩
  intro q u Du η a R hu hη hR hGrowth c
  let U := fun x=>u (a+R • x)
  let DU := fun x i=>R • Du (a+R • x) i
  obtain ⟨hU,hUGrowth⟩ := affine_unit_truncated_criticalLp_growth hn p hpOne hpTwo u Du hu a R η hR hη hGrowth
  obtain ⟨hf,hI,hMoment⟩ := HC q U DU η hU hη hUGrowth
  have hMean : (⨍x in ball (0 : Domain n) 1,U x)=c := by
    simpa only [div_self hR.ne',sub_zero] using average_affineBall a (0 : Domain n) hR R u
  rw [hMean] at hf hI hMoment
  have hBack (x : Domain n) : U ((R⁻¹) • (x-a))-c=u x-c := by
    simp only [U,smul_smul,mul_inv_cancel₀ hR.ne',one_smul,add_sub_cancel]
  have hMemBack : MemLp (fun x=>u x-c) (ENNReal.ofReal s)
      (volume.restrict (ball a ((7/8 : ℝ)*R))) := by
    simpa only [zero_add,div_inv_eq_mul,hBack] using
      memLp_affineBall_exponent (0 : Domain n) a (inv_pos.mpr hR) (7/8) (ENNReal.ofReal s) hf
  have hIBack : IntegrableOn (fun x=>‖u x-c‖^s) (ball a ((7/8 : ℝ)*R)) volume := by
    simpa only [zero_add,div_inv_eq_mul,hBack] using
      integrable_affineBall (0 : Domain n) a (inv_pos.mpr hR) (7/8) hI
  have hScale : (∫x in ball a ((7/8 : ℝ)*R),‖u x-c‖^s)=
      R^n*(∫x in ball (0 : Domain n) (7/8 : ℝ),‖U x-c‖^s) := by
    simpa only [zero_add,div_inv_eq_mul,hBack,inv_pow,inv_inv,smul_eq_mul] using
      integral_affineBall (0 : Domain n) a (inv_pos.mpr hR) (7/8) (fun x=>‖U x-c‖^s)
  refine ⟨hMemBack,hIBack,?_⟩
  rw [hScale]
  exact (mul_le_mul_of_nonneg_left hMoment (pow_nonneg hR.le n)).trans_eq (by ring)

end StationaryHarmonicMaps.Analysis

end

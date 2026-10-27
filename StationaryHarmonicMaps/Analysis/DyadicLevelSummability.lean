module

public import StationaryHarmonicMaps.Analysis.GrandLevelIntegralLimits
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Max

/-!
# Actual summability of all integer dyadic level masses

The genuine finite geometric sum retains negative integer scales.
Its bound is uniform over every finite set of scales, giving the actual
extended full series without a real-sum fallback.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem sum_dyadic_Icc (a b : ℤ) (hab : a≤b) :
    (∑ j ∈ Finset.Icc a b,(2 : ℝ)^j)=(2 : ℝ)^(b+1)-(2 : ℝ)^a := by
  let N := (b+1-a).toNat
  have hN : (N : ℤ)=b+1-a := Int.toNat_of_nonneg (by omega)
  rw [Int.Icc_eq_finset_map,Finset.sum_map]
  change (∑ k ∈ Finset.range N,(2 : ℝ)^(a+(k : ℤ)))=_
  simp_rw [zpow_add₀ (by norm_num : (2 : ℝ)≠0),zpow_natCast]
  rw [← Finset.mul_sum,geom_sum_eq (by norm_num : (2 : ℝ)≠1)]
  norm_num only [show (2 : ℝ)-1=1 by norm_num,div_one]
  rw [mul_sub,mul_one]
  have hPow : (2 : ℝ)^a*(2 : ℝ)^N=(2 : ℝ)^(b+1) := by
    rw [← zpow_natCast,← zpow_add₀ (by norm_num : (2 : ℝ)≠0),hN]
    congr 1
    omega
  rw [hPow,zpow_add₀ (by norm_num : (2 : ℝ)≠0),zpow_one]

/-- Every actual finite set of integer levels has its below-threshold dyadic sum bounded by twice the original nonnegative level. -/
theorem finite_dyadic_lower_level_sum_le (F : Finset ℤ) (T : ℝ) (hT : 0≤T) :
    (∑ j ∈ F,if (2 : ℝ)^j<T then (2 : ℝ)^j else 0)≤2*T := by
  classical
  let S := F.filter (fun j=>(2 : ℝ)^j<T)
  have hFilter : (∑ j ∈ F,if (2 : ℝ)^j<T then (2 : ℝ)^j else 0)=
      ∑ j ∈ S,(2 : ℝ)^j := by rw [Finset.sum_filter]
  rw [hFilter]
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let b := S.max' hS
    have hSub : S⊆Finset.Icc a b := by
      intro j hj
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S j hj,Finset.le_max' S j hj⟩
    have hab : a≤b := Finset.min'_le_max' S hS
    have hb : (2 : ℝ)^b≤T := (Finset.mem_filter.mp (S.max'_mem hS)).2.le
    calc
      _ ≤ ∑ j ∈ Finset.Icc a b,(2 : ℝ)^j :=
        Finset.sum_le_sum_of_subset_of_nonneg hSub (fun j _ _=>(zpow_pos (by norm_num) j).le)
      _ = (2 : ℝ)^(b+1)-(2 : ℝ)^a := sum_dyadic_Icc a b hab
      _ ≤ 2*(2 : ℝ)^b := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ)≠0),zpow_one]
        nlinarith only [(zpow_pos (by norm_num : (0 : ℝ)<2) a).le]
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by norm_num)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.sum_empty]
    positivity

/-- The full literal extended sum over every positive and negative integer scale is at most twice the original extended value. -/
theorem tsum_dyadic_lower_level_le (T : ℝ≥0∞) :
    (∑' j : ℤ,if ENNReal.ofReal ((2 : ℝ)^j)<T then ENNReal.ofReal ((2 : ℝ)^j) else 0)≤2*T := by
  classical
  by_cases hTop : T=∞
  · rw [hTop,ENNReal.mul_top (by norm_num : (2 : ℝ≥0∞)≠0)]
    exact le_top
  · rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    have hCond (j : ℤ) : (ENNReal.ofReal ((2 : ℝ)^j)<T)↔(2 : ℝ)^j<T.toReal :=
      ENNReal.ofReal_lt_iff_lt_toReal (zpow_pos (by norm_num) j).le hTop
    have hEq : (∑ j ∈ F,if ENNReal.ofReal ((2 : ℝ)^j)<T then ENNReal.ofReal ((2 : ℝ)^j) else 0)=
        ENNReal.ofReal (∑ j ∈ F,if (2 : ℝ)^j<T.toReal then (2 : ℝ)^j else 0) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _=>by split_ifs <;> positivity)]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : (2 : ℝ)^j<T.toReal
      · rw [if_pos ((hCond j).mpr hj),if_pos hj]
      · rw [if_neg (fun h=>hj ((hCond j).mp h)),if_neg hj,ENNReal.ofReal_zero]
    rw [hEq]
    calc
      _ ≤ ENNReal.ofReal (2*T.toReal) := ENNReal.ofReal_le_ofReal
        (finite_dyadic_lower_level_sum_le F T.toReal ENNReal.toReal_nonneg)
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_ofNat,ENNReal.ofReal_toReal hTop]

/-- The original measurable extended field controls the actual sum of every integer dyadic level times its superlevel measure. -/
theorem tsum_dyadic_superlevel_mass_le_lintegral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (J : X → ℝ≥0∞) (hJ : Measurable J) :
    (∑' j : ℤ,ENNReal.ofReal ((2 : ℝ)^j)*μ {x | ENNReal.ofReal ((2 : ℝ)^j)<J x}) ≤
      2*(∫⁻ x,J x ∂μ) := by
  classical
  let v := fun (j : ℤ) (x : X) =>
    if ENNReal.ofReal ((2 : ℝ)^j)<J x then ENNReal.ofReal ((2 : ℝ)^j) else 0
  have hMeas (j : ℤ) : Measurable (v j) :=
    Measurable.ite (measurableSet_lt measurable_const hJ) measurable_const measurable_const
  have hInt (j : ℤ) : (∫⁻ x,v j x ∂μ)=
      ENNReal.ofReal ((2 : ℝ)^j)*μ {x | ENNReal.ofReal ((2 : ℝ)^j)<J x} := by
    let S := {x | ENNReal.ofReal ((2 : ℝ)^j)<J x}
    have hS : MeasurableSet S := measurableSet_lt measurable_const hJ
    have hFun : v j=S.indicator (fun _=>ENNReal.ofReal ((2 : ℝ)^j)) := by
      funext x
      by_cases hx : ENNReal.ofReal ((2 : ℝ)^j)<J x
      · simp only [v,if_pos hx,indicator_of_mem (show x∈S from hx)]
      · simp only [v,if_neg hx,indicator_of_notMem (show x∉S from hx)]
    rw [hFun,lintegral_indicator hS,lintegral_const,Measure.restrict_apply_univ]
  calc
    _ = ∑' j : ℤ,∫⁻ x,v j x ∂μ := tsum_congr fun j=>(hInt j).symm
    _ = ∫⁻ x,∑' j : ℤ,v j x ∂μ :=
      (lintegral_tsum (fun j=>(hMeas j).aemeasurable)).symm
    _ ≤ ∫⁻ x,2*J x ∂μ := lintegral_mono fun x=>tsum_dyadic_lower_level_le (J x)
    _ = _ := lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞)≠∞)

end StationaryHarmonicMaps.Analysis

end

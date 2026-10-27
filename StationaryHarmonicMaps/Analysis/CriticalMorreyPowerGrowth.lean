module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds

/-!
# The actual critical supremum from full truncated-ball power growth

Finite original L2 columns make every real truncated energy genuine.
The critical radius power cancels each normalized energy before taking
the literal double extended supremum.
-/

public section

open HarmonicMaps MeasureTheory Set Metric

namespace StationaryHarmonicMaps.Analysis

/-- All actual truncated-ball critical-power bounds control the original
complete critical supremum on the same set and same explicit field. -/
theorem criticalGradientMorreySquare_le_of_truncated_power_growth {n q : ℕ}
    (F : Domain n → Gradient n q) (D : Set (Domain n))
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict D)) (K : ℝ)
    (hGrowth : ∀a∈D,∀r : ℝ,0<r →
      (∫x in ball a r∩D,hsNormSq (F x))≤K*r^((n : ℝ)-2)) :
    criticalGradientMorreySquare F D≤ENNReal.ofReal K := by
  unfold criticalGradientMorreySquare
  refine iSup_le fun a=>iSup_le fun r=>?_
  let S := ball a.val r.val∩D
  have hSI : IntegrableOn (fun x=>hsNormSq (F x)) S volume :=
    integrable_hsNormSq_of_columns F (fun i=>(hF i).mono_measure
      (Measure.restrict_mono_set volume inter_subset_right))
  have hBound := hGrowth a.val a.property r.val r.property
  have hCancel : r.val^((n : ℝ)-2)*r.val^(2-(n : ℤ))=1 := by
    rw [←Real.rpow_intCast,Int.cast_sub,Int.cast_ofNat,Int.cast_natCast,←Real.rpow_add r.property]
    norm_num
  change ENNReal.ofReal (r.val^(2-(n : ℤ)))*dirichletEnergy F S≤_
  rw [dirichletEnergy_eq_ofReal_integral hSI]
  calc
    _≤ENNReal.ofReal (r.val^(2-(n : ℤ)))*ENNReal.ofReal (K*r.val^((n : ℝ)-2)) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal hBound) _
    _=ENNReal.ofReal K := by
      rw [←ENNReal.ofReal_mul (zpow_nonneg r.property.le _)]
      congr 1
      calc
        _=K*(r.val^((n : ℝ)-2)*r.val^(2-(n : ℤ))) := by ring
        _=_ := by rw [hCancel,mul_one]

end StationaryHarmonicMaps.Analysis

end

module

public import HarmonicMaps.Energy
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # Exact HS energy of literal zero extension -/

public section

open HarmonicMaps MeasureTheory Set

namespace StationaryHarmonicMaps.Analysis

theorem hsNormSq_indicator {n q : ℕ} (S : Set (Domain n))
    (F : Domain n → Gradient n q) :
    (fun x=>hsNormSq (S.indicator F x))=S.indicator (fun x=>hsNormSq (F x)) := by
  classical
  funext x
  by_cases hx : x∈S
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx,hsNormSq,Pi.zero_apply,norm_zero,
      zero_pow (by decide : (2 : ℕ)≠0),Finset.sum_const_zero]

theorem integral_hsNormSq_indicator {n q : ℕ} (S : Set (Domain n)) (hS : MeasurableSet S)
    (F : Domain n → Gradient n q) :
    (∫x,hsNormSq (S.indicator F x))=∫x in S,hsNormSq (F x) := by
  rw [hsNormSq_indicator,integral_indicator hS]

theorem setIntegral_hsNormSq_indicator {n q : ℕ} (S : Set (Domain n)) (hS : MeasurableSet S)
    (U : Set (Domain n)) (F : Domain n → Gradient n q) :
    (∫x in U,hsNormSq (S.indicator F x))=∫x in U∩S,hsNormSq (F x) := by
  rw [hsNormSq_indicator,setIntegral_indicator hS]

theorem memLp_columns_indicator {n q : ℕ} (S : Set (Domain n)) (hS : MeasurableSet S)
    (F : Domain n → Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict S)) :
    ∀i,MemLp (fun x=>S.indicator F x i) 2 volume := by
  classical
  intro i
  have hEq : (fun x=>S.indicator F x i)=S.indicator (fun x=>F x i) := by
    funext x
    by_cases hx : x∈S
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,Pi.zero_apply]
  rw [hEq]
  exact (memLp_indicator_iff_restrict hS).mpr (hF i)

end StationaryHarmonicMaps.Analysis

end

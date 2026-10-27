module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Actual finite local sums of smooth supported functions

Local finiteness of the original supports gives one genuine finite
sum on a neighborhood of each original interior point. Outside the
original open set every supported function is zero. The displayed
total sum is therefore pointwise a finite sum before its smoothness
or derivatives are used.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual local finiteness gives one finite sum equal to the original series on a neighborhood, with every omitted summand locally zero. -/
theorem exists_local_finset_tsum_eq {n : ℕ} {I : Type*}
    (η : I → Domain n → ℝ) (x : Domain n)
    (hLocal : ∃ V∈𝓝 x,{i | (Function.support (η i)∩V).Nonempty}.Finite) :
    ∃ F : Finset I,(fun y=>∑' i,η i y)=ᶠ[𝓝 x](fun y=>∑ i∈F,η i y) ∧
      ∀ i∉F,η i=ᶠ[𝓝 x](fun _=>0) := by
  classical
  obtain ⟨V,hV,hFinite⟩ := hLocal
  let F := hFinite.toFinset
  have hZero (i : I) (hi : i∉F) (y : Domain n) (hy : y∈V) : η i y=0 := by
    by_contra hn
    have H : i∈{i | (Function.support (η i)∩V).Nonempty} := ⟨y,hn,hy⟩
    exact hi (hFinite.mem_toFinset.mpr H)
  refine ⟨F,?_,?_⟩
  · filter_upwards [hV] with y hy
    exact tsum_eq_sum (fun i hi=>hZero i hi y hy)
  · intro i hi
    filter_upwards [hV] with y hy
    exact hZero i hi y hy

/-- The original supported smooth family has actual finite support at every point, and its genuine total sum is smooth on the original set. -/
theorem finite_support_contDiffOn_tsum_of_locallyFinite {n : ℕ} {I : Type*}
    (S : Set (Domain n)) (η : I → Domain n → ℝ)
    (hη : ∀ i,ContDiff ℝ ∞ (η i)) (hSupp : ∀ i,Function.support (η i)⊆S)
    (hLocal : ∀ x∈S,∃ V∈𝓝 x,{i | (Function.support (η i)∩V).Nonempty}.Finite) :
    (∀ x,Function.HasFiniteSupport (fun i=>η i x)) ∧
      ContDiffOn ℝ ∞ (fun x=>∑' i,η i x) S := by
  classical
  have hFinite (x : Domain n) : Function.HasFiniteSupport (fun i=>η i x) := by
    by_cases hx : x∈S
    · obtain ⟨V,hV,hFin⟩ := hLocal x hx
      apply hFin.subset
      intro i hi
      exact ⟨x,hi,mem_of_mem_nhds hV⟩
    · have hZero (i : I) : η i x=0 := by
        by_contra hi
        exact hx (hSupp i hi)
      apply (finite_empty : (∅ : Set I).Finite).subset
      intro i hi
      exact False.elim (hi (hZero i))
  refine ⟨hFinite,?_⟩
  intro x hx
  obtain ⟨F,hEq,_hZero⟩ := exists_local_finset_tsum_eq η x (hLocal x hx)
  have hSmooth : ContDiff ℝ ∞ (fun y=>∑ i∈F,η i y) := ContDiff.sum (fun i _=>hη i)
  exact (hSmooth.contDiffAt.congr_of_eventuallyEq hEq).contDiffWithinAt

/-- Actual local finiteness differentiates the original series as a genuine finite sum, and all omitted original derivatives vanish. -/
theorem exists_hasFDerivAt_locallyFinite_tsum {n : ℕ} {I : Type*}
    (η : I → Domain n → ℝ) (hη : ∀ i,ContDiff ℝ ∞ (η i)) (x : Domain n)
    (hLocal : ∃ V∈𝓝 x,{i | (Function.support (η i)∩V).Nonempty}.Finite) :
    ∃ F : Finset I,HasFDerivAt (fun y=>∑' i,η i y) (∑ i∈F,fderiv ℝ (η i) x) x ∧
      ∀ i∉F,fderiv ℝ (η i) x=0 := by
  classical
  obtain ⟨F,hEq,hZero⟩ := exists_local_finset_tsum_eq η x hLocal
  refine ⟨F,?_,?_⟩
  · have hD := HasFDerivAt.fun_sum (u := F) (fun i _=>(hη i).differentiable (by simp) x |>.hasFDerivAt)
    exact hD.congr_of_eventuallyEq hEq
  · intro i hi
    rw [(hZero i hi).fderiv_eq]
    exact fderiv_const_apply _

end StationaryHarmonicMaps.Analysis

end

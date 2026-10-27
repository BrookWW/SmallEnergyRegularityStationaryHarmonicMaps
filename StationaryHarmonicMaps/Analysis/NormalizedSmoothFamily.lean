module

public import StationaryHarmonicMaps.Analysis.LocallyFiniteSmoothSum
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Actual normalization of a locally finite smooth supported family

The original support family makes the original total sum pointwise
finite. Its positive values on the original open set normalize every
summand. Both original and normalized sums have actual finite support
at every point; every normalized function is globally smooth and
compactly supported in its original support, and their sum is one
on the original open set.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual supported smooth data with a positive original sum produce the genuine normalized smooth compact family and its partition identity. -/
theorem normalized_smooth_supported_family {n : ℕ} {I : Type*}
    (S : Set (Domain n)) (hOpen : IsOpen S) (η : I → Domain n → ℝ)
    (hη : ∀ i,ContDiff ℝ ∞ (η i)) (hcη : ∀ i,HasCompactSupport (η i))
    (hSupp : ∀ i,tsupport (η i)⊆S) (hNonneg : ∀ i x,0≤η i x)
    (hLocal : ∀ x∈S,∃ V∈𝓝 x,{i | (Function.support (η i)∩V).Nonempty}.Finite)
    (hPos : ∀ x∈S,0<∑' i,η i x) :
    let P := fun x=>∑' i,η i x
    let θ := fun i x=>η i x/P x
    (∀ x,Function.HasFiniteSupport (fun i=>η i x)) ∧
      (∀ x,Function.HasFiniteSupport (fun i=>θ i x)) ∧
      (∀ i,ContDiff ℝ ∞ (θ i) ∧ HasCompactSupport (θ i) ∧ tsupport (θ i)⊆tsupport (η i)) ∧
      (∀ i x,0≤θ i x ∧ θ i x≤1) ∧ (∀ x∈S,∑' i,θ i x=1) := by
  classical
  intro P θ
  obtain ⟨hFinite,hSmooth⟩ := finite_support_contDiffOn_tsum_of_locallyFinite S η hη
    (fun i=>(subset_tsupport (η i)).trans (hSupp i)) hLocal
  have hZero (i : I) (x : Domain n) (hx : x∉S) : η i x=0 := by
    by_contra hn
    exact hx (hSupp i (subset_tsupport (η i) hn))
  have hSuppθ (i : I) : Function.support (θ i)⊆Function.support (η i) := by
    intro x hx
    by_contra hn
    have H : η i x=0 := not_not.mp hn
    exact hx (by change η i x/P x=0;rw [H,zero_div])
  have hTSuppθ (i : I) : tsupport (θ i)⊆tsupport (η i) := closure_mono (hSuppθ i)
  have hFiniteθ (x : Domain n) : Function.HasFiniteSupport (fun i=>θ i x) := by
    apply (hFinite x).subset
    intro i hi
    by_contra hn
    have H : η i x=0 := not_not.mp hn
    exact hi (by change η i x/P x=0;rw [H,zero_div])
  have hSmoothθ (i : I) : ContDiff ℝ ∞ (θ i) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x∈S
    · exact (hη i).contDiffAt.div (hSmooth.contDiffAt (hOpen.mem_nhds hx)) (hPos x hx).ne'
    · have hxNot : x∉tsupport (η i) := fun H=>hx (hSupp i H)
      have hLoc : η i=ᶠ[𝓝 x](fun _=>0) := notMem_tsupport_iff_eventuallyEq.mp hxNot
      have hθZero : θ i=ᶠ[𝓝 x](fun _=>0) := hLoc.mono (fun y hy=>by change η i y/P y=0;rw [hy,zero_div])
      exact contDiffAt_const.congr_of_eventuallyEq hθZero
  have hBounds (i : I) (x : Domain n) : 0≤θ i x ∧ θ i x≤1 := by
    by_cases hx : x∈S
    · have hSum : η i x≤P x := by
        have hSummable : Summable (fun j=>η j x) := summable_of_hasFiniteSupport (hFinite x)
        have H := hSummable.sum_le_tsum
          ({i} : Finset I) (fun j _=>hNonneg j x)
        simpa only [Finset.sum_singleton] using H
      exact ⟨div_nonneg (hNonneg i x) (hPos x hx).le,(div_le_one (hPos x hx)).mpr hSum⟩
    · change 0≤η i x/P x ∧ η i x/P x≤1
      rw [hZero i x hx,zero_div]
      exact ⟨le_rfl,zero_le_one⟩
  refine ⟨hFinite,hFiniteθ,?_,hBounds,?_⟩
  · intro i
    exact ⟨hSmoothθ i,(hcη i).of_isClosed_subset (isClosed_tsupport (θ i)) (hTSuppθ i),hTSuppθ i⟩
  · intro x hx
    change (∑' i,η i x/P x)=1
    rw [tsum_div_const]
    exact div_self (hPos x hx).ne'

end StationaryHarmonicMaps.Analysis

end

module

public import HarmonicMaps.Sobolev
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # Actual finite nonnegative weights control scalar weighted sums -/

public section

open HarmonicMaps Set

namespace StationaryHarmonicMaps.Analysis

/-- Genuine finitely supported nonnegative weights of total mass one bound the actual sum of weighted absolute values. -/
theorem tsum_abs_mul_le_of_finite_weights {I : Type*} (w c : I → ℝ)
    (hFinite : Function.HasFiniteSupport w) (hNonneg : ∀ i,0≤w i) (hSum : ∑' i,w i=1)
    (M : ℝ) (hBound : ∀ i,|c i|≤M) : (∑' i,|w i*c i|)≤M := by
  classical
  let F := hFinite.toFinset
  have hZero (i : I) (hi : i∉F) : w i=0 := by
    by_contra hn
    exact hi (hFinite.mem_toFinset.mpr hn)
  have hFiniteSum : (∑ i∈F,w i)=1 := (tsum_eq_sum hZero).symm.trans hSum
  rw [tsum_eq_sum (fun i hi=>by rw [hZero i hi,zero_mul,abs_zero])]
  calc
    _ = ∑ i∈F,w i*|c i| := by apply Finset.sum_congr rfl;intro i _;rw [abs_mul,abs_of_nonneg (hNonneg i)]
    _ ≤ ∑ i∈F,w i*M := Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hBound i) (hNonneg i))
    _ = (∑ i∈F,w i)*M := (Finset.sum_mul _ _ _).symm
    _ = M := by rw [hFiniteSum,one_mul]

/-- The actual scalar weighted sum obeys the same bound, from genuine finite support rather than an infinite-series fallback. -/
theorem abs_tsum_mul_le_of_finite_weights {I : Type*} (w c : I → ℝ)
    (hFinite : Function.HasFiniteSupport w) (hNonneg : ∀ i,0≤w i) (hSum : ∑' i,w i=1)
    (M : ℝ) (hBound : ∀ i,|c i|≤M) : |∑' i,w i*c i|≤M := by
  have hFiniteNorm : Function.HasFiniteSupport (fun i=>‖w i*c i‖) := hFinite.subset (by
    intro i hi
    by_contra hw
    exact hi (by change ‖w i*c i‖=0;rw [not_not.mp hw,zero_mul,norm_zero]))
  have hSummable : Summable (fun i=>‖w i*c i‖) := summable_of_hasFiniteSupport hFiniteNorm
  have H := norm_tsum_le_tsum_norm hSummable
  simp only [Real.norm_eq_abs] at H
  exact H.trans (tsum_abs_mul_le_of_finite_weights w c hFinite hNonneg hSum M hBound)

end StationaryHarmonicMaps.Analysis

end

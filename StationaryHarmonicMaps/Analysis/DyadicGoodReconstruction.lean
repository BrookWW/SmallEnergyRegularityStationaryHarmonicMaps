module

public import StationaryHarmonicMaps.Analysis.WhitneyPartitionQuantitative
public import StationaryHarmonicMaps.Analysis.GrandKernelLocalization
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import StationaryHarmonicMaps.Analysis.PartitionCancellationSum
public import StationaryHarmonicMaps.Analysis.GrandMaximalLebesgueDomination
public import StationaryHarmonicMaps.Analysis.GrandLevelIntegralLimits
public import Mathlib.Order.Interval.Finset.SuccPred

/-!
# Actual two-sided integer reconstruction from the same good family

The finite original differences telescope over every full integer
window, including its negative endpoint. The original small-level and
large-level L1 limits give strong L1 reconstruction of the original
function. Each original difference has zero integral from the common
original mean, so every actual finite window also has zero integral.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem sum_symmetric_integer_differences {E : Type*} [AddCommGroup E]
    (H : ℤ → E) (N : ℕ) :
    (∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),(H (j+1)-H j))=H ((N : ℤ)+1)-H (-(N : ℤ)) := by
  induction N with
  | zero => simp only [Nat.cast_zero,neg_zero,Finset.Icc_self,Finset.sum_singleton,zero_add]
  | succ N hN =>
    have hInterval : Finset.Icc (-((N+1 : ℕ) : ℤ)) ((N+1 : ℕ) : ℤ)=
        insert (-(N : ℤ)-1) (insert ((N : ℤ)+1) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
      ext j
      simp only [Finset.mem_Icc,Finset.mem_insert,Nat.cast_add,Nat.cast_one]
      omega
    have hRight : (N : ℤ)+1∉Finset.Icc (-(N : ℤ)) (N : ℤ) := by simp
    have hLeft : -(N : ℤ)-1∉insert ((N : ℤ)+1) (Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
      simp only [Finset.mem_insert,Finset.mem_Icc]
      omega
    rw [hInterval,Finset.sum_insert hLeft,Finset.sum_insert hRight,hN]
    simp only [Nat.cast_add,Nat.cast_one,show -(N : ℤ)-1+1= -(N : ℤ) by ring]
    abel_nf

/-- The same actual integrable integer good family and its two genuine L1 end limits produce the true finite-window zero-mean reconstruction of the original function. -/
theorem symmetric_good_differences_strong_L1_reconstruct {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ) (G : ℤ → X → ℝ)
    (hG : ∀ j,Integrable (G j) μ) (hMean : ∀ j,(∫ x,G j x ∂μ)=(∫ x,f x ∂μ))
    (hLow : Tendsto (fun N : ℕ=>∫ x,|G (-(N : ℤ)) x| ∂μ) atTop (𝓝 (0 : ℝ)))
    (hHigh : Tendsto (fun N : ℕ=>∫ x,|f x-G ((N : ℤ)+1) x| ∂μ) atTop (𝓝 (0 : ℝ))) :
    let H := fun j x=>G (j+1) x-G j x
    (∀ j,Integrable (H j) μ ∧ (∫ x,H j x ∂μ)=0) ∧
      (∀ N : ℕ,Integrable (fun x=>∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),H j x) μ ∧
        (∫ x,(∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),H j x) ∂μ)=0) ∧
      Tendsto (fun N : ℕ=>∫ x,|f x-∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),H j x| ∂μ)
        atTop (𝓝 (0 : ℝ)) := by
  intro H
  have hHI (j : ℤ) : Integrable (H j) μ := (hG (j+1)).sub (hG j)
  have hHMean (j : ℤ) : (∫ x,H j x ∂μ)=0 := by rw [integral_sub (hG (j+1)) (hG j),hMean (j+1),hMean j,sub_self]
  have hSI (N : ℕ) : Integrable (fun x=>∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),H j x) μ :=
    integrable_finsetSum _ (fun j _=>hHI j)
  have hSMean (N : ℕ) : (∫ x,(∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),H j x) ∂μ)=0 := by
    rw [integral_finsetSum _ (fun j _=>hHI j)]
    simp only [hHMean,Finset.sum_const_zero]
  have hPoint (N : ℕ) (x : X) : (∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),H j x)=
      G ((N : ℤ)+1) x-G (-(N : ℤ)) x := sum_symmetric_integer_differences (fun j=>G j x) N
  have hBound (N : ℕ) : (∫ x,|f x-∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),H j x| ∂μ)≤
      (∫ x,|f x-G ((N : ℤ)+1) x| ∂μ)+(∫ x,|G (-(N : ℤ)) x| ∂μ) := by
    calc
      _ ≤ ∫ x,|f x-G ((N : ℤ)+1) x|+|G (-(N : ℤ)) x| ∂μ := integral_mono (hf.sub (hSI N)).abs
        (((hf.sub (hG ((N : ℤ)+1))).abs).add (hG (-(N : ℤ))).abs) (fun x=>by
          change |f x-(∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),H j x)|≤_
          rw [hPoint]
          have H := abs_add_le (f x-G ((N : ℤ)+1) x) (G (-(N : ℤ)) x)
          have hAlg : f x-(G ((N : ℤ)+1) x-G (-(N : ℤ)) x)=
              (f x-G ((N : ℤ)+1) x)+G (-(N : ℤ)) x := by ring
          rw [hAlg]
          exact H)
      _ = _ := integral_add (hf.sub (hG ((N : ℤ)+1))).abs (hG (-(N : ℤ))).abs
  refine ⟨fun j=>⟨hHI j,hHMean j⟩,fun N=>⟨hSI N,hSMean N⟩,?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hHigh.add hLow)
    (fun _=>integral_nonneg fun _=>abs_nonneg _) hBound

end StationaryHarmonicMaps.Analysis

end

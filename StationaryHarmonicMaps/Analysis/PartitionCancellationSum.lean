module

public import StationaryHarmonicMaps.Analysis.FiniteWeightedSum
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Genuine global reconstruction from the original partition pieces

The original partition and original bounded coefficients make every
pointwise series finite. The actual sum of the absolute bad pieces is
bounded by the original integrable function plus the original level on
the finite-volume bad set. This supplies a real integrable dominator
for interchange of the original integrals and series. The original
zero integrals therefore give a zero integral for the full bad sum.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual finite partition pieces reconstruct an integrable good function, preserve the original integral and obey the original coefficient bound on the bad set. -/
theorem integrable_partition_cancellation_sum {X I : Type*} [MeasurableSpace X] [Countable I]
    (μ : Measure X) (S : Set X) (hS : MeasurableSet S) (hSFinite : μ S≠∞)
    (f : X → ℝ) (hf : Integrable f μ) (θ : I → X → ℝ)
    (hθ : ∀ i,AEStronglyMeasurable (θ i) μ)
    (hFinite : ∀ x,Function.HasFiniteSupport (fun i=>θ i x))
    (hSupp : ∀ i,Function.support (θ i)⊆S) (hNonneg : ∀ i x,0≤θ i x)
    (hPartition : ∀ x∈S,∑' i,θ i x=1)
    (c : I → ℝ) (M : ℝ) (hc : ∀ i,|c i|≤M)
    (hMean : ∀ i,(∫ x,θ i x*(f x-c i) ∂μ)=0) :
    let b := fun i x=>θ i x*(f x-c i)
    let g := fun x=>f x-∑' i,b i x
    (∀ x,Function.HasFiniteSupport (fun i=>b i x)) ∧
      (∀ i,Integrable (b i) μ) ∧ Integrable (fun x=>∑' i,|b i x|) μ ∧
      Integrable (fun x=>∑' i,b i x) μ ∧ (∫ x,(∑' i,b i x) ∂μ)=0 ∧
      Integrable g μ ∧ (∫ x,g x ∂μ)=(∫ x,f x ∂μ) ∧
      (∀ x∈S,g x=∑' i,θ i x*c i) ∧ (∀ x∈S,|g x|≤M) ∧
      (∀ x∉S,g x=f x) ∧ (∀ x,f x=g x+∑' i,b i x) := by
  classical
  intro b g
  have hZero (i : I) (x : X) (hx : x∉S) : θ i x=0 := by
    by_contra hn
    exact hx (hSupp i hn)
  have hOne (i : I) (x : X) : θ i x≤1 := by
    by_cases hx : x∈S
    · have hSum : Summable (fun i=>θ i x) := summable_of_hasFiniteSupport (hFinite x)
      have H := hSum.sum_le_tsum ({i} : Finset I) (fun j _=>hNonneg j x)
      simpa only [Finset.sum_singleton,hPartition x hx] using H
    · rw [hZero i x hx]
      exact zero_le_one
  have hθI (i : I) : Integrable (θ i) μ := by
    letI : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hSFinite
    apply (integrableOn_iff_integrable_of_support_subset (hSupp i)).mp
    exact (integrable_const (1 : ℝ)).mono' (hθ i).restrict (Eventually.of_forall fun x=>by
      rw [Real.norm_of_nonneg (hNonneg i x)];exact hOne i x)
  have hBI (i : I) : Integrable (b i) μ := by
    have hProd := hf.bdd_mul (hθ i) (Eventually.of_forall fun x=>by
      rw [Real.norm_of_nonneg (hNonneg i x)];exact hOne i x)
    exact (hProd.sub ((hθI i).mul_const (c i))).congr (Eventually.of_forall fun x=>by change θ i x*f x-θ i x*c i=θ i x*(f x-c i);ring)
  have hBFinite (x : X) : Function.HasFiniteSupport (fun i=>b i x) := (hFinite x).subset (by
    intro i hi
    by_contra hn
    have H : θ i x=0 := not_not.mp hn
    exact hi (by change θ i x*(f x-c i)=0;rw [H,zero_mul]))
  have hAbsFinite (x : X) : Function.HasFiniteSupport (fun i=>|b i x|) := (hBFinite x).subset (by
    intro i hi
    by_contra hn
    have H : b i x=0 := not_not.mp hn
    exact hi (by change |b i x|=0;rw [H,abs_zero]))
  let H := S.indicator (fun x=>|f x|+M)
  have hHI : Integrable H μ := by
    letI : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hSFinite
    exact (hf.abs.integrableOn.add (integrable_const M)).integrable_indicator hS
  have hAbsBound (x : X) : (∑' i,|b i x|)≤H x := by
    dsimp only [H]
    by_cases hx : x∈S
    · rw [indicator_of_mem hx]
      apply tsum_abs_mul_le_of_finite_weights (fun i=>θ i x) (fun i=>f x-c i)
        (hFinite x) (fun i=>hNonneg i x) (hPartition x hx) (|f x|+M)
      intro i
      exact (abs_sub (f x) (c i)).trans (add_le_add le_rfl (hc i))
    · rw [indicator_of_notMem hx]
      have hBZero (i : I) : b i x=0 := by dsimp only [b];rw [hZero i x hx,zero_mul]
      simp only [hBZero,abs_zero,tsum_zero,le_refl]
  have hAbsNonneg (x : X) : 0≤∑' i,|b i x| := tsum_nonneg (fun _=>abs_nonneg _)
  have hAbsMeas : AEStronglyMeasurable (fun x=>∑' i,|b i x|) μ :=
    (AEMeasurable.tsum (fun i=>(hBI i).abs.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hAbsI : Integrable (fun x=>∑' i,|b i x|) μ := hHI.mono' hAbsMeas
    (Eventually.of_forall fun x=>by rw [Real.norm_of_nonneg (hAbsNonneg x)];exact hAbsBound x)
  have hBMeas : AEStronglyMeasurable (fun x=>∑' i,b i x) μ :=
    (AEMeasurable.tsum (fun i=>(hBI i).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hSumBI : Integrable (fun x=>∑' i,b i x) μ := hAbsI.mono' hBMeas (Eventually.of_forall fun x=>by
    have H := norm_tsum_le_tsum_norm (show Summable (fun i=>‖b i x‖) from by
      simpa only [Real.norm_eq_abs] using summable_of_hasFiniteSupport (hAbsFinite x))
    simpa only [Real.norm_eq_abs] using H)
  have hInterchange := hasSum_integral_of_dominated_convergence (fun i x=>|b i x|)
    (fun i=>(hBI i).aestronglyMeasurable) (fun _=>Eventually.of_forall fun _=>by simp only [Real.norm_eq_abs,le_refl])
    (Eventually.of_forall fun x=>summable_of_hasFiniteSupport (hAbsFinite x)) hAbsI
    (Eventually.of_forall fun x=>(summable_of_hasFiniteSupport (hBFinite x)).hasSum)
  have hSumZero : (∫ x,(∑' i,b i x) ∂μ)=0 := by
    have H := hInterchange.tsum_eq
    have hMeanB (i : I) : (∫ x,b i x ∂μ)=0 := hMean i
    simp only [hMeanB,tsum_zero] at H
    exact H.symm
  have hgI : Integrable g μ := hf.sub hSumBI
  have hgMean : (∫ x,g x ∂μ)=(∫ x,f x ∂μ) := by rw [integral_sub hf hSumBI,hSumZero,sub_zero]
  have hInside (x : X) (hx : x∈S) : g x=∑' i,θ i x*c i := by
    have hSummable1 : Summable (fun i=>θ i x*f x) := (summable_of_hasFiniteSupport (hFinite x)).mul_right _
    have hCFinite : Function.HasFiniteSupport (fun i=>θ i x*c i) := (hFinite x).subset (by
      intro i hi;by_contra hn
      have H : θ i x=0 := not_not.mp hn
      exact hi (by change θ i x*c i=0;rw [H,zero_mul]))
    have hSummable2 : Summable (fun i=>θ i x*c i) := summable_of_hasFiniteSupport hCFinite
    dsimp only [g,b]
    simp_rw [mul_sub]
    rw [hSummable1.tsum_sub hSummable2,tsum_mul_right,hPartition x hx,one_mul]
    ring
  have hGoodBound (x : X) (hx : x∈S) : |g x|≤M := by
    rw [hInside x hx]
    exact abs_tsum_mul_le_of_finite_weights (fun i=>θ i x) c (hFinite x) (fun i=>hNonneg i x) (hPartition x hx) M hc
  have hOutside (x : X) (hx : x∉S) : g x=f x := by
    have hBZero (i : I) : b i x=0 := by dsimp only [b];rw [hZero i x hx,zero_mul]
    dsimp only [g]
    simp only [hBZero,tsum_zero,sub_zero]
  exact ⟨hBFinite,hBI,hAbsI,hSumBI,hSumZero,hgI,hgMean,hInside,hGoodBound,hOutside,fun _=>by dsimp only [g];ring⟩

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.AtomicPairingLimit
public import StationaryHarmonicMaps.Analysis.NormalizedAtomL1
public import StationaryHarmonicMaps.Analysis.TruncatedProductLimit

/-!
# Continuous mean-oscillation pairings of an actual atomic reconstruction

Actual normalized cancellation atoms pair with the original local L1
function. Literal bounded symmetric truncations retain uniform mean
oscillation. Their actual original-function integrals have a genuine
limit controlled by the original summable coefficient family. Whenever
the untruncated product is integrable this limit is its ordinary integral.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Original normalized atoms, genuine reconstruction and original local mean-oscillation bounds produce the actual continuous symmetric-truncation pairing, agreeing with every integrable original product. -/
theorem exists_atomic_mean_oscillation_pairing_limit {X I : Type*}
    [MeasurableSpace X] [Countable I]
    (μ : Measure X) (S : I → Set X) (hS : ∀ i,MeasurableSet (S i))
    (hS0 : ∀ i,μ (S i)≠0) (hSFin : ∀ i,μ (S i)≠⊤)
    (a : I → X → ℝ) (ha : ∀ i,AEStronglyMeasurable (a i) (μ.restrict (S i)))
    (hSupp : ∀ i,Function.support (a i)⊆S i)
    (haBound : ∀ i,∀ᵐ x ∂μ.restrict (S i),|a i x|≤(μ.real (S i))⁻¹)
    (hCancel : ∀ i,(∫ x,a i x ∂μ)=0)
    (c : I → ℝ) (hc : Summable (fun i=>|c i|))
    (f b : X → ℝ) (hRecon : f=ᵐ[μ](fun x=>∑' i,c i*a i x))
    (hb : AEStronglyMeasurable b μ) (hbLocal : ∀ i,IntegrableOn b (S i) μ)
    (B : ℝ) (hOsc : ∀ i,(⨍ x in S i,|b x-(⨍ y in S i,b y ∂μ)| ∂μ)≤B) :
    ∃ s : ℝ,
      (∀ k : ℕ,Integrable (fun x=>f x*min (k : ℝ) (max (-(k : ℝ)) (b x))) μ) ∧
      Tendsto (fun k : ℕ=>∫ x,f x*min (k : ℝ) (max (-(k : ℝ)) (b x)) ∂μ) atTop (𝓝 s) ∧
      |s|≤2*B*(∑' i,|c i|) ∧
      (Integrable (fun x=>f x*b x) μ → s=(∫ x,f x*b x ∂μ)) := by
  have hAtom (i : I) := normalized_supported_atom_integrable_abs_le_one
    μ (S i) (hS0 i) (hSFin i) (a i) (ha i) (hSupp i) (haBound i)
  have hOriginalPair (i : I) := atom_pairing_le_mean_oscillation μ (S i) (hS i)
    (hS0 i) (hSFin i) (a i) b (ha i) (hSupp i) (haBound i) (hCancel i) (hbLocal i)
  let T := fun (k : ℕ) (x : X)=>min (k : ℝ) (max (-(k : ℝ)) (b x))
  have hTMeas (k : ℕ) : AEStronglyMeasurable (T k) μ :=
    (symmetric_truncation_lipschitz_bounds (k : ℝ) (Nat.cast_nonneg k)).1.continuous.comp_aestronglyMeasurable hb
  have hTBound (k : ℕ) : ∀ᵐ x ∂μ,|T k x|≤(k : ℝ) := Eventually.of_forall fun x=>
    ((symmetric_truncation_lipschitz_bounds (k : ℝ) (Nat.cast_nonneg k)).2 (b x)).1
  have hTPair (k : ℕ) (i : I) : |∫ x,a i x*T k x ∂μ|≤2*B := by
    letI : IsFiniteMeasure (μ.restrict (S i)) := isFiniteMeasure_restrict.mpr (hSFin i)
    letI : NeZero (μ.restrict (S i)) := ⟨by
      intro hz
      have H := congrArg (fun ν : Measure X=>ν univ) hz
      exact (hS0 i) (by simpa using H)⟩
    have hTrunc := integrable_symmetric_truncation_mean_oscillation_le (μ.restrict (S i))
      b (hbLocal i) (k : ℝ) (Nat.cast_nonneg k)
    have hPair := atom_pairing_le_mean_oscillation μ (S i) (hS i) (hS0 i) (hSFin i)
      (a i) (T k) (ha i) (hSupp i) (haBound i) (hCancel i) hTrunc.1
    exact hPair.2.2.trans (hTrunc.2.trans (mul_le_mul_of_nonneg_left (hOsc i) (by norm_num)))
  have hAtomLimit (i : I) : Tendsto (fun k=>∫ x,a i x*T k x ∂μ) atTop
      (𝓝 (∫ x,a i x*b x ∂μ)) :=
    (tendsto_integral_product_symmetric_truncation μ (a i) b (hAtom i).1.aestronglyMeasurable
      hb (hOriginalPair i).2.1).2
  obtain ⟨_hSummable,hAllI,hLimit,hEstimate⟩ := atomic_pairing_limit_of_bounded_approximants
    μ a (fun i=>(hAtom i).1) (fun i=>(hAtom i).2) c hc f hRecon T hTMeas
    (fun k=>(k : ℝ)) (fun k=>Nat.cast_nonneg k) hTBound (2*B) hTPair
    (fun i=>∫ x,a i x*b x ∂μ) hAtomLimit
  refine ⟨_,hAllI,hLimit,hEstimate,?_⟩
  intro hProduct
  have hfMeas : AEStronglyMeasurable f μ := by
    have hSeries : AEStronglyMeasurable (fun x=>∑' i,c i*a i x) μ :=
      (AEMeasurable.tsum (fun i=>((hAtom i).1.aestronglyMeasurable.const_mul (c i)).aemeasurable)).aestronglyMeasurable
    exact hSeries.congr hRecon.symm
  exact tendsto_nhds_unique hLimit
    (tendsto_integral_product_symmetric_truncation μ f b hfMeas hb hProduct).2

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.SobolevStrongCompleteness
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Actual finite sums and uniqueness of strong L2 limits -/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- A finite family of original L2 strong limits gives the strong limit of its actual pointwise sum. -/
theorem tendsto_L2_finset_sum {X I : Type*} [MeasurableSpace X] [Fintype I] {q : ℕ}
    (μ : Measure X) (f : ℕ → I → X → Ambient q) (v : I → X → Ambient q)
    (hf : ∀ s i,MemLp (f s i) 2 μ) (hv : ∀ i,MemLp (v i) 2 μ)
    (hConv : ∀ i,Tendsto (fun s=>eLpNorm (fun x=>f s i x-v i x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun s=>eLpNorm (fun x=>(∑ i : I,f s i x)-(∑ i : I,v i x)) 2 μ) atTop (𝓝 0) := by
  have hSum : Tendsto (fun s=>∑ i : I,eLpNorm (fun x=>f s i x-v i x) 2 μ) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _=>hConv i)
  have hBound (s : ℕ) : eLpNorm (fun x=>(∑ i : I,f s i x)-(∑ i : I,v i x)) 2 μ ≤
      ∑ i : I,eLpNorm (fun x=>f s i x-v i x) 2 μ := by
    have heq : (fun x=>(∑ i : I,f s i x)-(∑ i : I,v i x)) =
        ∑ i : I,(fun x=>f s i x-v i x) := by
      funext x
      simp only [Finset.sum_apply,Finset.sum_sub_distrib]
    rw [heq]
    exact eLpNorm_sum_le (fun i _=>(hf s i).aestronglyMeasurable.sub (hv i).aestronglyMeasurable) (by norm_num)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSum (fun _=>bot_le) hBound

/-- Two actual strong L2 limits of the same original field sequence agree almost everywhere. -/
theorem ae_eq_of_strong_L2_limits {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (f : ℕ → X → Ambient q) (v w : X → Ambient q)
    (hf : ∀ s,MemLp (f s) 2 μ) (hv : MemLp v 2 μ) (hw : MemLp w 2 μ)
    (hV : Tendsto (fun s=>eLpNorm (fun x=>f s x-v x) 2 μ) atTop (𝓝 0))
    (hW : Tendsto (fun s=>eLpNorm (fun x=>f s x-w x) 2 μ) atTop (𝓝 0)) :
    v =ᵐ[μ] w := by
  have hVLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf v hv).mpr hV
  have hWLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf w hw).mpr hW
  exact (MemLp.toLp_eq_toLp_iff hv hw).mp (tendsto_nhds_unique hVLp hWLp)

end StationaryHarmonicMaps.Analysis

end

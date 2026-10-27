module

public import StationaryHarmonicMaps.Analysis.SobolevWeakGradientClosure

/-!
# Actual strong completeness of the native Sobolev graph

L2 completeness applies to the original maps and each displayed weak
column. Actual strong convergence supplies every weak pairing needed by
the native weak-gradient closure theorem.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual native maps and columns with genuine L2 Cauchy data have one native strong Sobolev limit. -/
theorem exists_native_strong_limit_of_L2_cauchy {n q : ℕ} (Ω : OpenDomain n)
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (hW : ∀ k,MemW12 Ω (u k) (Du k))
    (hMap : CauchySeq (fun k=>(hW k).2.1.toLp (u k)))
    (hColumns : ∀ i : Fin n,CauchySeq (fun k=>(hW k).2.2 i |>.toLp (fun x=>Du k x i))) :
    ∃ (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
      MemW12 Ω v Dv ∧
      Tendsto (fun k=>eLpNorm (fun x=>u k x-v x) 2 (volume.restrict Ω.val)) atTop (𝓝 0) ∧
      ∀ i : Fin n,Tendsto (fun k=>eLpNorm (fun x=>Du k x i-Dv x i) 2
        (volume.restrict Ω.val)) atTop (𝓝 0) := by
  let μ := volume.restrict Ω.val
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hMap
  choose D hD using fun i=>cauchySeq_tendsto_of_complete (hColumns i)
  let Dv := fun (x : Domain n) (i : Fin n)=>D i x
  have hMapLimit : Tendsto (fun k=>eLpNorm (fun x=>u k x-v x) 2 μ) atTop (𝓝 0) := by
    have H := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun k=>(hW k).2.1.toLp (u k)) v).mp hv
    apply H.congr
    intro k
    apply eLpNorm_congr_ae
    filter_upwards [(hW k).2.1.coeFn_toLp] with x hx
    change ((hW k).2.1.toLp (u k)) x-v x=u k x-v x
    rw [hx]
  have hColumnLimit (i : Fin n) : Tendsto (fun k=>eLpNorm
      (fun x=>Du k x i-Dv x i) 2 μ) atTop (𝓝 0) := by
    have H := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun k=>(hW k).2.2 i |>.toLp (fun x=>Du k x i)) (D i)).mp (hD i)
    apply H.congr
    intro k
    apply eLpNorm_congr_ae
    filter_upwards [(hW k).2.2 i |>.coeFn_toLp] with x hx
    change ((hW k).2.2 i |>.toLp (fun x=>Du k x i)) x-D i x=Du k x i-D i x
    rw [hx]
  have hDLp (i : Fin n) : MemLp (fun x=>Dv x i) 2 μ := Lp.memLp (D i)
  have hWeak (i : Fin n) (g : Domain n → Ambient q) (hg : MemLp g 2 μ) :
      Tendsto (fun k=>∫ x,inner ℝ (Du k x i) (g x) ∂μ) atTop
        (𝓝 (∫ x,inner ℝ (Dv x i) (g x) ∂μ)) := by
    simpa only [real_inner_comm] using HolderToCK.tendsto_integral_inner_of_L2
      (fun k=>(hW k).2.2 i) (hDLp i) hg (hColumnLimit i)
  have hNative := memW12_of_strong_map_weak_gradient_L2 Ω u Du hW
    (v : Domain n → Ambient q) Dv (Lp.memLp v) hDLp hMapLimit hWeak
  exact ⟨v,Dv,hNative,hMapLimit,hColumnLimit⟩

end StationaryHarmonicMaps.Analysis

end

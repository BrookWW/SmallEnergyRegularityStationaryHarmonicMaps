module

public import StationaryHarmonicMaps.Analysis.ClosedNormalTensorCauchy
public import StationaryHarmonicMaps.Analysis.NormalOneFormIntegration
public import StationaryHarmonicMaps.Analysis.L2FiniteLinearLimits

/-!
# Actual closed tensor constraints and normal boundary under strong limits

The same original smooth tensor sequence supplies the native limit.
Actual finite L2 operations preserve antisymmetry, differential closedness
and its divergence. The original full-boundary integration identities pass
to the same limit against every native whole-ball Sobolev test.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

private theorem tendsto_L2_add {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (f g : ℕ → X → Ambient q) (v w : X → Ambient q)
    (hf : ∀ s,MemLp (f s) 2 μ) (hg : ∀ s,MemLp (g s) 2 μ)
    (hv : MemLp v 2 μ) (hw : MemLp w 2 μ)
    (hF : Tendsto (fun s=>eLpNorm (fun x=>f s x-v x) 2 μ) atTop (𝓝 0))
    (hG : Tendsto (fun s=>eLpNorm (fun x=>g s x-w x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun s=>eLpNorm (fun x=>(f s x+g s x)-(v x+w x)) 2 μ) atTop (𝓝 0) := by
  let F := fun (s : ℕ) (a : Fin 2) (x : X)=>if a=0 then f s x else g s x
  let V := fun (a : Fin 2) (x : X)=>if a=0 then v x else w x
  have hFLp (s : ℕ) (a : Fin 2) : MemLp (F s a) 2 μ := by
    by_cases ha : a=0
    · simpa only [F,if_pos ha] using hf s
    · simpa only [F,if_neg ha] using hg s
  have hVLp (a : Fin 2) : MemLp (V a) 2 μ := by
    by_cases ha : a=0
    · simpa only [V,if_pos ha] using hv
    · simpa only [V,if_neg ha] using hw
  have hConv (a : Fin 2) : Tendsto (fun s=>eLpNorm (fun x=>F s a x-V a x) 2 μ) atTop (𝓝 0) := by
    by_cases ha : a=0
    · simpa only [F,V,if_pos ha] using hF
    · simpa only [F,V,if_neg ha] using hG
  have H := tendsto_L2_finset_sum μ F V hFLp hVLp hConv
  simpa only [Fin.sum_univ_two,F,V,ite_true,show (1:Fin 2)≠0 by decide,ite_false] using H

private theorem ae_zero_of_strong_L2_zero_sequence {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (f : ℕ → X → Ambient q) (v : X → Ambient q)
    (hf : ∀ s,MemLp (f s) 2 μ) (hv : MemLp v 2 μ)
    (hConv : Tendsto (fun s=>eLpNorm (fun x=>f s x-v x) 2 μ) atTop (𝓝 0))
    (hZero : ∀ s,f s =ᵐ[μ] (fun _=>0)) : v =ᵐ[μ] (fun _=>0) := by
  have h0 : Tendsto (fun s=>eLpNorm (fun x=>f s x-(0:Ambient q)) 2 μ) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall (fun s=>by
      have H : eLpNorm (fun x=>f s x-(0:Ambient q)) 2 μ=0 := by
        calc
          _ = eLpNorm (fun _x : X=>(0:Ambient q)) 2 μ := eLpNorm_congr_ae
            ((hZero s).mono fun x hx=>by simp only [hx,sub_zero])
          _ = 0 := eLpNorm_zero'
      exact H.symm)
  exact ae_eq_of_strong_L2_limits μ f v (fun _=>0) hf hv MemLp.zero' hConv h0

/-- Original strong native tensor limits preserve all actual antisymmetric, closed and divergence identities almost everywhere. -/
theorem closed_tensor_strong_limit_constraints {n q : ℕ}
    (B : ℕ → Fin n → Fin n → Domain n → Ambient q)
    (hB : ∀ s i j,ContDiff ℝ ∞ (B s i j))
    (hSkew : ∀ s i j x,B s i j x = -B s j i x)
    (hClosed : ∀ s i j k x,fderiv ℝ (B s i j) x (EuclideanSpace.single k 1)+
      fderiv ℝ (B s j k) x (EuclideanSpace.single i 1)+fderiv ℝ (B s k i) x (EuclideanSpace.single j 1)=0)
    (b : Fin n → Fin n → Domain n → Ambient q) (Db : Fin n → Fin n → Domain n → Gradient n q)
    (hb : ∀ i j,MemW12 (ballDomain (0 : Domain n) 1) (b i j) (Db i j))
    (hMap : ∀ i j,Tendsto (fun s=>eLpNorm (fun x=>B s i j x-b i j x) 2
      (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0))
    (hGrad : ∀ i j k,Tendsto (fun s=>eLpNorm (fun x=>
      fderiv ℝ (B s i j) x (EuclideanSpace.single k 1)-Db i j x k) 2
        (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0))
    (P : Domain n → Gradient n q)
    (hP : ∀ j,MemLp (fun x=>P x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hConv : ∀ j,Tendsto (fun s=>eLpNorm (fun x=>(∑ i : Fin n,
      fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))-P x j) 2
        (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0)) :
    (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ i j,b i j x = -b j i x) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ i j k,
        Db i j x k+Db j k x i+Db k i x j=0) ∧
      ∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ j,
        (∑ i : Fin n,Db i j x i)=P x j := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  have hOld (s : ℕ) (i j : Fin n) := memW12_ball_of_ambient_c1 (0 : Domain n) 1 (B s i j)
    ((hB s i j).of_le (by simp))
  have hSkewLimit (i j : Fin n) : ∀ᵐ x ∂μ,b i j x = -b j i x := by
    have hAdd := tendsto_L2_add μ (fun s=>B s i j) (fun s=>B s j i) (b i j) (b j i)
      (fun s=>(hOld s i j).2.1) (fun s=>(hOld s j i).2.1) (hb i j).2.1 (hb j i).2.1 (hMap i j) (hMap j i)
    have hZero := ae_zero_of_strong_L2_zero_sequence μ
      (fun s x=>B s i j x+B s j i x) (fun x=>b i j x+b j i x)
      (fun s=>(hOld s i j).2.1.add (hOld s j i).2.1) ((hb i j).2.1.add (hb j i).2.1) hAdd
      (fun s=>Eventually.of_forall (fun x=>by
        change B s i j x+B s j i x=0
        rw [hSkew,neg_add_cancel]))
    exact hZero.mono (fun x hx=>eq_neg_of_add_eq_zero_left hx)
  have hClosedLimit (i j k : Fin n) : ∀ᵐ x ∂μ,Db i j x k+Db j k x i+Db k i x j=0 := by
    have h12 := tendsto_L2_add μ
      (fun s x=>fderiv ℝ (B s i j) x (EuclideanSpace.single k 1))
      (fun s x=>fderiv ℝ (B s j k) x (EuclideanSpace.single i 1))
      (fun x=>Db i j x k) (fun x=>Db j k x i)
      (fun s=>(hOld s i j).2.2 k) (fun s=>(hOld s j k).2.2 i)
      ((hb i j).2.2 k) ((hb j k).2.2 i) (hGrad i j k) (hGrad j k i)
    have h123 := tendsto_L2_add μ
      (fun s x=>fderiv ℝ (B s i j) x (EuclideanSpace.single k 1)+
        fderiv ℝ (B s j k) x (EuclideanSpace.single i 1))
      (fun s x=>fderiv ℝ (B s k i) x (EuclideanSpace.single j 1))
      (fun x=>Db i j x k+Db j k x i) (fun x=>Db k i x j)
      (fun s=>((hOld s i j).2.2 k).add ((hOld s j k).2.2 i))
      (fun s=>(hOld s k i).2.2 j)
      (((hb i j).2.2 k).add ((hb j k).2.2 i)) ((hb k i).2.2 j) h12 (hGrad k i j)
    exact ae_zero_of_strong_L2_zero_sequence μ _ _
      (fun s=>(((hOld s i j).2.2 k).add ((hOld s j k).2.2 i)).add ((hOld s k i).2.2 j))
      ((((hb i j).2.2 k).add ((hb j k).2.2 i)).add ((hb k i).2.2 j)) h123
      (fun s=>Eventually.of_forall (hClosed s i j k))
  have hDivLimit (j : Fin n) : ∀ᵐ x ∂μ,(∑ i : Fin n,Db i j x i)=P x j := by
    have hSum := tendsto_L2_finset_sum μ
      (fun s i x=>fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))
      (fun i x=>Db i j x i) (fun s i=>(hOld s i j).2.2 i) (fun i=>(hb i j).2.2 i)
      (fun i=>hGrad i j i)
    exact ae_eq_of_strong_L2_limits μ _ _ _
      (fun s=>memLp_finsetSum _ (fun i _=>(hOld s i j).2.2 i))
      (memLp_finsetSum _ (fun i _=>(hb i j).2.2 i)) (hP j) hSum (hConv j)
  exact ⟨ae_all_iff.mpr (fun i=>ae_all_iff.mpr (hSkewLimit i)),
    ae_all_iff.mpr (fun i=>ae_all_iff.mpr (fun j=>ae_all_iff.mpr (hClosedLimit i j))),
    ae_all_iff.mpr hDivLimit⟩

/-- Actual strong coefficient and divergence convergence preserves the whole native normal-boundary integration identity. -/
theorem normal_tensor_strong_limit_integration {n q : ℕ}
    (B : ℕ → Fin n → Fin n → Domain n → Ambient q)
    (hB : ∀ s i j,ContDiff ℝ ∞ (B s i j))
    (hNormal : ∀ s j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • B s i j x)=0)
    (b : Fin n → Fin n → Domain n → Ambient q)
    (hb : ∀ i j,MemLp (b i j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hMap : ∀ i j,Tendsto (fun s=>eLpNorm (fun x=>B s i j x-b i j x) 2
      (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0))
    (P : Domain n → Gradient n q)
    (hP : ∀ j,MemLp (fun x=>P x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hConv : ∀ j,Tendsto (fun s=>eLpNorm (fun x=>(∑ i : Fin n,
      fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))-P x j) 2
        (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0))
    (j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q)
    (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
    IntegrableOn (fun x=>∑ i : Fin n,inner ℝ (b i j x) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
      IntegrableOn (fun x=>inner ℝ (P x j) (ψ x)) (ball (0 : Domain n) 1) volume ∧
      (∫ x in ball (0 : Domain n) 1,∑ i : Fin n,inner ℝ (b i j x) (Dψ x i)) =
        -(∫ x in ball (0 : Domain n) 1,inner ℝ (P x j) (ψ x)) := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let d := fun (s : ℕ) (x : Domain n)=>∑ i : Fin n,fderiv ℝ (B s i j) x (EuclideanSpace.single i 1)
  have hOld (s : ℕ) (i : Fin n) : MemLp (B s i j) 2 μ :=
    (memW12_ball_of_ambient_c1 (0 : Domain n) 1 _ ((hB s i j).of_le (by simp))).2.1
  have hdLp (s : ℕ) : MemLp (d s) 2 μ := memLp_finsetSum _ (fun i _=>
    (memW12_ball_of_ambient_c1 (0 : Domain n) 1 _ ((hB s i j).of_le (by simp))).2.2 i)
  have hlI : Integrable (fun x=>∑ i : Fin n,inner ℝ (b i j x) (Dψ x i)) μ :=
    integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hb i j) (hψ.2.2 i))
  have hrI : Integrable (fun x=>inner ℝ (P x j) (ψ x)) μ :=
    HolderToCK.integrable_inner_of_memLp_two (hP j) hψ.2.1
  have hL (i : Fin n) : Tendsto (fun s=>∫ x,inner ℝ (B s i j x) (Dψ x i) ∂μ) atTop
      (𝓝 (∫ x,inner ℝ (b i j x) (Dψ x i) ∂μ)) := by
    simpa only [real_inner_comm] using HolderToCK.tendsto_integral_inner_of_L2
      (fun s=>hOld s i) (hb i j) (hψ.2.2 i) (hMap i j)
  have hR : Tendsto (fun s=>∫ x,inner ℝ (d s x) (ψ x) ∂μ) atTop
      (𝓝 (∫ x,inner ℝ (P x j) (ψ x) ∂μ)) := by
    simpa only [real_inner_comm] using HolderToCK.tendsto_integral_inner_of_L2
      hdLp (hP j) hψ.2.1 (hConv j)
  have hSeq (s : ℕ) : (∑ i : Fin n,∫ x,inner ℝ (B s i j x) (Dψ x i) ∂μ) =
      -(∫ x,inner ℝ (d s x) (ψ x) ∂μ) := by
    rw [← integral_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hOld s i) (hψ.2.2 i))]
    exact (smooth_normal_oneForm_native_integration_by_parts (fun i=>B s i j)
      (fun i=>hB s i j) (hNormal s j) ψ Dψ hψ).2.2
  have hEq := tendsto_nhds_unique (tendsto_finsetSum Finset.univ (fun i _=>hL i))
    (hR.neg.congr' (Eventually.of_forall (fun s=>(hSeq s).symm)))
  refine ⟨hlI,hrI,?_⟩
  rw [integral_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hb i j) (hψ.2.2 i))]
  exact hEq


/-- The actual closed normal smooth divergence range has a true native tensor potential at each actual strong L2 limit, with its original algebraic and full-boundary identities produced. -/
theorem exists_closed_normal_native_tensor_of_divergence_strong_limit {n q : ℕ}
    (B : ℕ → Fin n → Fin n → Domain n → Ambient q)
    (hB : ∀ s i j,ContDiff ℝ ∞ (B s i j))
    (hSkew : ∀ s i j x,B s i j x = -B s j i x)
    (hClosed : ∀ s i j k x,fderiv ℝ (B s i j) x (EuclideanSpace.single k 1)+
      fderiv ℝ (B s j k) x (EuclideanSpace.single i 1)+fderiv ℝ (B s k i) x (EuclideanSpace.single j 1)=0)
    (hNormal : ∀ s j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • B s i j x)=0)
    (P : Domain n → Gradient n q)
    (hP : ∀ j,MemLp (fun x=>P x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hConv : ∀ j,Tendsto (fun s=>eLpNorm (fun x=>(∑ i : Fin n,
      fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))-P x j) 2
        (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0)) :
    ∃ (b : Fin n → Fin n → Domain n → Ambient q)
      (Db : Fin n → Fin n → Domain n → Gradient n q),
      (∀ i j,MemW12 (ballDomain (0 : Domain n) 1) (b i j) (Db i j)) ∧
      (∀ i j,Tendsto (fun s=>eLpNorm (fun x=>B s i j x-b i j x) 2
        (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0)) ∧
      (∀ i j k,Tendsto (fun s=>eLpNorm (fun x=>
        fderiv ℝ (B s i j) x (EuclideanSpace.single k 1)-Db i j x k) 2
          (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0)) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ i j,b i j x = -b j i x) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ i j k,
        Db i j x k+Db j k x i+Db k i x j=0) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ j,
        (∑ i : Fin n,Db i j x i)=P x j) ∧
      ∀ (j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑ i : Fin n,inner ℝ (b i j x) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
        IntegrableOn (fun x=>inner ℝ (P x j) (ψ x)) (ball (0 : Domain n) 1) volume ∧
        (∫ x in ball (0 : Domain n) 1,∑ i : Fin n,inner ℝ (b i j x) (Dψ x i)) =
          -(∫ x in ball (0 : Domain n) 1,inner ℝ (P x j) (ψ x)) := by
  obtain ⟨b,Db,hb,hMap,hGrad⟩ := exists_native_tensor_limit_of_divergence_strong_limit
    B hB hSkew hClosed hNormal P hP hConv
  obtain ⟨hs,hc,hd⟩ := closed_tensor_strong_limit_constraints B hB hSkew hClosed b Db hb hMap hGrad P hP hConv
  refine ⟨b,Db,hb,hMap,hGrad,hs,hc,hd,?_⟩
  exact normal_tensor_strong_limit_integration B hB hNormal b (fun i j=>(hb i j).2.1) hMap P hP hConv

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.ClosedNormalTensorStrongClosure
public import StationaryHarmonicMaps.Analysis.LpSobolevLimit

/-!
# Actual H1 energy bound of the recovered closed normal tensor

Strong convergence of the original maps, derivative columns and divergence
columns gives their actual finite energy limits. The original smooth-core
coercivity inequality therefore controls the same recovered native tensor.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

private theorem norm_sq_energy_limit {n q : ℕ} {μ : Measure (Domain n)} [IsFiniteMeasure μ]
    (f : ℕ → Domain n → Ambient q) (v : Domain n → Ambient q)
    (hf : ∀ s,MemLp (f s) 2 μ) (hv : MemLp v 2 μ)
    (hConv : Tendsto (fun s=>eLpNorm (fun x=>f s x-v x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun s=>∫ x,‖f s x‖^2 ∂μ) atTop (𝓝 (∫ x,‖v x‖^2 ∂μ)) := by
  have hc : Tendsto (fun s=>eLpNorm (f s-v) 2 μ) atTop (𝓝 0) := by
    apply hConv.congr
    intro s
    exact eLpNorm_congr_ae (Eventually.of_forall fun _x=>rfl)
  simpa only [Real.rpow_two] using tendsto_integral_norm_rpow_of_L2 hf hv hc
    (by norm_num : (1:ℝ)≤2) le_rfl

/-- Actual strong recovery from the smooth closed normal core preserves the full native H1 coercivity bound with the original divergence limit. -/
theorem closed_normal_tensor_strong_limit_energy_bound {n q : ℕ}
    (B : ℕ → Fin n → Fin n → Domain n → Ambient q)
    (hB : ∀ s i j,ContDiff ℝ ∞ (B s i j))
    (hSkew : ∀ s i j x,B s i j x = -B s j i x)
    (hClosed : ∀ s i j k x,fderiv ℝ (B s i j) x (EuclideanSpace.single k 1)+
      fderiv ℝ (B s j k) x (EuclideanSpace.single i 1)+fderiv ℝ (B s k i) x (EuclideanSpace.single j 1)=0)
    (hNormal : ∀ s j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • B s i j x)=0)
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
    let e := fun x : Domain n=>∑ j : Fin n,∑ i : Fin n,‖b i j x‖^2
    let g := fun x : Domain n=>∑ j : Fin n,∑ k : Fin n,∑ i : Fin n,‖Db i j x k‖^2
    IntegrableOn e (ball (0 : Domain n) 1) volume ∧
      IntegrableOn g (ball (0 : Domain n) 1) volume ∧
      IntegrableOn (fun x=>hsNormSq (P x)) (ball (0 : Domain n) 1) volume ∧
      (∫ x in ball (0 : Domain n) 1,e x)+(∫ x in ball (0 : Domain n) 1,g x) ≤
        (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)*(∫ x in ball (0 : Domain n) 1,hsNormSq (P x)) := by
  intro e g
  let μ := volume.restrict (ball (0 : Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let E := fun (s : ℕ) (x : Domain n)=>∑ j : Fin n,∑ i : Fin n,‖B s i j x‖^2
  let G := fun (s : ℕ) (x : Domain n)=>∑ j : Fin n,∑ k : Fin n,∑ i : Fin n,
    ‖fderiv ℝ (B s i j) x (EuclideanSpace.single k 1)‖^2
  let D := fun (s : ℕ) (x : Domain n) (j : Fin n)=>∑ i : Fin n,
    fderiv ℝ (B s i j) x (EuclideanSpace.single i 1)
  have hOld (s : ℕ) (i j : Fin n) := memW12_ball_of_ambient_c1 (0 : Domain n) 1 (B s i j)
    ((hB s i j).of_le (by simp))
  have hOldMapLp (s : ℕ) (i j : Fin n) : MemLp (B s i j) 2 μ := (hOld s i j).2.1
  have hOldGradLp (s : ℕ) (i j k : Fin n) : MemLp
      (fun x=>fderiv ℝ (B s i j) x (EuclideanSpace.single k 1)) 2 μ := (hOld s i j).2.2 k
  have hNewMapLp (i j : Fin n) : MemLp (b i j) 2 μ := (hb i j).2.1
  have hNewGradLp (i j k : Fin n) : MemLp (fun x=>Db i j x k) 2 μ := (hb i j).2.2 k
  have hDLp (s : ℕ) (j : Fin n) : MemLp (fun x=>D s x j) 2 μ :=
    memLp_finsetSum _ (fun i _=>(hOldGradLp s i j i))
  have hEI (i j : Fin n) : Integrable (fun x=>‖b i j x‖^2) μ :=
    (hNewMapLp i j).integrable_norm_pow (by decide : (2:ℕ)≠0)
  have hGI (i j k : Fin n) : Integrable (fun x=>‖Db i j x k‖^2) μ :=
    ((hNewGradLp i j k)).integrable_norm_pow (by decide : (2:ℕ)≠0)
  have hPI (j : Fin n) : Integrable (fun x=>‖P x j‖^2) μ :=
    (hP j).integrable_norm_pow (by decide : (2:ℕ)≠0)
  have heI : Integrable e μ := integrable_finsetSum _ (fun j _=>integrable_finsetSum _ (fun i _=>hEI i j))
  have hgI : Integrable g μ := integrable_finsetSum _ (fun j _=>integrable_finsetSum _ (fun k _=>
    integrable_finsetSum _ (fun i _=>hGI i j k)))
  have hpI : Integrable (fun x=>hsNormSq (P x)) μ := integrable_finsetSum _ (fun j _=>hPI j)
  have hESwap (s : ℕ) : (∫ x,E s x ∂μ)=∑ j : Fin n,∑ i : Fin n,∫ x,‖B s i j x‖^2 ∂μ := by
    rw [integral_finsetSum _ (fun j _=>integrable_finsetSum _ (fun i _=>
      (hOldMapLp s i j).integrable_norm_pow (by decide : (2:ℕ)≠0)))]
    exact Finset.sum_congr rfl (fun j _=>integral_finsetSum _ (fun i _=>
      (hOldMapLp s i j).integrable_norm_pow (by decide : (2:ℕ)≠0)))
  have heSwap : (∫ x,e x ∂μ)=∑ j : Fin n,∑ i : Fin n,∫ x,‖b i j x‖^2 ∂μ := by
    rw [integral_finsetSum _ (fun j _=>integrable_finsetSum _ (fun i _=>hEI i j))]
    exact Finset.sum_congr rfl (fun j _=>integral_finsetSum _ (fun i _=>hEI i j))
  have hGSwap (s : ℕ) : (∫ x,G s x ∂μ)=∑ j : Fin n,∑ k : Fin n,∑ i : Fin n,
      ∫ x,‖fderiv ℝ (B s i j) x (EuclideanSpace.single k 1)‖^2 ∂μ := by
    rw [integral_finsetSum _ (fun j _=>integrable_finsetSum _ (fun k _=>integrable_finsetSum _ (fun i _=>
      ((hOldGradLp s i j k)).integrable_norm_pow (by decide : (2:ℕ)≠0))))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum _ (fun k _=>integrable_finsetSum _ (fun i _=>
      ((hOldGradLp s i j k)).integrable_norm_pow (by decide : (2:ℕ)≠0)))]
    exact Finset.sum_congr rfl (fun k _=>integral_finsetSum _ (fun i _=>
      ((hOldGradLp s i j k)).integrable_norm_pow (by decide : (2:ℕ)≠0)))
  have hgSwap : (∫ x,g x ∂μ)=∑ j : Fin n,∑ k : Fin n,∑ i : Fin n,∫ x,‖Db i j x k‖^2 ∂μ := by
    rw [integral_finsetSum _ (fun j _=>integrable_finsetSum _ (fun k _=>integrable_finsetSum _ (fun i _=>hGI i j k)))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum _ (fun k _=>integrable_finsetSum _ (fun i _=>hGI i j k))]
    exact Finset.sum_congr rfl (fun k _=>integral_finsetSum _ (fun i _=>hGI i j k))
  have hDSwap (s : ℕ) : (∫ x,hsNormSq (D s x) ∂μ)=∑ j : Fin n,∫ x,‖D s x j‖^2 ∂μ :=
    integral_finsetSum _ (fun j _=>(hDLp s j).integrable_norm_pow (by decide : (2:ℕ)≠0))
  have hpSwap : (∫ x,hsNormSq (P x) ∂μ)=∑ j : Fin n,∫ x,‖P x j‖^2 ∂μ :=
    integral_finsetSum _ (fun j _=>hPI j)
  have hEConv : Tendsto (fun s=>∫ x,E s x ∂μ) atTop (𝓝 (∫ x,e x ∂μ)) := by
    have H := tendsto_finsetSum Finset.univ (fun j _=>tendsto_finsetSum Finset.univ (fun i _=>
      norm_sq_energy_limit (μ := μ) (fun s=>B s i j) (b i j) (fun s=>(hOldMapLp s i j)) (hNewMapLp i j) (hMap i j)))
    simpa only [← hESwap,← heSwap] using H
  have hGConv : Tendsto (fun s=>∫ x,G s x ∂μ) atTop (𝓝 (∫ x,g x ∂μ)) := by
    have H := tendsto_finsetSum Finset.univ (fun j _=>tendsto_finsetSum Finset.univ (fun k _=>
      tendsto_finsetSum Finset.univ (fun i _=>norm_sq_energy_limit (μ := μ)
        (fun s x=>fderiv ℝ (B s i j) x (EuclideanSpace.single k 1)) (fun x=>Db i j x k)
        (fun s=>(hOldGradLp s i j k)) ((hNewGradLp i j k)) (hGrad i j k))))
    simpa only [← hGSwap,← hgSwap] using H
  have hDConv : Tendsto (fun s=>∫ x,hsNormSq (D s x) ∂μ) atTop (𝓝 (∫ x,hsNormSq (P x) ∂μ)) := by
    have H := tendsto_finsetSum Finset.univ (fun j _=>norm_sq_energy_limit (μ := μ)
      (fun s x=>D s x j) (fun x=>P x j) (fun s=>hDLp s j) (hP j) (hConv j))
    simpa only [← hDSwap,← hpSwap] using H
  refine ⟨heI,hgI,hpI,?_⟩
  exact le_of_tendsto_of_tendsto (hEConv.add hGConv)
    (hDConv.const_mul (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)) (Eventually.of_forall (fun s=>
      (smooth_closed_normal_twoTensor_coercivity (B s) (hB s) (hSkew s) (hClosed s) (hNormal s)).2.2.2))

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.ClosedNormalTensorOperations
public import StationaryHarmonicMaps.Analysis.SobolevQuadraticControl

/-!
# Actual native tensor limits from divergence convergence

The closed normal tensor coercivity controls every original coefficient
and every original derivative column. Actual strong L2 convergence of the
same divergence columns therefore recovers one native strong H1 limit
without a compactness, trace or response assumption.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

private theorem tensor_pair_energy_control {n q : ℕ}
    (B C : Fin n → Fin n → Domain n → Ambient q)
    (hB : ∀ i j,ContDiff ℝ ∞ (B i j)) (hC : ∀ i j,ContDiff ℝ ∞ (C i j))
    (hBS : ∀ i j x,B i j x = -B j i x) (hCS : ∀ i j x,C i j x = -C j i x)
    (hBD : ∀ i j k x,fderiv ℝ (B i j) x (EuclideanSpace.single k 1)+
      fderiv ℝ (B j k) x (EuclideanSpace.single i 1)+fderiv ℝ (B k i) x (EuclideanSpace.single j 1)=0)
    (hCD : ∀ i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
      fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0)
    (hBN : ∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • B i j x)=0)
    (hCN : ∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • C i j x)=0)
    (i j : Fin n) :
    (∫ x in ball (0 : Domain n) 1,‖B i j x-C i j x‖^2) +
      (∫ x in ball (0 : Domain n) 1,hsNormSq (fun k=>
        fderiv ℝ (B i j) x (EuclideanSpace.single k 1)-
          fderiv ℝ (C i j) x (EuclideanSpace.single k 1))) ≤
      (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)*(∑ a : Fin n,∫ x in ball (0 : Domain n) 1,
        ‖(∑ k : Fin n,fderiv ℝ (B k a) x (EuclideanSpace.single k 1))-
          (∑ k : Fin n,fderiv ℝ (C k a) x (EuclideanSpace.single k 1))‖^2) := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let D := fun a b x=>B a b x-C a b x
  obtain ⟨hD,hDS,hDD,hDN⟩ := smooth_closed_normal_twoTensor_sub B C hB hC hBS hCS hBD hCD hBN hCN
  have H := smooth_closed_normal_twoTensor_coercivity D hD hDS hDD hDN
  have hWB (a b : Fin n) := memW12_ball_of_ambient_c1 (0 : Domain n) 1 (B a b) ((hB a b).of_le (by simp))
  have hWC (a b : Fin n) := memW12_ball_of_ambient_c1 (0 : Domain n) 1 (C a b) ((hC a b).of_le (by simp))
  have hDF (a b : Fin n) (x : Domain n) : fderiv ℝ (D a b) x =
      fderiv ℝ (B a b) x-fderiv ℝ (C a b) x := by
    have hh := (((hB a b).differentiable (by simp) x).hasFDerivAt.sub
      ((hC a b).differentiable (by simp) x).hasFDerivAt).fderiv
    have heq : B a b-C a b=D a b := rfl
    rw [heq] at hh
    exact hh
  have hmI : Integrable (fun x=>‖B i j x-C i j x‖^2) μ :=
    ((hWB i j).2.1.sub (hWC i j).2.1).integrable_norm_pow (by decide : (2:ℕ)≠0)
  have hgI : Integrable (fun x=>hsNormSq (fun k=>fderiv ℝ (B i j) x (EuclideanSpace.single k 1)-
      fderiv ℝ (C i j) x (EuclideanSpace.single k 1))) μ :=
    integrable_finsetSum _ (fun k _=>((hWB i j).2.2 k |>.sub ((hWC i j).2.2 k)).integrable_norm_pow
      (by decide : (2:ℕ)≠0))
  have hmPoint (x : Domain n) : ‖B i j x-C i j x‖^2 ≤ ∑ b : Fin n,∑ a : Fin n,‖D a b x‖^2 := by
    calc
      _ ≤ ∑ a : Fin n,‖D a j x‖^2 :=
        Finset.single_le_sum (fun a _=>sq_nonneg ‖D a j x‖) (Finset.mem_univ i)
      _ ≤ _ := Finset.single_le_sum
        (fun b _=>Finset.sum_nonneg (fun a _=>sq_nonneg ‖D a b x‖)) (Finset.mem_univ j)
  have hgPoint (x : Domain n) : hsNormSq (fun k=>fderiv ℝ (B i j) x (EuclideanSpace.single k 1)-
      fderiv ℝ (C i j) x (EuclideanSpace.single k 1)) ≤
        ∑ b : Fin n,∑ k : Fin n,∑ a : Fin n,‖fderiv ℝ (D a b) x (EuclideanSpace.single k 1)‖^2 := by
    calc
      _ = ∑ k : Fin n,‖fderiv ℝ (D i j) x (EuclideanSpace.single k 1)‖^2 := by
        simp only [hsNormSq,hDF,sub_apply]
      _ ≤ ∑ k : Fin n,∑ a : Fin n,‖fderiv ℝ (D a j) x (EuclideanSpace.single k 1)‖^2 :=
        Finset.sum_le_sum (fun k _=>Finset.single_le_sum
          (fun a _=>sq_nonneg ‖fderiv ℝ (D a j) x (EuclideanSpace.single k 1)‖) (Finset.mem_univ i))
      _ ≤ _ := Finset.single_le_sum (fun b _=>Finset.sum_nonneg (fun k _=>
        Finset.sum_nonneg (fun a _=>sq_nonneg ‖fderiv ℝ (D a b) x (EuclideanSpace.single k 1)‖))) (Finset.mem_univ j)
  have hDivEq (a : Fin n) (x : Domain n) : (∑ k : Fin n,fderiv ℝ (D k a) x (EuclideanSpace.single k 1)) =
      (∑ k : Fin n,fderiv ℝ (B k a) x (EuclideanSpace.single k 1))-
        (∑ k : Fin n,fderiv ℝ (C k a) x (EuclideanSpace.single k 1)) := by
    simp only [hDF,sub_apply,Finset.sum_sub_distrib]
  have hDivI (a : Fin n) : Integrable (fun x=>‖(∑ k : Fin n,fderiv ℝ (B k a) x (EuclideanSpace.single k 1))-
      (∑ k : Fin n,fderiv ℝ (C k a) x (EuclideanSpace.single k 1))‖^2) μ := by
    have hLp : MemLp (fun x=>∑ k : Fin n,
        (fderiv ℝ (B k a) x (EuclideanSpace.single k 1)-fderiv ℝ (C k a) x (EuclideanSpace.single k 1))) 2 μ :=
      memLp_finsetSum _ (fun k _=>((hWB k a).2.2 k).sub ((hWC k a).2.2 k))
    simpa only [Finset.sum_sub_distrib] using hLp.integrable_norm_pow (by decide : (2:ℕ)≠0)
  have hDivIntegral : (∫ x,∑ a : Fin n,‖∑ k : Fin n,fderiv ℝ (D k a) x (EuclideanSpace.single k 1)‖^2 ∂μ) =
      ∑ a : Fin n,∫ x,‖(∑ k : Fin n,fderiv ℝ (B k a) x (EuclideanSpace.single k 1))-
        (∑ k : Fin n,fderiv ℝ (C k a) x (EuclideanSpace.single k 1))‖^2 ∂μ := by
    simp_rw [hDivEq]
    exact integral_finsetSum _ (fun a _=>hDivI a)
  calc
    _ ≤ (∫ x,∑ b : Fin n,∑ a : Fin n,‖D a b x‖^2 ∂μ)+
        ∫ x,∑ b : Fin n,∑ k : Fin n,∑ a : Fin n,‖fderiv ℝ (D a b) x (EuclideanSpace.single k 1)‖^2 ∂μ :=
      add_le_add (integral_mono hmI H.1 hmPoint) (integral_mono hgI H.2.1 hgPoint)
    _ ≤ (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)*(∫ x,∑ a : Fin n,
        ‖∑ k : Fin n,fderiv ℝ (D k a) x (EuclideanSpace.single k 1)‖^2 ∂μ) := H.2.2.2
    _ = _ := by rw [hDivIntegral]

/-- Actual strong divergence convergence in the closed normal smooth core produces one native strong coefficient-and-gradient limit. -/
theorem exists_native_tensor_limit_of_divergence_strong_limit {n q : ℕ}
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
      ∀ i j k,Tendsto (fun s=>eLpNorm (fun x=>
        fderiv ℝ (B s i j) x (EuclideanSpace.single k 1)-Db i j x k) 2
          (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0) := by
  let Ω := ballDomain (0 : Domain n) 1
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let W := fun (s : ℕ) (x : Domain n) (j : Fin n)=>∑ i : Fin n,
    fderiv ℝ (B s i j) x (EuclideanSpace.single i 1)
  have hWLp (s : ℕ) (j : Fin n) : MemLp (fun x=>W s x j) 2 μ := by
    have hW : ContDiff ℝ ∞ (fun x=>W s x j) := ContDiff.sum (fun i _=>
      ((hB s i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
    exact (memW12_ball_of_ambient_c1 (0 : Domain n) 1 _ (hW.of_le (by simp))).2.1
  have hWCauchy (j : Fin n) : CauchySeq (fun s=>(hWLp s j).toLp (fun x=>W s x j)) := by
    have H := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun s x=>W s x j) (fun s=>hWLp s j)
      (fun x=>P x j) (hP j)).mpr (hConv j)
    exact H.cauchySeq
  have hExists (i j : Fin n) : ∃ (b : Domain n → Ambient q) (Db : Domain n → Gradient n q),
      MemW12 Ω b Db ∧
      Tendsto (fun s=>eLpNorm (fun x=>B s i j x-b x) 2 μ) atTop (𝓝 0) ∧
      ∀ k,Tendsto (fun s=>eLpNorm (fun x=>
        fderiv ℝ (B s i j) x (EuclideanSpace.single k 1)-Db x k) 2 μ) atTop (𝓝 0) := by
    exact exists_native_strong_limit_of_quadratic_control Ω (fun s=>B s i j)
      (fun s x k=>fderiv ℝ (B s i j) x (EuclideanSpace.single k 1))
      (fun s=>memW12_ball_of_ambient_c1 (0 : Domain n) 1 _ ((hB s i j).of_le (by simp)))
      W hWLp hWCauchy (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)
      (fun s t=>tensor_pair_energy_control (B s) (B t) (hB s) (hB t) (hSkew s) (hSkew t)
        (hClosed s) (hClosed t) (hNormal s) (hNormal t) i j)
  choose b Db hb hMap hGrad using hExists
  exact ⟨b,Db,hb,hMap,hGrad⟩

end StationaryHarmonicMaps.Analysis

end

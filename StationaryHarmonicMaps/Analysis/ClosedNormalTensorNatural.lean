module

public import StationaryHarmonicMaps.Analysis.NormalOneFormIntegration
public import StationaryHarmonicMaps.Analysis.NaturalBallTests
public import StationaryHarmonicMaps.Geometry.OneFormGaffneyIdentity

/-!
# Actual natural divergence identities of normal antisymmetric tensors

The full normal-core integration identity applied to derivatives of a
smooth test cancels by actual Hessian symmetry and antisymmetry. Actual
whole-ball density and strong L2 pairings retain all native boundary tests.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The actual divergence of every smooth antisymmetric normal tensor has all native whole-ball natural zero-divergence tests. -/
theorem smooth_skew_normal_tensor_divergence_native_tests {n q : ℕ}
    (B : Fin n → Fin n → Domain n → Ambient q)
    (hB : ∀ i j,ContDiff ℝ ∞ (B i j))
    (hSkew : ∀ i j x,B i j x = -B j i x)
    (hNormal : ∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • B i j x)=0) :
    let F := fun (x : Domain n) (j : Fin n)=>∑ i : Fin n,fderiv ℝ (B i j) x (EuclideanSpace.single i 1)
    (∀ j,MemLp (fun x=>F x j) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
      ∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑ j : Fin n,inner ℝ (F x j) (Dψ x j)) (ball (0 : Domain n) 1) volume ∧
        (∫ x in ball (0 : Domain n) 1,∑ j : Fin n,inner ℝ (F x j) (Dψ x j))=0 := by
  intro F
  let μ := volume.restrict (ball (0 : Domain n) 1)
  have hFLp (j : Fin n) : MemLp (fun x=>F x j) 2 μ := memLp_finsetSum _ (fun i _=>
    (memW12_ball_of_ambient_c1 (0 : Domain n) 1 _ ((hB i j).of_le (by simp))).2.2 i)
  have hSmooth (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ) :
      (∫ x in ball (0 : Domain n) 1,∑ j : Fin n,inner ℝ (F x j)
        (fderiv ℝ ψ x (EuclideanSpace.single j 1)))=0 := by
    let dψ := fun (j : Fin n) (x : Domain n)=>fderiv ℝ ψ x (EuclideanSpace.single j 1)
    have hdψ (j : Fin n) : ContDiff ℝ ∞ (dψ j) :=
      (hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hIBP (j : Fin n) := smooth_normal_oneForm_integration_by_parts
      (fun i=>B i j) (fun i=>hB i j) (hNormal j) (dψ j) (hdψ j)
    let A := fun (j : Fin n) (x : Domain n)=>∑ i : Fin n,inner ℝ (B i j x)
      (fderiv ℝ (dψ j) x (EuclideanSpace.single i 1))
    have hPoint (x : Domain n) : (∑ j : Fin n,A j x)=0 := by
      have hNeg : (∑ j : Fin n,A j x)=-(∑ j : Fin n,A j x) := by
        calc
          _ = ∑ i : Fin n,∑ j : Fin n,inner ℝ (B i j x)
              (fderiv ℝ (dψ j) x (EuclideanSpace.single i 1)) := Finset.sum_comm
          _ = ∑ j : Fin n,∑ i : Fin n,-(inner ℝ (B i j x)
              (fderiv ℝ (dψ j) x (EuclideanSpace.single i 1))) := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro i _
            change inner ℝ (B j i x) (fderiv ℝ (fun y=>fderiv ℝ ψ y (EuclideanSpace.single i 1)) x
              (EuclideanSpace.single j 1)) = _
            rw [hSkew j i,inner_neg_left,smooth_vector_mixed_fderiv ψ hψ x i j]
          _ = _ := by simp only [A,Finset.sum_neg_distrib]
      linarith only [hNeg]
    have hRI (j : Fin n) : Integrable (fun x=>inner ℝ (F x j) (dψ j x)) μ := (hIBP j).2.1
    have hLI (j : Fin n) : Integrable (A j) μ := (hIBP j).1
    have hR (j : Fin n) : (∫ x,inner ℝ (F x j) (dψ j x) ∂μ)=-(∫ x,A j x ∂μ) := by
      have H := (hIBP j).2.2
      linarith only [H]
    calc
      _ = ∑ j : Fin n,∫ x,inner ℝ (F x j) (dψ j x) ∂μ := integral_finsetSum _ (fun j _=>hRI j)
      _ = -(∑ j : Fin n,∫ x,A j x ∂μ) := by simp only [hR,Finset.sum_neg_distrib]
      _ = -(∫ x,∑ j : Fin n,A j x ∂μ) := by rw [integral_finsetSum _ (fun j _=>hLI j)]
      _ = 0 := by rw [integral_congr_ae (Eventually.of_forall hPoint),integral_zero,neg_zero]
  exact ⟨hFLp,native_ball_tests_of_all_smooth_tests (0 : Domain n) (by norm_num : (0:ℝ)<1) F hFLp hSmooth⟩

/-- Strong convergence of the actual original normal skew tensor divergences preserves all native natural tests. -/
theorem skew_normal_tensor_divergence_limit_native_tests {n q : ℕ}
    (B : ℕ → Fin n → Fin n → Domain n → Ambient q)
    (hB : ∀ s i j,ContDiff ℝ ∞ (B s i j))
    (hSkew : ∀ s i j x,B s i j x = -B s j i x)
    (hNormal : ∀ s j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • B s i j x)=0)
    (P : Domain n → Gradient n q)
    (hP : ∀ j,MemLp (fun x=>P x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hConv : ∀ j,Tendsto (fun s=>eLpNorm (fun x=>(∑ i : Fin n,
      fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))-P x j) 2
        (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0))
    (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q)
    (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
    IntegrableOn (fun x=>∑ j : Fin n,inner ℝ (P x j) (Dψ x j)) (ball (0 : Domain n) 1) volume ∧
      (∫ x in ball (0 : Domain n) 1,∑ j : Fin n,inner ℝ (P x j) (Dψ x j))=0 := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let D := fun (s : ℕ) (x : Domain n) (j : Fin n)=>∑ i : Fin n,fderiv ℝ (B s i j) x (EuclideanSpace.single i 1)
  have hCore (s : ℕ) := smooth_skew_normal_tensor_divergence_native_tests (B s) (hB s) (hSkew s) (hNormal s)
  have hI (j : Fin n) : Integrable (fun x=>inner ℝ (P x j) (Dψ x j)) μ :=
    HolderToCK.integrable_inner_of_memLp_two (hP j) (hψ.2.2 j)
  have hLimit (j : Fin n) : Tendsto (fun s=>∫ x,inner ℝ (D s x j) (Dψ x j) ∂μ) atTop
      (𝓝 (∫ x,inner ℝ (P x j) (Dψ x j) ∂μ)) := by
    simpa only [real_inner_comm] using HolderToCK.tendsto_integral_inner_of_L2
      (fun s=>(hCore s).1 j) (hP j) (hψ.2.2 j) (hConv j)
  have hSeq (s : ℕ) : (∑ j : Fin n,∫ x,inner ℝ (D s x j) (Dψ x j) ∂μ)=0 := by
    rw [← integral_finsetSum _ (fun j _=>
      HolderToCK.integrable_inner_of_memLp_two ((hCore s).1 j) (hψ.2.2 j))]
    exact ((hCore s).2 ψ Dψ hψ).2
  have H := tendsto_nhds_unique (tendsto_finsetSum Finset.univ (fun j _=>hLimit j))
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun s=>(hSeq s).symm)))
  refine ⟨integrable_finsetSum _ (fun j _=>hI j),?_⟩
  rw [integral_finsetSum _ (fun j _=>hI j)]
  exact H

end StationaryHarmonicMaps.Analysis

end

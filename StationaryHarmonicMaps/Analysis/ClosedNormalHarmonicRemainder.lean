module

public import StationaryHarmonicMaps.Analysis.ExactTensorLaplacianTest
public import StationaryHarmonicMaps.Analysis.NormalOneFormMean
public import HolderToCK.Foundation.WeakPoisson

/-!
# Actual coefficient harmonicity from closed-normal variational tests

A genuine supported single-component exact tensor has divergence equal to
a coefficient Laplacian minus a gradient. Its variational identity and the
original zero-divergence equation therefore give the actual distributional
Laplacian equation of each original L2 coefficient.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual L2 zero-divergence fields orthogonal to the smooth closed normal divergence tests have harmonic coefficient distributions. -/
theorem coefficient_laplacian_pairing_zero_of_closed_normal_tests {n q : ℕ}
    (h : Domain n → Gradient n q)
    (hL2 : ∀ j,MemLp (fun x=>h x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hDiv : HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) h (fun _=>0))
    (hTests : ∀ C : Fin n → Fin n → Domain n → Ambient q,
      (∀ i j,ContDiff ℝ ∞ (C i j)) → (∀ i j x,C i j x = -C j i x) →
      (∀ i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
        fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0) →
      (∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • C i j x)=0) →
      (∫ x in ball (0 : Domain n) 1,∑ j : Fin n,inner ℝ (h x j)
        (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)))=0)
    (l : Fin n) (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ ball (0 : Domain n) 1) :
    IntegrableOn (fun x=>inner ℝ (h x l) (Laplacian.laplacian ψ x)) (ball (0 : Domain n) 1) volume ∧
      (∫ x in ball (0 : Domain n) 1,inner ℝ (h x l) (Laplacian.laplacian ψ x))=0 := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let φ := fun (a : Fin n) (x : Domain n)=>if a=l then ψ x else 0
  let C := fun i j (x : Domain n)=>fderiv ℝ (φ j) x (EuclideanSpace.single i 1)-
    fderiv ℝ (φ i) x (EuclideanSpace.single j 1)
  obtain ⟨hC,hCS,hCD,hCN,hCdiv⟩ := single_component_exact_twoTensor_test ψ hψ hsψ l
  let dψ := fun x : Domain n=>fderiv ℝ ψ x (EuclideanSpace.single l 1)
  have hdψ : ContDiff ℝ ∞ dψ := (hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcdψ : HasCompactSupport dψ := hcψ.fderiv_apply ℝ (EuclideanSpace.single l 1)
  have hsdψ : tsupport dψ ⊆ (ballDomain (0 : Domain n) 1).val :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single l 1)).trans hsψ
  have hDivTest := hDiv.2 dψ hdψ hcdψ hsdψ
  have hGradI : Integrable (fun x=>∑ j : Fin n,inner ℝ (h x j)
      (fderiv ℝ dψ x (EuclideanSpace.single j 1))) μ := hDivTest.1
  have hGradZero : (∫ x,∑ j : Fin n,inner ℝ (h x j)
      (fderiv ℝ dψ x (EuclideanSpace.single j 1)) ∂μ)=0 := by
    simpa only [μ,ballDomain,inner_zero_left,integral_zero,neg_zero] using hDivTest.2.2
  have hLapLp : MemLp (Laplacian.laplacian ψ) 2 μ := by
    have hSum : MemLp (fun x=>∑ i : Fin n,fderiv ℝ
        (fun y=>fderiv ℝ ψ y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) 2 μ := by
      apply memLp_finsetSum
      intro i _
      have hd1 : ContDiff ℝ ∞ (fun x : Domain n=>fderiv ℝ ψ x (EuclideanSpace.single i 1)) :=
        (hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      have hd2 : ContDiff ℝ ∞ (fun x : Domain n=>fderiv ℝ
          (fun y=>fderiv ℝ ψ y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) :=
        (hd1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      exact (memW12_ball_of_ambient_c1 (0 : Domain n) 1 _ (hd2.of_le (by simp))).2.1
    exact MemLp.ae_eq (Eventually.of_forall (fun x=>(smooth_vector_laplacian_eq_coordinate_sum ψ hψ x).symm)) hSum
  have hLapI : Integrable (fun x=>inner ℝ (h x l) (Laplacian.laplacian ψ x)) μ :=
    HolderToCK.integrable_inner_of_memLp_two (hL2 l) hLapLp
  have hFormula (a : Fin n) (x : Domain n) : (∑ i : Fin n,fderiv ℝ (C i a) x (EuclideanSpace.single i 1)) =
      (if a=l then Laplacian.laplacian ψ x else 0)-fderiv ℝ dψ x (EuclideanSpace.single a 1) := hCdiv a x
  have hPoint (x : Domain n) : (∑ a : Fin n,inner ℝ (h x a)
      (∑ i : Fin n,fderiv ℝ (C i a) x (EuclideanSpace.single i 1))) =
        inner ℝ (h x l) (Laplacian.laplacian ψ x)-
          ∑ a : Fin n,inner ℝ (h x a) (fderiv ℝ dψ x (EuclideanSpace.single a 1)) := by
    simp only [hFormula,inner_sub_right,Finset.sum_sub_distrib]
    congr 1
    have hIf (a : Fin n) : inner ℝ (h x a) (if a=l then Laplacian.laplacian ψ x else 0)=
        if a=l then inner ℝ (h x a) (Laplacian.laplacian ψ x) else 0 := by
      by_cases ha : a=l <;> simp only [ha,ite_true,ite_false,inner_zero_right]
    simp only [hIf,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have H := hTests C hC hCS hCD hCN
  rw [integral_congr_ae (Eventually.of_forall hPoint)] at H
  have hSplit : (∫ x,inner ℝ (h x l) (Laplacian.laplacian ψ x)-
      (∑ a : Fin n,inner ℝ (h x a) (fderiv ℝ dψ x (EuclideanSpace.single a 1))) ∂μ) =
        (∫ x,inner ℝ (h x l) (Laplacian.laplacian ψ x) ∂μ)-
          (∫ x,∑ a : Fin n,inner ℝ (h x a) (fderiv ℝ dψ x (EuclideanSpace.single a 1)) ∂μ) := by
    simpa only [Pi.sub_apply] using integral_sub hLapI hGradI
  rw [hSplit,hGradZero,sub_zero] at H
  exact ⟨hLapI,H⟩

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.DistributionHarmonicMollification
public import HarmonicMaps.SobolevLemmas
public import HolderToCK.Foundation.WeakPoisson

/-!
# The distributional Laplacian of the same actual weak harmonic graph

The original weak-gradient identity is tested with each actual first
coordinate derivative of a compact scalar test. The original zero-forcing
vector equation annihilates their genuine Bochner sum. This produces the
literal scalar-test distribution identity needed by the Weyl theorem.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The original weak harmonic graph gives actual integrable scalar Laplacian tests of the same map; no smooth representative or distribution identity is assumed. -/
theorem distribution_laplacian_zero_of_weak_harmonic_graph {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : HasWeakGradient Ω u Du) (hEq : HolderToCK.WeakPoissonOn Ω Du (fun _=>(0:Ambient q)))
    (η : Domain n → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η⊆Ω.val) :
    IntegrableOn (fun x=>Laplacian.laplacian η x • u x) Ω.val volume ∧
      (∫x in Ω.val,Laplacian.laplacian η x • u x)=0 := by
  let d := fun (i : Fin n) (x : Domain n)=>fderiv ℝ η x (EuclideanSpace.single i 1)
  have hd (i : Fin n) : ContDiff ℝ ∞ (d i) :=
    (hη.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hc (i : Fin n) : HasCompactSupport (d i) := hcη.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hs (i : Fin n) : tsupport (d i)⊆Ω.val :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsη
  have hDI (i : Fin n) := hu.integrable_test_gradient i (hd i) (hc i) (hs i)
  have hLI (i : Fin n) := hu.integrable_test_derivative i (hd i) (hc i) (hs i)
  have hSumI : IntegrableOn (fun x=>∑i : Fin n,d i x • Du x i) Ω.val volume :=
    integrable_finsetSum _ (fun i _=>hDI i)
  have hSumZero : (∫x in Ω.val,∑i : Fin n,d i x • Du x i)=0 := by
    apply ext_inner_left ℝ
    intro v
    rw [← integral_inner hSumI v,inner_zero_right]
    let ψ := fun x : Domain n=>η x • v
    have hψ : ContDiff ℝ ∞ ψ := hη.smul contDiff_const
    have hcψ : HasCompactSupport ψ := hcη.smul_right
    have hsψ : tsupport ψ⊆Ω.val := (tsupport_smul_subset_left η (fun _=>v)).trans hsη
    have hDψ (x : Domain n) (i : Fin n) : fderiv ℝ ψ x (EuclideanSpace.single i 1)=d i x • v := by
      change fderiv ℝ (fun x=>η x • v) x (EuclideanSpace.single i 1)=_
      rw [fderiv_smul_const (hη.differentiable (by simp) x) v]
      rfl
    have hPoint (x : Domain n) : inner ℝ v (∑i : Fin n,d i x • Du x i)=
        ∑i : Fin n,inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
      rw [inner_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hDψ,real_inner_smul_right,real_inner_smul_right,real_inner_comm v (Du x i)]
    rw [integral_congr_ae (Eventually.of_forall hPoint)]
    simpa only [inner_zero_left,integral_zero,neg_zero] using (hEq.2 ψ hψ hcψ hsψ).2.2
  have hLap (x : Domain n) : Laplacian.laplacian η x • u x=
      ∑i : Fin n,coordinateDerivative (d i) (hd i) i x • u x := by
    rw [laplacian_eq_sum_second_coordinate η hη x,Finset.sum_smul]
    rfl
  have hI := integrable_finsetSum Finset.univ (fun i _=>hLI i)
  refine ⟨hI.congr (Eventually.of_forall fun x=>(hLap x).symm),?_⟩
  calc
    _ = ∫x in Ω.val,∑i : Fin n,coordinateDerivative (d i) (hd i) i x • u x :=
      integral_congr_ae (Eventually.of_forall hLap)
    _ = ∑i : Fin n,∫x in Ω.val,coordinateDerivative (d i) (hd i) i x • u x :=
      integral_finsetSum _ (fun i _=>hLI i)
    _ = ∑i : Fin n,-(∫x in Ω.val,d i x • Du x i) :=
      Finset.sum_congr rfl (fun i _=>hu.2.2 i (d i) (hd i) (hc i) (hs i))
    _ = -(∫x in Ω.val,∑i : Fin n,d i x • Du x i) := by
      rw [Finset.sum_neg_distrib,integral_finsetSum _ (fun i _=>hDI i)]
    _ = 0 := by rw [hSumZero,neg_zero]

end StationaryHarmonicMaps.Analysis

end

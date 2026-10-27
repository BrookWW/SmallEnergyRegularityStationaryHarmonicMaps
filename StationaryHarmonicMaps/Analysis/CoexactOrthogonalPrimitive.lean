module

public import StationaryHarmonicMaps.Analysis.RelativeCoexactKernel
public import StationaryHarmonicMaps.Analysis.NeumannGradientProjection
public import StationaryHarmonicMaps.Analysis.ClosedNormalTensorNatural
public import HarmonicMaps.Analysis.SobolevAECongruence

/-!
# Native primitives of the relative coexact orthogonal complement

The actual Neumann response splits off a native gradient. Its natural
residual retains orthogonality to all smooth closed normal divergences,
so the relative kernel theorem identifies the original field itself as
the displayed native weak gradient.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Orthogonality to the actual relative coexact core produces a mean-zero native primitive with the original raw field as its explicit weak gradient. -/
theorem exists_native_primitive_of_coexact_orthogonality {n q : ℕ} (hn : 1≤n)
    (F : Domain n → Gradient n q)
    (hF : ∀j,MemLp (fun x=>F x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hCore : ∀ C : Fin n → Fin n → Domain n → Ambient q,
      (∀i j,ContDiff ℝ ∞ (C i j)) → (∀i j x,C i j x= -C j i x) →
      (∀i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
        fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0) →
      (∀j (x : Domain n),‖x‖=1 → (∑i : Fin n,x i • C i j x)=0) →
      (∫x in ball (0 : Domain n) 1,∑j : Fin n,inner ℝ (F x j)
        (∑i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)))=0) :
    ∃g : Domain n → Ambient q,MemW12 (ballDomain (0 : Domain n) 1) g F ∧
      (∫x in ball (0 : Domain n) 1,g x)=0 := by
  let Ω := ballDomain (0 : Domain n) 1
  let μ := volume.restrict (ball (0 : Domain n) 1)
  obtain ⟨g,Dg,hg,hMean,_hEnergy,hTests⟩ := exists_neumann_gradient_projection
    (0 : Domain n) (by norm_num : (0 : ℝ)<1) F hF
  let h := fun x j=>F x j-Dg x j
  have hHLp (j : Fin n) : MemLp (fun x=>h x j) 2 μ := (hF j).sub (hg.2.2 j)
  have hNatural (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q)
      (hψ : MemW12 Ω ψ Dψ) : (∫x,∑j : Fin n,inner ℝ (h x j) (Dψ x j) ∂μ)=0 := by
    obtain ⟨hDI,hFI,hEq⟩ := hTests ψ Dψ hψ
    simp only [h,inner_sub_left,Finset.sum_sub_distrib]
    have hDI' : Integrable (fun x=>∑j : Fin n,inner ℝ (Dg x j) (Dψ x j)) μ := hDI
    have hFI' : Integrable (fun x=>∑j : Fin n,inner ℝ (F x j) (Dψ x j)) μ := hFI
    rw [integral_sub hFI' hDI',← hEq,sub_self]
  have hHCore (C : Fin n → Fin n → Domain n → Ambient q)
      (hC : ∀i j,ContDiff ℝ ∞ (C i j)) (hCS : ∀i j x,C i j x= -C j i x)
      (hCD : ∀i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
        fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0)
      (hCN : ∀j (x : Domain n),‖x‖=1 → (∑i : Fin n,x i • C i j x)=0) :
      (∫x in ball (0 : Domain n) 1,∑j : Fin n,inner ℝ (h x j)
        (∑i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)))=0 := by
    let dC := fun x j=>∑i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)
    have hdC (j : Fin n) : MemLp (fun x=>dC x j) 2 μ := by
      have hSmooth : ContDiff ℝ ∞ (fun x=>dC x j) := ContDiff.sum fun i _=>
        ((hC i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      exact (memW12_ball_of_ambient_c1 (0 : Domain n) 1 _ (hSmooth.of_le (by simp))).2.1
    have hFI : Integrable (fun x=>∑j : Fin n,inner ℝ (F x j) (dC x j)) μ :=
      integrable_finsetSum _ (fun j _=>HolderToCK.integrable_inner_of_memLp_two (hF j) (hdC j))
    have hDI : Integrable (fun x=>∑j : Fin n,inner ℝ (Dg x j) (dC x j)) μ :=
      integrable_finsetSum _ (fun j _=>HolderToCK.integrable_inner_of_memLp_two (hg.2.2 j) (hdC j))
    have hDZero := ((smooth_skew_normal_tensor_divergence_native_tests C hC hCS hCN).2 g Dg hg).2
    have hDZero' : (∫x,∑j : Fin n,inner ℝ (Dg x j) (dC x j) ∂μ)=0 := by
      simpa only [real_inner_comm] using hDZero
    change (∫x,∑j : Fin n,inner ℝ (h x j) (dC x j) ∂μ)=0
    simp only [h,inner_sub_left,Finset.sum_sub_distrib]
    rw [integral_sub hFI hDI,hCore C hC hCS hCD hCN,hDZero',sub_self]
  obtain ⟨_hEnergyZero,hZero⟩ := natural_coexact_kernel_eq_zero_unitBall hn h hHLp hNatural hHCore
  have hDgF : Dg=ᵐ[μ]F := by
    filter_upwards [hZero] with x hx
    funext j
    have H := congrFun hx j
    change F x j-Dg x j=0 at H
    exact (sub_eq_zero.mp H).symm
  exact ⟨g,hg.congr_ae (Eventually.of_forall fun _=>rfl) hDgF,hMean⟩

end StationaryHarmonicMaps.Analysis

end

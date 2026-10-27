module

public import StationaryHarmonicMaps.Analysis.WeakHodgeDecomposition
public import StationaryHarmonicMaps.Analysis.CoexactOrthogonalPrimitive

/-!
# Relative Hodge decomposition with a genuine closed harmonic remainder

Raw L2 data produce the original zero-boundary and closed normal tensor
responses. Orthogonality to the relative coexact core identifies their same
harmonic remainder as an actual native weak gradient. Both its exterior
closedness and its zero divergence follow without additional source data.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Original L2 data alone produce a relative Hodge decomposition whose same remainder is a native harmonic gradient, with the original normal boundary identity and energy bounds. -/
theorem exists_L2_relative_hodge_decomposition_unitBall {n q : ℕ} (hn : 2 ≤ n)
    (F : Domain n → Gradient n q)
    (hF : ∀ j,MemLp (fun x=>F x j) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    ∃ (f : Domain n → Ambient q) (Df : Domain n → Gradient n q)
      (b : Fin n → Fin n → Domain n → Ambient q)
      (Db : Fin n → Fin n → Domain n → Gradient n q) (P h : Domain n → Gradient n q) (g : Domain n → Ambient q),
      HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) f Df ∧
      MemW12 (ballDomain (0 : Domain n) 1) g h ∧
      (∫x in ball (0 : Domain n) 1,g x)=0 ∧
      (∀ i j,MemW12 (ballDomain (0 : Domain n) 1) (b i j) (Db i j)) ∧
      (∀ j,MemLp (fun x=>P x j) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ i j,b i j x = -b j i x) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ i j k,Db i j x k+Db j k x i+Db k i x j=0) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ j,(∑ i : Fin n,Db i j x i)=P x j) ∧
      (∀ (j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑ i : Fin n,inner ℝ (b i j x) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
        IntegrableOn (fun x=>inner ℝ (P x j) (ψ x)) (ball (0 : Domain n) 1) volume ∧
        (∫x in ball (0 : Domain n) 1,∑ i : Fin n,inner ℝ (b i j x) (Dψ x i)) =
          -(∫x in ball (0 : Domain n) 1,inner ℝ (P x j) (ψ x))) ∧
      (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑ j : Fin n,inner ℝ (P x j) (Dψ x j)) (ball (0 : Domain n) 1) volume ∧
        (∫x in ball (0 : Domain n) 1,∑ j : Fin n,inner ℝ (P x j) (Dψ x j))=0) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ j,
        F x j=Df x j+(∑ i : Fin n,Db i j x i)+h x j) ∧
      (∀ j,MemLp (fun x=>h x j) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
      HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) h (fun _=>0) ∧
      (∀ (j : Fin n) (ψ : Domain n → Ambient q),ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ ball (0 : Domain n) 1 →
        IntegrableOn (fun x=>inner ℝ (h x j) (Laplacian.laplacian ψ x)) (ball (0 : Domain n) 1) volume ∧
        (∫x in ball (0 : Domain n) 1,inner ℝ (h x j) (Laplacian.laplacian ψ x))=0) ∧
      ((∫x in ball (0 : Domain n) 1,hsNormSq (Df x))≤∫x in ball (0 : Domain n) 1,hsNormSq (F x)) ∧
      ((∫x in ball (0 : Domain n) 1,hsNormSq (P x))≤∫x in ball (0 : Domain n) 1,hsNormSq (F x)) ∧
      ((∫x in ball (0 : Domain n) 1,∑ j : Fin n,∑ i : Fin n,‖b i j x‖^2)+
        (∫x in ball (0 : Domain n) 1,∑ j : Fin n,∑ k : Fin n,∑ i : Fin n,‖Db i j x k‖^2) ≤
        (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)*(∫x in ball (0 : Domain n) 1,hsNormSq (F x))) ∧
      ∀ C : Fin n → Fin n → Domain n → Ambient q,
        (∀ i j,ContDiff ℝ ∞ (C i j)) → (∀ i j x,C i j x = -C j i x) →
        (∀ i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
          fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0) →
        (∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • C i j x)=0) →
        IntegrableOn (fun x=>∑ j : Fin n,inner ℝ (P x j)
          (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1))) (ball (0 : Domain n) 1) volume ∧
        IntegrableOn (fun x=>∑ j : Fin n,inner ℝ (F x j)
          (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1))) (ball (0 : Domain n) 1) volume ∧
        (∫x in ball (0 : Domain n) 1,∑ j : Fin n,inner ℝ (P x j)
          (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1))) =
        ∫x in ball (0 : Domain n) 1,∑ j : Fin n,inner ℝ (F x j)
          (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)) := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  obtain ⟨f,Df,b,Db,P,h,hf,hb,hP,hSkew,hClosed,hDivB,hNormal,hPNatural,hDecomp,hHLp,hHDiv,
    hHarm,hfEnergy,hPEnergy,hBEnergy,hPTests⟩ :=
    exists_L2_closed_normal_decomposition_harmonic_remainder_unitBall hn F hF
  have hResidual : ∀ᵐ x ∂μ,∀j,h x j=F x j-Df x j-P x j := by
    filter_upwards [hDecomp,hDivB] with x hx hDx j
    have H := hx j
    rw [hDx j] at H
    rw [H]
    abel
  have hHCore (C : Fin n → Fin n → Domain n → Ambient q)
      (hC : ∀i j,ContDiff ℝ ∞ (C i j)) (hCS : ∀i j x,C i j x= -C j i x)
      (hCD : ∀i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
        fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0)
      (hCN : ∀j (x : Domain n),‖x‖=1 → (∑i : Fin n,x i • C i j x)=0) :
      (∫x in ball (0 : Domain n) 1,∑j : Fin n,inner ℝ (h x j)
        (∑i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)))=0 := by
    let dC := fun x j=>∑i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)
    obtain ⟨hPI,hFI,hEq⟩ := hPTests C hC hCS hCD hCN
    obtain ⟨hDI,hDZero⟩ := (smooth_skew_normal_tensor_divergence_native_tests C hC hCS hCN).2 f Df hf.1
    have hDPairI : Integrable (fun x=>∑j : Fin n,inner ℝ (Df x j) (dC x j)) μ :=
      hDI.congr (Eventually.of_forall fun x=>Finset.sum_congr rfl fun j _=>real_inner_comm _ _)
    have hDPairZero : (∫x,∑j : Fin n,inner ℝ (Df x j) (dC x j) ∂μ)=0 := by
      simpa only [real_inner_comm] using hDZero
    have hPoint : (fun x=>∑j : Fin n,inner ℝ (h x j) (dC x j))=ᵐ[μ]
        (fun x=>(∑j : Fin n,inner ℝ (F x j) (dC x j))-
          (∑j : Fin n,inner ℝ (Df x j) (dC x j))-(∑j : Fin n,inner ℝ (P x j) (dC x j))) := by
      filter_upwards [hResidual] with x hx
      simp only [hx,inner_sub_left,Finset.sum_sub_distrib]
    have hFI' : Integrable (fun x=>∑j : Fin n,inner ℝ (F x j) (dC x j)) μ := hFI
    have hPI' : Integrable (fun x=>∑j : Fin n,inner ℝ (P x j) (dC x j)) μ := hPI
    have H1 := integral_sub (hFI'.sub hDPairI) hPI'
    have H2 := integral_sub hFI' hDPairI
    simp only [Pi.sub_apply] at H1 H2
    change (∫x,∑j : Fin n,inner ℝ (h x j) (dC x j) ∂μ)=0
    rw [integral_congr_ae hPoint,H1,H2,hDPairZero,sub_zero,← hEq,sub_self]
  obtain ⟨g,hg,hMean⟩ := exists_native_primitive_of_coexact_orthogonality (by omega : 1≤n) h hHLp hHCore
  exact ⟨f,Df,b,Db,P,h,g,hf,hg,hMean,hb,hP,hSkew,hClosed,hDivB,hNormal,hPNatural,hDecomp,hHLp,
    hHDiv,hHarm,hfEnergy,hPEnergy,hBEnergy,hPTests⟩

end StationaryHarmonicMaps.Analysis

end

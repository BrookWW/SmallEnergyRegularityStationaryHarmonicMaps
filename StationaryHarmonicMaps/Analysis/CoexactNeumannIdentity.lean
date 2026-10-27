module

public import StationaryHarmonicMaps.Analysis.CoexactDualOperator
public import StationaryHarmonicMaps.Analysis.CoexactOrthogonalPrimitive

/-!
# The same coexact operator is the complement of the native Neumann response

The actual closed-normal projection has a native mean-zero primitive for its
complement. Its original natural tests identify that same primitive as the
Neumann response, and uniqueness compares it with every native response.
Both operators retain the original raw L2 representatives.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- One actual relative coexact projection retains all its native tensor outputs and has the same native mean-zero Neumann complement for every raw L2 field. -/
theorem exists_coexact_projection_with_neumann_complement_unitBall {n q : ℕ} (hn : 1 ≤ n) :
    let μ := volume.restrict (ball (0 : Domain n) 1)
    let E : Gradient n q → Ambient (n*q) := fun A=>WithLp.toLp 2
      (fun k=>A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    let D := fun (V : Domain n → Ambient (n*q)) (x : Domain n) (j : Fin n)=>
      WithLp.toLp 2 (fun a : Fin q=>V x (finProdFinEquiv (j,a)))
    let G : Set (Lp (Ambient (n*q)) 2 μ) := {Z | ∃ B : Fin n → Fin n → Domain n → Ambient q,
      (∀ i j,ContDiff ℝ ∞ (B i j)) ∧
      (∀ i j x,B i j x = -B j i x) ∧
      (∀ i j k x,fderiv ℝ (B i j) x (EuclideanSpace.single k 1)+
        fderiv ℝ (B j k) x (EuclideanSpace.single i 1)+fderiv ℝ (B k i) x (EuclideanSpace.single j 1)=0) ∧
      (∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • B i j x)=0) ∧
      (Z : Domain n → Ambient (n*q)) =ᵐ[μ]
        (fun x=>E (fun j=>∑ i : Fin n,fderiv ℝ (B i j) x (EuclideanSpace.single i 1)))}
    ∃ T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
      ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀ V,T (T V)=T V) ∧
      T.range=(Submodule.span ℝ G).topologicalClosure ∧
      (∀ V W : Lp (Ambient (n*q)) 2 μ,Integrable (fun x=>∑ j : Fin n,inner ℝ (D (T V) x j) (D W x j)) μ ∧
        Integrable (fun x=>∑ j : Fin n,inner ℝ (D V x j) (D (T W) x j)) μ ∧
        (∫x,∑ j : Fin n,inner ℝ (D (T V) x j) (D W x j) ∂μ)=
          ∫x,∑ j : Fin n,inner ℝ (D V x j) (D (T W) x j) ∂μ) ∧
      (∀ V : Lp (Ambient (n*q)) 2 μ,
        ∃ (b : Fin n → Fin n → Domain n → Ambient q)
          (Db : Fin n → Fin n → Domain n → Gradient n q),
          (∀ i j,MemW12 (ballDomain (0 : Domain n) 1) (b i j) (Db i j)) ∧
          (∀ᵐ x ∂μ,∀ i j,b i j x = -b j i x) ∧
          (∀ᵐ x ∂μ,∀ i j k,Db i j x k+Db j k x i+Db k i x j=0) ∧
          (∀ᵐ x ∂μ,∀ j,(∑ i : Fin n,Db i j x i)=D (T V) x j) ∧
          (∀ (j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
            MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑ i : Fin n,inner ℝ (b i j x) (Dψ x i)) μ ∧
            Integrable (fun x=>inner ℝ (D (T V) x j) (ψ x)) μ ∧
            (∫x,∑ i : Fin n,inner ℝ (b i j x) (Dψ x i) ∂μ)=
              -(∫x,inner ℝ (D (T V) x j) (ψ x) ∂μ)) ∧
          (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
            MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑ j : Fin n,inner ℝ (D (T V) x j) (Dψ x j)) μ ∧
            (∫x,∑ j : Fin n,inner ℝ (D (T V) x j) (Dψ x j) ∂μ)=0) ∧
          Integrable (fun x=>∑ j : Fin n,∑ i : Fin n,‖b i j x‖^2) μ ∧
          Integrable (fun x=>∑ j : Fin n,∑ k : Fin n,∑ i : Fin n,‖Db i j x k‖^2) μ ∧
          (∫x,hsNormSq (D (T V) x) ∂μ)≤∫x,hsNormSq (D V x) ∂μ ∧
          (∫x,∑ j : Fin n,∑ i : Fin n,‖b i j x‖^2 ∂μ)+
            (∫x,∑ j : Fin n,∑ k : Fin n,∑ i : Fin n,‖Db i j x k‖^2 ∂μ)≤
              (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)*(∫x,hsNormSq (D (T V) x) ∂μ) ) ∧
      ∀ V : Lp (Ambient (n*q)) 2 μ,
        ∃ f : Domain n → Ambient q,
          MemW12 (ballDomain (0 : Domain n) 1) f (fun x j => D V x j - D (T V) x j) ∧
          (∫ x, f x ∂μ) = 0 ∧
          (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
            MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
            Integrable (fun x => ∑ j : Fin n, inner ℝ (D V x j - D (T V) x j) (Dψ x j)) μ ∧
            (∫ x, ∑ j : Fin n, inner ℝ (D V x j - D (T V) x j) (Dψ x j) ∂μ) =
              ∫ x, ∑ j : Fin n, inner ℝ (D V x j) (Dψ x j) ∂μ) ∧
          ∀ (g : Domain n → Ambient q) (Dg : Domain n → Gradient n q),
            MemW12 (ballDomain (0 : Domain n) 1) g Dg →
            (∫ x, g x ∂μ) = 0 →
            (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
              MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
              (∫ x, ∑ j : Fin n, inner ℝ (Dg x j) (Dψ x j) ∂μ) =
                ∫ x, ∑ j : Fin n, inner ℝ (D V x j) (Dψ x j) ∂μ) →
            g =ᵐ[μ] f ∧ Dg =ᵐ[μ] (fun x j => D V x j - D (T V) x j)
 := by
  intro μ E D G
  obtain ⟨T, hNorm, hAdj, hIdem, hRange, hPair, hNative⟩ :=
    exists_native_coexact_L2_projection_operator_unitBall n q
  refine ⟨T, hNorm, hAdj, hIdem, hRange, hPair, hNative, ?_⟩
  intro V
  let F := fun x j => D V x j - D (T V) x j
  have hVLp (j : Fin n) : MemLp (fun x => D V x j) 2 μ :=
    memLp_hs_unflatten V (Lp.memLp V) j
  have hTVLp (j : Fin n) : MemLp (fun x => D (T V) x j) 2 μ :=
    memLp_hs_unflatten (T V) (Lp.memLp (T V)) j
  have hF (j : Fin n) : MemLp (fun x => F x j) 2 μ := (hVLp j).sub (hTVLp j)
  have hCore (C : Fin n → Fin n → Domain n → Ambient q)
      (hC : ∀ i j, ContDiff ℝ ∞ (C i j)) (hCS : ∀ i j x, C i j x = -C j i x)
      (hCD : ∀ i j k x, fderiv ℝ (C i j) x (EuclideanSpace.single k 1) +
        fderiv ℝ (C j k) x (EuclideanSpace.single i 1) +
        fderiv ℝ (C k i) x (EuclideanSpace.single j 1) = 0)
      (hCN : ∀ j (x : Domain n), ‖x‖ = 1 → (∑ i : Fin n, x i • C i j x) = 0) :
      (∫ x, ∑ j : Fin n, inner ℝ (F x j)
        (∑ i : Fin n, fderiv ℝ (C i j) x (EuclideanSpace.single i 1)) ∂μ) = 0 := by
    let dC := fun (x : Domain n) (j : Fin n) => ∑ i : Fin n,
      fderiv ℝ (C i j) x (EuclideanSpace.single i 1)
    have hCLp (j : Fin n) : MemLp (fun x => dC x j) 2 μ :=
      (smooth_skew_normal_tensor_divergence_native_tests C hC hCS hCN).1 j
    have hEC : MemLp (fun x => E (dC x)) 2 μ := memLp_hs_flatten dC hCLp
    let W : Lp (Ambient (n*q)) 2 μ := hEC.toLp (fun x => E (dC x))
    have hW : (W : Domain n → Ambient (n*q)) =ᵐ[μ] (fun x => E (dC x)) := hEC.coeFn_toLp
    have hWCore : W ∈ G := ⟨C, hC, hCS, hCD, hCN, hW⟩
    have hWRange : W ∈ T.range := by
      rw [hRange]
      exact (Submodule.span ℝ G).le_topologicalClosure (Submodule.subset_span hWCore)
    obtain ⟨Y, hY⟩ := hWRange
    have hTW : T W = W := by
      rw [← hY]
      exact hIdem Y
    have hDecoded : D W =ᵐ[μ] dC := by
      filter_upwards [hW] with x hx
      change (fun j => WithLp.toLp 2 (fun a : Fin q => W x (finProdFinEquiv (j,a)))) = dC x
      rw [hx]
      exact hs_unflatten_flatten (dC x)
    have HP := (hPair V W).2.2
    rw [hTW] at HP
    have hL : (∫ x, ∑ j : Fin n, inner ℝ (D (T V) x j) (D W x j) ∂μ) =
        ∫ x, ∑ j : Fin n, inner ℝ (D (T V) x j) (dC x j) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hDecoded] with x hx
      rw [hx]
    have hR : (∫ x, ∑ j : Fin n, inner ℝ (D V x j) (D W x j) ∂μ) =
        ∫ x, ∑ j : Fin n, inner ℝ (D V x j) (dC x j) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hDecoded] with x hx
      rw [hx]
    rw [hL, hR] at HP
    have hVI := integrable_finsetSum Finset.univ (fun j _ =>
      HolderToCK.integrable_inner_of_memLp_two (hVLp j) (hCLp j))
    have hTI := integrable_finsetSum Finset.univ (fun j _ =>
      HolderToCK.integrable_inner_of_memLp_two (hTVLp j) (hCLp j))
    change (∫ x, ∑ j : Fin n, inner ℝ (F x j) (dC x j) ∂μ) = 0
    simp only [F, inner_sub_left, Finset.sum_sub_distrib]
    rw [integral_sub hVI hTI, ← HP, sub_self]
  obtain ⟨f, hf, hMean⟩ := exists_native_primitive_of_coexact_orthogonality hn F hF hCore
  obtain ⟨b, Db, _hb, _hs, _hc, _hd, _hn, hNatural, _hbi, _hdi, _he, _hbe⟩ := hNative V
  have hTests (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q)
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
      Integrable (fun x => ∑ j : Fin n, inner ℝ (F x j) (Dψ x j)) μ ∧
      (∫ x, ∑ j : Fin n, inner ℝ (F x j) (Dψ x j) ∂μ) =
        ∫ x, ∑ j : Fin n, inner ℝ (D V x j) (Dψ x j) ∂μ := by
    have hVI := integrable_finsetSum Finset.univ (fun j _ =>
      HolderToCK.integrable_inner_of_memLp_two (hVLp j) (hψ.2.2 j))
    obtain ⟨hTI, hTZero⟩ := hNatural ψ Dψ hψ
    refine ⟨integrable_finsetSum Finset.univ (fun j _ =>
      HolderToCK.integrable_inner_of_memLp_two (hF j) (hψ.2.2 j)), ?_⟩
    simp only [F, inner_sub_left, Finset.sum_sub_distrib]
    rw [integral_sub hVI hTI, hTZero, sub_zero]
  refine ⟨f, hf, hMean, hTests, ?_⟩
  intro g Dg hg hMeanG hResponse
  apply native_meanZero_gradient_response_unique_ae (0 : Domain n) (by norm_num : (0 : ℝ) < 1)
    g f Dg F hg hf hMeanG hMean
  intro ψ Dψ hψ
  exact (hResponse ψ Dψ hψ).trans (hTests ψ Dψ hψ).2.symm

end StationaryHarmonicMaps.Analysis

end

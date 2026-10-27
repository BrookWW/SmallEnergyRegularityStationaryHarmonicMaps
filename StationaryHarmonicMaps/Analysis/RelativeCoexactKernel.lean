module

public import StationaryHarmonicMaps.Analysis.CoexactRangeHarmonicFactory
public import StationaryHarmonicMaps.Analysis.SolenoidalHarmonicApproximation
public import StationaryHarmonicMaps.Analysis.ClosedNormalHarmonicRemainder
public import StationaryHarmonicMaps.Analysis.NeumannGradientSpace
public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds
public import HolderToCK.Analysis.L2PairingContinuity

/-!
# The natural orthogonal complement of the relative coexact range is zero

Core orthogonality first gives the genuine distributional harmonic equation.
One harmonic solenoidal approximation converges on the whole original ball.
Its actual closed normal potentials represent each approximant modulo a
native gradient. Both original orthogonality identities therefore annihilate
its pairing with the field. Strong L2 convergence forces the original energy
to vanish.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- A raw natural-solenoidal L2 field orthogonal to the actual smooth closed normal divergences vanishes on the whole unit ball. -/
theorem natural_coexact_kernel_eq_zero_unitBall {n q : ℕ} (hn : 1≤n)
    (F : Domain n → Gradient n q)
    (hF : ∀j,MemLp (fun x=>F x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hNatural : ∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
      (∫x in ball (0 : Domain n) 1,∑j : Fin n,inner ℝ (F x j) (Dψ x j))=0)
    (hCore : ∀ C : Fin n → Fin n → Domain n → Ambient q,
      (∀i j,ContDiff ℝ ∞ (C i j)) → (∀i j x,C i j x= -C j i x) →
      (∀i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
        fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0) →
      (∀j (x : Domain n),‖x‖=1 → (∑i : Fin n,x i • C i j x)=0) →
      (∫x in ball (0 : Domain n) 1,∑j : Fin n,inner ℝ (F x j)
        (∑i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)))=0) :
    (∫x in ball (0 : Domain n) 1,hsNormSq (F x))=0 ∧
      F=ᵐ[volume.restrict (ball (0 : Domain n) 1)] (fun _ _=>0) := by
  let Ω := ballDomain (0 : Domain n) 1
  let μ := volume.restrict (ball (0 : Domain n) 1)
  have hDiv : HolderToCK.WeakPoissonOn Ω F (fun _=>0) := by
    refine ⟨locallyIntegrableOn_zero,?_⟩
    intro ψ hψ _hc _hs
    have hW := memW12_ball_of_ambient_c1 (0 : Domain n) 1 ψ (hψ.of_le (by simp))
    have hI := integrable_finsetSum Finset.univ fun j _=>
      HolderToCK.integrable_inner_of_memLp_two (hF j) (hW.2.2 j)
    refine ⟨hI,?_,?_⟩
    · simp only [inner_zero_left]
      exact integrable_zero _ _ _
    · simpa only [Ω,ballDomain,inner_zero_left,integral_zero,neg_zero] using hNatural ψ _ hW
  have hHarm := coefficient_laplacian_pairing_zero_of_closed_normal_tests F hF hDiv hCore
  obtain ⟨G,ρ,hρ,hG,hGDiv,hGHarm,hConv⟩ :=
    exists_solenoidal_harmonic_L2_approximation_unitBall F hF hDiv
      (fun j ψ hψ hc hs=>(hHarm j ψ hψ hc hs).2)
  have hGLp (k : ℕ) (j : Fin n) : MemLp (fun x=>G k x j) 2 μ :=
    (memW12_ball_of_ambient_c1 (0 : Domain n) 1 (fun x=>G k x j)
      ((hG k j).of_le (by simp))).2.1
  have hZero (k : ℕ) : (∫x,∑j : Fin n,inner ℝ (F x j) (G k x j) ∂μ)=0 := by
    obtain ⟨C,g,hC,hSkew,hClosed,hNormal,hg,hEquation⟩ :=
      exists_smooth_closed_normal_potential_mod_gradient hn (G k) (hG k) (ρ k) (hρ k) (hGDiv k) (hGHarm k)
    let Dg := fun x j=>fderiv ℝ g x (EuclideanSpace.single j 1)
    have hgNative : MemW12 Ω g Dg := memW12_ball_of_ambient_c1 (0 : Domain n) 1 g (hg.of_le (by simp))
    have hgZero := hNatural g Dg hgNative
    have hCZero := hCore C hC hSkew hClosed hNormal
    have hGI : Integrable (fun x=>∑j : Fin n,inner ℝ (F x j) (G k x j)) μ :=
      integrable_finsetSum _ (fun j _=>HolderToCK.integrable_inner_of_memLp_two (hF j) (hGLp k j))
    have hgI : Integrable (fun x=>∑j : Fin n,inner ℝ (F x j) (Dg x j)) μ :=
      integrable_finsetSum _ (fun j _=>HolderToCK.integrable_inner_of_memLp_two (hF j) (hgNative.2.2 j))
    have hEq : (fun x=>∑j : Fin n,inner ℝ (F x j)
        (∑i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)))=ᵐ[μ]
        (fun x=>-(∑j : Fin n,inner ℝ (F x j) (G k x j))+
          (∑j : Fin n,inner ℝ (F x j) (Dg x j))) := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      simp only [hEquation x hx,inner_add_right,inner_neg_right,
        Finset.sum_add_distrib,Finset.sum_neg_distrib,Dg]
    change (∫x,∑j : Fin n,inner ℝ (F x j)
      (∑i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)) ∂μ)=0 at hCZero
    change (∫x,∑j : Fin n,inner ℝ (F x j) (Dg x j) ∂μ)=0 at hgZero
    have hNegGI : Integrable (fun x=>-(∑j : Fin n,inner ℝ (F x j) (G k x j))) μ := hGI.neg
    rw [integral_congr_ae hEq,integral_add hNegGI hgI,integral_neg,hgZero,add_zero] at hCZero
    exact neg_eq_zero.mp hCZero
  have hPair (j : Fin n) := HolderToCK.tendsto_integral_inner_of_L2
    (fun k=>hGLp k j) (hF j) (hF j) (hConv j)
  have hSum := tendsto_finsetSum Finset.univ (fun j _=>hPair j)
  have hSumEq (k : ℕ) : (∑j : Fin n,∫x,inner ℝ (F x j) (G k x j) ∂μ)=
      ∫x,∑j : Fin n,inner ℝ (F x j) (G k x j) ∂μ :=
    (integral_finsetSum _ (fun j _=>HolderToCK.integrable_inner_of_memLp_two (hF j) (hGLp k j))).symm
  have hSelf : (∑j : Fin n,∫x,inner ℝ (F x j) (F x j) ∂μ)=∫x,hsNormSq (F x) ∂μ := by
    simp only [real_inner_self_eq_norm_sq]
    exact (integral_finsetSum _ (fun j _=>(hF j).integrable_norm_pow (by decide : (2 : ℕ)≠0))).symm
  have hLimit : Tendsto (fun k=>∫x,∑j : Fin n,inner ℝ (F x j) (G k x j) ∂μ)
      atTop (𝓝 (∫x,hsNormSq (F x) ∂μ)) := by simpa only [hSumEq,hSelf] using hSum
  have hZeroLimit : Tendsto (fun k=>∫x,∑j : Fin n,inner ℝ (F x j) (G k x j) ∂μ) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hZero] using (tendsto_const_nhds (x := (0 : ℝ)))
  have hEnergy := tendsto_nhds_unique hLimit hZeroLimit
  refine ⟨hEnergy,?_⟩
  have hAE := (integral_eq_zero_iff_of_nonneg (fun x=>hsNormSq_nonneg (F x))
    (integrable_hsNormSq_of_columns F hF)).mp hEnergy
  filter_upwards [hAE] with x hx
  funext j
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  have H := Finset.single_le_sum (fun i _=>sq_nonneg ‖F x i‖) (Finset.mem_univ j)
  change ‖F x j‖^2≤hsNormSq (F x) at H
  rw [hx] at H
  exact le_antisymm H (sq_nonneg _)

end StationaryHarmonicMaps.Analysis

end

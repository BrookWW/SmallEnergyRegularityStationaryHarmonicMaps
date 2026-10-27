module

public import StationaryHarmonicMaps.Analysis.HodgeDirichletProjection
public import StationaryHarmonicMaps.Analysis.HilbertSchmidtDecoding
public import StationaryHarmonicMaps.Analysis.SupportedPoincare
public import StationaryHarmonicMaps.Analysis.C1SmoothWeakGradient
public import HarmonicMaps.Analysis.SobolevLocality
public import HolderToCK.Analysis.ZeroBoundaryClosure
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Recovery of actual zero-boundary Dirichlet potentials

The coercive compact-test Poincaré estimate makes maps Cauchy whenever their
actual gradients converge in L². Completeness and closure of the actual
zero-boundary Sobolev graph recover a map and the decoded gradient columns.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem integral_norm_sq_eq_toLp_norm_sq {n k : ℕ} {μ : Measure (Domain n)}
    {f : Domain n → Ambient k} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simpa only [real_inner_self_eq_norm_sq] using HolderToCK.integral_inner_eq_L2_inner hf hf

/-- Strong limits of actual compact gradients recover a genuine W₀¹,² map on a ball. -/
theorem exists_zeroBoundary_potential_of_encoded_gradient_limit {n q : ℕ}
    (hn : 1 ≤ n) (a : Domain n) {R : ℝ} (hR : 0 < R)
    (ψ : ℕ → Domain n → Ambient q)
    (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hcψ : ∀ j, HasCompactSupport (ψ j))
    (hsψ : ∀ j, tsupport (ψ j) ⊆ Metric.ball a R)
    (P : Domain n → Ambient (n * q))
    (hP : MemLp P 2 (volume.restrict (Metric.ball a R)))
    (hconv : Tendsto (fun j => eLpNorm (fun x =>
      WithLp.toLp 2 (fun k : Fin (n * q) =>
        (fderiv ℝ (ψ j) x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
          (finProdFinEquiv.symm k).2) - P x) 2 (volume.restrict (Metric.ball a R)))
        atTop (𝓝 0)) :
    ∃ f : Domain n → Ambient q,
      HasZeroBoundaryValues (ballDomain a R) f
        (fun x i => WithLp.toLp 2 (fun j : Fin q => P x (finProdFinEquiv (i, j)))) ∧
      Tendsto (fun j => eLpNorm (ψ j - f) 2 (volume.restrict (Metric.ball a R)))
        atTop (𝓝 0) := by
  let μ := volume.restrict (Metric.ball a R)
  let E : Gradient n q → Ambient (n * q) := fun A => WithLp.toLp 2
    (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  let G (j : ℕ) (x : Domain n) := E (fun i => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1))
  have hm (j : ℕ) : MemLp (ψ j) 2 μ :=
    (hψ j).continuous.memLp_of_hasCompactSupport (hcψ j)
  have hD (j : ℕ) (i : Fin n) :
      MemLp (fun x => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) 2 μ :=
    ((hψ j).continuous_fderiv (by simp) |>.clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hcψ j).fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hG (j : ℕ) : MemLp (G j) 2 μ :=
    memLp_hs_flatten (fun x i => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) (hD j)
  have hglim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' G hG P hP).mpr hconv
  have hfst : Tendsto (fun p : ℕ × ℕ => p.1) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (fun p : ℕ × ℕ => p.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hgradpair : Tendsto (fun p : ℕ × ℕ =>
      ‖(hG p.1).toLp (G p.1) - (hG p.2).toLp (G p.2)‖ ^ 2) atTop (𝓝 0) := by
    have H := (((hglim.comp hfst).sub (hglim.comp hsnd)).norm).pow 2
    simpa only [Function.comp_def, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using H
  let C : ℝ := (24 * (2 : ℝ) ^ (n + 1)) * R ^ 2
  have hpairbound (p : ℕ × ℕ) :
      ‖(hm p.1).toLp (ψ p.1) - (hm p.2).toLp (ψ p.2)‖ ^ 2 ≤
        C * ‖(hG p.1).toLp (G p.1) - (hG p.2).toLp (G p.2)‖ ^ 2 := by
    have hc := (hcψ p.1).sub (hcψ p.2)
    have hs : tsupport (ψ p.1 - ψ p.2) ⊆ Metric.ball a R :=
      (tsupport_sub _ _).trans (union_subset (hsψ p.1) (hsψ p.2))
    have hp := compactSmooth_zeroBoundary_poincare hn a hR (ψ p.1 - ψ p.2)
      ((hψ p.1).sub (hψ p.2)) hc hs
    have hEsub (x : Domain n) : E (fun i =>
        fderiv ℝ (ψ p.1 - ψ p.2) x (EuclideanSpace.single i 1)) = G p.1 x - G p.2 x := by
      ext k
      change (fderiv ℝ (ψ p.1 - ψ p.2) x
          (EuclideanSpace.single (finProdFinEquiv.symm k).1 1)) (finProdFinEquiv.symm k).2 =
        (fderiv ℝ (ψ p.1) x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
          (finProdFinEquiv.symm k).2 -
        (fderiv ℝ (ψ p.2) x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
          (finProdFinEquiv.symm k).2
      rw [fderiv_sub ((hψ p.1).differentiable (by simp) x)
        ((hψ p.2).differentiable (by simp) x)]
      rfl
    have hgradenergy : (∫ x, hsNormSq (fun i =>
        fderiv ℝ (ψ p.1 - ψ p.2) x (EuclideanSpace.single i 1)) ∂μ) =
        ‖(hG p.1).toLp (G p.1) - (hG p.2).toLp (G p.2)‖ ^ 2 := by
      calc
        _ = ∫ x, ‖G p.1 x - G p.2 x‖ ^ 2 ∂μ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x =>
            (hs_flatten_norm_sq (fun i =>
              fderiv ℝ (ψ p.1 - ψ p.2) x (EuclideanSpace.single i 1))).symm.trans
              (congrArg (fun v : Ambient (n * q) => ‖v‖ ^ 2) (hEsub x))
        _ = _ := by
          change (∫ x, ‖(G p.1 - G p.2) x‖ ^ 2 ∂μ) = _
          rw [integral_norm_sq_eq_toLp_norm_sq ((hG p.1).sub (hG p.2)), MemLp.toLp_sub]
    rw [← MemLp.toLp_sub, ← integral_norm_sq_eq_toLp_norm_sq]
    rw [← hgradenergy]
    exact hp
  have hmcauchy : CauchySeq (fun j => (hm j).toLp (ψ j)) := by
    apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
    have hsq : Tendsto (fun p : ℕ × ℕ =>
        ‖(hm p.1).toLp (ψ p.1) - (hm p.2).toLp (ψ p.2)‖ ^ 2) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa only [mul_zero] using hgradpair.const_mul C)
        (fun _ => sq_nonneg _) hpairbound
    have H := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
      Real.sqrt_zero, dist_eq_norm] using H
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hmcauchy
  have hmaplim : Tendsto (fun j => eLpNorm (ψ j - (f : Domain n → Ambient q)) 2 μ)
      atTop (𝓝 0) := by
    have H := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j => (hm j).toLp (ψ j)) f).mp hf
    apply H.congr
    intro j
    apply eLpNorm_congr_ae
    filter_upwards [(hm j).coeFn_toLp] with x hx
    change ((hm j).toLp (ψ j)) x - f x = ψ j x - f x
    rw [hx]
  have hDlim (i : Fin n) : Tendsto (fun j => eLpNorm (fun x =>
      fderiv ℝ (ψ j) x (EuclideanSpace.single i 1) -
        WithLp.toLp 2 (fun k : Fin q => P x (finProdFinEquiv (i, k)))) 2 μ)
      atTop (𝓝 0) := by
    have H := hs_unflatten_column_l2_limit hconv i
    apply H.congr
    intro j
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    congr 1
    exact congrFun (hs_unflatten_flatten
      (fun i => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1))) i
  have hw (j : ℕ) : HasZeroBoundaryValues (ballDomain a R) (ψ j)
      (fun x i => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) :=
    (memW12_of_c1 (ballDomain a R) ((hψ j).of_le (by simp)) (hm j) (hD j)).zeroBoundary_of_compactSupport_ball
      hR (hcψ j) (hsψ j)
  exact ⟨f, HolderToCK.hasZeroBoundaryValues_of_L2_limit_ball a R hw (Lp.memLp f)
    (fun i => memLp_hs_unflatten P hP i) hmaplim hDlim, hmaplim⟩

/-- Every L² one-form on a positive-dimensional ball has an actual zero-boundary gradient response. -/
theorem exists_dirichlet_gradient_projection {n q : ℕ} (hn : 1 ≤ n)
    (a : Domain n) {R : ℝ} (hR : 0 < R)
    (F : Domain n → Gradient n q)
    (hF : ∀ i : Fin n, MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a R))) :
    ∃ (f : Domain n → Ambient q) (Df : Domain n → Gradient n q),
      HasZeroBoundaryValues (ballDomain a R) f Df ∧
      (∫ x in Metric.ball a R, hsNormSq (Df x)) ≤ ∫ x in Metric.ball a R, hsNormSq (F x) ∧
      ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
        HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball a R →
        IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (Df x i)
          (fderiv ℝ ψ x (EuclideanSpace.single i 1))) (Metric.ball a R) volume ∧
        IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (F x i)
          (fderiv ℝ ψ x (EuclideanSpace.single i 1))) (Metric.ball a R) volume ∧
        (∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (Df x i)
          (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
          ∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (F x i)
            (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
  let μ := volume.restrict (Metric.ball a R)
  let E : Gradient n q → Ambient (n * q) := fun A => WithLp.toLp 2
    (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  obtain ⟨A, P, _hA, hPmem, _horth, _hseq, henergy, hweak⟩ :=
    exists_closed_compact_gradient_projection (ballDomain a R) F hF
  obtain ⟨ψ, hψ, hconv⟩ :=
    exists_smooth_gradient_approximation_of_mem_closedSpan (ballDomain a R) P hPmem
  obtain ⟨f, hf, _hmaplim⟩ := exists_zeroBoundary_potential_of_encoded_gradient_limit hn a hR ψ
    (fun j => (hψ j).1) (fun j => (hψ j).2.1) (fun j => (hψ j).2.2) P (Lp.memLp P) hconv
  let Df : Domain n → Gradient n q := fun x i => WithLp.toLp 2
    (fun j : Fin q => P x (finProdFinEquiv (i, j)))
  have henergyDf : (∫ x in Metric.ball a R, hsNormSq (Df x)) ≤
      ∫ x in Metric.ball a R, hsNormSq (F x) := by
    calc
      _ = ∫ x, ‖P x‖ ^ 2 ∂μ := integral_congr_ae
        (Eventually.of_forall fun x => hs_unflatten_hsNormSq (P x))
      _ ≤ _ := henergy
  refine ⟨f, Df, hf, henergyDf, ?_⟩
  intro φ hφ hcφ hsφ
  obtain ⟨hleft, hright, heq⟩ := hweak φ hφ hcφ hsφ
  have hpoint (x : Domain n) : inner ℝ (P x)
      (E (fun i => fderiv ℝ φ x (EuclideanSpace.single i 1))) =
      ∑ i : Fin n, inner ℝ (Df x i) (fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    have hEnc : E (Df x) = P x := hs_flatten_unflatten (P x)
    have H := hs_flatten_inner (Df x) (fun i => fderiv ℝ φ x (EuclideanSpace.single i 1))
    change inner ℝ (E (Df x)) (E (fun i => fderiv ℝ φ x (EuclideanSpace.single i 1))) = _ at H
    rw [hEnc] at H
    exact H
  exact ⟨hleft.congr (Eventually.of_forall hpoint), hright,
    (integral_congr_ae (Eventually.of_forall fun x => (hpoint x).symm)).trans heq⟩

end StationaryHarmonicMaps.Analysis

end

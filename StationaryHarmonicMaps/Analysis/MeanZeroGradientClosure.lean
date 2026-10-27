module

public import StationaryHarmonicMaps.Analysis.NeumannGradientSpace
public import StationaryHarmonicMaps.Analysis.HilbertSchmidtDecoding
public import StationaryHarmonicMaps.Analysis.SobolevWeakGradientClosure
public import HarmonicMaps.Analysis.SobolevDifference
public import HarmonicMaps.Analysis.SobolevPoincare
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Native mean-zero potentials of actual smooth gradient limits

True ball Poincare makes normalized maps Cauchy whenever their actual full
HS gradients converge. Completeness and the original weak-gradient
identities recover a genuine native potential. Subtracting its actual
ball mean fixes its additive constant and preserves the displayed columns.
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

/-- Actual mean-zero smooth maps with strongly convergent full HS gradients produce a genuine native mean-zero potential with those same columns. -/
theorem exists_native_potential_of_meanZero_smooth_gradient_limit {n q : ℕ} (a : Domain n) {R : ℝ} (hR : 0 < R)
    (ψ : ℕ → Domain n → Ambient q)
    (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hMean : ∀ j, (∫ x in Metric.ball a R, ψ j x) = 0)
    (P : Domain n → Ambient (n * q))
    (hP : MemLp P 2 (volume.restrict (Metric.ball a R)))
    (hconv : Tendsto (fun j => eLpNorm (fun x =>
      WithLp.toLp 2 (fun k : Fin (n * q) =>
        (fderiv ℝ (ψ j) x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
          (finProdFinEquiv.symm k).2) - P x) 2 (volume.restrict (Metric.ball a R)))
        atTop (𝓝 0)) :
    ∃ f : Domain n → Ambient q,
      MemW12 (ballDomain a R) f
        (fun x i => WithLp.toLp 2 (fun j : Fin q => P x (finProdFinEquiv (i,j)))) ∧
      (∫ x in Metric.ball a R, f x) = 0 := by
  let μ := volume.restrict (Metric.ball a R)
  let E : Gradient n q → Ambient (n * q) := fun A => WithLp.toLp 2
    (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  let G (j : ℕ) (x : Domain n) := E (fun i => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hW (j : ℕ) := memW12_ball_of_ambient_c1 a R (ψ j) ((hψ j).of_le (by simp))
  have hm (j : ℕ) : MemLp (ψ j) 2 μ := (hW j).2.1
  have hD (j : ℕ) (i : Fin n) :
      MemLp (fun x => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) 2 μ := (hW j).2.2 i
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
  let C : ℝ := (2 : ℝ) ^ (n+1) * R^2
  have hpairbound (p : ℕ × ℕ) :
      ‖(hm p.1).toLp (ψ p.1) - (hm p.2).toLp (ψ p.2)‖ ^ 2 ≤
        C * ‖(hG p.1).toLp (G p.1) - (hG p.2).toLp (G p.2)‖ ^ 2 := by
    have hp := ((hW p.1).sub (hW p.2)).poincare_ball hR
    have hMeanPair : (⨍ x in Metric.ball a R, (ψ p.1-ψ p.2) x) = 0 := by
      rw [average_eq]
      change (μ.real univ)⁻¹ • (∫ x, (ψ p.1 x-ψ p.2 x) ∂μ) = 0
      rw [integral_sub ((hm p.1).integrable (by norm_num))
        ((hm p.2).integrable (by norm_num)),
        (show (∫ x, ψ p.1 x ∂μ) = 0 from hMean p.1),
        (show (∫ x, ψ p.2 x ∂μ) = 0 from hMean p.2),sub_self,smul_zero]
    simp only [hMeanPair,sub_zero] at hp
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
    have hDer (x : Domain n) : fderiv ℝ (ψ p.1-ψ p.2) x =
        fderiv ℝ (ψ p.1) x-fderiv ℝ (ψ p.2) x :=
      fderiv_sub ((hψ p.1).differentiable (by simp) x) ((hψ p.2).differentiable (by simp) x)
    simp_rw [hDer,sub_apply]
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
  let Df := fun x i => WithLp.toLp 2 (fun j : Fin q => P x (finProdFinEquiv (i,j)))
  have hDf (i : Fin n) : MemLp (fun x => Df x i) 2 μ := memLp_hs_unflatten P hP i
  have hWeak (i : Fin n) (g : Domain n → Ambient q) (hg : MemLp g 2 μ) :
      Tendsto (fun j => ∫ x in Metric.ball a R, inner ℝ
        (fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) (g x)) atTop
        (𝓝 (∫ x in Metric.ball a R, inner ℝ (Df x i) (g x))) := by
    simpa only [real_inner_comm] using HolderToCK.tendsto_integral_inner_of_L2
      (fun j => hD j i) (hDf i) hg (hDlim i)
  have hNative := memW12_of_strong_map_weak_gradient_L2 (ballDomain a R) ψ
    (fun j x i => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) hW
    (f : Domain n → Ambient q) Df (Lp.memLp f) hDf hmaplim hWeak
  let c := ⨍ x in Metric.ball a R, (f : Domain n → Ambient q) x
  have hConst := memW12_ball_of_ambient_c1 a R (fun _x : Domain n => c) contDiff_const
  refine ⟨(fun x => f x-c),?_,?_⟩
  · convert hNative.sub hConst using 1
    · funext x
      rfl
    · funext x i
      simp only [fderiv_const_apply,zero_apply,sub_zero]
      rfl
  · exact integral_sub_average μ (f : Domain n → Ambient q)


/-- Actual ball-mean normalization produces the native mean-zero potential from any genuine smooth gradient limit. -/
theorem exists_native_meanZero_potential_of_smooth_gradient_limit {n q : ℕ} (a : Domain n) {R : ℝ} (hR : 0 < R)
    (ψ : ℕ → Domain n → Ambient q)
    (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (P : Domain n → Ambient (n * q))
    (hP : MemLp P 2 (volume.restrict (Metric.ball a R)))
    (hconv : Tendsto (fun j => eLpNorm (fun x =>
      WithLp.toLp 2 (fun k : Fin (n * q) =>
        (fderiv ℝ (ψ j) x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
          (finProdFinEquiv.symm k).2) - P x) 2 (volume.restrict (Metric.ball a R)))
        atTop (𝓝 0)) :
    ∃ f : Domain n → Ambient q,
      MemW12 (ballDomain a R) f
        (fun x i => WithLp.toLp 2 (fun j : Fin q => P x (finProdFinEquiv (i,j)))) ∧
      (∫ x in Metric.ball a R, f x) = 0 := by
  let μ := volume.restrict (Metric.ball a R)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let N := fun (j : ℕ) (x : Domain n) => ψ j x-(⨍ y in Metric.ball a R, ψ j y)
  have hN (j : ℕ) : ContDiff ℝ ∞ (N j) := (hψ j).sub contDiff_const
  have hMeanN (j : ℕ) : (∫ x in Metric.ball a R, N j x) = 0 :=
    integral_sub_average μ (ψ j)
  have hDN (j : ℕ) (x : Domain n) (i : Fin n) :
      fderiv ℝ (N j) x (EuclideanSpace.single i 1) =
        fderiv ℝ (ψ j) x (EuclideanSpace.single i 1) := by
    have H := (((hψ j).differentiable (by simp) x).hasFDerivAt.sub_const
      (⨍ y in Metric.ball a R, ψ j y)).fderiv
    exact congrArg (fun L : Domain n →L[ℝ] Ambient q => L (EuclideanSpace.single i 1)) H
  have hConvN : Tendsto (fun j => eLpNorm (fun x =>
      WithLp.toLp 2 (fun k : Fin (n*q) =>
        (fderiv ℝ (N j) x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
          (finProdFinEquiv.symm k).2)-P x) 2 μ) atTop (𝓝 0) := by
    apply hconv.congr
    intro j
    apply eLpNorm_congr_ae
    apply Eventually.of_forall
    intro x
    simp_rw [hDN]
  exact exists_native_potential_of_meanZero_smooth_gradient_limit a hR N hN hMeanN P hP hConvN

end StationaryHarmonicMaps.Analysis

end

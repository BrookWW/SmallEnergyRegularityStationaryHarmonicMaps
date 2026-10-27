module

public import StationaryHarmonicMaps.Analysis.BoundedSobolevTestApproximation
public import StationaryHarmonicMaps.Analysis.OrthogonalFrameVariation
public import StationaryHarmonicMaps.Analysis.BoundedL2MultiplierContinuity
public import HolderToCK.Analysis.ZeroBoundaryClosure
public import HarmonicMaps.Analysis.SobolevLocality

/-! # Bounded native operator fields acting on bounded native W0 tests

The actual uniformly bounded compact smooth approximation of the test
supplies native compact product graphs. Genuine weighted L2 continuity
and the bounded original operator field give strong convergence of both
Leibniz terms. Native W0 graph closure recovers the same literal product.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ContDiff ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem memLp_bounded_operator_apply {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (A : X → Ambient q →L[ℝ] Ambient q)
    (hA : AEStronglyMeasurable A μ) (C : ℝ)
    (hBound : ∀ᵐ x ∂μ,‖A x‖≤C) (f : X → Ambient q) (hf : MemLp f 2 μ) :
    MemLp (fun x => A x (f x)) 2 μ := by
  have hm : AEStronglyMeasurable (fun x => A x (f x)) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk hf.aestronglyMeasurable)
  apply hf.of_le_mul hm
  filter_upwards [hBound] with x hx
  exact (A x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

private theorem tendsto_bounded_operator_L2_apply {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (A : X → Ambient q →L[ℝ] Ambient q) (C : ℝ)
    (hBound : ∀ᵐ x ∂μ,‖A x‖≤C)
    (f : ℕ → X → Ambient q) (g : X → Ambient q)
    (hConv : Tendsto (fun k => eLpNorm (f k-g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun x => A x (f k x-g x)) 2 μ) atTop (𝓝 0) := by
  have H := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hConv (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using H) (fun _ => zero_le)
  intro k
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (p := 2)
  filter_upwards [hBound] with x hx
  exact (A x).le_opNorm (f k x-g x) |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

/-- A genuine bounded native operator graph acts on every genuine bounded native zero-boundary test, with the same literal Leibniz columns and actual zero trace. -/
theorem zeroBoundary_bounded_native_operator_apply_ball {n m q : ℕ}
    (a : Domain n) (R : ℝ) (hR : 0<R)
    (p : Domain n → Ambient m) (Dp : Domain n → Gradient n m)
    (hp : MemW12 (ballDomain a R) p Dp) (M : ℝ)
    (hpBound : ∀ᵐ x ∂volume.restrict (Metric.ball a R),‖p x‖≤M)
    (L : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q)
    (hφ : HasZeroBoundaryValues (ballDomain a R) φ Dφ) (N : ℝ)
    (hφBound : ∀ᵐ x ∂volume.restrict (Metric.ball a R),‖φ x‖≤N) :
    HasZeroBoundaryValues (ballDomain a R) (fun x => L (p x) (φ x))
      (fun x i => L (Dp x i) (φ x)+L (p x) (Dφ x i)) := by
  let μ := volume.restrict (Metric.ball a R)
  obtain ⟨B,ψ,hB,hψ,hcψ,hψBound,_hAE,hConv,hDConv⟩ :=
    exists_bounded_smooth_zeroBoundary_approximation (ballDomain a R) hφ hφBound
  let A := fun x => L (p x)
  let Ai := fun (i : Fin n) x => L (Dp x i)
  let w := fun x => A x (φ x)
  let Dw := fun x i => Ai i x (φ x)+A x (Dφ x i)
  let wk := fun k x => A x (ψ k x)
  let Dwk := fun k x i => Ai i x (ψ k x)+A x (fderiv ℝ (ψ k) x (EuclideanSpace.single i 1))
  have hALp : MemLp A 2 μ := L.lipschitz.comp_memLp (map_zero L) hp.2.1
  have hAiLp (i : Fin n) : MemLp (Ai i) 2 μ := L.lipschitz.comp_memLp (map_zero L) (hp.2.2 i)
  have hψLp (k : ℕ) : MemLp (ψ k) 2 μ :=
    ((hψ k).continuous.memLp_of_hasCompactSupport (hcψ k).1).mono_measure Measure.restrict_le_self
  have hDψLp (k : ℕ) (i : Fin n) :
      MemLp (fun x => fderiv ℝ (ψ k) x (EuclideanSpace.single i 1)) 2 μ :=
    ((((hψ k).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hcψ k).1.fderiv_apply ℝ (EuclideanSpace.single i 1))).mono_measure Measure.restrict_le_self
  have hBψ (k : ℕ) : ∀ᵐ x ∂μ,‖ψ k x‖≤B := Eventually.of_forall (hψBound k)
  have hMap := bounded_L2_limit_fixed_operator_L2 μ ψ φ hψLp hφ.1.2.1 hConv hBψ A hALp
  have hFirst (i : Fin n) :=
    bounded_L2_limit_fixed_operator_L2 μ ψ φ hψLp hφ.1.2.1 hConv hBψ (Ai i) (hAiLp i)
  let C := ‖L‖*|M|
  have hABound : ∀ᵐ x ∂μ,‖A x‖≤C := by
    filter_upwards [hpBound] with x hx
    exact (L.le_opNorm (p x)).trans
      (mul_le_mul_of_nonneg_left (hx.trans (le_abs_self M)) (norm_nonneg _))
  have hSecond (i : Fin n) : MemLp (fun x => A x (Dφ x i)) 2 μ :=
    memLp_bounded_operator_apply μ A hALp.aestronglyMeasurable C hABound (fun x => Dφ x i) (hφ.1.2.2 i)
  have hDw (i : Fin n) : MemLp (fun x => Dw x i) 2 μ := (hFirst i).2.1.add (hSecond i)
  have hWk (k : ℕ) : MemW12 (ballDomain a R) (wk k) (Dwk k) :=
    memW12_operator_test hp hpBound L (ψ k) (hψ k) (hcψ k).1
  have hWkZero (k : ℕ) : HasZeroBoundaryValues (ballDomain a R) (wk k) (Dwk k) := by
    have hSupport : tsupport (wk k)⊆tsupport (ψ k) := by
      apply closure_mono
      intro x hx hz
      apply hx
      change A x (ψ k x)=0
      rw [hz,map_zero]
    have hc : HasCompactSupport (wk k) :=
      (hcψ k).1.of_isClosed_subset (isClosed_tsupport _) hSupport
    exact (hWk k).zeroBoundary_of_compactSupport_ball hR hc (hSupport.trans (hcψ k).2)
  have hMapConv : Tendsto (fun k => eLpNorm (wk k-w) 2 μ) atTop (𝓝 0) := by
    apply (hMap.2.2.2.2).congr
    intro k
    apply eLpNorm_congr_ae
    exact Eventually.of_forall fun x => by
      change A x (ψ k x-φ x)=A x (ψ k x)-A x (φ x)
      exact map_sub _ _ _
  have hGradConv (i : Fin n) : Tendsto (fun k => eLpNorm (fun x => Dwk k x i-Dw x i) 2 μ) atTop (𝓝 0) := by
    let U := fun k x => Ai i x (ψ k x-φ x)
    let V := fun k x => A x (fderiv ℝ (ψ k) x (EuclideanSpace.single i 1)-Dφ x i)
    have hU (k : ℕ) : MemLp (U k) 2 μ := (hFirst i).2.2.2.1 k
    have hV (k : ℕ) : MemLp (V k) 2 μ :=
      memLp_bounded_operator_apply μ A hALp.aestronglyMeasurable C hABound _
        ((hDψLp k i).sub (hφ.1.2.2 i))
    have hVC := tendsto_bounded_operator_L2_apply μ A C hABound
      (fun k x => fderiv ℝ (ψ k) x (EuclideanSpace.single i 1)) (fun x => Dφ x i) (hDConv i)
    have hSum : Tendsto (fun k => eLpNorm (U k) 2 μ+eLpNorm (V k) 2 μ) atTop (𝓝 0) := by
      simpa only [zero_add] using ((hFirst i).2.2.2.2).add hVC
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSum (fun _ => zero_le)
    intro k
    have hEq : (fun x => Dwk k x i-Dw x i)=U k+V k := by
      funext x
      simp only [Dwk,Dw,U,V,Pi.add_apply,map_sub]
      abel
    change eLpNorm (fun x => Dwk k x i-Dw x i) 2 μ≤eLpNorm (U k) 2 μ+eLpNorm (V k) 2 μ
    rw [hEq]
    exact eLpNorm_add_le (hU k).aestronglyMeasurable (hV k).aestronglyMeasurable (by norm_num)
  exact HolderToCK.hasZeroBoundaryValues_of_L2_limit_ball a R hWkZero hMap.2.1 hDw hMapConv hGradConv

end StationaryHarmonicMaps.Analysis
end

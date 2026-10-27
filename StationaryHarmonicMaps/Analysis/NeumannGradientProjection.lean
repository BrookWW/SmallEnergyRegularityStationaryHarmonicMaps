module

public import StationaryHarmonicMaps.Analysis.NeumannClosedProjection
public import StationaryHarmonicMaps.Analysis.MeanZeroGradientClosure
public import StationaryHarmonicMaps.Analysis.NaturalBallTests
public import StationaryHarmonicMaps.Analysis.ZeroEnergyRepresentative

/-!
# Actual native Neumann gradient response

The genuine closed full-gradient projection has actual smooth-gradient
approximants. Ball Poincare and native weak-gradient closure recover a
mean-zero potential. The same projected columns have energy coefficient
one and answer every native Sobolev test with arbitrary boundary values.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Every raw L2 one-form on a positive-radius ball has an actual mean-zero native Neumann gradient response with energy coefficient one. -/
theorem exists_neumann_gradient_projection {n q : ℕ}
    (a : Domain n) {R : ℝ} (hR : 0 < R)
    (F : Domain n → Gradient n q)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a R))) :
    ∃ (f : Domain n → Ambient q) (Df : Domain n → Gradient n q),
      MemW12 (ballDomain a R) f Df ∧
      (∫ x in Metric.ball a R, f x) = 0 ∧
      (∫ x in Metric.ball a R, hsNormSq (Df x)) ≤ ∫ x in Metric.ball a R, hsNormSq (F x) ∧
      ∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain a R) ψ Dψ →
        IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (Df x i) (Dψ x i)) (Metric.ball a R) volume ∧
        IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (F x i) (Dψ x i)) (Metric.ball a R) volume ∧
        (∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (Df x i) (Dψ x i)) =
          ∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (F x i) (Dψ x i) := by
  let μ := volume.restrict (Metric.ball a R)
  let E : Gradient n q → Ambient (n*q) := fun A => WithLp.toLp 2
    (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  obtain ⟨A,P,_hA,_hPmem,_hOrth,⟨Z,hZ,hLim⟩,hEnergy,hWeak⟩ :=
    exists_closed_smooth_gradient_projection_ball a R F hF
  choose ψ hψ hAE using hZ
  have hConv : Tendsto (fun j => eLpNorm (fun x =>
      E (fun i => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1))-P x) 2 μ) atTop (𝓝 0) := by
    have H := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' Z P).mp hLim
    apply H.congr
    intro j
    apply eLpNorm_congr_ae
    filter_upwards [hAE j] with x hx
    change Z j x-P x = E (fun i => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1))-P x
    rw [hx]
  obtain ⟨f,hf,hMean⟩ := exists_native_meanZero_potential_of_smooth_gradient_limit
    a hR ψ hψ P (Lp.memLp P) hConv
  let Df := fun x i => WithLp.toLp 2 (fun j : Fin q => P x (finProdFinEquiv (i,j)))
  have hEnergyDf : (∫ x in Metric.ball a R, hsNormSq (Df x)) ≤
      ∫ x in Metric.ball a R, hsNormSq (F x) := by
    calc
      _ = ∫ x, ‖P x‖ ^ 2 ∂μ := integral_congr_ae
        (Eventually.of_forall fun x => hs_unflatten_hsNormSq (P x))
      _ ≤ _ := hEnergy
  have hSmooth (φ : Domain n → Ambient q) (hφ : ContDiff ℝ ∞ φ) :
      IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (Df x i)
        (fderiv ℝ φ x (EuclideanSpace.single i 1))) (Metric.ball a R) volume ∧
      IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (F x i)
        (fderiv ℝ φ x (EuclideanSpace.single i 1))) (Metric.ball a R) volume ∧
      (∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (Df x i)
        (fderiv ℝ φ x (EuclideanSpace.single i 1))) =
        ∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (F x i)
          (fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    obtain ⟨hPI,hFI,hEq⟩ := hWeak φ hφ
    have hPoint (x : Domain n) : inner ℝ (P x)
        (E (fun i => fderiv ℝ φ x (EuclideanSpace.single i 1))) =
        ∑ i : Fin n, inner ℝ (Df x i) (fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
      have hEnc : E (Df x) = P x := hs_flatten_unflatten (P x)
      have H := hs_flatten_inner (Df x) (fun i => fderiv ℝ φ x (EuclideanSpace.single i 1))
      change inner ℝ (E (Df x)) (E (fun i => fderiv ℝ φ x (EuclideanSpace.single i 1))) = _ at H
      rw [hEnc] at H
      exact H
    exact ⟨hPI.congr (Eventually.of_forall hPoint),hFI,
      (integral_congr_ae (Eventually.of_forall fun x => (hPoint x).symm)).trans hEq⟩
  let H := fun x i => F x i-Df x i
  have hH (i : Fin n) : MemLp (fun x => H x i) 2 μ := (hF i).sub (hf.2.2 i)
  have hPoint (Dψ : Domain n → Gradient n q) (x : Domain n) :
      (∑ i : Fin n, inner ℝ (H x i) (Dψ x i)) =
        (∑ i : Fin n, inner ℝ (F x i) (Dψ x i)) -
          ∑ i : Fin n, inner ℝ (Df x i) (Dψ x i) := by
    simp only [H,inner_sub_left,Finset.sum_sub_distrib]
  have hZero (φ : Domain n → Ambient q) (hφ : ContDiff ℝ ∞ φ) :
      (∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (H x i)
        (fderiv ℝ φ x (EuclideanSpace.single i 1))) = 0 := by
    obtain ⟨hDI,hFI,hEq⟩ := hSmooth φ hφ
    rw [integral_congr_ae (Eventually.of_forall (hPoint _)),integral_sub hFI hDI,← hEq,sub_self]
  refine ⟨f,Df,hf,hMean,hEnergyDf,?_⟩
  intro φ Dφ hφ
  have hDI := integrable_column_pairing μ Df Dφ hf.2.2 hφ.2.2
  have hFI := integrable_column_pairing μ F Dφ hF hφ.2.2
  have hNat := (native_ball_tests_of_all_smooth_tests a hR H hH hZero φ Dφ hφ).2
  rw [integral_congr_ae (Eventually.of_forall (hPoint Dφ)),integral_sub hFI hDI] at hNat
  exact ⟨hDI,hFI,(sub_eq_zero.mp hNat).symm⟩

/-- Native mean-zero gradient responses agreeing on all native tests have the same map and displayed columns almost everywhere. -/
theorem native_meanZero_gradient_response_unique_ae {n q : ℕ}
    (a : Domain n) {R : ℝ} (hR : 0 < R)
    (f g : Domain n → Ambient q) (Df Dg : Domain n → Gradient n q)
    (hf : MemW12 (ballDomain a R) f Df) (hg : MemW12 (ballDomain a R) g Dg)
    (hMeanF : (∫ x in Metric.ball a R, f x) = 0)
    (hMeanG : (∫ x in Metric.ball a R, g x) = 0)
    (hEq : ∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain a R) ψ Dψ →
      (∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (Df x i) (Dψ x i)) =
        ∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (Dg x i) (Dψ x i)) :
    f =ᵐ[volume.restrict (Metric.ball a R)] g ∧ Df =ᵐ[volume.restrict (Metric.ball a R)] Dg := by
  let μ := volume.restrict (Metric.ball a R)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (ballDomain a R).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hDiff := hf.sub hg
  have hIF := integrable_column_pairing μ Df (fun x i => Df x i-Dg x i) hf.2.2 hDiff.2.2
  have hIG := integrable_column_pairing μ Dg (fun x i => Df x i-Dg x i) hg.2.2 hDiff.2.2
  have hEnergy : (∫ x in Metric.ball a R, hsNormSq (fun i => Df x i-Dg x i)) = 0 := by
    calc
      _ = (∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (Df x i) (Df x i-Dg x i)) -
          ∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (Dg x i) (Df x i-Dg x i) := by
        rw [← integral_sub hIF hIG]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [hsNormSq,← real_inner_self_eq_norm_sq,inner_sub_left,Finset.sum_sub_distrib]
      _ = 0 := by rw [hEq (f-g) _ hDiff,sub_self]
  have hConst := ae_eq_ballMean_of_zero_energy a hR hDiff hEnergy
  have hFInt : Integrable f μ := hf.2.1.integrable (by norm_num)
  have hGInt : Integrable g μ := hg.2.1.integrable (by norm_num)
  have hMeanDiff : (⨍ x in Metric.ball a R, (f-g) x) = 0 := by
    rw [average_eq]
    change (μ.real univ)⁻¹ • (∫ x, (f x-g x) ∂μ) = 0
    rw [integral_sub hFInt hGInt,
      (show (∫ x, f x ∂μ) = 0 from hMeanF),(show (∫ x, g x ∂μ) = 0 from hMeanG),
      sub_self,smul_zero]
  have hMap : f =ᵐ[volume.restrict (Metric.ball a R)] g := by
    filter_upwards [hConst] with x hx
    rw [hMeanDiff] at hx
    exact sub_eq_zero.mp hx
  exact ⟨hMap,hf.1.ae_eq_of_ae_eq_map hg.1 hMap⟩

end StationaryHarmonicMaps.Analysis

end

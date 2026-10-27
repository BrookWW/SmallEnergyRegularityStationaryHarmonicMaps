module

public import StationaryHarmonicMaps.Analysis.LinearFluxHarmonicDecomposition
public import StationaryHarmonicMaps.Analysis.NativeHarmonicGradient
public import HolderToCK.Foundation.BallVolume

/-!
# Actual full-HS energy decay for native linear flux solutions

The original native harmonic gradient has a genuine interior essential
bound from its actual Weyl representative. The true ball-volume ratio
gives its dimension-only energy decay. An actual W0 forcing response and
exact energy orthogonality then give the linear flux estimate with the
original coefficient two on its forcing energy.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

/-- The same original native harmonic gradient has genuine full-HS energy decay on every concentric smaller ball. -/
theorem native_harmonic_gradient_energy_decay_ball {n q : ℕ} (hn : 2≤n)
    (a : Domain n) (R : PositiveRadius)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12 (ballDomain a R.val) u Du)
    (hEquation : HolderToCK.WeakPoissonOn (ballDomain a R.val) Du (fun _ => (0 : Ambient q)))
    {θ : ℝ} (hθ : 0<θ) (hθHalf : θ≤1/2) :
    (∫ x in Metric.ball a (θ*R.val),hsNormSq (Du x))≤
      (2 : ℝ)^n*θ^n*(∫ x in Metric.ball a R.val,hsNormSq (Du x)) := by
  obtain ⟨_U,_hU,_hAE,_hLap,_hGrad,_hCols,_hPoint,hBound,_hTop,_hLp⟩ :=
    exists_smooth_harmonic_representative_with_original_gradient_ball hn a R u Du hu hEquation
  let K := (volume.real (Metric.ball a (R.val/2)))⁻¹*(∫ x in Metric.ball a R.val,hsNormSq (Du x))
  have hSubHalf : Metric.ball a (θ*R.val)⊆Metric.ball a (R.val/2) :=
    Metric.ball_subset_ball (by nlinarith only [hθHalf,R.property])
  have hSub : Metric.ball a (θ*R.val)⊆Metric.ball a R.val :=
    hSubHalf.trans (Metric.ball_subset_ball (by linarith only [R.property]))
  have hSmallBound : ∀ᵐ x ∂volume.restrict (Metric.ball a (θ*R.val)),hsNormSq (Du x)≤K :=
    hBound.filter_mono (ae_mono (Measure.restrict_mono_set volume hSubHalf))
  have hMass : volume.real (Metric.ball a (R.val/2))=
      volume.real (Metric.ball (0 : Domain n) (R.val/2)) := by
    simp only [measureReal_def,Measure.addHaar_ball_center volume]
  calc
    _ ≤ ∫ _x in Metric.ball a (θ*R.val),K :=
      integral_mono_ae (hu.integrable_hsNormSq.mono_set hSub)
        (integrableOn_const measure_ball_ne_top) hSmallBound
    _ = volume.real (Metric.ball a (θ*R.val))*(volume.real (Metric.ball a (R.val/2)))⁻¹*
        (∫ x in Metric.ball a R.val,hsNormSq (Du x)) := by
      simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,K]
      ring
    _ = _ := by rw [hMass,HolderToCK.ball_volume_ratio_half a R.property hθ]

/-- Actual native div(DV+F)=0 and actual L2 forcing give the full-HS decay estimate with the same original energies. -/
theorem linear_flux_dirichlet_energy_decay_ball {n q : ℕ} (hn : 2≤n)
    (a : Domain n) (R : PositiveRadius)
    (V : Domain n → Ambient q) (DV F : Domain n → Gradient n q)
    (hV : MemW12 (ballDomain a R.val) V DV)
    (hF : ∀ i,MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a R.val)))
    (hEquation : HolderToCK.WeakPoissonOn (ballDomain a R.val)
      (fun x i => DV x i+F x i) (fun _ => (0 : Ambient q)))
    {θ : ℝ} (hθ : 0<θ) (hθHalf : θ≤1/2) :
    (∫ x in Metric.ball a (θ*R.val),hsNormSq (DV x))≤
      2*(2 : ℝ)^n*θ^n*(∫ x in Metric.ball a R.val,hsNormSq (DV x))+
        2*(∫ x in Metric.ball a R.val,hsNormSq (F x)) := by
  obtain ⟨f,Df,hf,hEf,hh,_hResponse,hHarmonic,_hCrossI,_hCrossZero,hEnergy⟩ :=
    exists_linear_flux_harmonic_decomposition_ball (by omega : 1≤n) a R V DV F hV hF hEquation
  let Dh := fun x i => DV x i-Df x i
  have hSub : Metric.ball a (θ*R.val)⊆Metric.ball a R.val :=
    Metric.ball_subset_ball (by nlinarith only [hθHalf,R.property])
  have hHDecay := native_harmonic_gradient_energy_decay_ball hn a R (V-f) Dh hh hHarmonic hθ hθHalf
  have hFullH : (∫ x in Metric.ball a R.val,hsNormSq (Dh x))≤
      ∫ x in Metric.ball a R.val,hsNormSq (DV x) := by
    have H : 0≤∫ x in Metric.ball a R.val,hsNormSq (Df x) := integral_nonneg fun _ => hsNormSq_nonneg _
    linarith only [hEnergy,H]
  have hDfSmall : (∫ x in Metric.ball a (θ*R.val),hsNormSq (Df x))≤
      ∫ x in Metric.ball a R.val,hsNormSq (Df x) :=
    setIntegral_mono_set hf.1.integrable_hsNormSq (Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Eventually.of_forall fun _ hx => hSub hx)
  have hPoint (x : Domain n) : hsNormSq (DV x)≤2*hsNormSq (Dh x)+2*hsNormSq (Df x) := by
    have hCol (i : Fin n) : ‖DV x i‖^2≤2*‖Dh x i‖^2+2*‖Df x i‖^2 := by
      have H : DV x i=Dh x i+Df x i := by dsimp only [Dh];abel
      rw [H,norm_add_sq_real]
      nlinarith only [real_inner_le_norm (Dh x i) (Df x i),sq_nonneg (‖Dh x i‖-‖Df x i‖)]
    calc
      _ ≤ ∑ i : Fin n,(2*‖Dh x i‖^2+2*‖Df x i‖^2) := Finset.sum_le_sum fun i _ => hCol i
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.mul_sum,hsNormSq]
  have hDHInt : IntegrableOn (fun x => hsNormSq (Dh x)) (Metric.ball a (θ*R.val)) volume :=
    hh.integrable_hsNormSq.mono_set hSub
  have hDfInt : IntegrableOn (fun x => hsNormSq (Df x)) (Metric.ball a (θ*R.val)) volume :=
    hf.1.integrable_hsNormSq.mono_set hSub
  calc
    _ ≤ ∫ x in Metric.ball a (θ*R.val),2*hsNormSq (Dh x)+2*hsNormSq (Df x) :=
      integral_mono (hV.integrable_hsNormSq.mono_set hSub)
        ((hDHInt.const_mul 2).add (hDfInt.const_mul 2)) hPoint
    _ = 2*(∫ x in Metric.ball a (θ*R.val),hsNormSq (Dh x))+
        2*(∫ x in Metric.ball a (θ*R.val),hsNormSq (Df x)) := by
      rw [integral_add (hDHInt.const_mul 2) (hDfInt.const_mul 2),integral_const_mul,integral_const_mul]
    _ ≤ 2*((2 : ℝ)^n*θ^n*(∫ x in Metric.ball a R.val,hsNormSq (Dh x)))+
        2*(∫ x in Metric.ball a R.val,hsNormSq (Df x)) :=
      add_le_add (mul_le_mul_of_nonneg_left hHDecay (by norm_num))
        (mul_le_mul_of_nonneg_left hDfSmall (by norm_num))
    _ ≤ 2*((2 : ℝ)^n*θ^n*(∫ x in Metric.ball a R.val,hsNormSq (DV x)))+
        2*(∫ x in Metric.ball a R.val,hsNormSq (F x)) :=
      add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hFullH (by positivity)) (by norm_num))
        (mul_le_mul_of_nonneg_left hEf (by norm_num))
    _ = _ := by ring

end StationaryHarmonicMaps.Analysis

end

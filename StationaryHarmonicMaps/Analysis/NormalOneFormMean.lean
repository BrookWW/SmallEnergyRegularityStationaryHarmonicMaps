module

public import StationaryHarmonicMaps.Analysis.BallDivergenceZero
public import StationaryHarmonicMaps.Geometry.NormalOneFormBoundary
public import Mathlib.MeasureTheory.Function.L2Space
public import StationaryHarmonicMaps.Analysis.SmoothLpPoincare
public import StationaryHarmonicMaps.Analysis.NeumannGradientSpace

/-!
# Actual ball means of normal one-form coefficients

Testing the true normal contraction with a coordinate multiplier gives the
coefficient integral directly from its divergence. No zero-mean condition
is imposed on the original coefficient field.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The original normal condition produces the exact vector coefficient-mean identity and both true Bochner integrabilities. -/
theorem smooth_normal_oneForm_integral {n q : ℕ}
    (A : Fin n → Domain n → Ambient q) (hA : ∀ i, ContDiff ℝ ∞ (A i))
    (hNormal : ∀ y : Domain n, ‖y‖=1 → (∑ i : Fin n, y i • A i y)=0)
    (j : Fin n) :
    let d := fun x : Domain n => ∑ i : Fin n, fderiv ℝ (A i) x (EuclideanSpace.single i 1)
    IntegrableOn (A j) (ball (0 : Domain n) 1) volume ∧
      IntegrableOn (fun x=>x j • d x) (ball (0 : Domain n) 1) volume ∧
      (∫ x in ball (0 : Domain n) 1,A j x) =
        -(∫ x in ball (0 : Domain n) 1,x j • d x) := by
  intro d
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let πj := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n=>ℝ) j
  have hd : ContDiff ℝ ∞ d := ContDiff.sum (fun i _ =>
    ((hA i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have hAjI : Integrable (A j) μ :=
    ((hA j).continuous.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Domain n) 1)).mono_set ball_subset_closedBall
  have hwI : Integrable (fun x=>x j • d x) μ :=
    ((πj.contDiff.smul hd).continuous.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Domain n) 1)).mono_set ball_subset_closedBall
  have hSumI : Integrable (fun x=>A j x+x j • d x) μ := hAjI.add hwI
  have hAll (v : Ambient q) : (∫ x,inner ℝ v (A j x+x j • d x) ∂μ)=0 := by
    let V := fun x : Domain n => WithLp.toLp 2 (fun i : Fin n=>x j*inner ℝ v (A i x))
    have hV : ContDiff ℝ ∞ V := by
      apply (contDiff_piLp 2).2
      intro i
      exact πj.contDiff.mul ((innerSL ℝ v).contDiff.comp (hA i))
    have hFlux (x : Domain n) (hx : ‖x‖=1) : inner ℝ x (V x)=0 := by
      have H : inner ℝ x (V x)=x j*inner ℝ v (∑ i : Fin n,x i • A i x) := by
        simp only [PiLp.inner_apply,Real.inner_apply,V,inner_sum,inner_smul_right,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring_nf
      rw [H,hNormal x hx,inner_zero_right,mul_zero]
    have hViD (i : Fin n) (x : Domain n) :
        fderiv ℝ (fun y : Domain n=>y j*inner ℝ v (A i y)) x (EuclideanSpace.single i 1) =
          x j*inner ℝ v (fderiv ℝ (A i) x (EuclideanSpace.single i 1)) +
            (if j=i then inner ℝ v (A i x) else 0) := by
      have hi : HasFDerivAt (fun y=>inner ℝ v (A i y))
          ((innerSL ℝ v).comp (fderiv ℝ (A i) x)) x :=
        (innerSL ℝ v).hasFDerivAt.comp x ((hA i).differentiable (by simp) x).hasFDerivAt
      have H := congrArg (fun L : Domain n →L[ℝ] ℝ=>L (EuclideanSpace.single i 1))
        (πj.hasFDerivAt.smul hi).fderiv
      have heq : ((fun y=>πj y) • (fun y=>inner ℝ v (A i y))) =
          (fun y : Domain n=>y j*inner ℝ v (A i y)) := rfl
      rw [heq] at H
      simpa only [add_apply,smul_apply,ContinuousLinearMap.comp_apply,innerSL_apply_apply,
        ContinuousLinearMap.smulRight_apply,πj,PiLp.proj_apply,PiLp.single_apply,
        smul_eq_mul,ite_mul,one_mul,zero_mul] using H
    have hCoord (i : Fin n) (x : Domain n) :
        (fderiv ℝ V x (EuclideanSpace.single i 1)) i =
          fderiv ℝ (fun y : Domain n=>y j*inner ℝ v (A i y)) x (EuclideanSpace.single i 1) := by
      let πi := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n=>ℝ) i
      have heq : (fun y : Domain n=>y j*inner ℝ v (A i y)) = πi ∘ V := rfl
      rw [heq,fderiv_comp x πi.differentiableAt (hV.differentiable (by simp) x),πi.fderiv]
      rfl
    have hDiv (x : Domain n) : (∑ i : Fin n,(fderiv ℝ V x (EuclideanSpace.single i 1)) i) =
        inner ℝ v (A j x+x j • d x) := by
      simp_rw [hCoord,hViD]
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
        inner_add_right,inner_smul_right,d,inner_sum,Finset.mul_sum]
      ring_nf
    have H := (unitBall_integral_divergence_eq_zero V (hV.of_le (by simp)) hFlux).2
    rw [integral_congr_ae (Eventually.of_forall hDiv)] at H
    exact H
  have H := integral_eq_zero_of_forall_integral_inner_eq_zero (𝕜 := ℝ)
    (fun x=>A j x+x j • d x) hSumI hAll
  have heq : (∫ x,A j x ∂μ)+(∫ x,x j • d x ∂μ)=0 := by
    rw [← integral_add hAjI hwI]
    exact H
  exact ⟨hAjI,hwI,eq_neg_of_add_eq_zero_left heq⟩


/-- The actual normal condition controls each original coefficient mean by the actual divergence energy. -/
theorem smooth_normal_oneForm_mean_square_bound {n q : ℕ}
    (A : Fin n → Domain n → Ambient q) (hA : ∀ i, ContDiff ℝ ∞ (A i))
    (hNormal : ∀ y : Domain n, ‖y‖=1 → (∑ i : Fin n, y i • A i y)=0)
    (j : Fin n) :
    let d := fun x : Domain n => ∑ i : Fin n,fderiv ℝ (A i) x (EuclideanSpace.single i 1)
    IntegrableOn (fun x=>‖d x‖^2) (ball (0 : Domain n) 1) volume ∧
      volume.real (ball (0 : Domain n) 1) * ‖⨍ x in ball (0 : Domain n) 1,A j x‖^2 ≤
        ∫ x in ball (0 : Domain n) 1,‖d x‖^2 := by
  intro d
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let m := μ.real univ
  let w := fun x : Domain n => x j • d x
  let πj := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n=>ℝ) j
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hμpos : 0 < μ univ := by
    simpa only [μ,Measure.restrict_apply_univ] using
      (Metric.measure_ball_pos volume (0 : Domain n) (by norm_num : (0:ℝ)<1))
  letI : NeZero μ := ⟨by
    intro hz
    simp [hz] at hμpos⟩
  have hm : 0 < m := ENNReal.toReal_pos hμpos.ne' (measure_ne_top μ univ)
  have hd : ContDiff ℝ ∞ d := ContDiff.sum (fun i _=>
    ((hA i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have hw : ContDiff ℝ ∞ w := πj.contDiff.smul hd
  have hdLp : MemLp d 2 μ :=
    (memW12_ball_of_ambient_c1 (0 : Domain n) 1 d (hd.of_le (by simp))).2.1
  have hwLp : MemLp w 2 μ :=
    (memW12_ball_of_ambient_c1 (0 : Domain n) 1 w (hw.of_le (by simp))).2.1
  have hdI : Integrable (fun x=>‖d x‖^2) μ := hdLp.integrable_norm_pow (by decide : (2:ℕ)≠0)
  have hwI : Integrable (fun x=>‖w x‖^2) μ := hwLp.integrable_norm_pow (by decide : (2:ℕ)≠0)
  have hNormBound : (∫ x,‖w x‖^2 ∂μ) ≤ ∫ x,‖d x‖^2 ∂μ := by
    apply integral_mono_ae hwI hdI
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hxn : ‖x‖<1 := by simpa only [mem_ball,dist_zero_right] using hx
    have hcoord : ‖x j‖≤1 := (PiLp.norm_apply_le x j).trans hxn.le
    have hnorm : ‖w x‖≤‖d x‖ := by
      rw [show w x=x j • d x from rfl,norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) hcoord
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hMean := (smooth_normal_oneForm_integral A hA hNormal j).2.2
  have hAvg : (⨍ x,A j x ∂μ) = -(⨍ x,w x ∂μ) := by
    simp only [average_eq]
    rw [show (∫ x,A j x ∂μ)=-(∫ x,w x ∂μ) from hMean,smul_neg]
  have hJ := norm_average_rpow_le_average_norm_rpow w (hwLp.integrable (by norm_num))
    (by norm_num : (1:ℝ)≤2) (by simpa only [Real.rpow_two] using hwI)
  have hJ' : ‖⨍ x,w x ∂μ‖^2 ≤ m⁻¹*(∫ x,‖w x‖^2 ∂μ) := by
    simpa only [Real.rpow_two,average_eq,smul_eq_mul] using hJ
  refine ⟨hdI,?_⟩
  have hmass : volume.real (ball (0 : Domain n) 1)=m := by
    simp only [m,μ,measureReal_def,Measure.restrict_apply_univ]
  rw [hmass]
  change m*‖⨍ x,A j x ∂μ‖^2 ≤ ∫ x,‖d x‖^2 ∂μ
  calc
    _ = m*‖⨍ x,w x ∂μ‖^2 := by rw [hAvg,norm_neg]
    _ ≤ m*(m⁻¹*(∫ x,‖w x‖^2 ∂μ)) := mul_le_mul_of_nonneg_left hJ' hm.le
    _ = ∫ x,‖w x‖^2 ∂μ := by rw [← mul_assoc,mul_inv_cancel₀ hm.ne',one_mul]
    _ ≤ _ := hNormBound

end StationaryHarmonicMaps.Analysis

end

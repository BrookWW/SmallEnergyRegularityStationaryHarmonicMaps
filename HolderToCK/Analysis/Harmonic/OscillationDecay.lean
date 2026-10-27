module

public import HolderToCK.Analysis.Harmonic.DerivativeEstimates
public import HolderToCK.Analysis.Harmonic.DerivativeFields
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Quadratic oscillation decay for a harmonic field

An interior first derivative estimate bounds the Lipschitz oscillation. The
smaller-ball volume supplies the exact dimension exponent, independently of
the target dimension and of the chosen constant used to center the large-ball
integral.
-/

public section

open HarmonicMaps MeasureTheory Set InnerProductSpace
open scoped ContDiff

namespace HolderToCK

noncomputable section

theorem harmonic_ball_oscillation_decay (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (R : PositiveRadius)
      (f : Domain n → Ambient q) (c : Ambient q),
      ContDiffOn ℝ ∞ f (Metric.ball a R.val) →
      (∀ z ∈ Metric.ball a R.val, Laplacian.laplacian f z = 0) →
      IntegrableOn (fun z => ‖f z - c‖ ^ 2) (Metric.ball a R.val) →
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
        (∫ z in Metric.ball a (θ * R.val), ‖f z - f a‖ ^ 2) ≤
          C * θ ^ (n + 2) * ∫ z in Metric.ball a R.val, ‖f z - c‖ ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := harmonic_iteratedFDeriv_sq_L2_bound n 1 hn
  let V := volume.real (Metric.ball (0 : Domain n) 1)
  have hV : 0 < V := ball_volume_real_pos 0 (by norm_num)
  refine ⟨K * V, mul_pos hK hV, ?_⟩
  intro q a R f c hf hh hE θ hθ hθhalf
  let g : Domain n → Ambient q := fun z => f z - c
  let E := ∫ z in Metric.ball a R.val, ‖g z‖ ^ 2
  let T := K * (R.val ^ (n + 2))⁻¹ * E
  have hgsmooth : ContDiffOn ℝ ∞ g (Metric.ball a R.val) := hf.sub contDiffOn_const
  have hgH : HarmonicOnNhd g (Metric.ball a R.val) :=
    (harmonicOnNhd_of_smooth_laplacian_zero Metric.isOpen_ball hf hh).sub (harmonicOnNhd_const c)
  have hgh : ∀ z ∈ Metric.ball a R.val, Laplacian.laplacian g z = 0 :=
    fun z hz => (hgH z hz).2.eq_of_nhds
  have hEpos : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hTpos : 0 ≤ T :=
    mul_nonneg (mul_nonneg hK.le (inv_nonneg.mpr (pow_nonneg R.property.le _))) hEpos
  have hhalf : Metric.ball a (R.val / 2) ⊆ Metric.ball a R.val :=
    Metric.ball_subset_ball (by linarith only [R.property])
  have hsub : Metric.ball a (θ * R.val) ⊆ Metric.ball a (R.val / 2) :=
    Metric.ball_subset_ball (by nlinarith only [hθhalf, R.property])
  have hclosed : Metric.closedBall a (θ * R.val) ⊆ Metric.ball a R.val :=
    Metric.closedBall_subset_ball (by nlinarith only [hθhalf, R.property])
  have hdiff (z : Domain n) (hz : z ∈ Metric.ball a (R.val / 2)) :
      DifferentiableAt ℝ g z :=
    (hgsmooth.contDiffAt (Metric.isOpen_ball.mem_nhds (hhalf hz))).differentiableAt (by simp)
  have hD (z : Domain n) (hz : z ∈ Metric.ball a (R.val / 2)) :
      ‖fderiv ℝ g z‖ ≤ Real.sqrt T := by
    have h := hbound q a R g hgsmooth hgh hE z hz
    simp only [norm_iteratedFDeriv_one, Nat.mul_one, Nat.add_comm 2 n] at h
    exact Real.le_sqrt_of_sq_le h
  have ha : a ∈ Metric.ball a (R.val / 2) := Metric.mem_ball_self (half_pos R.property)
  have hpoint : ∀ z ∈ Metric.ball a (θ * R.val),
      ‖f z - f a‖ ^ 2 ≤ T * (θ * R.val) ^ 2 := by
    intro z hz
    have hLip := (convex_ball a (R.val / 2)).norm_image_sub_le_of_norm_fderiv_le
      hdiff hD ha (hsub hz)
    have hnorm : ‖z - a‖ ≤ θ * R.val :=
      (show ‖z - a‖ < θ * R.val from by simpa only [Metric.mem_ball, dist_eq_norm] using hz).le
    have hcenter : g z - g a = f z - f a := sub_sub_sub_cancel_right _ _ _
    rw [hcenter] at hLip
    have hLip' := hLip.trans (mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _))
    have hsquared := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hθ.le R.property.le))).mpr hLip'
    rw [mul_pow, Real.sq_sqrt hTpos] at hsquared
    exact hsquared
  have hInt : IntegrableOn (fun z => ‖f z - f a‖ ^ 2) (Metric.ball a (θ * R.val)) :=
    (((hf.continuousOn.mono hclosed).sub continuousOn_const).norm.pow 2).integrableOn_compact (isCompact_closedBall a (θ * R.val)) |>.mono_set
      Metric.ball_subset_closedBall
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a (θ * R.val))) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hIntegral := setIntegral_mono_on hInt (integrable_const _)
    measurableSet_ball hpoint
  rw [setIntegral_const, smul_eq_mul] at hIntegral
  have hcoeff : volume.real (Metric.ball a (θ * R.val)) * (T * (θ * R.val) ^ 2) =
      (K * V) * θ ^ (n + 2) * E := by
    rw [ball_volume_real a (mul_pos hθ R.property)]
    dsimp only [T, V]
    rw [mul_pow, mul_pow, pow_add]
    field_simp [R.property.ne']
    ring
  rw [hcoeff] at hIntegral
  exact hIntegral

end
end HolderToCK
end

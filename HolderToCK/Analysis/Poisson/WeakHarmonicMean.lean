module

public import HolderToCK.Analysis.ContinuousMollification
public import HolderToCK.Analysis.WeakPoissonLocality
public import HolderToCK.Analysis.Harmonic.SphereMean
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Spherical means of continuous weak harmonic maps

The signed weak equation makes the interior mollifications harmonic. Uniform
convergence on the sampling sphere passes their exact mean identities to the
original continuous Sobolev function with its original weak gradient.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace HolderToCK

theorem WeakPoissonOn.harmonic_sphere_meanValue_of_continuous
    {n q : ℕ} (hn : 2 ≤ n) (a : Domain n) {R : ℝ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du)
    (hcont : ContinuousOn u (Metric.ball a R))
    (hEq : WeakPoissonOn (ballDomain a R) Du (fun _ => 0))
    (r : PositiveRadius) (hrR : r.val < R) :
    u a = ((volume : Measure (Domain n)).toSphere.real univ)⁻¹ •
      ∫ θ : Metric.sphere (0 : Domain n) 1, u (a + r.val • θ.val)
        ∂(volume : Measure (Domain n)).toSphere := by
  let s := (R + r.val) / 2
  have hrs : r.val < s := by dsimp only [s]; linarith only [hrR]
  have hsR : s < R := by dsimp only [s]; linarith only [hrR]
  let h : ℕ → PositiveRadius := fun k =>
    ⟨(R - r.val) / ((k : ℝ) + 1), by positivity⟩
  have hle (k : ℕ) : (h k).val ≤ R - r.val := by
    change (R - r.val) / ((k : ℝ) + 1) ≤ R - r.val
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    nlinarith only [sub_pos.mpr hrR, Nat.cast_nonneg (α := ℝ) k]
  have hh : Tendsto (fun k => (h k).val) atTop (𝓝 0) := by
    simpa only [h, div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := R - r.val)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  let M := fun k => euclideanMollification (ballDomain a R) u hu.integrable_ball (h k)
  have hM (k : ℕ) := hEq.mollification_laplacian_ball hu 0
    (Eventually.of_forall fun x => by simp only [norm_zero, zero_mul, le_refl])
    (h k) (show s + (h k).val / 2 ≤ R by dsimp only [s]; linarith only [hle k])
  have hclosedS : Metric.closedBall a s ⊆ Metric.ball a R :=
    Metric.closedBall_subset_ball hsR
  have hlim : TendstoUniformlyOn M u atTop (Metric.closedBall a r.val) :=
    euclideanMollification_tendstoUniformlyOn_closedBall_of_continuous
      (ballDomain a R) u hu.integrable_ball a hrs hclosedS (hcont.mono hclosedS) h hh
  let p : Metric.sphere (0 : Domain n) 1 → Domain n := fun θ => a + r.val • θ.val
  have hp : Continuous p := continuous_const.add
    ((continuous_const : Continuous (fun _ : Metric.sphere (0 : Domain n) 1 => r.val)).smul
      continuous_subtype_val)
  have hpclosed (θ : Metric.sphere (0 : Domain n) 1) : p θ ∈ Metric.closedBall a r.val := by
    change dist (a + r.val • θ.val) a ≤ r.val
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg r.property.le]
    have hθ : ‖θ.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    rw [hθ, mul_one]
  have hpsample (θ : Metric.sphere (0 : Domain n) 1) : p θ ∈ Metric.ball a R :=
    (Metric.closedBall_subset_ball hrR) (hpclosed θ)
  have hlimSphere : TendstoUniformlyOn (fun k θ => M k (p θ)) (fun θ => u (p θ))
      atTop univ := (hlim.comp p).mono (fun θ _ => hpclosed θ)
  have hInt := tendsto_setIntegral_of_uniformlyOn_compact
    ((volume : Measure (Domain n)).toSphere) isCompact_univ (measure_ne_top _ _)
    (hcont.comp_continuous hp hpsample).continuousOn
    (fun k => ((hM k).1.continuous.comp hp).continuousOn) hlimSphere
  simp only [setIntegral_univ] at hInt
  have hval : Tendsto (fun k => M k a) atTop (𝓝 (u a)) :=
    hlim.tendsto_at (Metric.mem_closedBall_self r.property.le)
  have hmean (k : ℕ) : M k a =
      ((volume : Measure (Domain n)).toSphere.real univ)⁻¹ •
        ∫ θ : Metric.sphere (0 : Domain n) 1, M k (p θ)
          ∂(volume : Measure (Domain n)).toSphere :=
    harmonic_sphere_meanValue hn a r (Metric.ball a s) Metric.isOpen_ball
      (Metric.closedBall_subset_ball hrs) (M k) (hM k).1.contDiffOn
      (fun x hx => by
        have hxS := Metric.ball_subset_ball hrs.le hx
        simpa only [Pi.zero_apply, smul_zero, integral_zero] using (hM k).2 x hxS)
  apply tendsto_nhds_unique hval
  exact (tendsto_const_nhds.smul hInt).congr (fun k => (hmean k).symm)

theorem WeakPoissonOn.harmonic_sphere_integral_eq_of_continuous
    {n q : ℕ} (hn : 2 ≤ n) (a : Domain n) {R : ℝ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du)
    (hcont : ContinuousOn u (Metric.ball a R))
    (hEq : WeakPoissonOn (ballDomain a R) Du (fun _ => 0))
    (r : PositiveRadius) (hrR : r.val < R) :
    (∫ θ : Metric.sphere (0 : Domain n) 1, u (a + r.val • θ.val)
      ∂(volume : Measure (Domain n)).toSphere) =
      (volume : Measure (Domain n)).toSphere.real univ • u a := by
  have h := hEq.harmonic_sphere_meanValue_of_continuous hn a hu hcont r hrR
  have hmass := (polar_angular_mass_pos (by omega : 0 < n)).ne'
  have heq := congrArg (fun v : Ambient q =>
    (volume : Measure (Domain n)).toSphere.real univ • v) h.symm
  simpa only [smul_smul, mul_inv_cancel₀ hmass, one_smul] using heq

end HolderToCK
end

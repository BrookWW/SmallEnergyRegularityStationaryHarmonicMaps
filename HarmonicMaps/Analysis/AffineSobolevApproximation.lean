module

public import HarmonicMaps.Analysis.AffineSobolevTransform

/-!
# Inward affine approximation on a whole ball

Zero extensions supply global L2 data only. For strictly inward dilations,
their values agree with the original map and its displayed gradient on the
whole source ball, so global affine continuity gives restricted continuity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace HarmonicMaps

noncomputable section

theorem ballAffine_mem_ball_of_inward {n : ℕ} (a : Domain n) {R t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) {x : Domain n} (hx : x ∈ Metric.ball a R) :
    ballAffine a t x ∈ Metric.ball a R := by
  rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
  simp only [ballAffine, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  exact (mul_le_of_le_one_left (norm_nonneg _) ht1).trans_lt hx

/-- Inward dilation converges in L2 on the entire source ball. -/
theorem tendsto_eLpNorm_ballAffine_sub {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Domain n) (R : ℝ) {f : Domain n → E}
    (hf : MemLp f 2 (volume.restrict (Metric.ball a R))) :
    Tendsto (fun t : ℝ => eLpNorm (fun x => f (ballAffine a t x) - f x)
      2 (volume.restrict (Metric.ball a R))) (𝓝[Ioo (0 : ℝ) 1] 1) (𝓝 0) := by
  let F := (Metric.ball a R).indicator f
  have hF : MemLp F 2 volume := memLp_zeroExtension measurableSet_ball hf
  have hlim := (tendsto_eLpNorm_centeredDilation_sub hF a).mono_left
    (nhdsWithin_le_nhds (s := Ioo (0 : ℝ) 1))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have heq : (fun x => f (ballAffine a t x) - f x) =ᵐ[volume.restrict (Metric.ball a R)]
      (fun x => F (ballAffine a t x) - F x) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simp only [F, indicator_of_mem hx,
      indicator_of_mem (ballAffine_mem_ball_of_inward a ht.1 ht.2.le hx)]
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- The same convergence holds with the amplitude of an actual weak-gradient pullback. -/
theorem tendsto_eLpNorm_smul_ballAffine_sub {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Domain n) (R : ℝ) {f : Domain n → E}
    (hf : MemLp f 2 (volume.restrict (Metric.ball a R))) :
    Tendsto (fun t : ℝ => eLpNorm (fun x => t • f (ballAffine a t x) - f x)
      2 (volume.restrict (Metric.ball a R))) (𝓝[Ioo (0 : ℝ) 1] 1) (𝓝 0) := by
  let F := (Metric.ball a R).indicator f
  have hF : MemLp F 2 volume := memLp_zeroExtension measurableSet_ball hf
  have hlim := (tendsto_eLpNorm_smul_centeredDilation_sub hF a).mono_left
    (nhdsWithin_le_nhds (s := Ioo (0 : ℝ) 1))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have heq : (fun x => t • f (ballAffine a t x) - f x) =ᵐ[volume.restrict (Metric.ball a R)]
      (fun x => t • F (ballAffine a t x) - F x) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simp only [F, indicator_of_mem hx,
      indicator_of_mem (ballAffine_mem_ball_of_inward a ht.1 ht.2.le hx)]
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- An inward pullback simultaneously approximates the map and every displayed
weak-gradient column on the whole ball. -/
theorem MemW12.exists_inward_affine_approximation_ball {n q : ℕ}
    {a : Domain n} {R : ℝ} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12 (ballDomain a R) u Du)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      MemW12 (ballDomain a (R / t)) (fun x => u (ballAffine a t x))
        (fun x i => t • Du (ballAffine a t x) i) ∧
      eLpNorm (fun x => u (ballAffine a t x) - u x)
        2 (volume.restrict (Metric.ball a R)) ≤ ε ∧
      ∀ i : Fin n, eLpNorm (fun x => t • Du (ballAffine a t x) i - Du x i)
        2 (volume.restrict (Metric.ball a R)) ≤ ε := by
  letI : NeBot (𝓝[Ioo (0 : ℝ) 1] 1) := right_nhdsWithin_Ioo_neBot (by norm_num)
  have hm : ∀ᶠ t : ℝ in 𝓝[Ioo (0 : ℝ) 1] 1,
      eLpNorm (fun x => u (ballAffine a t x) - u x)
        2 (volume.restrict (Metric.ball a R)) ≤ ε :=
    ENNReal.tendsto_nhds_zero.mp (tendsto_eLpNorm_ballAffine_sub a R hu.2.1) ε hε
  have hd : ∀ᶠ t : ℝ in 𝓝[Ioo (0 : ℝ) 1] 1,
      ∀ i : Fin n, eLpNorm (fun x => t • Du (ballAffine a t x) i - Du x i)
        2 (volume.restrict (Metric.ball a R)) ≤ ε := by
    apply eventually_all.mpr
    intro i
    exact ENNReal.tendsto_nhds_zero.mp
      (tendsto_eLpNorm_smul_ballAffine_sub a R (hu.2.2 i)) ε hε
  have ht : ∀ᶠ t : ℝ in 𝓝[Ioo (0 : ℝ) 1] 1, t ∈ Ioo (0 : ℝ) 1 :=
    self_mem_nhdsWithin
  have hall := ht.and (hm.and hd)
  obtain ⟨t, ht, hmt, hdt⟩ := hall.exists
  exact ⟨t, ht.1, ht.2, hu.affinePullback_ball ht.1, hmt, hdt⟩

end
end HarmonicMaps

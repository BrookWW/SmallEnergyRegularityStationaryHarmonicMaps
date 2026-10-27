module

public import HolderToCK.Analysis.Poisson.PotentialGradient
public import HolderToCK.Analysis.Poisson.PotentialLimitsMollification

/-! # Uniform local convergence against locally integrable kernels -/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Convolution Topology

namespace HolderToCK

theorem compactData_translate_eq_zero {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] {g : Domain n → E} {R S : ℝ}
    (hSupp : tsupport g ⊆ Metric.closedBall (0 : Domain n) S)
    {x z : Domain n} (hx : ‖x‖ ≤ R)
    (hz : z ∉ Metric.closedBall (0 : Domain n) (R + S)) :
    g (x - z) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hg : ‖x - z‖ ≤ S := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hSupp hmem
  have hz' : R + S < ‖z‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz
  have hn : ‖z‖ ≤ ‖x‖ + ‖x - z‖ := by
    calc
      _ = ‖x - (x - z)‖ := by rw [sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  exact (not_lt_of_ge (hn.trans (add_le_add hx hg))) hz'

theorem locallyIntegrableKernel_compactData_norm_bound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : Domain n → ℝ} (hk : LocallyIntegrable k volume)
    {g : Domain n → E} (hg : Continuous g) (hcg : HasCompactSupport g)
    {R S M : ℝ} (hSupp : tsupport g ⊆ Metric.closedBall (0 : Domain n) S)
    (hbound : ∀ y, ‖g y‖ ≤ M) {x : Domain n} (hx : ‖x‖ ≤ R) :
    ‖∫ z, k z • g (x - z)‖ ≤
      M * ∫ z in Metric.closedBall (0 : Domain n) (R + S), ‖k z‖ := by
  have hi := hk.integrable_smul_right_of_hasCompactSupport
    (hg.comp (continuous_const.sub continuous_id)) (hcg.comp_homeomorph (Homeomorph.subLeft x))
  have heq : (∫ z, k z • g (x - z)) =
      ∫ z in Metric.closedBall (0 : Domain n) (R + S), k z • g (x - z) := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
    intro z hz
    rw [compactData_translate_eq_zero hSupp hx hz, smul_zero]
  rw [heq]
  have hki := hk.integrableOn_isCompact (isCompact_closedBall (0 : Domain n) (R + S))
  calc
    _ ≤ ∫ z in Metric.closedBall (0 : Domain n) (R + S), ‖k z • g (x - z)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z in Metric.closedBall (0 : Domain n) (R + S), M * ‖k z‖ := by
      apply integral_mono_ae hi.integrableOn.norm (hki.norm.const_mul M)
      filter_upwards with z
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := integral_const_mul _ _

theorem locallyIntegrableKernel_tendstoUniformlyOn {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : Domain n → ℝ} (hk : LocallyIntegrable k volume)
    {F : ℕ → Domain n → E} {g : Domain n → E} {R S : ℝ}
    (hF : ∀ m, Continuous (F m)) (hg : Continuous g)
    (hFS : ∀ m, tsupport (F m) ⊆ Metric.closedBall (0 : Domain n) S)
    (hgS : tsupport g ⊆ Metric.closedBall (0 : Domain n) S)
    (hlim : TendstoUniformly F g atTop) :
    TendstoUniformlyOn (fun m x => ∫ z, k z • F m (x - z))
      (fun x => ∫ z, k z • g (x - z)) atTop (Metric.closedBall (0 : Domain n) R) := by
  let C := ∫ z in Metric.closedBall (0 : Domain n) (R + S), ‖k z‖
  have hC : 0 ≤ C := integral_nonneg (fun _ => norm_nonneg _)
  have hcF (m : ℕ) : HasCompactSupport (F m) :=
    (isCompact_closedBall (0 : Domain n) S).of_isClosed_subset (isClosed_tsupport _) (hFS m)
  have hcg : HasCompactSupport g :=
    (isCompact_closedBall (0 : Domain n) S).of_isClosed_subset (isClosed_tsupport _) hgS
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith only [hC])
  filter_upwards [Metric.tendstoUniformly_iff.mp hlim (ε / (C + 1)) hδ] with m hm x hx
  have hiF : Integrable (fun z => k z • F m (x - z)) volume :=
    hk.integrable_smul_right_of_hasCompactSupport
    ((hF m).comp (continuous_const.sub continuous_id))
    ((hcF m).comp_homeomorph (Homeomorph.subLeft x))
  have hig : Integrable (fun z => k z • g (x - z)) volume :=
    hk.integrable_smul_right_of_hasCompactSupport
    (hg.comp (continuous_const.sub continuous_id))
    (hcg.comp_homeomorph (Homeomorph.subLeft x))
  have hsubS : tsupport (F m - g) ⊆ Metric.closedBall (0 : Domain n) S :=
    (tsupport_sub _ _).trans (union_subset (hFS m) hgS)
  have hbound (y : Domain n) : ‖(F m - g) y‖ ≤ ε / (C + 1) := by
    simpa only [Pi.sub_apply, ← dist_eq_norm, dist_comm] using (hm y).le
  rw [dist_eq_norm, ← integral_sub hig hiF]
  have heq : (fun z => k z • g (x - z) - k z • F m (x - z)) =
      (fun z => -(k z • (F m - g) (x - z))) := by
    funext z
    simp only [Pi.sub_apply, smul_sub, neg_sub]
  rw [heq, integral_neg, norm_neg]
  have hestimate := locallyIntegrableKernel_compactData_norm_bound hk
    ((hF m).sub hg) ((hcF m).sub hcg) hsubS hbound
    (show ‖x‖ ≤ R by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  change _ ≤ ε / (C + 1) * C at hestimate
  apply hestimate.trans_lt
  calc
    ε / (C + 1) * C < ε / (C + 1) * (C + 1) :=
      mul_lt_mul_of_pos_left (lt_add_one C) hδ
    _ = ε := div_mul_cancel₀ ε (by linarith only [hC])

theorem newtonianPotential_tendstoUniformlyOn {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 2 ≤ n) {F : ℕ → Domain n → E} {g : Domain n → E} {R S : ℝ}
    (hF : ∀ m, Continuous (F m)) (hg : Continuous g)
    (hFS : ∀ m, tsupport (F m) ⊆ Metric.closedBall (0 : Domain n) S)
    (hgS : tsupport g ⊆ Metric.closedBall (0 : Domain n) S)
    (hlim : TendstoUniformly F g atTop) :
    TendstoUniformlyOn (fun m => newtonianPotential hn (F m))
      (newtonianPotential hn g) atTop (Metric.closedBall (0 : Domain n) R) := by
  by_cases hn2 : n = 2
  · subst n
    have heq : newtonianPotential hn =
        (fun (g : Domain 2 → E) x => ∫ z, fundamentalLogExpression z • g (x - z)) :=
      funext fun g => funext (newtonianPotential_eq_log g)
    rw [heq]
    exact locallyIntegrableKernel_tendstoUniformlyOn fundamentalLog_locallyIntegrable
      hF hg hFS hgS hlim
  · have hn3 : 3 ≤ n := by omega
    have heq : newtonianPotential hn =
        (fun (g : Domain n → E) x => ∫ z, fundamentalPowerExpression z • g (x - z)) :=
      funext fun g => funext (newtonianPotential_eq_power hn3 g)
    rw [heq]
    exact locallyIntegrableKernel_tendstoUniformlyOn (fundamentalPower_locallyIntegrable hn3)
      hF hg hFS hgS hlim

theorem potentialGradientColumn_tendstoUniformlyOn {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 0 < n) (i : Fin n) {F : ℕ → Domain n → E} {g : Domain n → E} {R S : ℝ}
    (hF : ∀ m, Continuous (F m)) (hg : Continuous g)
    (hFS : ∀ m, tsupport (F m) ⊆ Metric.closedBall (0 : Domain n) S)
    (hgS : tsupport g ⊆ Metric.closedBall (0 : Domain n) S)
    (hlim : TendstoUniformly F g atTop) :
    TendstoUniformlyOn (fun m => potentialGradientColumn i (F m))
      (potentialGradientColumn i g) atTop (Metric.closedBall (0 : Domain n) R) := by
  exact locallyIntegrableKernel_tendstoUniformlyOn (normalizedRadialColumn_locallyIntegrable hn i)
    hF hg hFS hgS hlim

end HolderToCK
end

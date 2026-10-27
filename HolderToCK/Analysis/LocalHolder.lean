module

public import HolderToCK.Integration.HolderInput
public import HolderToCK.Analysis.RepresentativeGluing
public import HolderToCK.Analysis.LocalHolderChaining
public import HarmonicMaps.Analysis.SobolevAECongruence
public import HarmonicMaps.SobolevRestriction

/-! # Uniform Holder representatives on an enlarged inner ball

The HarmonicMaps half-ball representative theorem is applied on quarter-radius
balls. Open-overlap uniqueness and countable gluing preserve the original
map and its displayed weak gradient.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace HolderToCK

theorem quarter_closedBall_subset_unitBall {n : ℕ} {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    Metric.closedBall x (1 / 4) ⊆ Metric.ball (0 : Domain n) 1 := by
  intro y hy
  have hyx : dist y x ≤ 1 / 4 := hy
  have hx0 : dist x 0 < 3 / 4 := hx
  change dist y 0 < 1
  exact lt_of_le_of_lt (dist_triangle y x 0) (by linarith only [hyx, hx0])

theorem quarter_normalizationFactor (n : ℕ) (hn : 2 ≤ n) :
    (1 / 4 : ℝ) ^ (2 - (n : ℤ)) = (4 : ℝ) ^ (n - 2) := by
  have hpower : (2 : ℤ) - n = -((n - 2 : ℕ) : ℤ) := by omega
  rw [hpower, zpow_neg, zpow_natCast, ← inv_pow]
  norm_num

theorem quarterBall_normalizedEnergy_le_unitEnergy {n q : ℕ} (hn : 2 ≤ n)
    {Du : Domain n → Gradient n q}
    (hE : IntegrableOn (fun x => hsNormSq (Du x)) (Metric.ball (0 : Domain n) 1))
    {x : Domain n} (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    (normalizedEnergy Du x ⟨1 / 4, by norm_num⟩).toReal ≤
      (4 : ℝ) ^ (n - 2) * ∫ y in Metric.ball (0 : Domain n) 1, hsNormSq (Du y) := by
  have hsub := Metric.ball_subset_closedBall.trans (quarter_closedBall_subset_unitBall hx)
  have hsmall := hE.mono_set hsub
  rw [normalizedEnergy_toReal hsmall, quarter_normalizationFactor n hn]
  exact mul_le_mul_of_nonneg_left
    (setIntegral_mono_set hE (Filter.Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Filter.Eventually.of_forall fun _ hy => hsub hy)) (by positivity)

theorem smallEnergy_enlarged_holder_representative {n q : ℕ}
    (hn : 2 ≤ n) (N : CompactSmoothEmbeddedTarget q) :
    ∃ ε α L : ℝ, 0 < ε ∧ 0 < α ∧ α < 1 ∧ 0 < L ∧
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
        MemW12Loc Ω u Du → TakesValuesIn N Ω u → IsLocallyEnergyMinimizing N Ω u Du →
        Metric.closedBall (0 : Domain n) 1 ⊆ Ω.val →
        (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x)) ≤ ε →
        ∃ w : Domain n → Ambient q,
          ContinuousOn w (Metric.ball (0 : Domain n) (3 / 4)) ∧
          w =ᵐ[volume.restrict (Metric.ball (0 : Domain n) (3 / 4))] u ∧
          (∀ x ∈ Metric.ball (0 : Domain n) (3 / 4), w x ∈ N.carrierSet) ∧
          HolderBoundOn (Metric.ball (0 : Domain n) (3 / 4)) w α
            (L * Real.sqrt (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x))) ∧
          MemW12Loc (ballDomain (0 : Domain n) (3 / 4)) w Du ∧
          IntegrableOn (fun x => hsNormSq (Du x)) (Metric.ball (0 : Domain n) (3 / 4)) ∧
          (∫ x in Metric.ball (0 : Domain n) (3 / 4), hsNormSq (Du x)) ≤
            ∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x) := by
  classical
  obtain ⟨εH, α, C, hεH, hα, hαone, hH⟩ := smallEnergyRegularity hn N
  let P : ℝ := (4 : ℝ) ^ (n - 2)
  let K : ℝ := (C : ℝ) * Real.rpow (1 / 4 : ℝ) (-α) * Real.sqrt P
  let L : ℝ := (K + 1) * Real.rpow (24 : ℝ) (1 - α)
  have hP : 0 < P := pow_pos (by norm_num) _
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg C.coe_nonneg (Real.rpow_nonneg (by norm_num) _)) (Real.sqrt_nonneg _)
  have hL : 0 < L := mul_pos (by linarith only [hK]) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨εH / P, α, L, div_pos hεH hP, hα, hαone, hL, ?_⟩
  intro Ω u Du hu huN hmin hclosed henergy
  let E : ℝ := ∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x)
  let s : Set (Domain n) := Metric.ball 0 (3 / 4)
  have hE : 0 ≤ E := integral_nonneg (fun _ => hsNormSq_nonneg _)
  have hEint := hu.integrable_hsNormSq_ball hclosed
  have hlocal (x : s) : ∃ v : Domain n → Ambient q,
      ContinuousOn v (Metric.ball x.val (1 / 8)) ∧
      v =ᵐ[volume.restrict (Metric.ball x.val (1 / 8))] u ∧
      (∀ y ∈ Metric.ball x.val (1 / 8), v y ∈ N.carrierSet) ∧
      HolderBoundOn (Metric.ball x.val (1 / 8)) v α ((K + 1) * Real.sqrt E) := by
    have hxclosed := (quarter_closedBall_subset_unitBall x.property).trans
      (Metric.ball_subset_closedBall.trans hclosed)
    have hNbound := quarterBall_normalizedEnergy_le_unitEnergy hn hEint x.property
    have hNfinite : normalizedEnergy Du x.val ⟨1 / 4, by norm_num⟩ ≠ ⊤ :=
      normalizedEnergy_ne_top_of_dirichletEnergy_ne_top (hu.dirichletEnergy_ne_top_ball hxclosed)
    have hNsmall : normalizedEnergy Du x.val ⟨1 / 4, by norm_num⟩ ≤ ENNReal.ofReal εH := by
      have hreal : (normalizedEnergy Du x.val ⟨1 / 4, by norm_num⟩).toReal ≤ εH :=
        hNbound.trans ((mul_le_mul_of_nonneg_left henergy hP.le).trans_eq
          (mul_div_cancel₀ εH hP.ne'))
      calc
        _ = ENNReal.ofReal (normalizedEnergy Du x.val ⟨1 / 4, by norm_num⟩).toReal :=
          (ENNReal.ofReal_toReal hNfinite).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
    have hquarter := hH Ω u Du hu huN hmin x.val ⟨1 / 4, by norm_num⟩ hxclosed hNsmall
    have hhalf : (⟨1 / 4, by norm_num⟩ : PositiveRadius).val / 2 = (1 / 8 : ℝ) := by norm_num
    rw [hhalf] at hquarter
    obtain ⟨v, hvrep, hvN, hvbound, _⟩ := hquarter
    let V : Domain n → Ambient q := fun y => if hy : y ∈ Metric.ball x.val (1 / 8)
      then v ⟨y, hy⟩ else u y
    have hV (y : Domain n) (hy : y ∈ Metric.ball x.val (1 / 8)) : V y = v ⟨y, hy⟩ := by
      exact dif_pos hy
    refine ⟨V, ?_, ?_, ?_, ?_⟩
    · apply continuousOn_iff_continuous_restrict.mpr
      have heq : (Metric.ball x.val (1 / 8)).restrict V = v := by
        funext y
        exact hV y y.property
      rw [heq]
      exact hvrep.1
    · filter_upwards [hvrep.2, ae_restrict_mem measurableSet_ball] with y hy hyball
      exact (hV y hyball).trans (hy hyball)
    · intro y hy
      rw [hV y hy]
      exact hvN ⟨y, hy⟩
    · intro y hy z hz
      rw [hV y hy, hV z hz]
      have hcoeff : 0 ≤ (C : ℝ) * Real.rpow (1 / 4 : ℝ) (-α) :=
        mul_nonneg C.coe_nonneg (Real.rpow_nonneg (by norm_num) _)
      have hdist : 0 ≤ Real.rpow (dist y z) α := Real.rpow_nonneg dist_nonneg _
      calc
        _ ≤ (C : ℝ) * Real.rpow (1 / 4 : ℝ) (-α) *
            Real.sqrt (normalizedEnergy Du x.val ⟨1 / 4, by norm_num⟩).toReal *
              Real.rpow (dist y z) α := hvbound ⟨y, hy⟩ ⟨z, hz⟩
        _ ≤ (C : ℝ) * Real.rpow (1 / 4 : ℝ) (-α) * Real.sqrt (P * E) *
            Real.rpow (dist y z) α := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hNbound) hcoeff) hdist
        _ = K * Real.sqrt E * Real.rpow (dist y z) α := by
          rw [Real.sqrt_mul hP.le]
          dsimp only [K]
          ring
        _ ≤ ((K + 1) * Real.sqrt E) * Real.rpow (dist y z) α :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith)
            (Real.sqrt_nonneg _)) hdist
  choose v hvcont hvAE hvN hvHolder using hlocal
  have hcover : s ⊆ ⋃ x : s, Metric.ball x.val (1 / 8) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (by norm_num)⟩
  obtain ⟨w, hwcont, hwAE, hsame⟩ := continuous_representatives_glue u s Metric.isOpen_ball
    (fun x : s => Metric.ball x.val (1 / 8)) v (fun _ => Metric.isOpen_ball) hvcont hvAE hcover
  refine ⟨w, hwcont, hwAE, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    let X : s := ⟨x, hx⟩
    rw [hsame X ⟨hx, Metric.mem_ball_self (by norm_num)⟩]
    exact hvN X x (Metric.mem_ball_self (by norm_num))
  · have hshort : ∀ x ∈ s, ∀ y ∈ s, dist x y < (1 / 8 : ℝ) →
        ‖w x - w y‖ ≤ ((K + 1) * Real.sqrt E) * Real.rpow (dist x y) α := by
      intro x hx y hy hxy
      let X : s := ⟨x, hx⟩
      have hyX : y ∈ Metric.ball X.val (1 / 8) := by
        change dist y x < 1 / 8
        simpa only [dist_comm] using hxy
      rw [hsame X ⟨hx, Metric.mem_ball_self (by norm_num)⟩, hsame X ⟨hy, hyX⟩]
      exact hvHolder X x (Metric.mem_ball_self (by norm_num)) y hyX
    have hdiam : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ (3 / 2 : ℝ) := by
      intro x hx y hy
      have hx0 : dist x 0 < 3 / 4 := hx
      have hy0 : dist y 0 < 3 / 4 := hy
      exact (dist_triangle x 0 y).trans (by rw [dist_comm 0 y]; linarith only [hx0, hy0])
    have hbound : HolderBoundOn s w α
        (((K + 1) * Real.sqrt E) * Real.rpow (24 : ℝ) (1 - α)) :=
      holderBoundOn_of_uniform_short_segments (convex_ball (0 : Domain n) (3 / 4))
        24 (by norm_num) hdiam (by norm_num : (3 / 2 : ℝ) < 24 * (1 / 8)) hshort
    have hconst : ((K + 1) * Real.sqrt E) * Real.rpow (24 : ℝ) (1 - α) =
        L * Real.sqrt E := by dsimp only [L]; ring
    rw [hconst] at hbound
    exact hbound
  · have hsΩ : (ballDomain (0 : Domain n) (3 / 4)).val ⊆ Ω.val :=
      (Metric.ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 1)).trans
        (Metric.ball_subset_closedBall.trans hclosed)
    exact (hu.mono hsΩ).congr_ae hwAE.symm (Filter.EventuallyEq.refl _ _)
  · exact hEint.mono_set (Metric.ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 1))
  · exact setIntegral_mono_set hEint (Filter.Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Filter.Eventually.of_forall fun _ hx =>
        (Metric.ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 1)) hx)

end HolderToCK
end

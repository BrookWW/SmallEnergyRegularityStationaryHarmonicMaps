module

public import HolderToCK.Analysis.Campanato.BallEstimates
public import HolderToCK.Foundation.HolderBounds
public import HarmonicMaps.Analysis.BallAverageDifferentiation
public import HarmonicMaps.Analysis.MorreyHolder

/-! # Reconstruction of an L2 field from Campanato oscillation

The actual means of the field have an all-radius limit at every inner point.
Lebesgue differentiation identifies that limit with the original field
almost everywhere. Contained-ball comparison supplies the pointwise Holder
and norm estimates of the resulting continuous representative.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace HolderToCK

theorem campanato_ball_subset_outer {n : ℕ} {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (5 / 8)) {r : ℝ} (hr : r ≤ 1 / 8) :
    Metric.ball x r ⊆ Metric.ball (0 : Domain n) (3 / 4) := by
  intro y hy
  have hyx : dist y x < r := hy
  have hx0 : dist x 0 < (5 / 8 : ℝ) := hx
  change dist y 0 < 3 / 4
  exact lt_of_le_of_lt (dist_triangle y x 0) (by linarith only [hyx, hx0, hr])

theorem campanato_ballMean_ae_tendsto {n q : ℕ} (g : Domain n → Ambient q)
    (hg : MemLp g 2 (volume.restrict (Metric.ball (0 : Domain n) (3 / 4)))) :
    ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) (5 / 8)),
      Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, g y)
        (𝓝[>] (0 : ℝ)) (𝓝 (g x)) := by
  let K : Set (Domain n) := Metric.ball 0 (3 / 4)
  let f : Domain n → Ambient q := K.indicator g
  letI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hgi : Integrable f volume :=
    (integrable_indicator_iff measurableSet_ball).mpr (hg.integrable (by norm_num))
  have hn := IsUnifLocDoublingMeasure.ae_tendsto_average volume hgi.locallyIntegrable 1
  filter_upwards [hn.filter_mono (ae_mono (Measure.restrict_le_self)),
    ae_restrict_mem measurableSet_ball] with x hx hxin
  have hxK : x ∈ K := (Metric.ball_subset_ball (by norm_num : (5 / 8 : ℝ) ≤ 3 / 4)) hxin
  have hcenter : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), x ∈ Metric.closedBall x (1 * r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [mem_closedBall, dist_self, one_mul] using hr.le
  have hnative := hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id hcenter
  have heq : (fun r : ℝ => ⨍ y in Metric.ball x r, g y) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r : ℝ => ⨍ y in Metric.closedBall x r, f y) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))] with r hr hrsmall
    have hrpos : 0 < r := hr
    change r < 1 / 8 at hrsmall
    rw [← setAverage_congr (ball_ae_eq_closedBall x hrpos)]
    apply setAverage_congr_fun measurableSet_ball
    exact Filter.Eventually.of_forall (fun y hy =>
      (indicator_of_mem (campanato_ball_subset_outer hxin hrsmall.le hy) g).symm)
  have hfx : f x = g x := indicator_of_mem hxK g
  rw [hfx] at hnative
  exact hnative.congr' heq.symm

theorem campanato_ballMean_existsUnique {n q : ℕ} {g : Domain n → Ambient q}
    (hg : MemLp g 2 (volume.restrict (Metric.ball (0 : Domain n) (3 / 4))))
    {γ M E r₀ : ℝ} (hγ : 0 < γ) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hr₀ : 0 < r₀) (hr₀small : r₀ ≤ 1 / 8)
    (hOsc : ∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), ∀ r : ℝ,
      0 < r → r ≤ r₀ →
      (∫ y in Metric.ball x r, ‖g y - ⨍ z in Metric.ball x r, g z‖ ^ 2) ≤
        M * E * Real.rpow r ((n : ℝ) + 2 * γ))
    (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (5 / 8)) :
    ∃! G : Ambient q,
      Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, g y)
        (𝓝[>] (0 : ℝ)) (𝓝 G) ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        ‖(⨍ y in Metric.ball x r, g y) - G‖ ≤
          (Real.sqrt ((2 : ℝ) ^ n / volume.real (Metric.ball (0 : Domain n) 1)) /
            (1 - (1 / 2 : ℝ) ^ γ)) * Real.sqrt (M * E) * Real.rpow r γ := by
  let F : ℝ → Ambient q := fun r => ⨍ y in Metric.ball x r, g y
  let K := Real.sqrt ((2 : ℝ) ^ n / volume.real (Metric.ball (0 : Domain n) 1)) *
    Real.sqrt (M * E)
  have hK : 0 ≤ K := by positivity
  have hcomp : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ r₀ → t ≤ 2 * s →
      dist (F s) (F t) ≤ K * t ^ γ := by
    intro s t hs hst ht hratio
    have ht0 : 0 < t := hs.trans_le hst
    have hgt : MemLp g 2 (volume.restrict (Metric.ball x t)) :=
      hg.mono_measure (Measure.restrict_mono_set volume (campanato_ball_subset_outer hx (ht.trans hr₀small)))
    have h := norm_ballAverage_sub_le_oscillation_bound hs ht0 (mul_nonneg hM hE)
      (by norm_num : (0 : ℝ) ≤ 2) (Metric.ball_subset_ball hst) hratio hgt (hOsc x hx t ht0 ht)
    simpa only [F, K, dist_eq_norm, Real.rpow_eq_pow] using h
  obtain ⟨G, hG, _⟩ := existsUnique_allRadius_limit_of_comparable_at_radius F hγ hK hr₀ hcomp
  refine ⟨G, ⟨hG.1, ?_⟩, ?_⟩
  · intro r hr hrr₀
    have h := hG.2 r hr hrr₀
    simp only [F, K, dist_eq_norm] at h
    change ‖(⨍ y in Metric.ball x r, g y) - G‖ ≤
      (Real.sqrt ((2 : ℝ) ^ n / volume.real (Metric.ball (0 : Domain n) 1)) /
        (1 - (1 / 2 : ℝ) ^ γ)) * Real.sqrt (M * E) * r ^ γ
    exact h.trans_eq (by ring)
  · intro v hv
    exact tendsto_nhds_unique hv.1 hG.1

/-- The dimension-only constant for comparison at radius ratio two. -/
@[expose] noncomputable def campanatoComparisonConstant (n : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ) ^ n / volume.real (Metric.ball (0 : Domain n) 1))

/-- The geometric tail constant of the actual ball means. -/
@[expose] noncomputable def campanatoTailConstant (n : ℕ) (γ : ℝ) : ℝ :=
  campanatoComparisonConstant n / (1 - (1 / 2 : ℝ) ^ γ)

/-- The norm bound obtained from the mean at the fixed outer radius. -/
@[expose] noncomputable def campanatoSupConstant (n : ℕ) (γ r₀ M : ℝ) : ℝ :=
  (Real.sqrt (r₀ ^ n * volume.real (Metric.ball (0 : Domain n) 1)))⁻¹ +
    campanatoTailConstant n γ * Real.sqrt M * r₀ ^ γ

/-- The comparison of two small means with their common enclosing ball. -/
@[expose] noncomputable def campanatoNearConstant (n : ℕ) (γ M : ℝ) : ℝ :=
  (2 * campanatoTailConstant n γ * (2 : ℝ) ^ γ +
    2 * campanatoComparisonConstant n * (4 : ℝ) ^ γ) * Real.sqrt M

/-- One finite constant for the norm and Holder bounds of the representative. -/
@[expose] noncomputable def campanatoReconstructionConstant (n : ℕ) (γ r₀ M : ℝ) : ℝ :=
  campanatoSupConstant n γ r₀ M + campanatoNearConstant n γ M +
    2 * campanatoSupConstant n γ r₀ M / (r₀ / 4) ^ γ + 1

theorem campanato_reconstruction (n : ℕ) (γ r₀ M : ℝ)
    (hγ : 0 < γ) (_hγone : γ < 1) (hr₀ : 0 < r₀) (hr₀small : r₀ ≤ 1 / 8)
    (hM : 0 ≤ M) :
    0 < campanatoReconstructionConstant n γ r₀ M ∧
      ∀ (q : ℕ) (g : Domain n → Ambient q) (E : ℝ),
        MemLp g 2 (volume.restrict (Metric.ball (0 : Domain n) (3 / 4))) → 0 ≤ E →
        (∫ x in Metric.ball (0 : Domain n) (3 / 4), ‖g x‖ ^ 2) ≤ E →
        (∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), ∀ r : ℝ, 0 < r → r ≤ r₀ →
          (∫ y in Metric.ball x r, ‖g y - ⨍ z in Metric.ball x r, g z‖ ^ 2) ≤
            M * E * Real.rpow r ((n : ℝ) + 2 * γ)) →
        ∃ G : Domain n → Ambient q,
          ContinuousOn G (Metric.ball (0 : Domain n) (5 / 8)) ∧
          G =ᵐ[volume.restrict (Metric.ball (0 : Domain n) (5 / 8))] g ∧
          (∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), ‖G x‖ ≤
            campanatoReconstructionConstant n γ r₀ M * Real.sqrt E) ∧
          HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8)) G γ
            (campanatoReconstructionConstant n γ r₀ M * Real.sqrt E) ∧
          ∀ x ∈ Metric.ball (0 : Domain n) (5 / 8),
            Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, g y)
              (𝓝[>] (0 : ℝ)) (𝓝 (G x)) := by
  classical
  let J := campanatoComparisonConstant n
  let H := campanatoTailConstant n γ
  let S := campanatoSupConstant n γ r₀ M
  let N := campanatoNearConstant n γ M
  let F := 2 * S / (r₀ / 4) ^ γ
  have hden : 0 < 1 - (1 / 2 : ℝ) ^ γ :=
    sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) hγ)
  have hJ : 0 ≤ J := Real.sqrt_nonneg _
  have hH : 0 ≤ H := div_nonneg hJ hden.le
  have hS : 0 ≤ S := by dsimp only [S, campanatoSupConstant]; positivity
  have hN : 0 ≤ N := by dsimp only [N, campanatoNearConstant]; positivity
  have hbase : 0 < (r₀ / 4) ^ γ := Real.rpow_pos_of_pos (by positivity) _
  have hF : 0 ≤ F := div_nonneg (mul_nonneg (by norm_num) hS) hbase.le
  have hC : 0 < campanatoReconstructionConstant n γ r₀ M := by
    change 0 < S + N + F + 1
    linarith only [hS, hN, hF]
  have hSC : S ≤ campanatoReconstructionConstant n γ r₀ M := by
    change S ≤ S + N + F + 1
    linarith only [hN, hF]
  have hNFC : N + F ≤ campanatoReconstructionConstant n γ r₀ M := by
    change N + F ≤ S + N + F + 1
    linarith only [hS]
  refine ⟨hC, ?_⟩
  intro q g E hg hE hEnergy hOsc
  let s : Set (Domain n) := Metric.ball 0 (5 / 8)
  have hex (x : s) := campanato_ballMean_existsUnique hg hγ hM hE hr₀ hr₀small hOsc x x.property
  let G : Domain n → Ambient q := fun x => if hx : x ∈ s then
    (hex ⟨x, hx⟩).exists.choose else g x
  have hGvalue (x : Domain n) (hx : x ∈ s) :
      G x = (hex ⟨x, hx⟩).exists.choose := dif_pos hx
  have hlimit (x : Domain n) (hx : x ∈ s) :
      Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, g y) (𝓝[>] (0 : ℝ)) (𝓝 (G x)) := by
    rw [hGvalue x hx]
    exact (hex ⟨x, hx⟩).exists.choose_spec.1
  have htail (x : Domain n) (hx : x ∈ s) (r : ℝ) (hr : 0 < r) (hrr₀ : r ≤ r₀) :
      ‖(⨍ y in Metric.ball x r, g y) - G x‖ ≤ H * Real.sqrt (M * E) * r ^ γ := by
    rw [hGvalue x hx]
    exact (hex ⟨x, hx⟩).exists.choose_spec.2 r hr hrr₀
  have hEnergyI : IntegrableOn (fun x => ‖g x‖ ^ 2) (Metric.ball (0 : Domain n) (3 / 4)) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hsup : ∀ x ∈ s, ‖G x‖ ≤ S * Real.sqrt E := by
    intro x hx
    have hsub := campanato_ball_subset_outer hx hr₀small
    have hgball : MemLp g 2 (volume.restrict (Metric.ball x r₀)) :=
      hg.mono_measure (Measure.restrict_mono_set volume hsub)
    have hEball : (∫ y in Metric.ball x r₀, ‖g y‖ ^ 2) ≤ E :=
      (setIntegral_mono_set hEnergyI (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (Filter.Eventually.of_forall fun _ hy => hsub hy)).trans hEnergy
    have hmean := norm_ballAverage_le_of_l2_integral_le x hr₀ hE hgball hEball
    rw [ball_volume_real x hr₀] at hmean
    have ht := htail x hx r₀ hr₀ le_rfl
    let m := ⨍ y in Metric.ball x r₀, g y
    calc
      ‖G x‖ = ‖m + (G x - m)‖ := congrArg norm (by abel)
      _ ≤ ‖m‖ + ‖G x - m‖ := norm_add_le _ _
      _ ≤ (Real.sqrt (r₀ ^ n * volume.real (Metric.ball (0 : Domain n) 1)))⁻¹ * Real.sqrt E +
          H * Real.sqrt (M * E) * r₀ ^ γ :=
        add_le_add hmean (by simpa only [m, norm_sub_rev] using ht)
      _ = S * Real.sqrt E := by
        rw [Real.sqrt_mul hM]
        dsimp only [S, campanatoSupConstant, H]
        ring
  have hnear : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ r₀ / 4 →
      ‖G x - G y‖ ≤ N * Real.sqrt E * (dist x y) ^ γ := by
    intro x hx y hy hd
    by_cases hxy : x = y
    · subst y
      simp only [sub_self, norm_zero, dist_self, Real.zero_rpow hγ.ne', mul_zero, le_refl]
    let d := dist x y
    have hd0 : 0 < d := dist_pos.mpr hxy
    have h2d : 0 < 2 * d := by positivity
    have h4d : 0 < 4 * d := by positivity
    have h2r₀ : 2 * d ≤ r₀ := by dsimp only [d]; linarith only [hd, hr₀]
    have h4r₀ : 4 * d ≤ r₀ := by dsimp only [d]; linarith only [hd]
    have hxsub : Metric.ball x (2 * d) ⊆ Metric.ball x (4 * d) :=
      Metric.ball_subset_ball (by linarith only [hd0])
    have hysub : Metric.ball y (2 * d) ⊆ Metric.ball x (4 * d) := by
      apply Metric.ball_subset_ball'
      rw [dist_comm]
      change 2 * d + d ≤ 4 * d
      linarith only [hd0]
    have hg4 : MemLp g 2 (volume.restrict (Metric.ball x (4 * d))) :=
      hg.mono_measure (Measure.restrict_mono_set volume
        (campanato_ball_subset_outer hx (h4r₀.trans hr₀small)))
    have hxc := norm_ballAverage_sub_le_oscillation_bound h2d h4d (mul_nonneg hM hE)
      (by norm_num : (0 : ℝ) ≤ 2) hxsub (by ring_nf; exact le_refl _) hg4
      (hOsc x hx (4 * d) h4d h4r₀)
    have hyc := norm_ballAverage_sub_le_oscillation_bound h2d h4d (mul_nonneg hM hE)
      (by norm_num : (0 : ℝ) ≤ 2) hysub (by ring_nf; exact le_refl _) hg4
      (hOsc x hx (4 * d) h4d h4r₀)
    have hxt := htail x hx (2 * d) h2d h2r₀
    have hyt := htail y hy (2 * d) h2d h2r₀
    let mx := ⨍ z in Metric.ball x (2 * d), g z
    let my := ⨍ z in Metric.ball y (2 * d), g z
    let mc := ⨍ z in Metric.ball x (4 * d), g z
    have hsum : ‖G x - G y‖ ≤ ‖mx - G x‖ + ‖mx - mc‖ + ‖my - mc‖ + ‖my - G y‖ := by
      calc
        _ ≤ ‖G x - mx‖ + ‖mx - G y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ‖G x - mx‖ + (‖mx - mc‖ + ‖mc - G y‖) :=
          add_le_add_right (norm_sub_le_norm_sub_add_norm_sub _ _ _) _
        _ ≤ ‖G x - mx‖ + (‖mx - mc‖ + (‖mc - my‖ + ‖my - G y‖)) :=
          add_le_add_right (add_le_add_right (norm_sub_le_norm_sub_add_norm_sub _ _ _) _) _
        _ = _ := by rw [norm_sub_rev (G x) mx, norm_sub_rev mc my]; ring
    have hsum' := hsum.trans (add_le_add (add_le_add (add_le_add hxt hxc) hyc) hyt)
    simp only [Real.rpow_eq_pow] at hsum'
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hd0.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hd0.le, Real.sqrt_mul hM] at hsum'
    exact hsum'.trans_eq (by
      dsimp only [N, campanatoNearConstant, H, J, campanatoComparisonConstant, d]
      ring)
  have hholder : HolderBoundOn s G γ ((N + F) * Real.sqrt E) := by
    intro x hx y hy
    by_cases hd : dist x y ≤ r₀ / 4
    · exact (hnear x hx y hy hd).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hF) (Real.sqrt_nonneg E))
        (Real.rpow_nonneg dist_nonneg _))
    · have hp : (r₀ / 4) ^ γ ≤ (dist x y) ^ γ :=
        Real.rpow_le_rpow (by positivity) (le_of_lt (lt_of_not_ge hd)) hγ.le
      have htri : ‖G x - G y‖ ≤ 2 * S * Real.sqrt E :=
        (norm_sub_le _ _).trans ((add_le_add (hsup x hx) (hsup y hy)).trans_eq (by ring))
      calc
        _ ≤ 2 * S * Real.sqrt E := htri
        _ = (F * Real.sqrt E) * (r₀ / 4) ^ γ := by dsimp only [F]; field_simp [hbase.ne']
        _ ≤ (F * Real.sqrt E) * (dist x y) ^ γ :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg hF (Real.sqrt_nonneg E))
        _ ≤ ((N + F) * Real.sqrt E) * Real.rpow (dist x y) γ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hN) (Real.sqrt_nonneg E))
            (Real.rpow_nonneg dist_nonneg _)
  have hcontinuous : ContinuousOn G s := by
    apply continuousOn_iff_continuous_restrict.mpr
    apply continuous_of_norm_sub_le_rpow _ hγ
    intro x y
    exact hholder x x.property y y.property
  have hAE : G =ᵐ[volume.restrict s] g := by
    filter_upwards [campanato_ballMean_ae_tendsto g hg, ae_restrict_mem measurableSet_ball]
      with x hx hxin
    exact tendsto_nhds_unique (hlimit x hxin) hx
  refine ⟨G, hcontinuous, hAE, ?_, ?_, hlimit⟩
  · intro x hx
    exact (hsup x hx).trans (mul_le_mul_of_nonneg_right hSC (Real.sqrt_nonneg E))
  · intro x hx y hy
    exact (hholder x hx y hy).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hNFC (Real.sqrt_nonneg E)) (Real.rpow_nonneg dist_nonneg _))

end HolderToCK
end

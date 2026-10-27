module

public import HolderToCK.Analysis.Poisson.HessianAnnularBounds
public import HolderToCK.Analysis.Poisson.HessianNearFar

/-! # Translation of Hessian cancellation across expanding outer balls

The discrepancy between outer balls centered at two points lies in a radial
shell. Its absolute integral vanishes as the radius tends to infinity.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace HolderToCK

theorem hessianKernelExpression_shiftedAnnulus_cancellation {n : ℕ}
    (hn : 0 < n) (i j : Fin n) (x : Domain n) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ z in Metric.ball x b \ Metric.ball x a,
      hessianKernelExpression i j (x - z)) = 0 := by
  have hpre : (fun z => x - z) ⁻¹'
      (Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) a) =
      Metric.ball x b \ Metric.ball x a := by
    rw [preimage_sdiff, subLeft_preimage_ball, subLeft_preimage_ball]
  rw [← hpre, integral_subLeft_preimage x _
    (measurableSet_ball.diff measurableSet_ball)]
  exact hessianKernelExpression_annulus_cancellation hn i j ha hab

theorem hessianKernelExpression_shiftedAnnulus_norm_integral_bound {n : ℕ}
    (hn : 0 < n) (i j : Fin n) (x : Domain n) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ z in Metric.ball x b \ Metric.ball x a,
      ‖hessianKernelExpression i j (x - z)‖) ≤
      ((n : ℝ) + 1) * Real.log (b / a) := by
  have hpre : (fun z => x - z) ⁻¹'
      (Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) a) =
      Metric.ball x b \ Metric.ball x a := by
    rw [preimage_sdiff, subLeft_preimage_ball, subLeft_preimage_ball]
  rw [← hpre, integral_subLeft_preimage x (fun z => ‖hessianKernelExpression i j z‖)
    (measurableSet_ball.diff measurableSet_ball)]
  exact hessianKernelExpression_annulus_norm_integral_bound hn i j ha hab

theorem hessianKernelExpression_shell_subset_integral_bound {n : ℕ}
    (hn : 0 < n) (i j : Fin n) (x : Domain n) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {s : Set (Domain n)}
    (hsub : s ⊆ Metric.ball x b \ Metric.ball x a) :
    ‖∫ z in s, hessianKernelExpression i j (x - z)‖ ≤
      ((n : ℝ) + 1) * Real.log (b / a) := by
  have hi := hessianKernelExpression_shifted_integrableOn_annulus i j x ha (b := b)
  calc
    _ ≤ ∫ z in s, ‖hessianKernelExpression i j (x - z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in Metric.ball x b \ Metric.ball x a,
        ‖hessianKernelExpression i j (x - z)‖ :=
      setIntegral_mono_set hi.norm
        (Eventually.of_forall (fun _ => norm_nonneg _)) (Eventually.of_forall hsub)
    _ ≤ _ := hessianKernelExpression_shiftedAnnulus_norm_integral_bound hn i j x ha hab

theorem hessianKernelDifference_truncated_cancellation_bound {n : ℕ}
    (hn : 0 < n) (i j : Fin n) (x y : Domain n) (hxy : x ≠ y)
    {R : ℝ} (hR : 3 * dist x y < R) :
    ‖(∫ z in Metric.ball x R \ Metric.ball x (2 * dist x y),
        hessianKernelExpression i j (x - z) - hessianKernelExpression i j (y - z)) -
      ∫ z in Metric.ball x (2 * dist x y) \ Metric.ball y (dist x y),
        hessianKernelExpression i j (y - z)‖ ≤
      ((n : ℝ) + 1) * Real.log ((R + dist x y) / (R - dist x y)) := by
  let d : ℝ := dist x y
  have hd : 0 < d := dist_pos.mpr hxy
  have hRm : 0 < R - d := by dsimp only [d]; linarith only [hR, dist_nonneg (x := x) (y := y)]
  let U := Metric.ball x R
  let V := Metric.ball x (2 * d)
  let W := Metric.ball y d
  let A := U \ W
  let D := V \ W
  let J := Metric.ball y (R - d)
  let C := J \ W
  have hWV : W ⊆ V := ball_dist_subset_ball_twoDist x y
  have hVU : V ⊆ U := Metric.ball_subset_ball (by dsimp only [d]; linarith only [hR, hd])
  have hupper : A ⊆ Metric.ball y (R + d) \ W := by
    intro z hz
    refine ⟨?_, hz.2⟩
    have hzU : dist z x < R := hz.1
    change dist z y < R + d
    exact (dist_triangle z x y).trans_lt (by dsimp only [d]; linarith only [hzU])
  have hiA : IntegrableOn (fun z => hessianKernelExpression i j (y - z)) A volume :=
    (hessianKernelExpression_shifted_integrableOn_annulus i j y hd (b := R + d)).mono_set hupper
  have hDA : D ⊆ A := fun z hz => ⟨hVU hz.1, hz.2⟩
  have hdiff : A \ D = U \ V := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.1.1, fun hzV => hz.2 ⟨hzV, hz.1.2⟩⟩
    · intro hz
      exact ⟨⟨hz.1, fun hzW => hz.2 (hWV hzW)⟩, fun hzD => hz.2 hzD.1⟩
  have hKy : (∫ z in U \ V, hessianKernelExpression i j (y - z)) =
      (∫ z in A, hessianKernelExpression i j (y - z)) -
        ∫ z in D, hessianKernelExpression i j (y - z) := by
    rw [← hdiff]
    exact setIntegral_sdiff (measurableSet_ball.diff measurableSet_ball) hiA hDA
  have hKx : (∫ z in U \ V, hessianKernelExpression i j (x - z)) = 0 :=
    hessianKernelExpression_shiftedAnnulus_cancellation hn i j x
      (mul_pos zero_lt_two hd) (by dsimp only [d]; linarith only [hR, hd])
  have hJU : J ⊆ U := by
    intro z hz
    have hzJ : dist z y < R - d := hz
    change dist z x < R
    exact (dist_triangle z y x).trans_lt (by rw [dist_comm y x]; dsimp only [d] at hzJ; linarith only [hzJ])
  have hCA : C ⊆ A := fun z hz => ⟨hJU hz.1, hz.2⟩
  have hCzero : (∫ z in C, hessianKernelExpression i j (y - z)) = 0 :=
    hessianKernelExpression_shiftedAnnulus_cancellation hn i j y hd
      (by dsimp only [d]; linarith only [hR, hd])
  have htail : A \ C ⊆ Metric.ball y (R + d) \ Metric.ball y (R - d) := by
    intro z hz
    refine ⟨(hupper hz.1).1, ?_⟩
    intro hzJ
    exact hz.2 ⟨hzJ, hz.1.2⟩
  have hAeq : (∫ z in A, hessianKernelExpression i j (y - z)) =
      ∫ z in A \ C, hessianKernelExpression i j (y - z) := by
    rw [setIntegral_sdiff (measurableSet_ball.diff measurableSet_ball) hiA hCA,
      hCzero, sub_zero]
  have hbound : ‖∫ z in A, hessianKernelExpression i j (y - z)‖ ≤
      ((n : ℝ) + 1) * Real.log ((R + d) / (R - d)) := by
    rw [hAeq]
    exact hessianKernelExpression_shell_subset_integral_bound hn i j y hRm
      (by linarith only [hd]) htail
  have hiX := hessianKernelExpression_shifted_integrableOn_annulus i j x
    (mul_pos zero_lt_two hd) (b := R)
  have hiY : IntegrableOn (fun z => hessianKernelExpression i j (y - z)) (U \ V) volume := by
    rw [← hdiff]
    exact hiA.mono_set sdiff_subset
  change ‖(∫ z in U \ V, hessianKernelExpression i j (x - z) -
      hessianKernelExpression i j (y - z)) -
    ∫ z in D, hessianKernelExpression i j (y - z)‖ ≤ _
  rw [integral_sub hiX hiY, hKx, hKy]
  have halgebra (a b : ℝ) : 0 - (a - b) - b = -a := by ring
  rw [halgebra, norm_neg]
  exact hbound

theorem hessianKernelDifference_exterior_cancellation {n : ℕ}
    (hn : 0 < n) (i j : Fin n) (x y : Domain n) (hxy : x ≠ y) :
    (∫ z in (Metric.ball x (2 * dist x y))ᶜ,
      hessianKernelExpression i j (x - z) - hessianKernelExpression i j (y - z)) =
      ∫ z in Metric.ball x (2 * dist x y) \ Metric.ball y (dist x y),
        hessianKernelExpression i j (y - z) := by
  let d : ℝ := dist x y
  let F : Domain n → ℝ := fun z =>
    hessianKernelExpression i j (x - z) - hessianKernelExpression i j (y - z)
  let s : ℝ → Set (Domain n) := fun R => Metric.ball x R \ Metric.ball x (2 * d)
  let A : ℝ := ∫ z in Metric.ball x (2 * d) \ Metric.ball y d,
    hessianKernelExpression i j (y - z)
  have hUnion : (⋃ R : ℝ, s R) = (Metric.ball x (2 * d))ᶜ := by
    ext z
    constructor
    · intro hz
      obtain ⟨R, hzR⟩ := mem_iUnion.mp hz
      exact hzR.2
    · intro hz
      exact mem_iUnion.mpr ⟨dist z x + 1, ⟨by change dist z x < dist z x + 1; linarith, hz⟩⟩
  have hmono : Monotone s := fun R S hRS _ hz =>
    ⟨Metric.ball_subset_ball hRS hz.1, hz.2⟩
  have hi : IntegrableOn F (⋃ R : ℝ, s R) volume := by
    rw [hUnion]
    exact hessianKernelDifference_integrableOn hn i j x y hxy
  have ht := tendsto_setIntegral_of_monotone
    (fun R => measurableSet_ball.diff measurableSet_ball) hmono hi
  rw [hUnion] at ht
  have hsub : Tendsto (fun R : ℝ => R - d) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-d) tendsto_id
  have hzero : Tendsto (fun R : ℝ => (2 * d) / (R - d)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsub
  have hratio : Tendsto (fun R : ℝ => (R + d) / (R - d)) atTop (𝓝 1) := by
    have h : Tendsto (fun R : ℝ => 1 + (2 * d) / (R - d)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hzero
    have h1 : Tendsto (fun R : ℝ => 1 + (2 * d) / (R - d)) atTop (𝓝 1) := by
      simpa only [add_zero] using h
    apply h1.congr'
    filter_upwards [eventually_gt_atTop d] with R hR
    field_simp [(sub_pos.mpr hR).ne']
    ring
  have hlog : Tendsto (fun R : ℝ =>
      ((n : ℝ) + 1) * Real.log ((R + d) / (R - d))) atTop (𝓝 0) := by
    simpa only [Real.log_one, mul_zero, Function.comp_def] using
      ((Real.continuousAt_log one_ne_zero).tendsto.comp hratio).const_mul ((n : ℝ) + 1)
  have hlim : Tendsto (fun R : ℝ => (∫ z in s R, F z) - A) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hlog
    filter_upwards [eventually_gt_atTop (3 * d)] with R hR
    exact hessianKernelDifference_truncated_cancellation_bound hn i j x y hxy hR
  exact sub_eq_zero.mp (tendsto_nhds_unique (ht.sub_const A) hlim)

end HolderToCK
end

module

public import StationaryHarmonicMaps.Analysis.BallDivergenceSign

/-!
# Divergence inequalities with a genuine sphere flux sign

The radial derivative weight is normalized by integration by parts against
identity. Dominated convergence then recovers the divergence integral on
the open unit ball from actual smooth compact tests.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The radial derivative weight has the exact dimension-dependent mass, proved by testing the identity field. -/
theorem integral_radial_weight_norm_sq {n : ℕ}
    (κ : Domain n → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (w : Domain n → ℝ)
    (hDκ : ∀ (x : Domain n) (i : Fin n),
      fderiv ℝ κ x (EuclideanSpace.single i 1) = -w x * x i) :
    Integrable (fun x => w x * ‖x‖^2) volume ∧
      (∫ x, w x * ‖x‖^2) = (n : ℝ) * ∫ x, κ x := by
  have H := integral_radial_test_divergence (fun x : Domain n => x) contDiff_id κ hκ hcκ w hDκ
  have htrace (x : Domain n) :
      (∑ i : Fin n, (fderiv ℝ (fun y : Domain n => y) x (EuclideanSpace.single i 1)) i) = (n : ℝ) := by
    change (∑ i : Fin n, (fderiv ℝ (id : Domain n → Domain n) x (EuclideanSpace.single i 1)) i) = (n : ℝ)
    simp only [fderiv_id, ContinuousLinearMap.id_apply, PiLp.single_apply, ite_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hinner (x : Domain n) : inner ℝ x x = ‖x‖^2 := real_inner_self_eq_norm_sq x
  refine ⟨H.2.1.congr (Eventually.of_forall (fun x => by change w x * inner ℝ x x = w x * ‖x‖^2; rw [hinner])), ?_⟩
  calc
    _ = ∫ x, w x * inner ℝ x x := integral_congr_ae (Eventually.of_forall (fun x => by change w x * ‖x‖^2 = w x * inner ℝ x x; rw [hinner]))
    _ = ∫ x, κ x * (n : ℝ) := by simpa only [htrace] using H.2.2.symm
    _ = _ := by rw [integral_mul_const, mul_comm]

/-- The actual radial compact tests tend pointwise to the open unit-ball indicator. -/
theorem radial_unitBall_test_tendsto (n : ℕ) (x : Domain n) :
    Tendsto (fun j : ℕ => Real.smoothTransition ((1-‖x‖^2)/(1/((j:ℝ)+1)))) atTop
      (𝓝 ((ball (0 : Domain n) 1).indicator (fun _ => (1:ℝ)) x)) := by
  have hε : Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  by_cases hx : x∈ball (0 : Domain n) 1
  · have hxNorm : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
    have hgap : 0 < 1-‖x‖^2 := by nlinarith only [norm_nonneg x, hxNorm]
    have hev : ∀ᶠ j : ℕ in atTop, 1/((j:ℝ)+1) < 1-‖x‖^2 := hε.eventually_lt_const hgap
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with j hj
    rw [indicator_of_mem hx]
    exact ((radial_unitBall_test_properties n (1/((j:ℝ)+1)) (by positivity)).2.2.2.1 x (by linarith)).symm
  · have hxNorm : 1 ≤ ‖x‖ := not_lt.mp (by simpa only [mem_ball, dist_zero_right] using hx)
    have hxSq : 1 ≤ ‖x‖^2 := by nlinarith only [sq_nonneg (‖x‖-1), hxNorm]
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall (fun j => by
      rw [indicator_of_notMem hx]
      exact ((radial_unitBall_test_properties n (1/((j:ℝ)+1)) (by positivity)).2.2.2.2.1 x hxSq).symm)


/-- A genuine nonpositive sphere flux forces the actual open-ball divergence integral to be nonpositive. -/
theorem unitBall_integral_divergence_nonpos {n : ℕ}
    (V : Domain n → Domain n) (hV : ContDiff ℝ 1 V)
    (hSphere : ∀ x : Domain n, ‖x‖=1 → inner ℝ x (V x) ≤ 0) :
    IntegrableOn (fun x => ∑ i : Fin n,
      (fderiv ℝ V x (EuclideanSpace.single i 1)) i) (ball (0 : Domain n) 1) volume ∧
      (∫ x in ball (0 : Domain n) 1, ∑ i : Fin n,
        (fderiv ℝ V x (EuclideanSpace.single i 1)) i) ≤ 0 := by
  let d := fun x : Domain n => ∑ i : Fin n,
    (fderiv ℝ V x (EuclideanSpace.single i 1)) i
  let K := closedBall (0 : Domain n) 1
  let b := K.indicator (fun _ : Domain n => (1:ℝ))
  let C := (n:ℝ) * ∫ x, b x
  let ε := fun j : ℕ => 1/((j:ℝ)+1)
  let κ := fun j (x : Domain n) => Real.smoothTransition ((1-‖x‖^2)/ε j)
  let w := fun j (x : Domain n) => (2/ε j)*deriv Real.smoothTransition ((1-‖x‖^2)/ε j)
  have hεpos (j : ℕ) : 0 < ε j := by dsimp only [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 (0:ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hprops (j : ℕ) := radial_unitBall_test_properties n (ε j) (hεpos j)
  have hd : Continuous d := by
    apply continuous_finsetSum
    intro i _
    exact (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).continuous.comp
      ((hV.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hK : IsCompact K := isCompact_closedBall (0 : Domain n) 1
  have hIK : IntegrableOn d K volume := hd.continuousOn.integrableOn_compact hK
  have hb : Integrable b volume :=
    (continuous_const.continuousOn.integrableOn_compact hK).integrable_indicator measurableSet_closedBall
  have hκbound (j : ℕ) (x : Domain n) : κ j x ≤ b x := by
    by_cases hx : x∈K
    · rw [show b x=1 from indicator_of_mem hx _]
      exact (hprops j).2.2.1 x |>.2
    · rw [show b x=0 from indicator_of_notMem hx _]
      have hn : 1<‖x‖ := not_le.mp (by simpa only [K,mem_closedBall,dist_zero_right] using hx)
      exact le_of_eq ((hprops j).2.2.2.2.1 x (by nlinarith only [sq_nonneg (‖x‖-1), hn]))
  have hκI (j : ℕ) : Integrable (κ j) volume :=
    (hprops j).1.continuous.integrable_of_hasCompactSupport (hprops j).2.1
  have hpair (j : ℕ) := integral_radial_test_divergence V hV (κ j)
    (hprops j).1 (hprops j).2.1 (w j) (hprops j).2.2.2.2.2.2.2
  have hmass (j : ℕ) := integral_radial_weight_norm_sq (κ j)
    (hprops j).1 (hprops j).2.1 (w j) (hprops j).2.2.2.2.2.2.2
  have hbdI : Integrable (K.indicator (fun x => ‖d x‖)) volume :=
    (hd.norm.continuousOn.integrableOn_compact hK).integrable_indicator measurableSet_closedBall
  have hbound (j : ℕ) (x : Domain n) : ‖κ j x*d x‖ ≤ K.indicator (fun x => ‖d x‖) x := by
    by_cases hx : x∈K
    · rw [indicator_of_mem hx, norm_mul, Real.norm_of_nonneg ((hprops j).2.2.1 x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) ((hprops j).2.2.1 x).2
    · have hk0 : κ j x=0 := le_antisymm (by simpa only [b,indicator_of_notMem hx] using hκbound j x)
        ((hprops j).2.2.1 x).1
      simp only [hk0,zero_mul,norm_zero,indicator_of_notMem hx,le_refl]
  have hlim : Tendsto (fun j => ∫ x, κ j x*d x) atTop
      (𝓝 (∫ x in ball (0 : Domain n) 1, d x)) := by
    have hpoint (x : Domain n) : Tendsto (fun j => κ j x*d x) atTop
        (𝓝 ((ball (0 : Domain n) 1).indicator d x)) := by
      have H := (radial_unitBall_test_tendsto n x).mul (tendsto_const_nhds (x := d x))
      have heq : (ball (0 : Domain n) 1).indicator (fun _ => (1:ℝ)) x * d x =
          (ball (0 : Domain n) 1).indicator d x := by
        by_cases hx : x∈ball (0 : Domain n) 1
        · rw [indicator_of_mem hx,indicator_of_mem hx,one_mul]
        · rw [indicator_of_notMem hx,indicator_of_notMem hx,zero_mul]
      simpa only [κ,ε,heq] using H
    have H := tendsto_integral_of_dominated_convergence
      (F := fun j x => κ j x*d x) (f := (ball (0 : Domain n) 1).indicator d)
      (K.indicator (fun x => ‖d x‖))
      (fun j => ((hprops j).1.continuous.mul hd).aestronglyMeasurable) hbdI
      (fun j => Eventually.of_forall (hbound j)) (Eventually.of_forall hpoint)
    simpa only [integral_indicator measurableSet_ball] using H
  have hestimate (η : ℝ) (hη : 0<η) : (∫ x in ball (0 : Domain n) 1, d x) ≤ η*C := by
    obtain ⟨δ,hδ,_hδhalf,hband⟩ := exists_unitSphere_boundary_band
      (fun x => inner ℝ x (V x)) (continuous_id.inner hV.continuous) hSphere η hη
    have hev : ∀ᶠ j : ℕ in atTop, ε j<δ := hε.eventually_lt_const hδ
    have hseq : ∀ᶠ j : ℕ in atTop, (∫ x, κ j x*d x) ≤ η*C := by
      filter_upwards [hev] with j hj
      have hpoint (x : Domain n) : w j x * inner ℝ x (V x) ≤ η*(w j x*‖x‖^2) := by
        by_cases hx : 1<‖x‖^2 ∨ ‖x‖^2<1-ε j
        · have hw0 : w j x=0 := (hprops j).2.2.2.2.2.2.1 x hx
          rw [hw0]
          simp only [zero_mul,mul_zero,le_refl]
        · have hn : ‖x‖≤1 := by
            have H : ‖x‖^2≤1 := not_lt.mp (fun H => hx (Or.inl H))
            nlinarith only [H,norm_nonneg x]
          have hlow : 1-δ≤‖x‖^2 := by
            have H : 1-ε j≤‖x‖^2 := not_lt.mp (fun H => hx (Or.inr H))
            linarith only [H,hj]
          have H := mul_le_mul_of_nonneg_left (hband x hn hlow) ((hprops j).2.2.2.2.2.1 x)
          nlinarith only [H]
      calc
        _ = ∫ x, w j x*inner ℝ x (V x) := (hpair j).2.2
        _ ≤ ∫ x, η*(w j x*‖x‖^2) := integral_mono (hpair j).2.1 ((hmass j).1.const_mul η) hpoint
        _ = η*((n:ℝ)*∫ x,κ j x) := by rw [integral_const_mul,(hmass j).2]
        _ ≤ η*C := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (integral_mono (hκI j) hb (hκbound j)) (Nat.cast_nonneg n)) hη.le
    exact le_of_tendsto hlim hseq
  have hzero : Tendsto (fun j : ℕ => ε j*C) atTop (𝓝 (0:ℝ)) := by
    simpa only [zero_mul] using hε.mul_const C
  refine ⟨hIK.mono_set ball_subset_closedBall, ?_⟩
  exact ge_of_tendsto hzero (Eventually.of_forall (fun j => hestimate (ε j) (hεpos j)))

end StationaryHarmonicMaps.Analysis

end

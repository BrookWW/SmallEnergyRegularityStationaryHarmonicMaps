module

public import StationaryHarmonicMaps.Analysis.LinearBoundaryPowerGrowth

/-! # Full-ball real-power growth for actual linear Dirichlet responses

Boundary-centered growth and true contained-ball forcing-response decay
control all original centers, including points arbitrarily close to the
sphere. Every positive query radius remains included.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

private theorem exists_radial_unit_sphere_point {n : ℕ} (a : Domain n)
    (ha : 0<‖a‖) (haOne : ‖a‖≤1) :
    ∃ b : Domain n,‖b‖=1 ∧ dist a b=1-‖a‖ := by
  let b := ‖a‖⁻¹ • a
  have hb : ‖b‖=1 := norm_smul_inv_norm (norm_pos_iff.mp ha)
  have hCoeff : 0≤‖a‖⁻¹-1 := sub_nonneg.mpr ((one_le_inv₀ ha).mpr haOne)
  refine ⟨b,hb,?_⟩
  have hDiff : b-a=(‖a‖⁻¹-1) • a := by dsimp only [b];rw [sub_smul,one_smul]
  rw [dist_comm,dist_eq_norm,hDiff,norm_smul,Real.norm_eq_abs,abs_of_nonneg hCoeff,
    sub_mul,inv_mul_cancel₀ ha.ne',one_mul]

/-- The same actual zero-boundary linear solution has full-ball growth for every real exponent below dimension; its total-energy premise is the original L2 response estimate. -/
theorem exists_linear_zeroBoundary_full_real_power_growth (n : ℕ) (hn : 2≤n)
    (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (f : Domain n → Ambient q)
      (Df F : Domain n → Gradient n q) (K : ℝ),
      HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) f Df →
      (∀ i,MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) →
      0≤K →
      (∀ (a : Domain n),a∈Metric.ball (0 : Domain n) 1 → ∀ r : ℝ,0<r →
        (∫ x in Metric.ball a r∩Metric.ball (0 : Domain n) 1,hsNormSq (F x))≤K*r^ν) →
      (∫ x in Metric.ball (0 : Domain n) 1,hsNormSq (Df x))≤K →
      HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1)
        (fun x i => Df x i+F x i) (fun _ => (0 : Ambient q)) →
      ∀ (a : Domain n),a∈Metric.ball (0 : Domain n) 1 → ∀ r : ℝ,0<r →
        (∫ x in Metric.ball a r∩Metric.ball (0 : Domain n) 1,hsNormSq (Df x))≤C*K*r^ν := by
  obtain ⟨Cb,hCb,hBoundary⟩ := exists_linear_flux_boundary_real_power_growth n hn ν hν hνn
  obtain ⟨Ci,hCi,hInterior⟩ := exists_linear_flux_interior_real_power_growth n hn ν hν hνn
  obtain ⟨θ,hθ,hθHalf,hScale⟩ := exists_scale_absorbing_higher_power
    (C := 2*(2 : ℝ)^n) (p := (n : ℝ)) (β := ν)
    (by positivity) hνn
  have hθOne : θ<1 := by linarith
  have hScaleN : 2*(2 : ℝ)^n*θ^n≤(1/2 : ℝ)*θ^ν := by
    simpa only [Real.rpow_natCast] using hScale
  let ρ := 2*(2 : ℝ)^n*θ^n
  have hρ : 0≤ρ := by dsimp only [ρ];positivity
  have hgap : ρ<θ^ν := lt_of_le_of_lt hScaleN (by nlinarith only [Real.rpow_pos_of_pos hθ ν])
  let Cnear := Cb*(3 : ℝ)^ν
  let Citer := (Cnear+2/(θ^ν-ρ))/θ^ν
  let C := 1+2*Ci+(4 : ℝ)^ν+Cnear+Citer
  have hCnear : 0≤Cnear := by dsimp only [Cnear];positivity
  have hCiter : 0≤Citer := by dsimp only [Citer];positivity
  have hC : 0<C := by dsimp only [C];positivity
  have hOneC : 1≤C := by dsimp only [C];linarith only [hCi.le,hCnear,hCiter,Real.rpow_nonneg (by norm_num : (0 : ℝ)≤4) ν]
  have hCiC : Ci≤C := by dsimp only [C];linarith only [hCi.le,hCnear,hCiter,Real.rpow_nonneg (by norm_num : (0 : ℝ)≤4) ν]
  have hFourC : (4 : ℝ)^ν≤C := by dsimp only [C];linarith only [hCi.le,hCnear,hCiter]
  have hNearC : Cnear≤C := by dsimp only [C];linarith only [hCi.le,hCiter,Real.rpow_nonneg (by norm_num : (0 : ℝ)≤4) ν]
  have hIterC : Citer≤C := by dsimp only [C];linarith only [hCi.le,hCnear,Real.rpow_nonneg (by norm_num : (0 : ℝ)≤4) ν]
  refine ⟨C,hC,?_⟩
  intro q f Df F K hf hF hK hGrowth hEnergy hEquation
  let U := Metric.ball (0 : Domain n) 1
  have hAll (a : Domain n) (ha : a∈U) (r : ℝ) (hr : 0<r) :
      (∫ x in Metric.ball a r∩U,hsNormSq (Df x))≤C*K*r^ν := by
    let E := fun s : ℝ => ∫ x in Metric.ball a s∩U,hsNormSq (Df x)
    have hFull (s : ℝ) : E s≤K :=
      (setIntegral_mono_set hf.1.integrable_hsNormSq
        (Eventually.of_forall fun _ => hsNormSq_nonneg _)
        (Eventually.of_forall fun _ hx => hx.2)).trans hEnergy
    by_cases hZero : ν=0
    · have H : E r≤C*K := (hFull r).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hOneC hK)
      simpa only [hZero,Real.rpow_zero,mul_one,E] using H
    by_cases hrLarge : 1/4≤r
    · have hP : 1≤(4 : ℝ)^ν*r^ν := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ)≤4) hr.le]
        simpa only [Real.one_rpow] using
          Real.rpow_le_rpow (by norm_num : (0 : ℝ)≤1) (by linarith : (1 : ℝ)≤4*r) hν
      calc
        _ ≤ K := hFull r
        _ = K*1 := (mul_one K).symm
        _ ≤ K*((4 : ℝ)^ν*r^ν) := mul_le_mul_of_nonneg_left hP hK
        _ = (4 : ℝ)^ν*K*r^ν := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hFourC hK) (Real.rpow_nonneg hr.le ν)
    have hrQuarter : r≤1/4 := (not_le.mp hrLarge).le
    by_cases haHalf : a∈Metric.ball (0 : Domain n) (1/2 : ℝ)
    · have hB : Metric.ball a r⊆U := by
        intro x hx
        have H := dist_triangle x a (0 : Domain n)
        have Hx := Metric.mem_ball.mp hx
        have Ha := Metric.mem_ball.mp haHalf
        exact Metric.mem_ball.mpr (by linarith)
      have hSub : E r≤∫ x in Metric.ball a r,hsNormSq (Df x) :=
        setIntegral_mono_set (hf.1.integrable_hsNormSq.mono_set hB)
          (Eventually.of_forall fun _ => hsNormSq_nonneg _)
          (Eventually.of_forall fun _ hx => hx.1)
      have HG := hInterior q f Df F K hf.1 hF hK hGrowth hEnergy hEquation a haHalf r hr hrQuarter
      exact (hSub.trans HG).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCiC hK) (Real.rpow_nonneg hr.le _))
    have haNorm : ‖a‖<1 := by simpa only [U,Metric.mem_ball,dist_zero_right] using ha
    have haNormHalf : 1/2≤‖a‖ := by
      simpa only [Metric.mem_ball,dist_zero_right,not_lt] using haHalf
    obtain ⟨b,hb,hDist⟩ := exists_radial_unit_sphere_point a (by linarith) haNorm.le
    let t := (1-‖a‖)/2
    have ht : 0<t := by dsimp only [t];linarith
    have htQuarter : t≤1/4 := by dsimp only [t];linarith
    have hDistT : dist a b=2*t := by rw [hDist];dsimp only [t];ring
    have hQuerySub (s : ℝ) (hs : t≤s) : Metric.ball a s⊆Metric.ball b (3*s) := by
      intro x hx
      have H := dist_triangle x a b
      have Hx := Metric.mem_ball.mp hx
      rw [hDistT] at H
      exact Metric.mem_ball.mpr (by linarith)
    by_cases htr : t≤r
    · have hSub : (∫ x in Metric.ball a r∩U,hsNormSq (Df x))≤
          ∫ x in Metric.ball b (3*r)∩U,hsNormSq (Df x) :=
        setIntegral_mono_set (hf.1.integrable_hsNormSq.mono_set inter_subset_right)
          (Eventually.of_forall fun _ => hsNormSq_nonneg _)
          (Eventually.of_forall fun _ hx => ⟨hQuerySub r htr hx.1,hx.2⟩)
      have HB := hBoundary q f Df F K hf hF hK hGrowth hEnergy hEquation b hb (3*r)
        (by positivity) (by linarith only [hrQuarter])
      calc
        _ ≤ Cb*K*(3*r)^ν := hSub.trans HB
        _ = Cnear*K*r^ν := by rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤3) hr.le];dsimp only [Cnear];ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNearC hK) (Real.rpow_nonneg hr.le ν)
    have hrt : r≤t := (not_le.mp htr).le
    have hClosed (s : ℝ) (hs : s≤t) : Metric.closedBall a s⊆U := by
      intro x hx
      have H := dist_triangle x a (0 : Domain n)
      have Hx := Metric.mem_closedBall.mp hx
      simp only [dist_zero_right] at H
      apply Metric.mem_ball.mpr
      simp only [dist_zero_right]
      dsimp only [t] at hs
      linarith only [H,Hx,hs,haNorm]
    have hBall (s : ℝ) (hs : s≤t) : Metric.ball a s⊆U :=
      Metric.ball_subset_closedBall.trans (hClosed s hs)
    have hMono (s v : ℝ) (_hs : 0<s) (hsv : s≤v) (_hv : v≤t) : E s≤E v :=
      setIntegral_mono_set (hf.1.integrable_hsNormSq.mono_set inter_subset_right)
        (Eventually.of_forall fun _ => hsNormSq_nonneg _)
        (Eventually.of_forall fun _ hx => ⟨Metric.ball_subset_ball hsv hx.1,hx.2⟩)
    have hBase : E t≤(Cnear*K)*t^ν := by
      have hSub : E t≤∫ x in Metric.ball b (3*t)∩U,hsNormSq (Df x) :=
        setIntegral_mono_set (hf.1.integrable_hsNormSq.mono_set inter_subset_right)
          (Eventually.of_forall fun _ => hsNormSq_nonneg _)
          (Eventually.of_forall fun _ hx => ⟨hQuerySub t le_rfl hx.1,hx.2⟩)
      have HB := hBoundary q f Df F K hf hF hK hGrowth hEnergy hEquation b hb (3*t)
        (by positivity) (by linarith only [htQuarter])
      exact hSub.trans (HB.trans_eq (by rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤3) ht.le];dsimp only [Cnear];ring))
    have hStep (s : ℝ) (hs : 0<s) (hst : s≤t) : E (θ*s)≤ρ*E s+(2*K)*s^ν := by
      have hW : MemW12 (ballDomain a s) f Df := hf.1.to_memW12Loc.memW12_ball (hClosed s hst)
      have hFL (i : Fin n) : MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a s)) :=
        (hF i).mono_measure (Measure.restrict_mono_set volume (hBall s hst))
      have HD := linear_flux_dirichlet_energy_decay_ball hn a ⟨s,hs⟩ f Df F hW hFL
        (hEquation.mono (hBall s hst)) hθ hθHalf
      have HFN := hGrowth a ha s hs
      rw [inter_eq_left.mpr (hBall s hst)] at HFN
      have hSmall : Metric.ball a (θ*s)⊆U := hBall (θ*s) (by nlinarith only [hθHalf,hs,hst])
      change (∫ x in Metric.ball a (θ*s)∩U,hsNormSq (Df x))≤_
      rw [inter_eq_left.mpr hSmall]
      change _≤ρ*(∫ x in Metric.ball a s∩U,hsNormSq (Df x))+(2*K)*s^ν
      rw [inter_eq_left.mpr (hBall s hst)]
      exact HD.trans ((add_le_add le_rfl (mul_le_mul_of_nonneg_left HFN (by norm_num))).trans_eq (by ring))
    have H := all_radius_rpow_bound_of_recurrence E hν hθ hθOne hρ hgap
      (show 0≤2*K by positivity) (show 0≤Cnear*K by positivity) ht hMono hBase hStep r hr hrt
    have hForm : ((Cnear*K+(2*K)/(θ^ν-ρ))/θ^ν)=Citer*K := by dsimp only [Citer];ring
    rw [hForm] at H
    exact H.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hIterC hK) (Real.rpow_nonneg hr.le ν))
  exact hAll

end StationaryHarmonicMaps.Analysis
end

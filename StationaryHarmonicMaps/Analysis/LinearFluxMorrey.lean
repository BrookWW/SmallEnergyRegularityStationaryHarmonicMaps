module

public import StationaryHarmonicMaps.Analysis.GeometricPowerIteration
public import StationaryHarmonicMaps.Analysis.LinearFluxEnergyDecay
public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds
public import HolderToCK.Analysis.WeakPoissonLocality
public import HarmonicMaps.SobolevRestriction

/-! # Interior critical Morrey control for actual linear flux solutions

The original native gradient solves div(DV+F)=0. The actual complete
critical bound of F and the proved forcing-response energy decay control
the same DV on interior balls. This is a linear estimate.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

private theorem quarter_closedBall_subset_unitBall {n : ℕ} {a : Domain n} {r : ℝ}
    (ha : a∈Metric.ball (0 : Domain n) (1/2 : ℝ)) (hr : r≤1/4) :
    Metric.closedBall a r⊆Metric.ball (0 : Domain n) 1 := by
  intro x hx
  have H := dist_triangle x a (0 : Domain n)
  have hxR := Metric.mem_closedBall.mp hx
  have haR := Metric.mem_ball.mp ha
  exact Metric.mem_ball.mpr (by linarith)

/-- Dimension-only, all-center critical energy growth for the original linear gradient. -/
theorem exists_linear_flux_interior_energy_growth (n : ℕ) (hn : 2≤n) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (V : Domain n → Ambient q)
      (DV F : Domain n → Gradient n q) (K : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) V DV →
      (∀ i,MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) →
      0≤K → criticalGradientMorreySquare F (Metric.ball (0 : Domain n) 1)≤ENNReal.ofReal K →
      HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1)
        (fun x i => DV x i+F x i) (fun _ => (0 : Ambient q)) →
      ∀ (a : Domain n) (r : ℝ), a∈Metric.ball (0 : Domain n) (1/2 : ℝ) →
        0<r → r≤1/4 →
        (∫ x in Metric.ball a r,hsNormSq (DV x))≤
          C*((∫ x in Metric.ball (0 : Domain n) 1,hsNormSq (DV x))+K)*r^(n-2) := by
  let d := n-2
  have hdCast : (d : ℝ)=(n : ℝ)-2 := by dsimp only [d]; exact Nat.cast_sub hn
  obtain ⟨θ,hθ,hθHalf,hScale⟩ := exists_scale_absorbing_higher_power
    (C := 2*(2 : ℝ)^n) (p := (n : ℝ)) (β := (d : ℝ))
    (by positivity) (by rw [hdCast]; linarith)
  have hθOne : θ<1 := by linarith
  have hScaleN : 2*(2 : ℝ)^n*θ^n≤(1/2 : ℝ)*θ^d := by
    simpa only [Real.rpow_natCast] using hScale
  let ρ := 2*(2 : ℝ)^n*θ^n
  have hρ : 0≤ρ := by dsimp only [ρ]; positivity
  have hgap : ρ<θ^d := lt_of_le_of_lt hScaleN (by nlinarith only [pow_pos hθ d])
  let C₀ := ((4 : ℝ)^d+2/(θ^d-ρ))/θ^d
  let C := 1+C₀
  have hC₀ : 0≤C₀ := by dsimp only [C₀]; positivity
  have hC : 0<C := by dsimp only [C]; positivity
  have hOneC : 1≤C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro q V DV F K hV hF hK hCritical hEquation a r ha hr hrQuarter
  let E₀ := ∫ x in Metric.ball (0 : Domain n) 1,hsNormSq (DV x)
  let H := E₀+K
  have hE₀ : 0≤E₀ := integral_nonneg fun _ => hsNormSq_nonneg _
  have hH : 0≤H := add_nonneg hE₀ hK
  have hBall (s : ℝ) (hs : s≤1/4) : Metric.ball a s⊆Metric.ball (0 : Domain n) 1 :=
    Metric.ball_subset_closedBall.trans (quarter_closedBall_subset_unitBall ha hs)
  have hMono (s t : ℝ) (_hs : 0<s) (hst : s≤t) (ht : t≤1/4) :
      (∫ x in Metric.ball a s,hsNormSq (DV x))≤∫ x in Metric.ball a t,hsNormSq (DV x) :=
    setIntegral_mono_set (hV.integrable_hsNormSq.mono_set (hBall t ht))
      (Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Eventually.of_forall fun _ hx => Metric.ball_subset_ball hst hx)
  have hFull (s : ℝ) (hs : s≤1/4) :
      (∫ x in Metric.ball a s,hsNormSq (DV x))≤E₀ :=
    setIntegral_mono_set hV.integrable_hsNormSq
      (Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Eventually.of_forall fun _ hx => hBall s hs hx)
  by_cases hnTwo : n=2
  · have hCFull : E₀≤C*H := by
      calc
        E₀≤H := le_add_of_nonneg_right hK
        _ = 1*H := (one_mul H).symm
        _ ≤ C*H := mul_le_mul_of_nonneg_right hOneC hH
    simpa only [hnTwo,Nat.sub_self,pow_zero,mul_one] using (hFull r hrQuarter).trans hCFull
  · have hStep (s : ℝ) (hs : 0<s) (hsQ : s≤1/4) :
        (∫ x in Metric.ball a (θ*s),hsNormSq (DV x))≤
          ρ*(∫ x in Metric.ball a s,hsNormSq (DV x))+(2*H)*s^d := by
      have hW : MemW12 (ballDomain a s) V DV :=
        hV.to_memW12Loc.memW12_ball (quarter_closedBall_subset_unitBall ha hsQ)
      have hFL (i : Fin n) : MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a s)) :=
        (hF i).mono_measure (Measure.restrict_mono_set volume (hBall s hsQ))
      have hDecay := linear_flux_dirichlet_energy_decay_ball hn a ⟨s,hs⟩ V DV F hW hFL
        (hEquation.mono (hBall s hsQ)) hθ hθHalf
      have hForce := integral_hsNormSq_le_of_criticalMorrey F
        (hBall s hsQ (Metric.mem_ball_self hs)) hs hK
        (subset_inter (Subset.refl _) (hBall s hsQ)) hFL hCritical
      have hForceN : (∫ x in Metric.ball a s,hsNormSq (F x))≤K*s^d := by
        simpa only [← hdCast,Real.rpow_natCast] using hForce
      calc
        _ ≤ ρ*(∫ x in Metric.ball a s,hsNormSq (DV x))+
            2*(∫ x in Metric.ball a s,hsNormSq (F x)) := hDecay
        _ ≤ ρ*(∫ x in Metric.ball a s,hsNormSq (DV x))+2*(K*s^d) := by
          gcongr
        _ ≤ ρ*(∫ x in Metric.ball a s,hsNormSq (DV x))+(2*H)*s^d := by
          have hKH : K≤H := le_add_of_nonneg_left hE₀
          nlinarith only [mul_le_mul_of_nonneg_right hKH (pow_nonneg hs.le d)]
    have hBase : (∫ x in Metric.ball a (1/4 : ℝ),hsNormSq (DV x))≤
        ((4 : ℝ)^d*H)*(1/4 : ℝ)^d := by
      have hP : (4 : ℝ)^d*(1/4 : ℝ)^d=1 := by rw [← mul_pow]; norm_num
      calc
        _ ≤ E₀ := hFull _ le_rfl
        _ ≤ H := le_add_of_nonneg_right hK
        _ = _ := by rw [mul_right_comm _ H,hP,one_mul]
    have hGrowth := all_radius_power_bound_of_recurrence
      (fun s => ∫ x in Metric.ball a s,hsNormSq (DV x)) d hθ hθOne hρ hgap
      (show 0≤2*H by positivity) (show 0≤(4 : ℝ)^d*H by positivity)
      (by norm_num : (0 : ℝ)<1/4) hMono hBase hStep r hr hrQuarter
    have hForm : (((4 : ℝ)^d*H+(2*H)/(θ^d-ρ))/θ^d)=C₀*H := by
      dsimp only [C₀]; ring
    rw [hForm] at hGrowth
    exact hGrowth.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show C₀≤C by dsimp only [C]; linarith) hH)
      (pow_nonneg hr.le d))

/-- The same linear gradient has a genuine complete truncated critical supremum bound on the quarter ball. -/
theorem exists_linear_flux_interior_criticalMorrey_bound (n : ℕ) (hn : 2≤n) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (V : Domain n → Ambient q)
      (DV F : Domain n → Gradient n q) (K : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) V DV →
      (∀ i,MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) →
      0≤K → criticalGradientMorreySquare F (Metric.ball (0 : Domain n) 1)≤ENNReal.ofReal K →
      HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1)
        (fun x i => DV x i+F x i) (fun _ => (0 : Ambient q)) →
      criticalGradientMorreySquare DV (Metric.ball (0 : Domain n) (1/4 : ℝ))≤
        ENNReal.ofReal (C*((∫ x in Metric.ball (0 : Domain n) 1,hsNormSq (DV x))+K)) := by
  obtain ⟨C₀,hC₀,hGrowth⟩ := exists_linear_flux_interior_energy_growth n hn
  let C := C₀+(4 : ℝ)^(n-2)
  have hC : 0<C := by dsimp only [C]; positivity
  have hC₀C : C₀≤C := le_add_of_nonneg_right (by positivity)
  have hFourC : (4 : ℝ)^(n-2)≤C := le_add_of_nonneg_left hC₀.le
  refine ⟨C,hC,?_⟩
  intro q V DV F K hV hF hK hCritical hEquation
  let E₀ := ∫ x in Metric.ball (0 : Domain n) 1,hsNormSq (DV x)
  let H := E₀+K
  have hE₀ : 0≤E₀ := integral_nonneg fun _ => hsNormSq_nonneg _
  have hH : 0≤H := add_nonneg hE₀ hK
  have hdCast : ((n-2 : ℕ) : ℝ)=(n : ℝ)-2 := Nat.cast_sub hn
  unfold criticalGradientMorreySquare
  refine iSup_le fun a => iSup_le fun r => ?_
  let S := Metric.ball a.val r.val∩Metric.ball (0 : Domain n) (1/4 : ℝ)
  have hSB : S⊆Metric.ball (0 : Domain n) 1 :=
    inter_subset_right.trans (Metric.ball_subset_ball (by norm_num))
  have hSI : IntegrableOn (fun x => hsNormSq (DV x)) S volume :=
    hV.integrable_hsNormSq.mono_set hSB
  have hBound : (∫ x in S,hsNormSq (DV x))≤C*H*r.val^(n-2) := by
    by_cases hrSmall : r.val≤1/4
    · have haHalf : a.val∈Metric.ball (0 : Domain n) (1/2 : ℝ) :=
        Metric.ball_subset_ball (by norm_num : (1/4 : ℝ)≤1/2) a.property
      have hBall := Metric.ball_subset_closedBall.trans (quarter_closedBall_subset_unitBall haHalf hrSmall)
      have hSub : (∫ x in S,hsNormSq (DV x))≤∫ x in Metric.ball a.val r.val,hsNormSq (DV x) :=
        setIntegral_mono_set (hV.integrable_hsNormSq.mono_set hBall)
          (Eventually.of_forall fun _ => hsNormSq_nonneg _)
          (Eventually.of_forall fun _ hx => hx.1)
      exact hSub.trans ((hGrowth q V DV F K hV hF hK hCritical hEquation a.val r.val
        haHalf r.property hrSmall).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC₀C hH) (pow_nonneg r.property.le _)))
    · have hrLarge : 1/4≤r.val := (lt_of_not_ge hrSmall).le
      have hFactor : 1≤(4 : ℝ)^(n-2)*r.val^(n-2) := by
        rw [← mul_pow]
        exact (pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤1)
          (by linarith : (1 : ℝ)≤4*r.val) (n-2)).trans' (by simp)
      have hFull : (∫ x in S,hsNormSq (DV x))≤E₀ :=
        setIntegral_mono_set hV.integrable_hsNormSq
          (Eventually.of_forall fun _ => hsNormSq_nonneg _)
          (Eventually.of_forall fun _ hx => hSB hx)
      calc
        _ ≤ E₀ := hFull
        _ ≤ H := le_add_of_nonneg_right hK
        _ = H*1 := (mul_one H).symm
        _ ≤ H*((4 : ℝ)^(n-2)*r.val^(n-2)) := mul_le_mul_of_nonneg_left hFactor hH
        _ = (4 : ℝ)^(n-2)*H*r.val^(n-2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hFourC hH) (pow_nonneg r.property.le _)
  have hCancel : r.val^(n-2)*r.val^(2-(n : ℤ))=1 := by
    rw [← Real.rpow_natCast,hdCast,← Real.rpow_intCast,Int.cast_sub,
      Int.cast_ofNat,Int.cast_natCast,← Real.rpow_add r.property]
    norm_num
  change ENNReal.ofReal (r.val^(2-(n : ℤ)))*dirichletEnergy DV S≤_
  rw [dirichletEnergy_eq_ofReal_integral hSI]
  calc
    _ ≤ ENNReal.ofReal (r.val^(2-(n : ℤ)))*ENNReal.ofReal (C*H*r.val^(n-2)) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal hBound) _
    _ = ENNReal.ofReal (C*H) := by
      rw [← ENNReal.ofReal_mul (zpow_nonneg r.property.le _)]
      congr 1
      calc
        _ = C*H*(r.val^(n-2)*r.val^(2-(n : ℤ))) := by ring
        _ = _ := by rw [hCancel,mul_one]

end StationaryHarmonicMaps.Analysis
end

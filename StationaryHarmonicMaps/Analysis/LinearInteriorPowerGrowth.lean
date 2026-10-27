module

public import StationaryHarmonicMaps.Analysis.GeometricRpowIteration
public import StationaryHarmonicMaps.Analysis.LinearFluxEnergyDecay
public import StationaryHarmonicMaps.Analysis.UniformPowerGrowthBounds
public import HolderToCK.Analysis.WeakPoissonLocality
public import HarmonicMaps.SobolevRestriction

/-! # Actual interior linear growth for every nonnegative subdimensional power

Original L2 forcing with all-center truncated power growth and the genuine
forcing-response decay control the same native solution. Constants are
selected before target dimensions and original fields.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

/-- The original linear gradient has interior energy growth at every real exponent between zero and the source dimension. -/
theorem exists_linear_flux_interior_real_power_growth (n : ℕ) (hn : 2≤n)
    (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (f : Domain n → Ambient q)
      (Df F : Domain n → Gradient n q) (K : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) f Df →
      (∀ i,MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) →
      0≤K →
      (∀ (a : Domain n),a∈Metric.ball (0 : Domain n) 1 → ∀ r : ℝ,0<r →
        (∫ x in Metric.ball a r∩Metric.ball (0 : Domain n) 1,hsNormSq (F x))≤K*r^ν) →
      (∫ x in Metric.ball (0 : Domain n) 1,hsNormSq (Df x))≤K →
      HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1)
        (fun x i => Df x i+F x i) (fun _ => (0 : Ambient q)) →
      ∀ (a : Domain n),a∈Metric.ball (0 : Domain n) (1/2 : ℝ) →
        ∀ r : ℝ,0<r → r≤1/4 → (∫ x in Metric.ball a r,hsNormSq (Df x))≤C*K*r^ν := by
  obtain ⟨θ,hθ,hθHalf,hScale⟩ := exists_scale_absorbing_higher_power
    (C := 2*(2 : ℝ)^n) (p := (n : ℝ)) (β := ν) (by positivity) hνn
  have hθOne : θ<1 := by linarith
  have hScaleN : 2*(2 : ℝ)^n*θ^n≤(1/2 : ℝ)*θ^ν := by
    simpa only [Real.rpow_natCast] using hScale
  let ρ := 2*(2 : ℝ)^n*θ^n
  have hρ : 0≤ρ := by dsimp only [ρ];positivity
  have hgap : ρ<θ^ν := lt_of_le_of_lt hScaleN (by nlinarith only [Real.rpow_pos_of_pos hθ ν])
  let C₀ := ((4 : ℝ)^ν+2/(θ^ν-ρ))/θ^ν
  let C := 1+C₀
  have hC₀ : 0≤C₀ := by dsimp only [C₀];positivity
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro q f Df F K hf hF hK hGrowth hEnergy hEquation a ha r hr hrQuarter
  have hClosed (s : ℝ) (hs : s≤1/4) : Metric.closedBall a s⊆Metric.ball (0 : Domain n) 1 := by
    intro x hx
    have H := dist_triangle x a (0 : Domain n)
    have Hx := Metric.mem_closedBall.mp hx
    have Ha := Metric.mem_ball.mp ha
    exact Metric.mem_ball.mpr (by linarith)
  have hBall (s : ℝ) (hs : s≤1/4) : Metric.ball a s⊆Metric.ball (0 : Domain n) 1 :=
    Metric.ball_subset_closedBall.trans (hClosed s hs)
  let E := fun s : ℝ => ∫ x in Metric.ball a s,hsNormSq (Df x)
  have hMono (s t : ℝ) (_hs : 0<s) (hst : s≤t) (ht : t≤1/4) : E s≤E t :=
    setIntegral_mono_set (hf.integrable_hsNormSq.mono_set (hBall t ht))
      (Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Eventually.of_forall fun _ hx => Metric.ball_subset_ball hst hx)
  have hFull : E (1/4)≤K :=
    (setIntegral_mono_set hf.integrable_hsNormSq
      (Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Eventually.of_forall fun _ hx => hBall (1/4) le_rfl hx)).trans hEnergy
  have hBase : E (1/4)≤((4 : ℝ)^ν*K)*(1/4 : ℝ)^ν := by
    have hP : (4 : ℝ)^ν*(1/4 : ℝ)^ν=1 := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ)≤4) (by norm_num : (0 : ℝ)≤1/4)]
      norm_num
    exact hFull.trans_eq (by rw [mul_right_comm _ K,hP,one_mul])
  have hStep (s : ℝ) (hs : 0<s) (hsQ : s≤1/4) : E (θ*s)≤ρ*E s+(2*K)*s^ν := by
    have hW := hf.to_memW12Loc.memW12_ball (hClosed s hsQ)
    have hFL (i : Fin n) : MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a s)) :=
      (hF i).mono_measure (Measure.restrict_mono_set volume (hBall s hsQ))
    have HD := linear_flux_dirichlet_energy_decay_ball hn a ⟨s,hs⟩ f Df F hW hFL
      (hEquation.mono (hBall s hsQ)) hθ hθHalf
    have HF := hGrowth a (hBall s hsQ (Metric.mem_ball_self hs)) s hs
    rw [inter_eq_left.mpr (hBall s hsQ)] at HF
    exact HD.trans ((add_le_add le_rfl (mul_le_mul_of_nonneg_left HF (by norm_num))).trans_eq (by ring))
  have H := all_radius_rpow_bound_of_recurrence E hν hθ hθOne hρ hgap
    (show 0≤2*K by positivity) (show 0≤(4 : ℝ)^ν*K by positivity)
    (by norm_num : (0 : ℝ)<1/4) hMono hBase hStep r hr hrQuarter
  have hForm : (((4 : ℝ)^ν*K+(2*K)/(θ^ν-ρ))/θ^ν)=C₀*K := by dsimp only [C₀];ring
  rw [hForm] at H
  exact H.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (show C₀≤C by dsimp only [C];linarith) hK) (Real.rpow_nonneg hr.le _))

end StationaryHarmonicMaps.Analysis
end

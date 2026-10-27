module

public import StationaryHarmonicMaps.Analysis.BoundaryCriticalEvenMorrey
public import StationaryHarmonicMaps.Analysis.CutoffGlobalMeanOscillation
public import StationaryHarmonicMaps.Analysis.AffineMeanOscillation

/-!
# Whole-space scalar BMO observables of the original boundary graph

Even inversion extends the same critical native graph to the double ball.
A fixed cutoff of its rescaling and exact dilation of ball averages give
whole-space scalar mean-oscillation bounds agreeing with the original
centered map throughout the unit ball.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set Metric
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The original critical Sobolev graph has scalar whole-space extensions
which agree on the entire source ball, with one common centering vector. -/
theorem exists_boundary_critical_scalar_mean_oscillation_extension (n : ℕ) (hn : 2≤n) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∃ c : Ambient q,∀ L : Ambient q →L[ℝ] ℝ,∃ b : Domain n → ℝ,
        AEStronglyMeasurable b volume ∧
        (∀ x∈ball (0 : Domain n) 1,b x=L (u x-c)) ∧
        ∀ (a : Domain n) (r : ℝ),0<r →
          IntegrableOn b (ball a r) volume ∧
          (⨍ x in ball a r,|b x-(⨍ y in ball a r,b y)|)≤C*‖L‖*η := by
  let χ : ContDiffBump (0 : Domain n) := ⟨1/2,3/4,by norm_num,by norm_num⟩
  have hχ : ContDiff ℝ ∞ (χ : Domain n → ℝ) := χ.contDiff
  obtain ⟨B,hB⟩ := (χ.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hχ.continuous_fderiv (by simp))
  have hDχ (x : Domain n) (i : Fin n) :
      |fderiv ℝ (χ : Domain n → ℝ) x (EuclideanSpace.single i 1)|≤|B| := by
    calc
      _≤‖fderiv ℝ (χ : Domain n → ℝ) x‖*‖EuclideanSpace.single i (1 : ℝ)‖ :=
        (fderiv ℝ (χ : Domain n → ℝ) x).le_opNorm _
      _=‖fderiv ℝ (χ : Domain n → ℝ) x‖ := by simp only [PiLp.norm_single,norm_one,mul_one]
      _≤|B| := (hB x).trans (le_abs_self B)
  obtain ⟨D,hD,Hcut⟩ := exists_cutoff_global_scalar_mean_oscillation_bound n hn 1 |B|
    (by norm_num) (abs_nonneg B)
  let K := (2 : ℝ)^((n : ℝ)-2)*(1+(2 : ℝ)^(2*n))
  have hK : 0<K := by dsimp only [K];positivity
  refine ⟨D*Real.sqrt K,mul_pos hD (Real.sqrt_pos.mpr hK),?_⟩
  intro q u Du η hu hη hCritical
  let I := inversion (0 : Domain n) 1
  let U := fun x=>if ‖x‖≤1 then u x else u (I x)
  let DU := fun x i=>if ‖x‖≤1 then Du x i else
    ∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • Du (I x) j
  have hU : MemW12 (ballDomain (0 : Domain n) 2) U DU :=
    memW12_even_inversion_extension_ball_two hn u Du hu
  let v := fun x=>U ((2 : ℝ) • x)
  let Dv := fun x i=>(2 : ℝ) • DU ((2 : ℝ) • x) i
  have hv : MemW12 (ballDomain (0 : Domain n) 1) v Dv := by
    simpa only [ballAffine,sub_zero,add_zero,zero_add,div_self (by norm_num : (2 : ℝ)≠0)] using
      hU.affinePullback_ball (t:=2) (by norm_num)
  have hDUCritical : criticalGradientMorreySquare DU (ball (0 : Domain n) 2)≤
      ENNReal.ofReal (K*η^2) := even_inversion_criticalMorrey_bound_unitBall hn u Du hu
        (η^2) (sq_nonneg η) hCritical
  have hDvCritical : criticalGradientMorreySquare Dv (ball (0 : Domain n) 1)≤
      ENNReal.ofReal ((Real.sqrt K*η)^2) := by
    have hScale := criticalGradientMorreySquare_unitBall (0 : Domain n) ⟨2,by norm_num⟩ DU
    have hSquare : (Real.sqrt K*η)^2=K*η^2 := by rw [mul_pow,Real.sq_sqrt hK.le]
    rw [hSquare]
    exact (show criticalGradientMorreySquare Dv (ball (0 : Domain n) 1)=
      criticalGradientMorreySquare DU (ball (0 : Domain n) 2) from by
        simpa only [zero_add] using hScale).le.trans hDUCritical
  let c := ⨍ x in ball (0 : Domain n) 1,v x
  refine ⟨c,?_⟩
  intro L
  let b₀ := fun x=>L (χ x • (v x-c))
  let b := fun x=>b₀ ((1/2 : ℝ) • x)
  obtain ⟨hb₀,_hInside,hBMO⟩ := Hcut q v Dv (Real.sqrt K*η) hv
    (mul_nonneg (Real.sqrt_nonneg K) hη) hDvCritical χ χ.contDiff χ.hasCompactSupport
    (by rw [χ.tsupport_eq]) (fun x=>by rw [abs_of_nonneg χ.nonneg];exact χ.le_one) hDχ L
  have hb : AEStronglyMeasurable b volume := hb₀.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_smul volume (by norm_num : (1/2 : ℝ)≠0))
  refine ⟨b,hb,?_,?_⟩
  · intro x hx
    have hxNorm : ‖x‖<1 := by simpa only [mem_ball,dist_zero_right] using hx
    have hHalf : (1/2 : ℝ) • x∈closedBall (0 : Domain n) (1/2 : ℝ) := by
      rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      linarith only [hxNorm]
    change L (χ ((1/2 : ℝ) • x) • (U ((2 : ℝ) • ((1/2 : ℝ) • x))-c))=L (u x-c)
    rw [χ.one_of_mem_closedBall hHalf,one_smul,smul_smul]
    norm_num only [show (2 : ℝ)*(1/2)=1 by norm_num,one_smul]
    rw [show U x=u x from if_pos hxNorm.le]
  · intro a r hr
    have H := meanOscillation_dilation_bound b₀ (D*‖L‖*(Real.sqrt K*η)) hBMO
      (t:=1/2) (by norm_num) a r hr
    exact ⟨H.1,H.2.trans_eq (by ring)⟩

end StationaryHarmonicMaps.Analysis

end

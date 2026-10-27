module

public import StationaryHarmonicMaps.Analysis.BoundaryCriticalEvenMorrey
public import StationaryHarmonicMaps.Analysis.CutoffGlobalMeanOscillation
public import StationaryHarmonicMaps.Analysis.AffineMeanOscillation
public import StationaryHarmonicMaps.Analysis.EffectiveBallCutoff

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

/-- The integer reflection factor for the critical native gradient square. -/
@[expose] def effectiveBoundaryReflectionFactor (n : ℕ) : ℕ :=
  2^(n-2)*(1+2^(2*n))

theorem effectiveBoundaryReflectionFactor_cast (n : ℕ) (hn : 2≤n) :
    (effectiveBoundaryReflectionFactor n : ℝ)=
      (2 : ℝ)^((n : ℝ)-2)*(1+(2 : ℝ)^(2*n)) := by
  have hN : (n : ℝ)-2=((n-2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn]
    norm_num
  rw [hN, Real.rpow_natCast]
  unfold effectiveBoundaryReflectionFactor
  push_cast
  rfl

theorem sqrt_boundary_reflection_factor_le (n : ℕ) (hn : 2≤n) :
    Real.sqrt ((2 : ℝ)^((n : ℝ)-2)*(1+(2 : ℝ)^(2*n))) ≤
      ((1+effectiveBoundaryReflectionFactor n : ℕ) : ℝ) := by
  rw [← effectiveBoundaryReflectionFactor_cast n hn, Nat.cast_add, Nat.cast_one]
  apply (Real.sqrt_le_left (by positivity : (0 : ℝ)≤1+effectiveBoundaryReflectionFactor n)).mpr
  have hK : (0 : ℝ)≤effectiveBoundaryReflectionFactor n := Nat.cast_nonneg _
  nlinarith only [hK, sq_nonneg (effectiveBoundaryReflectionFactor n : ℝ)]

/-- A computable integer bound for the native boundary scalar extension. -/
@[expose] def effectiveBoundaryCriticalMeanConstant (n : ℕ) : ℕ :=
  effectiveCutoffGlobalMeanConstant n 1 (2^23) *
    (1+effectiveBoundaryReflectionFactor n)

theorem effectiveBoundaryCriticalMeanConstant_pos (n : ℕ) :
    0<(effectiveBoundaryCriticalMeanConstant n : ℝ) := by
  have hD := effectiveCutoffGlobalMeanConstant_pos n 1 (2^23)
  simp only [effectiveBoundaryCriticalMeanConstant, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  positivity

/-- The original critical Sobolev graph has scalar whole-space extensions
which agree on the entire source ball, with an explicit integer bound. -/
theorem effective_boundary_critical_scalar_mean_oscillation_extension (n : ℕ) (hn : 2≤n) :
    ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∃ c : Ambient q,∀ L : Ambient q →L[ℝ] ℝ,∃ b : Domain n → ℝ,
        AEStronglyMeasurable b volume ∧
        (∀ x∈ball (0 : Domain n) 1,b x=L (u x-c)) ∧
        ∀ (a : Domain n) (r : ℝ),0<r →
          IntegrableOn b (ball a r) volume ∧
          (⨍ x in ball a r,|b x-(⨍ y in ball a r,b y)|)≤
            (effectiveBoundaryCriticalMeanConstant n : ℝ)*‖L‖*η := by
  let χ : Domain n → ℝ := effectiveRadialCutoff (1/2) (3/4)
  have hχ : ContDiff ℝ ∞ χ := effectiveRadialCutoff_contDiff _ _
  have hcχ : HasCompactSupport χ :=
    effectiveRadialCutoff_hasCompactSupport (by norm_num) (by norm_num)
  have hDχNorm (x : Domain n) : ‖fderiv ℝ χ x‖ ≤ (2 : ℝ)^23 := by
    calc
      _ ≤ 2*(3/4 : ℝ)*(2 : ℝ)^20/((3/4 : ℝ)^2-(1/2 : ℝ)^2) :=
        effectiveRadialCutoff_fderiv_bound (by norm_num) (by norm_num) x
      _ ≤ (2 : ℝ)^23 := by norm_num
  have hDχ (x : Domain n) (i : Fin n) :
      |fderiv ℝ χ x (EuclideanSpace.single i 1)|≤(2 : ℝ)^23 := by
    calc
      _≤‖fderiv ℝ (χ : Domain n → ℝ) x‖*‖EuclideanSpace.single i (1 : ℝ)‖ :=
        (fderiv ℝ (χ : Domain n → ℝ) x).le_opNorm _
      _=‖fderiv ℝ (χ : Domain n → ℝ) x‖ := by simp only [PiLp.norm_single,norm_one,mul_one]
      _≤(2 : ℝ)^23 := hDχNorm x
  let D : ℝ := effectiveCutoffGlobalMeanConstant n 1 (2^23)
  have hD : 0<D := effectiveCutoffGlobalMeanConstant_pos n 1 (2^23)
  have Hcut := effective_cutoff_global_scalar_mean_oscillation_bound n hn 1 (2^23)
  let K := (2 : ℝ)^((n : ℝ)-2)*(1+(2 : ℝ)^(2*n))
  have hK : 0<K := by dsimp only [K];positivity
  have hMajor : D*Real.sqrt K≤(effectiveBoundaryCriticalMeanConstant n : ℝ) := by
    calc
      _≤D*((1+effectiveBoundaryReflectionFactor n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (sqrt_boundary_reflection_factor_le n hn) hD.le
      _=(effectiveBoundaryCriticalMeanConstant n : ℝ) := by
        simp only [effectiveBoundaryCriticalMeanConstant, Nat.cast_mul, D]
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
    (mul_nonneg (Real.sqrt_nonneg K) hη) hDvCritical χ hχ hcχ
    (effectiveRadialCutoff_tsupport_subset (by norm_num) (by norm_num))
    (fun x=>by
      have hval := effectiveRadialCutoff_mem_Icc (1/2) (3/4) x
      rw [abs_of_nonneg hval.1]
      simpa only [Nat.cast_one] using hval.2)
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hDχ) L
  have hb : AEStronglyMeasurable b volume := hb₀.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_smul volume (by norm_num : (1/2 : ℝ)≠0))
  refine ⟨b,hb,?_,?_⟩
  · intro x hx
    have hxNorm : ‖x‖<1 := by simpa only [mem_ball,dist_zero_right] using hx
    have hHalf : (1/2 : ℝ) • x∈closedBall (0 : Domain n) (1/2 : ℝ) := by
      rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      linarith only [hxNorm]
    change L (χ ((1/2 : ℝ) • x) • (U ((2 : ℝ) • ((1/2 : ℝ) • x))-c))=L (u x-c)
    have hχOne : χ ((1/2 : ℝ) • x)=1 :=
      effectiveRadialCutoff_eq_one (by norm_num) (by norm_num)
        (by simpa only [mem_closedBall,dist_zero_right] using hHalf)
    rw [hχOne,one_smul,smul_smul]
    norm_num only [show (2 : ℝ)*(1/2)=1 by norm_num,one_smul]
    rw [show U x=u x from if_pos hxNorm.le]
  · intro a r hr
    have H := meanOscillation_dilation_bound b₀ (D*‖L‖*(Real.sqrt K*η)) hBMO
      (t:=1/2) (by norm_num) a r hr
    refine ⟨H.1,H.2.trans ?_⟩
    calc
      D*‖L‖*(Real.sqrt K*η)=(D*Real.sqrt K)*‖L‖*η := by ring
      _≤(effectiveBoundaryCriticalMeanConstant n : ℝ)*‖L‖*η :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMajor (norm_nonneg L)) hη

/-- The boundary extension constant is exactly the displayed computable integer. -/
theorem exists_boundary_critical_scalar_mean_oscillation_extension_explicit
    (n : ℕ) (hn : 2≤n) :
    ∃ C : ℝ,0<C ∧ C=(effectiveBoundaryCriticalMeanConstant n : ℝ) ∧
      ∀ (q : ℕ) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ),
        MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
        criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
        ∃ c : Ambient q,∀ L : Ambient q →L[ℝ] ℝ,∃ b : Domain n → ℝ,
          AEStronglyMeasurable b volume ∧
          (∀ x∈ball (0 : Domain n) 1,b x=L (u x-c)) ∧
          ∀ (a : Domain n) (r : ℝ),0<r →
            IntegrableOn b (ball a r) volume ∧
            (⨍ x in ball a r,|b x-(⨍ y in ball a r,b y)|)≤C*‖L‖*η :=
  ⟨_,effectiveBoundaryCriticalMeanConstant_pos n,rfl,
    effective_boundary_critical_scalar_mean_oscillation_extension n hn⟩

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
  obtain ⟨C,hC,_hEq,H⟩ := exists_boundary_critical_scalar_mean_oscillation_extension_explicit n hn
  exact ⟨C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end

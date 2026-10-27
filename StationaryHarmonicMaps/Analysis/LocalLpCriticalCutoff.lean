module

public import StationaryHarmonicMaps.Analysis.LocalMeanOscillationCutoff
public import StationaryHarmonicMaps.Analysis.LpMorreyRepresentative
public import StationaryHarmonicMaps.Analysis.ScaledBallCutoff
public import StationaryHarmonicMaps.Analysis.SobolevCutoff
public import StationaryHarmonicMaps.Analysis.EffectiveEuclideanVolume
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# A genuine local critical Lp gradient bound supplies a global BMO cutoff

The original native graph restricts to each positive ball. Its actual
Lp HS growth gives the original local oscillation. One scaled smooth
profile then supplies the same centered cutoff on the reference ball,
with global scalar oscillation controlled by the original Lp amplitude.
-/

@[expose] public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

def effectiveLocalMeanOscillationCutoffConstant (n : ℕ) : ℕ :=
  2*(32^n+1+2^23*(2*2^n+2*4^n))

def effectiveLpMeanOscillationConstant (n : ℕ) : ℕ :=
  2^(n+1)*(n+1)*(1+(n+1)^n)

def effectiveLocalLpCriticalCutoffConstant (n : ℕ) : ℕ :=
  1+effectiveLocalMeanOscillationCutoffConstant n*effectiveLpMeanOscillationConstant n

theorem lpMeanOscillationFactor_le_effective (n : ℕ) (p : ℝ) (hp : 1≤p) :
    ((2:ℝ)^(n+1)*Real.sqrt (n:ℝ))*
      (volume.real (ball (0:Domain n) 1))^(-(1/p))≤
      (effectiveLpMeanOscillationConstant n:ℝ) := by
  have hp0 : 0<p := zero_lt_one.trans_le hp
  have hVolume := euclidean_unit_ball_inverse_rpow_le n (1/p) (by positivity)
    ((div_le_one hp0).mpr hp)
  have hRoot : Real.sqrt (n:ℝ)≤(n:ℝ)+1 := by
    apply (Real.sqrt_le_left (by positivity : 0≤(n:ℝ)+1)).mpr
    nlinarith only [sq_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) n]
  calc
    _≤((2:ℝ)^(n+1)*((n:ℝ)+1))*(1+((n:ℝ)+1)^n) := by gcongr
    _=(effectiveLpMeanOscillationConstant n:ℝ) := by unfold effectiveLpMeanOscillationConstant;push_cast;rfl

/-- Original all-center critical Lp growth up to the reference scale produces an actual supported smooth cutoff and the same centered observable's all-ball BMO bound. -/
theorem exists_local_lp_critical_cutoff_scalar_mean_oscillation_bound_explicit
    (n : ℕ) (p : ℝ) (hp₁ : 1≤p) (hp₂ : p≤2) :
    ∃ C : ℝ,0<C ∧ C=(effectiveLocalLpCriticalCutoffConstant n:ℝ) ∧ ∀ (q : ℕ) (a : Domain n) (t : ℝ),0<t →
      ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (K : ℝ),
        MemW12Loc (⟨univ,isOpen_univ⟩ : OpenDomain n) u Du → 0≤K →
        (∀ (x : Domain n) (r : ℝ),0<r → r≤8*t →
          (∫ y in Metric.ball x r,(Real.sqrt (hsNormSq (Du y)))^p)≤K^p*r^((n : ℝ)-p)) →
        ∃ χ : Domain n → ℝ,ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
          tsupport χ⊆Metric.ball a t ∧
          (∀ x∈Metric.closedBall a (t/2),χ x=1) ∧ (∀ x,0≤χ x ∧ χ x≤1) ∧
          ∀ L : Ambient q →L[ℝ] ℝ,
            let c := ⨍ y in Metric.ball a (8*t),u y
            let b := fun x=>L (χ x • (u x-c))
            AEStronglyMeasurable b volume ∧
              ∀ (x : Domain n) (r : ℝ),0<r → IntegrableOn b (Metric.ball x r) volume ∧
                (⨍ y in Metric.ball x r,|b y-(⨍ z in Metric.ball x r,b z)|)≤C*‖L‖*K := by
  obtain ⟨A,hA,hAEq,Hcut⟩ := exists_scaled_ball_cutoff_explicit n
  obtain ⟨T,hT,hTEq,Hosc⟩ := exists_local_mean_oscillation_cutoff_bound_explicit n (2*A) (by positivity)
  let D : ℝ := ((2 : ℝ)^(n+1)*Real.sqrt (n : ℝ))*
    (volume.real (Metric.ball (0 : Domain n) 1))^(-(1/p))
  let C : ℝ := (effectiveLocalLpCriticalCutoffConstant n:ℝ)
  have hD : 0≤D := by dsimp only [D];positivity
  have hTNat : T=(effectiveLocalMeanOscillationCutoffConstant n:ℝ) := by
    rw [hTEq,hAEq]
    dsimp only [localMeanOscillationCutoffConstant,effectiveLocalMeanOscillationCutoffConstant]
    push_cast
    norm_num
  have hDMajorant := lpMeanOscillationFactor_le_effective n p hp₁
  have hTC : T*D≤C := by
    calc
      _≤(effectiveLocalMeanOscillationCutoffConstant n:ℝ)*
          (effectiveLpMeanOscillationConstant n:ℝ) := by rw [hTNat];gcongr
      _≤C := by dsimp only [C,effectiveLocalLpCriticalCutoffConstant];push_cast;linarith
  have hC : 0<C := by dsimp only [C,effectiveLocalLpCriticalCutoffConstant];push_cast;positivity
  refine ⟨C,hC,rfl,?_⟩
  intro q a t ht u Du K hu hK hGrowth
  obtain ⟨χ,hχ,hcχ,hsχ,hOne,hBounds,hDχ⟩ := Hcut a (t/2) (half_pos ht)
  have hSupport : tsupport χ⊆Metric.ball a t := by simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ)≠0)] using hsχ
  have hDerivative (x : Domain n) : ‖fderiv ℝ χ x‖≤(2*A)/t := (hDχ x).trans_eq (by ring)
  have hWI (x : Domain n) (r : ℝ) : MemW12 (ballDomain x r) u Du := hu.memW12_ball (subset_univ _)
  have hUI (x : Domain n) (r : ℝ) (_hr : 0<r) : IntegrableOn u (Metric.ball x r) volume := by
    letI : IsFiniteMeasure (volume.restrict (Metric.ball x r)) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
    have hLp : MemLp u 2 (volume.restrict (Metric.ball x r)) := (hWI x r).2.1
    exact hLp.integrable (by norm_num)
  have hVectorOsc (x : Domain n) (r : ℝ) (hr : 0<r) (hScale : r≤8*t) :
      (⨍ y in Metric.ball x r,‖u y-(⨍ z in Metric.ball x r,u z)‖)≤D*K := by
    have hG : (∫ y in Metric.ball x r,(Real.sqrt (hsNormSq (Du y)))^p)≤
        K^p*r^((n : ℝ)-p+p*0) := by simpa only [mul_zero,add_zero] using hGrowth x r hr hScale
    have H := sobolev_meanOscillation_of_lp_growth (α:=0) x hr hp₁ hp₂ hK (hWI x r) hG
    simpa only [Real.rpow_zero,mul_one] using H
  refine ⟨χ,hχ,hcχ,hSupport,hOne,hBounds,?_⟩
  intro L c b
  let f := fun x=>L (u x)
  have hFI (x : Domain n) (r : ℝ) (hr : 0<r) : IntegrableOn f (Metric.ball x r) volume :=
    L.integrable_comp (hUI x r hr)
  have hMeans (x : Domain n) (r : ℝ) (hr : 0<r) :
      (⨍ z in Metric.ball x r,f z)=L (⨍ z in Metric.ball x r,u z) :=
    L.integral_comp_comm (hUI x r hr).to_average
  have hScalarOsc (x : Domain n) (r : ℝ) (hr : 0<r) (hScale : r≤8*t) :
      (⨍ y in Metric.ball x r,|f y-(⨍ z in Metric.ball x r,f z)|)≤(‖L‖*D)*K := by
    have hVecI : IntegrableOn (fun y=>‖u y-(⨍ z in Metric.ball x r,u z)‖) (Metric.ball x r) volume := by
      letI : IsFiniteMeasure (volume.restrict (Metric.ball x r)) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
      exact ((hUI x r hr).sub (integrable_const _)).norm
    have hScalarI : IntegrableOn (fun y=>|f y-(⨍ z in Metric.ball x r,f z)|) (Metric.ball x r) volume := by
      letI : IsFiniteMeasure (volume.restrict (Metric.ball x r)) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
      exact ((hFI x r hr).sub (integrable_const _)).abs
    calc
      _ ≤ ⨍ y in Metric.ball x r,‖L‖*‖u y-(⨍ z in Metric.ball x r,u z)‖ := by
        apply integral_mono hScalarI.to_average (hVecI.const_mul ‖L‖).to_average
        intro y
        dsimp only
        rw [hMeans x r hr]
        change |L (u y)-L (⨍ z in Metric.ball x r,u z)|≤_
        rw [← L.map_sub,← Real.norm_eq_abs]
        exact L.le_opNorm _
      _ = ‖L‖*(⨍ y in Metric.ball x r,‖u y-(⨍ z in Metric.ball x r,u z)‖) := integral_const_mul _ _
      _ ≤ ‖L‖*(D*K) := mul_le_mul_of_nonneg_left (hVectorOsc x r hr hScale) (norm_nonneg _)
      _ = _ := by ring
  have hActual := Hosc a t ht f ((‖L‖*D)*K) (by positivity) hFI hScalarOsc χ
    (hχ.of_le (by simp)) (subset_tsupport χ |>.trans hSupport)
    (fun x=>by rw [abs_of_nonneg (hBounds x).1];exact (hBounds x).2) hDerivative
  have hFormula : b=(fun x=>χ x*(f x-(⨍ z in Metric.ball a (8*t),f z))) := by
    funext x
    rw [hMeans a (8*t) (by positivity)]
    change L (χ x • (u x-c))=χ x*(L (u x)-L c)
    rw [L.map_smul,L.map_sub,smul_eq_mul]
  have hCutW := memW12_cutoff_sub_const_univ hu c χ hχ hcχ (subset_univ _)
  have hCutLp : MemLp (fun x=>χ x • (u x-c)) 2 volume := by
    have H := hCutW.2.1
    change MemLp _ 2 (volume.restrict univ) at H
    rwa [Measure.restrict_univ] at H
  refine ⟨L.continuous.comp_aestronglyMeasurable hCutLp.aestronglyMeasurable,?_⟩
  intro x r hr
  obtain ⟨hI,hBound⟩ := hActual x r hr
  rw [← hFormula] at hI hBound
  refine ⟨hI,hBound.trans ?_⟩
  calc
    T*((‖L‖*D)*K) = (T*D)*(‖L‖*K) := by ring
    _ ≤ C*(‖L‖*K) := mul_le_mul_of_nonneg_right hTC (mul_nonneg (norm_nonneg _) hK)
    _ = _ := by ring

theorem exists_local_lp_critical_cutoff_scalar_mean_oscillation_bound
    (n : ℕ) (p : ℝ) (hp₁ : 1≤p) (hp₂ : p≤2) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (a : Domain n) (t : ℝ),0<t →
      ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (K : ℝ),
        MemW12Loc (⟨univ,isOpen_univ⟩ : OpenDomain n) u Du → 0≤K →
        (∀ (x : Domain n) (r : ℝ),0<r → r≤8*t →
          (∫ y in Metric.ball x r,(Real.sqrt (hsNormSq (Du y)))^p)≤K^p*r^((n : ℝ)-p)) →
        ∃ χ : Domain n → ℝ,ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
          tsupport χ⊆Metric.ball a t ∧
          (∀ x∈Metric.closedBall a (t/2),χ x=1) ∧ (∀ x,0≤χ x ∧ χ x≤1) ∧
          ∀ L : Ambient q →L[ℝ] ℝ,
            let c := ⨍ y in Metric.ball a (8*t),u y
            let b := fun x=>L (χ x • (u x-c))
            AEStronglyMeasurable b volume ∧
              ∀ (x : Domain n) (r : ℝ),0<r → IntegrableOn b (Metric.ball x r) volume ∧
                (⨍ y in Metric.ball x r,|b y-(⨍ z in Metric.ball x r,b z)|)≤C*‖L‖*K := by
  obtain ⟨C,hC,_hCEq,H⟩ := exists_local_lp_critical_cutoff_scalar_mean_oscillation_bound_explicit n p hp₁ hp₂
  exact ⟨C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end

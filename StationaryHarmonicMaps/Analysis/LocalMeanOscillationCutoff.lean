module

public import StationaryHarmonicMaps.Analysis.LocalBallMeanChain
public import StationaryHarmonicMaps.Analysis.MeanOscillationContraction
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Global oscillation of an actual cutoff from original local oscillation

The original means on balls of radius at most eight times the reference
radius control the same supported product on every ball. Large balls use
the original outer-ball integral. Small balls use the actual damped mean
comparison and the original cutoff derivative bound.
-/

@[expose] public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

def localMeanOscillationCutoffConstant (n : ℕ) (D : ℝ) : ℝ :=
  2*((32:ℝ)^n+1+D*(2*(2:ℝ)^n+2*(4:ℝ)^n))

/-- Actual local scalar oscillation and a genuinely supported differentiable cutoff produce global all-ball oscillation of the same original centered product. -/
theorem exists_local_mean_oscillation_cutoff_bound_explicit (n : ℕ) (D : ℝ) (hD : 0≤D) :
    ∃ C : ℝ,0<C ∧ C=localMeanOscillationCutoffConstant n D ∧ ∀ (a : Domain n) (t : ℝ),0<t →
      ∀ (f : Domain n → ℝ) (B : ℝ),0≤B →
        (∀ (x : Domain n) (r : ℝ),0<r → IntegrableOn f (Metric.ball x r) volume) →
        (∀ (x : Domain n) (r : ℝ),0<r → r≤8*t →
          (⨍ y in Metric.ball x r,|f y-(⨍ z in Metric.ball x r,f z)|)≤B) →
        ∀ (χ : Domain n → ℝ),ContDiff ℝ 1 χ → Function.support χ⊆Metric.ball a t →
          (∀ y,|χ y|≤1) → (∀ y,‖fderiv ℝ χ y‖≤D/t) →
          let β := fun y=>χ y*(f y-(⨍ z in Metric.ball a (8*t),f z))
          ∀ (x : Domain n) (r : ℝ),0<r → IntegrableOn β (Metric.ball x r) volume ∧
            (⨍ y in Metric.ball x r,|β y-(⨍ z in Metric.ball x r,β z)|)≤C*B := by
  let H : ℝ := 2*(2 : ℝ)^n+2*(4 : ℝ)^n
  let C : ℝ := 2*((32 : ℝ)^n+1+D*H)
  have hH : 0≤H := by dsimp only [H];positivity
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,rfl,?_⟩
  intro a t ht f B hB hf hOsc χ hχ hSupport hBound hDerivative β x r hr
  let m := ⨍ z in Metric.ball a (8*t),f z
  let μ := volume.restrict (Metric.ball x r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : NeZero μ := ⟨by
    intro hz
    have Hzero := congrArg (fun ν : Measure (Domain n)=>ν univ) hz
    exact (Metric.measure_ball_pos volume x hr).ne' (by simpa [μ] using Hzero)⟩
  have hβI : IntegrableOn β (Metric.ball x r) volume :=
    ((hf x r hr).sub (integrable_const m)).bdd_mul hχ.continuous.aestronglyMeasurable.restrict
      (Eventually.of_forall fun y=>by simpa only [Real.norm_eq_abs] using hBound y)
  refine ⟨hβI,?_⟩
  have hMeanCenter (c : ℝ) :
      (⨍ y in Metric.ball x r,|β y-(⨍ z in Metric.ball x r,β z)|)≤2*(⨍ y in Metric.ball x r,|β y-c|) :=
    mean_oscillation_le_twice_centered_average μ β hβI c
  by_cases hLarge : t/4≤r
  · letI : IsFiniteMeasure (volume.restrict (Metric.ball a (8*t))) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
    let G := (Metric.ball a (8*t)).indicator (fun y=>|f y-m|)
    have hOuterI : IntegrableOn (fun y=>|f y-m|) (Metric.ball a (8*t)) volume :=
      ((hf a (8*t) (by positivity)).sub (integrable_const m)).abs
    have hGI : Integrable G volume := (integrable_indicator_iff measurableSet_ball).mpr hOuterI
    have hGNonneg (y : Domain n) : 0≤G y := by
      dsimp only [G]
      exact indicator_nonneg (fun _ _=>abs_nonneg _) y
    have hDom (y : Domain n) : |β y|≤G y := by
      by_cases hy : y∈Metric.ball a (8*t)
      · rw [show G y=|f y-m| from indicator_of_mem hy _]
        change |χ y*(f y-m)|≤|f y-m|
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right (hBound y) (abs_nonneg _)).trans_eq (one_mul _)
      · have hχZero : χ y=0 := by
          by_contra hn
          exact hy ((Metric.ball_subset_ball (by linarith : t≤8*t)) (hSupport hn))
        rw [show G y=0 from indicator_of_notMem hy _]
        change |χ y*(f y-m)|≤0
        rw [hχZero,zero_mul,abs_zero]
    have hOuterMass : 0<volume.real (Metric.ball a (8*t)) :=
      ENNReal.toReal_pos (Metric.measure_ball_pos volume a (by positivity : 0<8*t)).ne' measure_ball_ne_top
    have hOuterBound : (∫ y in Metric.ball a (8*t),|f y-m|)≤volume.real (Metric.ball a (8*t))*B := by
      have hAvg := hOsc a (8*t) (by positivity) le_rfl
      have hDiv : (∫ y in Metric.ball a (8*t),|f y-m|)/volume.real (Metric.ball a (8*t))≤B := by
        simpa only [m,setAverage_eq,smul_eq_mul,div_eq_mul_inv,mul_comm] using hAvg
      simpa only [mul_comm] using (div_le_iff₀ hOuterMass).mp hDiv
    have hMass := ball_measureReal_le_of_radius_le_mul x a hr (by positivity : 0<8*t)
      (show 8*t≤32*r by linarith only [hLarge])
    have hIntegralBound : (∫ y in Metric.ball x r,|β y|)≤(32 : ℝ)^n*volume.real (Metric.ball x r)*B := by
      calc
        _ ≤ ∫ y in Metric.ball x r,G y := integral_mono hβI.abs hGI.integrableOn hDom
        _ ≤ ∫ y,G y := setIntegral_le_integral hGI (Eventually.of_forall hGNonneg)
        _ = ∫ y in Metric.ball a (8*t),|f y-m| := integral_indicator measurableSet_ball
        _ ≤ volume.real (Metric.ball a (8*t))*B := hOuterBound
        _ ≤ _ := mul_le_mul_of_nonneg_right hMass hB
    have hMassPos : 0<volume.real (Metric.ball x r) :=
      ENNReal.toReal_pos (Metric.measure_ball_pos volume x hr).ne' measure_ball_ne_top
    have hAverageBound : (⨍ y in Metric.ball x r,|β y|)≤(32 : ℝ)^n*B := by
      rw [setAverage_eq,smul_eq_mul]
      have hDiv : (∫ y in Metric.ball x r,|β y|)/volume.real (Metric.ball x r)≤(32 : ℝ)^n*B :=
        (div_le_iff₀ hMassPos).mpr (hIntegralBound.trans_eq (by ring))
      simpa only [div_eq_mul_inv,mul_comm] using hDiv
    have hBase := (hMeanCenter 0).trans (mul_le_mul_of_nonneg_left
      (by simpa only [sub_zero] using hAverageBound) (by norm_num : (0 : ℝ)≤2))
    have hConst : 2*(32 : ℝ)^n≤C := by dsimp only [C];nlinarith only [mul_nonneg hD hH]
    calc
      _ ≤ 2*((32 : ℝ)^n*B) := hBase
      _ = (2*(32 : ℝ)^n)*B := by ring
      _ ≤ C*B := mul_le_mul_of_nonneg_right hConst hB
  · have hrSmall : r<t/4 := lt_of_not_ge hLarge
    by_cases hNear : dist x a≤2*t
    · let q := ⨍ z in Metric.ball x r,f z
      let c := χ x*(q-m)
      have hDamp := local_ballMean_difference_damped_le f a x ht hr (by linarith only [hrSmall,ht]) hNear hB hf hOsc
      have hLip (y : Domain n) : |χ y-χ x|≤(D/t)*dist y x := by
        have hM := Convex.norm_image_sub_le_of_norm_fderiv_le
          (s:=univ) (fun z _=>hχ.differentiable (by norm_num) z) (fun z _=>hDerivative z)
          (convex_univ : Convex ℝ (univ : Set (Domain n))) (mem_univ x) (mem_univ y)
        simpa only [Real.norm_eq_abs,dist_eq_norm] using hM
      have hPoint (y : Domain n) (hy : y∈Metric.ball x r) :
          |β y-c|≤|f y-q|+(D*(r/t))*|q-m| := by
        have hχDiff : |χ y-χ x|≤D*(r/t) :=
          (hLip y).trans ((mul_le_mul_of_nonneg_left (le_of_lt hy) (div_nonneg hD ht.le)).trans_eq (by ring))
        have hAlg : β y-c=χ y*(f y-q)+(χ y-χ x)*(q-m) := by dsimp only [β,c];ring
        rw [hAlg]
        calc
          _ ≤ |χ y*(f y-q)|+|(χ y-χ x)*(q-m)| := abs_add_le _ _
          _ ≤ |f y-q|+(D*(r/t))*|q-m| := by
            simp only [abs_mul]
            exact add_le_add ((mul_le_mul_of_nonneg_right (hBound y) (abs_nonneg _)).trans_eq (one_mul _))
              (mul_le_mul_of_nonneg_right hχDiff (abs_nonneg _))
      have hErrorI : IntegrableOn (fun y=>|β y-c|) (Metric.ball x r) volume := (hβI.sub (integrable_const c)).abs
      have hRhsI : IntegrableOn (fun y=>|f y-q|+(D*(r/t))*|q-m|) (Metric.ball x r) volume :=
        ((hf x r hr).sub (integrable_const q)).abs.add (integrable_const _)
      have hAverage : (⨍ y in Metric.ball x r,|β y-c|)≤
          (⨍ y in Metric.ball x r,|f y-q|)+(D*(r/t))*|q-m| := by
        calc
          _ ≤ ⨍ y in Metric.ball x r,|f y-q|+(D*(r/t))*|q-m| := by
            rw [setAverage_eq,setAverage_eq,smul_eq_mul,smul_eq_mul]
            exact mul_le_mul_of_nonneg_left
              (setIntegral_mono_on hErrorI hRhsI measurableSet_ball hPoint) (inv_nonneg.mpr ENNReal.toReal_nonneg)
          _ = _ := by
            have hFI : Integrable (fun y=>|f y-q|) μ := ((hf x r hr).sub (integrable_const q)).abs
            calc
              _ = (⨍ y in Metric.ball x r,|f y-q|)+(⨍ _y in Metric.ball x r,(D*(r/t))*|q-m|) :=
                integral_add hFI.to_average (integrable_const _)
              _ = _ := by rw [average_const]
      have hProduct : (D*(r/t))*|q-m|≤D*H*B := by
        calc
          _ = D*((r/t)*|q-m|) := by ring
          _ ≤ D*(H*B) := mul_le_mul_of_nonneg_left hDamp hD
          _ = _ := by ring
      have hAvgB : (⨍ y in Metric.ball x r,|β y-c|)≤(1+D*H)*B :=
        hAverage.trans ((add_le_add (hOsc x r hr (by linarith only [hrSmall,ht])) hProduct).trans_eq (by ring))
      have hConst : 2*(1+D*H)≤C := by
        dsimp only [C]
        have hp : 0≤(32 : ℝ)^n := by positivity
        linarith only [hp]
      calc
        _ ≤ 2*(⨍ y in Metric.ball x r,|β y-c|) := hMeanCenter c
        _ ≤ 2*((1+D*H)*B) := mul_le_mul_of_nonneg_left hAvgB (by norm_num)
        _ = (2*(1+D*H))*B := by ring
        _ ≤ C*B := mul_le_mul_of_nonneg_right hConst hB
    · have hZero (y : Domain n) (hy : y∈Metric.ball x r) : β y=0 := by
        have hχZero : χ y=0 := by
          by_contra hn
          have hya : dist y a<t := hSupport hn
          have hyx : dist y x<r := hy
          have hTriangle := dist_triangle x y a
          rw [dist_comm x y] at hTriangle
          exact hNear (by linarith only [hTriangle,hya,hyx,hrSmall,ht])
        change χ y*(f y-m)=0
        rw [hχZero,zero_mul]
      have hMeanZero : (⨍ y in Metric.ball x r,β y)=0 := by
        rw [setAverage_eq]
        have hInt : (∫ y in Metric.ball x r,β y)=0 := by
          apply integral_eq_zero_of_ae
          filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
          exact hZero y hy
        rw [hInt,smul_zero]
      rw [hMeanZero]
      have hOscZero : (⨍ y in Metric.ball x r,|β y-0|)=0 := by
        rw [setAverage_eq]
        have hInt : (∫ y in Metric.ball x r,|β y-0|)=0 := by
          apply integral_eq_zero_of_ae
          filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
          change |β y-0|=(0 : ℝ)
          rw [hZero y hy,sub_zero,abs_zero]
        rw [hInt,smul_zero]
      rw [hOscZero]
      exact mul_nonneg hC.le hB

theorem exists_local_mean_oscillation_cutoff_bound (n : ℕ) (D : ℝ) (hD : 0≤D) :
    ∃ C : ℝ,0<C ∧ ∀ (a : Domain n) (t : ℝ),0<t →
      ∀ (f : Domain n → ℝ) (B : ℝ),0≤B →
        (∀ (x : Domain n) (r : ℝ),0<r → IntegrableOn f (Metric.ball x r) volume) →
        (∀ (x : Domain n) (r : ℝ),0<r → r≤8*t →
          (⨍ y in Metric.ball x r,|f y-(⨍ z in Metric.ball x r,f z)|)≤B) →
        ∀ (χ : Domain n → ℝ),ContDiff ℝ 1 χ → Function.support χ⊆Metric.ball a t →
          (∀ y,|χ y|≤1) → (∀ y,‖fderiv ℝ χ y‖≤D/t) →
          let β := fun y=>χ y*(f y-(⨍ z in Metric.ball a (8*t),f z))
          ∀ (x : Domain n) (r : ℝ),0<r → IntegrableOn β (Metric.ball x r) volume ∧
            (⨍ y in Metric.ball x r,|β y-(⨍ z in Metric.ball x r,β z)|)≤C*B := by
  obtain ⟨C,hC,_hCEq,H⟩ := exists_local_mean_oscillation_cutoff_bound_explicit n D hD
  exact ⟨C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.DivCurlLowerExponent
public import HolderToCK.Foundation.BallVolume

/-!
# Dimension-uniform scaled averages for actual div--curl kernels

The real Sobolev and Holder exponents are chosen from the dimension.
The ball volume factors cancel exactly with the actual kernel derivative
scale r to the power minus n minus one. Both factors in the resulting
estimate are literal averages of the original lower gradient powers.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal NNReal

namespace StationaryHarmonicMaps.Analysis

/-- The actual finite ball Lp norm is its measure factor times the literal average root. -/
theorem lpNorm_ball_eq_measure_rpow_mul_average_rpow {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (a : Domain n) {r : ℝ} (hr : 0 < r) (p : ℝ≥0) (hp : 0 < p)
    (f : Domain n → E)
    (hf : MemLp f (p : ℝ≥0∞) (volume.restrict (Metric.ball a r))) :
    lpNorm f (p : ℝ≥0∞) (volume.restrict (Metric.ball a r)) =
      (volume.real (Metric.ball a r))^(1/(p : ℝ)) *
        (⨍ x in Metric.ball a r,‖f x‖^(p : ℝ))^(1/(p : ℝ)) := by
  have hmass : 0 < volume.real (Metric.ball a r) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume a hr).ne' measure_ball_ne_top
  have hAvg : 0 ≤ ⨍ x in Metric.ball a r,‖f x‖^(p : ℝ) := by
    rw [setAverage_eq,smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hmass.le)
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have hI : (∫ x in Metric.ball a r,‖f x‖^(p : ℝ))=
      volume.real (Metric.ball a r)*(⨍ x in Metric.ball a r,‖f x‖^(p : ℝ)) := by
    simpa only [smul_eq_mul] using (measure_smul_setAverage
      (fun x => ‖f x‖^(p : ℝ)) measure_ball_ne_top).symm
  rw [lpNorm_eq_integral_norm_rpow_toReal (by exact_mod_cast hp.ne') ENNReal.coe_ne_top hf.aestronglyMeasurable]
  simp only [ENNReal.coe_toReal,← one_div]
  rw [hI,Real.mul_rpow hmass.le hAvg]

/-- The genuine dimension-dependent CLMS exponents are Sobolev and Holder partners below two. -/
theorem exists_divcurl_sobolev_holder_exponents (n : ℕ) (hn : 2 ≤ n) :
    ∃ p s : ℝ≥0, (p : ℝ)=2*(n : ℝ)/((n : ℝ)+1) ∧
      1 < p ∧ p < 2 ∧ 0 < s ∧
      (s : ℝ)⁻¹=(p : ℝ)⁻¹-(n : ℝ)⁻¹ ∧
      Real.HolderConjugate (p : ℝ) (s : ℝ) ∧
      2*(n : ℝ)/(p : ℝ)=(n : ℝ)+1 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hnPlus : 0 < (n : ℝ)+1 := by linarith
  have hnMinus : 0 < (n : ℝ)-1 := by linarith
  let p : ℝ≥0 := ⟨2*(n : ℝ)/((n : ℝ)+1),by positivity⟩
  let s : ℝ≥0 := ⟨2*(n : ℝ)/((n : ℝ)-1),by positivity⟩
  have hp1 : (1 : ℝ) < p := (lt_div_iff₀ hnPlus).mpr (by linarith)
  have hp2 : (p : ℝ) < 2 := (div_lt_iff₀ hnPlus).mpr (by linarith)
  have hs0 : (0 : ℝ) < s := div_pos (by positivity) hnMinus
  have hRel : (s : ℝ)⁻¹=(p : ℝ)⁻¹-(n : ℝ)⁻¹ := by
    change (2*(n : ℝ)/((n : ℝ)-1))⁻¹=(2*(n : ℝ)/((n : ℝ)+1))⁻¹-(n : ℝ)⁻¹
    field_simp [hn0.ne',hnPlus.ne',hnMinus.ne']
    ring
  have hHolder : Real.HolderConjugate (p : ℝ) (s : ℝ) := Real.holderConjugate_iff.mpr ⟨hp1,by
    change (2*(n : ℝ)/((n : ℝ)+1))⁻¹+(2*(n : ℝ)/((n : ℝ)-1))⁻¹=1
    field_simp [hn0.ne',hnPlus.ne',hnMinus.ne']
    ring⟩
  have hScale : 2*(n : ℝ)/(p : ℝ)=(n : ℝ)+1 := by
    change 2*(n : ℝ)/(2*(n : ℝ)/((n : ℝ)+1))=(n : ℝ)+1
    field_simp [hn0.ne',hnPlus.ne']
  exact ⟨p,s,rfl,by exact_mod_cast hp1,by exact_mod_cast hp2,by exact_mod_cast hs0,hRel,hHolder,hScale⟩

/-- The literal lower-power coefficient after cancellation of the ball scale. -/
@[expose] noncomputable def divcurlScaledAverageConstant (n : ℕ) (p : ℝ≥0) : ℝ :=
  divcurlLowerExponentConstant n p * ((2:ℝ)^n)^(1/(p:ℝ)) *
    (volume.real (Metric.ball (0:Domain n) 1))^(2/(p:ℝ))

/-- Original rough data have the scale-correct kernel estimate in literal lower-power ball averages. -/
theorem exists_divcurl_scaled_average_kernel_bound_explicit (n : ℕ) (hn : 2 ≤ n) :
    ∃ p : ℝ≥0, (p : ℝ)=2*(n : ℝ)/((n : ℝ)+1) ∧ 1 < p ∧ p < 2 ∧
      ∃ C : ℝ, C=divcurlScaledAverageConstant n p ∧ 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (r : ℝ), 0 < r →
        ∀ (Z : Domain n → Gradient n q),
          (∀ i,MemLp (fun x => Z x i) 2 (volume.restrict (Metric.ball a (2*r)))) →
          HolderToCK.WeakPoissonOn (ballDomain a (2*r)) Z (fun _ => (0 : Ambient q)) →
          ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
            MemW12 (ballDomain a (2*r)) w Dw →
            ∀ (κ : Domain n → ℝ), ContDiff ℝ ∞ κ → HasCompactSupport κ →
            tsupport κ ⊆ Metric.ball a r → ∀ B : ℝ, 0 ≤ B →
            (∀ x ∈ Metric.ball a r,∀ i : Fin n,
              |fderiv ℝ κ x (EuclideanSpace.single i 1)| ≤ B*r^(-(n : ℝ)-1)) →
            IntegrableOn (fun x => κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i))
              (Metric.ball a r) volume ∧
            |∫ x in Metric.ball a r,κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i)| ≤
              C*B*(⨍ x in Metric.ball a r,(Real.sqrt (hsNormSq (Z x)))^(p : ℝ))^(1/(p : ℝ))*
                (⨍ x in Metric.ball a (2*r),(Real.sqrt (hsNormSq (Dw x)))^(p : ℝ))^(1/(p : ℝ)) := by
  obtain ⟨p,s,hpFormula,hp1,hp2,hs0,hRel,hHolder,hScale⟩ := exists_divcurl_sobolev_holder_exponents n hn
  obtain ⟨K,hKEq,hK,Hkernel⟩ := exists_divcurl_lower_exponent_kernel_bound_explicit n (by omega)
    p s hp1.le hp2.le hs0 hRel hHolder
  let V : ℝ := volume.real (Metric.ball (0 : Domain n) 1)
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume (0 : Domain n) (by norm_num : (0 : ℝ)<1)).ne' measure_ball_ne_top
  let D : ℝ := ((2 : ℝ)^n)^(1/(p : ℝ))*V^(2/(p : ℝ))
  let C : ℝ := K*D
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨p,hpFormula,hp1,hp2,C,?_,mul_pos hK hD,?_⟩
  · dsimp only [C,D,divcurlScaledAverageConstant]
    rw [hKEq]
    ring
  intro q a r hr Z hZ hdiv w Dw hw κ hκ hcκ hsκ B hB hDκ
  have hB' : 0 ≤ B*r^(-(n : ℝ)-1) := mul_nonneg hB (Real.rpow_nonneg hr.le _)
  obtain ⟨hI,hBound⟩ := Hkernel q a r hr Z hZ hdiv w Dw hw κ hκ hcκ hsκ
    (B*r^(-(n : ℝ)-1)) hB' hDκ
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a (2*r))) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (ballDomain a (2*r)).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hsub : Metric.ball a r ⊆ Metric.ball a (2*r) := Metric.ball_subset_ball (by linarith)
  have hZr (i : Fin n) : MemLp (fun x => Z x i) 2 (volume.restrict (Metric.ball a r)) :=
    (hZ i).mono_measure (Measure.restrict_mono_set volume hsub)
  have hZp : MemLp (fun x => Real.sqrt (hsNormSq (Z x))) (p : ℝ≥0∞)
      (volume.restrict (Metric.ball a r)) :=
    (memLp_sqrt_sum_norm_sq Z hZr).mono_exponent (by exact_mod_cast hp2.le)
  have hWp : MemLp (fun x => Real.sqrt (hsNormSq (Dw x))) (p : ℝ≥0∞)
      (volume.restrict (Metric.ball a (2*r))) :=
    (memLp_sqrt_sum_norm_sq Dw hw.2.2).mono_exponent (by exact_mod_cast hp2.le)
  have hNormZ : lpNorm (fun x => Real.sqrt (hsNormSq (Z x))) (p : ℝ≥0∞)
      (volume.restrict (Metric.ball a r)) =
      (volume.real (Metric.ball a r))^(1/(p : ℝ))*
        (⨍ x in Metric.ball a r,(Real.sqrt (hsNormSq (Z x)))^(p : ℝ))^(1/(p : ℝ)) := by
    simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _)] using
      lpNorm_ball_eq_measure_rpow_mul_average_rpow a hr p hp0
        (fun x => Real.sqrt (hsNormSq (Z x))) hZp
  have hNormW : lpNorm (fun x => Real.sqrt (hsNormSq (Dw x))) (p : ℝ≥0∞)
      (volume.restrict (Metric.ball a (2*r))) =
      (volume.real (Metric.ball a (2*r)))^(1/(p : ℝ))*
        (⨍ x in Metric.ball a (2*r),(Real.sqrt (hsNormSq (Dw x)))^(p : ℝ))^(1/(p : ℝ)) := by
    simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _)] using
      lpNorm_ball_eq_measure_rpow_mul_average_rpow a (by positivity : 0<2*r) p hp0
        (fun x => Real.sqrt (hsNormSq (Dw x))) hWp
  have hVolumeScale : r^(-(n : ℝ)-1)*(volume.real (Metric.ball a r))^(1/(p : ℝ))*
      (volume.real (Metric.ball a (2*r)))^(1/(p : ℝ))=D := by
    rw [HolderToCK.ball_volume_real a hr,HolderToCK.ball_volume_real a (by positivity : 0<2*r),
      mul_pow,Real.mul_rpow (pow_nonneg hr.le _) hV.le,
      Real.mul_rpow (mul_nonneg (by positivity) (pow_nonneg hr.le _)) hV.le,
      Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ)^n) (pow_nonneg hr.le _)]
    simp only [← Real.rpow_natCast r n,← Real.rpow_mul hr.le]
    have hExponent : -(n : ℝ)-1+(n : ℝ)*(1/(p : ℝ))+(n : ℝ)*(1/(p : ℝ))=0 := by
      have HH := hScale
      rw [div_eq_mul_inv] at HH
      simp only [one_div]
      nlinarith only [HH]
    calc
      _ = ((2 : ℝ)^n)^(1/(p : ℝ))*(V^(1/(p : ℝ))*V^(1/(p : ℝ)))*
          ((r^(-(n : ℝ)-1)*r^((n : ℝ)*(1/(p : ℝ))))*r^((n : ℝ)*(1/(p : ℝ)))) := by ring
      _ = D := by
        rw [← Real.rpow_add hV,← Real.rpow_add hr,← Real.rpow_add hr,hExponent,Real.rpow_zero,mul_one]
        dsimp only [D]
        congr 2
        ring
  refine ⟨hI,?_⟩
  rw [hNormZ,hNormW] at hBound
  have hEq : K*(B*r^(-(n : ℝ)-1))*
      ((volume.real (Metric.ball a r))^(1/(p : ℝ))*
        (⨍ x in Metric.ball a r,(Real.sqrt (hsNormSq (Z x)))^(p : ℝ))^(1/(p : ℝ)))*
      ((volume.real (Metric.ball a (2*r)))^(1/(p : ℝ))*
        (⨍ x in Metric.ball a (2*r),(Real.sqrt (hsNormSq (Dw x)))^(p : ℝ))^(1/(p : ℝ))) =
      C*B*(⨍ x in Metric.ball a r,(Real.sqrt (hsNormSq (Z x)))^(p : ℝ))^(1/(p : ℝ))*
        (⨍ x in Metric.ball a (2*r),(Real.sqrt (hsNormSq (Dw x)))^(p : ℝ))^(1/(p : ℝ)) := by
    calc
      _ = K*B*(r^(-(n : ℝ)-1)*(volume.real (Metric.ball a r))^(1/(p : ℝ))*
          (volume.real (Metric.ball a (2*r)))^(1/(p : ℝ)))*
          (⨍ x in Metric.ball a r,(Real.sqrt (hsNormSq (Z x)))^(p : ℝ))^(1/(p : ℝ))*
          (⨍ x in Metric.ball a (2*r),(Real.sqrt (hsNormSq (Dw x)))^(p : ℝ))^(1/(p : ℝ)) := by ring
      _ = _ := by rw [hVolumeScale]; dsimp only [C]; ring
  exact hBound.trans_eq hEq

theorem exists_divcurl_scaled_average_kernel_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ p : ℝ≥0, (p : ℝ)=2*(n : ℝ)/((n : ℝ)+1) ∧ 1 < p ∧ p < 2 ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (r : ℝ), 0 < r →
        ∀ (Z : Domain n → Gradient n q),
          (∀ i,MemLp (fun x => Z x i) 2 (volume.restrict (Metric.ball a (2*r)))) →
          HolderToCK.WeakPoissonOn (ballDomain a (2*r)) Z (fun _ => (0 : Ambient q)) →
          ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
            MemW12 (ballDomain a (2*r)) w Dw →
            ∀ (κ : Domain n → ℝ), ContDiff ℝ ∞ κ → HasCompactSupport κ →
            tsupport κ ⊆ Metric.ball a r → ∀ B : ℝ, 0 ≤ B →
            (∀ x ∈ Metric.ball a r,∀ i : Fin n,
              |fderiv ℝ κ x (EuclideanSpace.single i 1)| ≤ B*r^(-(n : ℝ)-1)) →
            IntegrableOn (fun x => κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i))
              (Metric.ball a r) volume ∧
            |∫ x in Metric.ball a r,κ x*∑ i : Fin n,inner ℝ (Z x i) (Dw x i)| ≤
              C*B*(⨍ x in Metric.ball a r,(Real.sqrt (hsNormSq (Z x)))^(p : ℝ))^(1/(p : ℝ))*
                (⨍ x in Metric.ball a (2*r),(Real.sqrt (hsNormSq (Dw x)))^(p : ℝ))^(1/(p : ℝ)) := by
  obtain ⟨p,hpF,hp1,hp2,C,_hEq,hC,H⟩ := exists_divcurl_scaled_average_kernel_bound_explicit n hn
  exact ⟨p,hpF,hp1,hp2,C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end

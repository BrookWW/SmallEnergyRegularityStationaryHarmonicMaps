module

public import StationaryHarmonicMaps.Analysis.EffectiveZeroBoundarySobolevLp
public import StationaryHarmonicMaps.Analysis.LpPoincareNorm
public import StationaryHarmonicMaps.Analysis.ScaledBallCutoff
public import StationaryHarmonicMaps.Analysis.SobolevCutoff
public import HarmonicMaps.Analysis.SobolevCutoffBoundary

/-!
# Genuine interior Sobolev--Poincare for lower exponents

One actual uniformly scaled bump turns the original centered native graph
into a genuine W0 graph. The proved zero-boundary Sobolev gain and the
same-exponent Poincare estimate bound its actual derivative. The resulting
constant precedes target dimension, center, radius and original weak map.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal NNReal

namespace StationaryHarmonicMaps.Analysis

/-- The Euclidean local Sobolev--Poincaré coefficient with the fixed numerical cutoff. -/
@[expose] noncomputable def localSobolevPoincareConstant (n : ℕ) (p : ℝ≥0) : ℝ :=
  ((1+euclideanSobolevCoefficient n (p:ℝ):ℝ≥0):ℝ)*
    (1+Real.sqrt (n:ℝ)+4*(n:ℝ)*(2:ℝ)^22*Real.sqrt (n:ℝ)*((2:ℝ)^n)^(1/(p:ℝ)))

/-- Actual W12 data on the double ball produce higher local integrability and the scale-invariant Sobolev--Poincare bound. -/
theorem exists_local_sobolev_poincare_bound_explicit (n : ℕ) (hn : 0 < n)
    (p s : ℝ≥0) (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hs : 0 < s)
    (hsp : (s : ℝ)⁻¹=(p : ℝ)⁻¹-(n : ℝ)⁻¹) :
    ∃ C : ℝ, C=localSobolevPoincareConstant n p ∧ 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (r : ℝ), 0 < r →
      ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      MemW12 (ballDomain a (2*r)) u Du →
      let c := ⨍ y in Metric.ball a (2*r),u y
      MemLp (fun x => u x-c) (s : ℝ≥0∞) (volume.restrict (Metric.ball a r)) ∧
      lpNorm (fun x => u x-c) (s : ℝ≥0∞) (volume.restrict (Metric.ball a r)) ≤
        C * lpNorm (fun x => Real.sqrt (hsNormSq (Du x))) (p : ℝ≥0∞)
          (volume.restrict (Metric.ball a (2*r))) := by
  obtain ⟨S,hSEq,hS,Hsob⟩ := exists_zeroBoundary_sobolev_lp_bound_explicit n hn p s hp hp₂ hs hsp
  let M : ℝ := (2:ℝ)^22
  have hM : 0<M := by norm_num [M]
  have Hcut := scaled_ball_cutoff_explicit n
  let T : ℝ := ((2 : ℝ)^n)^(1/(p : ℝ))
  let L : ℝ := 1+Real.sqrt (n : ℝ)+4*(n : ℝ)*M*Real.sqrt (n : ℝ)*T
  let C : ℝ := (S : ℝ)*L
  have hT : 0 ≤ T := Real.rpow_nonneg (by positivity) _
  have hL : 0 < L := by dsimp only [L]; positivity
  have hSreal : 0 < (S : ℝ) := by exact_mod_cast hS
  refine ⟨C,?_,mul_pos hSreal hL,?_⟩
  · change (S:ℝ)*L=((1+euclideanSobolevCoefficient n (p:ℝ):ℝ≥0):ℝ)*L
    rw [hSEq]
  intro q a r hr u Du hu
  dsimp only
  let μ : Measure (Domain n) := volume.restrict (Metric.ball a (2*r))
  let ν : Measure (Domain n) := volume.restrict (Metric.ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (ballDomain a (2*r)).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let c : Ambient q := ⨍ y in Metric.ball a (2*r),u y
  let G : Domain n → ℝ := fun x => Real.sqrt (hsNormSq (Du x))
  obtain ⟨κ,hκ,hcκ,hsκ,hκone,hκbound,hDκ⟩ := Hcut a r hr
  let v : Domain n → Ambient q := fun x => κ x • (u x-c)
  let Dv : Domain n → Gradient n q := fun x i =>
    coordinateDerivative κ hκ i x • (u x-c)+κ x • Du x i
  have huc : MemW12 (ballDomain a (2*r)) (fun x => u x-c) Du :=
    ⟨(memW12Loc_sub_const hu.to_memW12Loc c).1,hu.2.1.sub (memLp_const c),hu.2.2⟩
  have hv : HasZeroBoundaryValues (ballDomain a (2*r)) v Dv :=
    huc.smoothCutoff_zeroBoundary_ball (by positivity) hκ hcκ hsκ
  obtain ⟨hvS,hSob⟩ := Hsob q a (2*r) v Dv hv
  have hG2 : MemLp G 2 μ := memLp_sqrt_sum_norm_sq Du hu.2.2
  have hGp : MemLp G (p : ℝ≥0∞) μ := hG2.mono_exponent (by exact_mod_cast hp₂)
  have hUp : MemLp (fun x => u x-c) (p : ℝ≥0∞) μ :=
    huc.2.1.mono_exponent (by exact_mod_cast hp₂)
  have hDp : MemLp (fun x => Real.sqrt (hsNormSq (Dv x))) (p : ℝ≥0∞) μ :=
    (memLp_sqrt_sum_norm_sq Dv hv.1.2.2).mono_exponent (by exact_mod_cast hp₂)
  have hDcol (x : Domain n) (i : Fin n) : |coordinateDerivative κ hκ i x| ≤ M/r := by
    calc
      _ ≤ ‖fderiv ℝ κ x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ κ x‖ := by rw [PiLp.norm_single,norm_one,mul_one]
      _ ≤ M/r := hDκ x
  have hPoint (x : Domain n) : Real.sqrt (hsNormSq (Dv x)) ≤
      Real.sqrt (n : ℝ)*G x+((n : ℝ)*M/r)*‖u x-c‖ := by
    have hsum : (∑ i : Fin n,‖Dv x i‖) ≤
        κ x*(∑ i : Fin n,‖Du x i‖)+((n : ℝ)*M/r)*‖u x-c‖ := by
      calc
        _ ≤ ∑ i : Fin n, (κ x*‖Du x i‖+(M/r)*‖u x-c‖) := by
          apply Finset.sum_le_sum
          intro i _
          have H := norm_add_le (coordinateDerivative κ hκ i x • (u x-c)) (κ x • Du x i)
          rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
            abs_of_nonneg (hκbound x).1] at H
          exact H.trans (by nlinarith only [mul_le_mul_of_nonneg_right (hDcol x i) (norm_nonneg (u x-c))])
        _ = _ := by
          simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
            Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
          ring
    have H := sum_column_norm_le_sqrt_dimension_mul_hs (Du x)
    have hSum0 : 0 ≤ ∑ i : Fin n,‖Du x i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    have hκsum : κ x*(∑ i : Fin n,‖Du x i‖) ≤ ∑ i : Fin n,‖Du x i‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hκbound x).2 hSum0
    exact (sqrt_hsNormSq_le_sum_norm (Dv x)).trans (hsum.trans (by
      change κ x*(∑ i : Fin n,‖Du x i‖)+_ ≤ Real.sqrt (n : ℝ)*Real.sqrt (hsNormSq (Du x))+_
      linarith))
  have hFirst : MemLp (fun x => Real.sqrt (n : ℝ)*G x) (p : ℝ≥0∞) μ := hGp.const_mul _
  have hSecond : MemLp (fun x => ((n : ℝ)*M/r)*‖u x-c‖) (p : ℝ≥0∞) μ := hUp.norm.const_mul _
  have hSum : MemLp (fun x => Real.sqrt (n : ℝ)*G x+((n : ℝ)*M/r)*‖u x-c‖)
      (p : ℝ≥0∞) μ := hFirst.add hSecond
  have hNormD : lpNorm (fun x => Real.sqrt (hsNormSq (Dv x))) (p : ℝ≥0∞) μ ≤
      Real.sqrt (n : ℝ)*lpNorm G (p : ℝ≥0∞) μ+
        ((n : ℝ)*M/r)*lpNorm (fun x => u x-c) (p : ℝ≥0∞) μ := by
    have H := lpNorm_mono_real hSum (fun x => by
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact hPoint x)
    have HH := lpNorm_add_le hFirst (g := fun x => ((n : ℝ)*M/r)*‖u x-c‖)
      (show 1 ≤ (p : ℝ≥0∞) by exact_mod_cast hp)
    have hF : (fun x => Real.sqrt (n : ℝ)*G x)=Real.sqrt (n : ℝ) • G := by funext x; rfl
    have hH : (fun x => ((n : ℝ)*M/r)*‖u x-c‖)=((n : ℝ)*M/r) • (fun x => ‖u x-c‖) := by funext x; rfl
    have hFnorm := lpNorm_const_smul (p := (p : ℝ≥0∞)) (Real.sqrt (n : ℝ)) G μ
    have hHnorm := lpNorm_const_smul (p := (p : ℝ≥0∞)) ((n : ℝ)*M/r) (fun x => ‖u x-c‖) μ
    rw [← hF,coe_nnnorm,Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hFnorm
    rw [← hH,coe_nnnorm,Real.norm_of_nonneg (by positivity),lpNorm_norm hUp.aestronglyMeasurable] at hHnorm
    have hSumEq : ((fun x => Real.sqrt (n : ℝ)*G x)+(fun x => ((n : ℝ)*M/r)*‖u x-c‖))=
        (fun x => Real.sqrt (n : ℝ)*G x+((n : ℝ)*M/r)*‖u x-c‖) := by funext x; rfl
    rw [hFnorm,hHnorm,hSumEq] at HH
    exact H.trans HH
  have hP := sobolev_poincare_lpNorm_ball a (by positivity : 0 < 2*r)
    (show (1 : ℝ) ≤ p by exact_mod_cast hp) (show (p : ℝ) ≤ 2 by exact_mod_cast hp₂) hu
  have hP' : lpNorm (fun x => u x-c) (p : ℝ≥0∞) μ ≤
      (4*r*Real.sqrt (n : ℝ))*T*lpNorm G (p : ℝ≥0∞) μ := by
    simpa only [ENNReal.ofReal_coe_nnreal,show 2*(2*r)=4*r by ring] using hP
  have hNormD' : lpNorm (fun x => Real.sqrt (hsNormSq (Dv x))) (p : ℝ≥0∞) μ ≤
      L*lpNorm G (p : ℝ≥0∞) μ := by
    have HH := hNormD.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hP' (by positivity : 0 ≤ (n : ℝ)*M/r)))
    have hEq : Real.sqrt (n : ℝ)*lpNorm G (p : ℝ≥0∞) μ+
        ((n : ℝ)*M/r)*((4*r*Real.sqrt (n : ℝ))*T*lpNorm G (p : ℝ≥0∞) μ)=
        (L-1)*lpNorm G (p : ℝ≥0∞) μ := by
      dsimp only [L]
      field_simp [hr.ne']
      ring
    rw [hEq] at HH
    exact HH.trans (mul_le_mul_of_nonneg_right (by linarith : L-1 ≤ L) lpNorm_nonneg)
  have hSobReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hDp.eLpNorm_ne_top) hSob
  rw [ENNReal.toReal_mul,ENNReal.coe_toReal,toReal_eLpNorm hvS.aestronglyMeasurable,
    toReal_eLpNorm hDp.aestronglyMeasurable] at hSobReal
  have hνμ : ν ≤ μ := Measure.restrict_mono_set volume (Metric.ball_subset_ball (by linarith))
  have hvSmall : MemLp v (s : ℝ≥0∞) ν := hvS.mono_measure hνμ
  have hEqSmall : v =ᵐ[ν] (fun x => u x-c) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    change κ x • (u x-c)=u x-c
    rw [hκone x (Metric.ball_subset_closedBall hx),one_smul]
  have huSmall := hvSmall.ae_eq hEqSmall
  have hSmallNorm := ENNReal.toReal_mono hvS.eLpNorm_ne_top (eLpNorm_mono_measure v hνμ)
  rw [eLpNorm_congr_ae hEqSmall,toReal_eLpNorm huSmall.aestronglyMeasurable,
    toReal_eLpNorm hvS.aestronglyMeasurable] at hSmallNorm
  refine ⟨huSmall,hSmallNorm.trans (hSobReal.trans ?_)⟩
  calc
    _ ≤ (S : ℝ)*(L*lpNorm G (p : ℝ≥0∞) μ) :=
      mul_le_mul_of_nonneg_left hNormD' hSreal.le
    _ = _ := by dsimp only [C]; ring

theorem exists_local_sobolev_poincare_bound (n : ℕ) (hn : 0 < n)
    (p s : ℝ≥0) (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hs : 0 < s)
    (hsp : (s : ℝ)⁻¹=(p : ℝ)⁻¹-(n : ℝ)⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (r : ℝ), 0 < r →
      ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      MemW12 (ballDomain a (2*r)) u Du →
      let c := ⨍ y in Metric.ball a (2*r),u y
      MemLp (fun x => u x-c) (s : ℝ≥0∞) (volume.restrict (Metric.ball a r)) ∧
      lpNorm (fun x => u x-c) (s : ℝ≥0∞) (volume.restrict (Metric.ball a r)) ≤
        C * lpNorm (fun x => Real.sqrt (hsNormSq (Du x))) (p : ℝ≥0∞)
          (volume.restrict (Metric.ball a (2*r))) := by
  obtain ⟨C,_hEq,hC,H⟩ := exists_local_sobolev_poincare_bound_explicit n hn p s hp hp₂ hs hsp
  exact ⟨C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end

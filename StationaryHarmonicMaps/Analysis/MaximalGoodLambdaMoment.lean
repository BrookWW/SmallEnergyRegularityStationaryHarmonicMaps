module

public import StationaryHarmonicMaps.Analysis.GoodLambdaAbsorption
public import StationaryHarmonicMaps.Analysis.HardyLittlewoodLp
public import StationaryHarmonicMaps.Analysis.DyadicMaximalWeakOne
public import StationaryHarmonicMaps.Analysis.DyadicMaximalLebesgueDomination

/-!
# Original density moments from uniform good-lambda level control

A positive small parameter is selected from the original dimension and
exponent constants. The actual weak L1 bound and the proved finite-cap
absorption control the original maximal moment. Genuine differentiation
then controls the original density moment. The operator application must
produce the displayed uniform level inequality from its actual inputs.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

@[expose] def uniformGoodLambdaDenominator (N A D : ℕ) : ℕ :=
  4*(1+D)*(1+A)^N

@[expose] def uniformGoodLambdaMomentMajorant (n N A D : ℕ) : ℕ :=
  2*(1+A)^N*(uniformGoodLambdaDenominator N A D)^N*2^N*N*5^n

/-- Uniform actual maximal good-lambda levels give a genuine original density moment bound, with no original output moment premise. -/
@[expose] noncomputable def uniformGoodLambdaCoefficient (n : ℕ) (s A D δ : ℝ) : ℝ :=
  (A^s*δ^(-s)/(1-(D*δ)*A^s))*(((2 : ℝ)^s*s/(s-1))*(5 : ℝ)^n)

@[expose] noncomputable def uniformGoodLambdaParameter (s A D : ℝ) : ℝ :=
  min 1 (1/(2*D*A^s))

@[expose] noncomputable def uniformGoodLambdaMomentConstant (n : ℕ) (s A D : ℝ) : ℝ :=
  uniformGoodLambdaCoefficient n s A D (uniformGoodLambdaParameter s A D)

theorem uniformGoodLambdaCoefficient_pos (n : ℕ) (s A D δ : ℝ)
    (hs : 1<s) (hA : 1≤A) (hδ : 0<δ) (hAbsorb : (D*δ)*A^s<1) :
    0 < uniformGoodLambdaCoefficient n s A D δ := by
  have hA0 : 0<A := zero_lt_one.trans_le hA
  unfold uniformGoodLambdaCoefficient
  positivity

theorem original_moment_bound_of_uniform_maximal_goodLambda_parameter
    (n : ℕ) (s A D δ : ℝ) (hs : 1<s) (hA : 1≤A) (hD : 0<D)
    (hδ : 0<δ) (hδOne : δ≤1) (hAbsorb : (D*δ)*A^s<1) :
    ∀ (f g : Domain n → ℝ),
      Integrable f volume → Integrable g volume →
      (∀ᵐ x ∂volume,0≤f x) → (∀ᵐ x ∂volume,0≤g x) →
      (∫⁻ x,(ENNReal.ofReal (g x))^s)<∞ →
      (∀ δ : ℝ,0<δ → δ≤1 → ∀ L : ℝ,0<L →
        volume {x | ENNReal.ofReal (A*L)<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x ∧
          dyadicBallMaximal (fun y=>ENNReal.ofReal (g y)) x≤ENNReal.ofReal (δ*L)}≤
          ENNReal.ofReal (D*δ)*volume {x | ENNReal.ofReal L<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x}) →
      (∫⁻ x,(ENNReal.ofReal (f x))^s)≤ENNReal.ofReal (uniformGoodLambdaCoefficient n s A D δ)*(∫⁻ x,(ENNReal.ofReal (g x))^s) ∧
        (∫⁻ x,(ENNReal.ofReal (f x))^s)<∞ := by
  have hs0 : 0<s := zero_lt_one.trans hs
  have hA0 : 0<A := zero_lt_one.trans_le hA
  let K := A^s*δ^(-s)/(1-(D*δ)*A^s)
  let H := (((2 : ℝ)^s*s/(s-1))*(5 : ℝ)^n)
  let C := K*H
  have hK : 0<K := by dsimp only [K];positivity
  have hH : 0<H := by dsimp only [H];positivity
  have hC : 0<C := mul_pos hK hH
  intro f g hf hg hf0 hg0 hGMoment hGood
  let F := fun x=>ENNReal.ofReal (f x)
  let G := fun x=>ENNReal.ofReal (g x)
  let MF := dyadicBallMaximal F
  let MG := dyadicBallMaximal G
  have hF : AEMeasurable F volume := hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hG : AEMeasurable G volume := hg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hMF : Measurable MF := measurable_dyadicBallMaximal F hF
  have hMG : Measurable MG := measurable_dyadicBallMaximal G hG
  have hfInt0 : 0≤∫x,f x := integral_nonneg_of_ae hf0
  let W := (5 : ℝ)^n*(∫x,f x)
  have hW : 0≤W := mul_nonneg (pow_nonneg (by norm_num) n) hfInt0
  have hWeak (L : ℝ) (hL : 0<L) : volume {x | ENNReal.ofReal L<MF x}≤ENNReal.ofReal (W/L) := by
    have Hweak := dyadicBallMaximal_weak_one F L hL
    have hI : (∫⁻ x,F x)=ENNReal.ofReal (∫x,f x) :=
      (ofReal_integral_eq_lintegral_ofReal hf hf0).symm
    rw [hI,← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (by norm_num) n) hL.le)] at Hweak
    exact Hweak.trans_eq (by congr 1;dsimp only [W];ring)
  have hGMax := dyadicBallMaximal_strongLp_control G hG hs hGMoment
  have hLevel := hGood δ hδ hδOne
  have hMoment := finite_rpow_moment_of_goodLambda volume MF MG hMF.aemeasurable hMG.aemeasurable
    W hW hWeak s A δ (D*δ) hs hA hδ (mul_nonneg hD.le hδ.le) hAbsorb hLevel hGMax.2.2.1
  have hMaxBound : (∫⁻ x,(MF x)^s)≤ENNReal.ofReal C*(∫⁻ x,(G x)^s) := by
    calc
      _ ≤ ENNReal.ofReal K*(∫⁻ x,(MG x)^s) := hMoment.1
      _ ≤ ENNReal.ofReal K*(ENNReal.ofReal H*(∫⁻ x,(G x)^s)) :=
        mul_le_mul_of_nonneg_left hGMax.2.1 zero_le
      _ = _ := by rw [← mul_assoc,← ENNReal.ofReal_mul hK.le]
  have hDom := ae_ofReal_le_dyadicBallMaximal f hf hf0
  have hOrig : (∫⁻ x,(F x)^s)≤∫⁻ x,(MF x)^s :=
    lintegral_mono_ae (hDom.mono fun x hx=>ENNReal.rpow_le_rpow hx hs0.le)
  exact ⟨hOrig.trans hMaxBound,hOrig.trans_lt hMoment.2.1⟩

theorem uniformGoodLambdaDenominator_pos (N A D : ℕ) :
    0 < (uniformGoodLambdaDenominator N A D : ℝ) := by
  unfold uniformGoodLambdaDenominator
  positivity

theorem uniformGoodLambdaMomentMajorant_pos (n N A D : ℕ) (hN : 0<N) :
    0 < (uniformGoodLambdaMomentMajorant n N A D : ℝ) := by
  have hd : 0 < uniformGoodLambdaDenominator N A D := by
    unfold uniformGoodLambdaDenominator
    positivity
  have H : 0 < uniformGoodLambdaMomentMajorant n N A D := by
    unfold uniformGoodLambdaMomentMajorant
    positivity
  exact_mod_cast H

/-- A rational small parameter gives an integer moment coefficient for every
real exponent in the displayed finite range. -/
theorem uniformGoodLambda_numeric_parameter_bounds
    (n N A D : ℕ) (s : ℝ) (hs : 2≤s) (hsN : s≤(N : ℝ))
    (hA : 1≤(A : ℝ)) :
    let δ : ℝ := 1/(uniformGoodLambdaDenominator N A D : ℝ)
    0<δ ∧ δ≤1 ∧ ((D : ℝ)*δ)*(A : ℝ)^s<1 ∧
      uniformGoodLambdaCoefficient n s A D δ ≤
        (uniformGoodLambdaMomentMajorant n N A D : ℝ) := by
  let d : ℝ := uniformGoodLambdaDenominator N A D
  let b : ℝ := (1+(A : ℝ))^N
  let δ : ℝ := 1/d
  have hd : 0<d := uniformGoodLambdaDenominator_pos N A D
  have hb : 0<b := by dsimp only [b]; positivity
  have hdEq : d=4*(1+(D : ℝ))*b := by
    simp only [d,b,uniformGoodLambdaDenominator,Nat.cast_mul,Nat.cast_add,
      Nat.cast_one,Nat.cast_ofNat,Nat.cast_pow]
  have hD0 : 0≤(D : ℝ) := Nat.cast_nonneg D
  have hBaseOne : 1≤1+(A : ℝ) := by linarith only [hA]
  have hbOne : 1≤b := one_le_pow₀ hBaseOne
  have hdOne : 1≤d := by rw [hdEq]; nlinarith only [hD0,hbOne]
  have hδ : 0<δ := one_div_pos.mpr hd
  have hδOne : δ≤1 := (div_le_one hd).mpr hdOne
  have hs0 : 0≤s := by linarith
  have hsm : 0<s-1 := by linarith
  have hApow : (A : ℝ)^s≤b := by
    calc
      _≤(1+(A : ℝ))^s := Real.rpow_le_rpow (Nat.cast_nonneg A) (by linarith) hs0
      _≤(1+(A : ℝ))^(N : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hBaseOne hsN
      _=b := by rw [Real.rpow_natCast]
  have hDpow : δ^(-s)≤d^N := by
    have hEq : δ^(-s)=d^s := by
      rw [Real.rpow_neg_eq_inv_rpow]
      simp only [δ,one_div,inv_inv]
    rw [hEq]
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hdOne hsN
  have hScale : 4*(D : ℝ)*(A : ℝ)^s≤d := by
    calc
      _≤4*(D : ℝ)*b := mul_le_mul_of_nonneg_left hApow (by positivity)
      _≤4*(1+(D : ℝ))*b := by nlinarith
      _=d := hdEq.symm
  have hQuarter : ((D : ℝ)*δ)*(A : ℝ)^s≤1/4 := by
    have hEq : ((D : ℝ)*δ)*(A : ℝ)^s=((D : ℝ)*(A : ℝ)^s)/d := by
      dsimp only [δ]
      ring
    rw [hEq]
    apply (div_le_iff₀ hd).mpr
    nlinarith only [hScale]
  have hAbsorb : ((D : ℝ)*δ)*(A : ℝ)^s<1 := by linarith
  have hGap : 1/2≤1-((D : ℝ)*δ)*(A : ℝ)^s := by linarith
  have hGapPos : 0<1-((D : ℝ)*δ)*(A : ℝ)^s := by linarith
  have hNum : (A : ℝ)^s*δ^(-s)≤b*d^N :=
    mul_le_mul hApow hDpow (Real.rpow_nonneg hδ.le _) hb.le
  have hBpow : 0≤b*d^N := mul_nonneg hb.le (pow_nonneg hd.le _)
  have hK : (A : ℝ)^s*δ^(-s)/(1-((D : ℝ)*δ)*(A : ℝ)^s)≤2*b*d^N := by
    apply (div_le_iff₀ hGapPos).mpr
    have H := mul_le_mul_of_nonneg_left hGap (by positivity : 0≤2*b*d^N)
    nlinarith only [hNum,H]
  have hTwo : (2 : ℝ)^s≤(2 : ℝ)^N := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) hsN
  have hFrac : s/(s-1)≤(N : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0<s-1)).mpr
    have H : (N : ℝ)≤(N : ℝ)*(s-1) :=
      le_mul_of_one_le_right (Nat.cast_nonneg N) (by linarith)
    exact hsN.trans H
  have hH : (((2 : ℝ)^s*s/(s-1))*(5 : ℝ)^n)≤
      ((2 : ℝ)^N*(N : ℝ))*(5 : ℝ)^n := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hTwo hFrac (by positivity) (by positivity)) (by positivity)
  refine ⟨hδ,hδOne,hAbsorb,?_⟩
  unfold uniformGoodLambdaCoefficient
  have H := mul_le_mul hK hH (by positivity) (by positivity)
  refine H.trans_eq ?_
  simp only [uniformGoodLambdaMomentMajorant,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,b,d]
  ring

theorem effective_original_moment_bound_of_uniform_maximal_goodLambda
    (n N A D : ℕ) (s : ℝ) (hs : 2≤s) (hsN : s≤(N : ℝ))
    (hA : 1≤(A : ℝ)) (hD : 0<(D : ℝ)) :
    ∀ (f g : Domain n → ℝ),
      Integrable f volume → Integrable g volume →
      (∀ᵐ x ∂volume,0≤f x) → (∀ᵐ x ∂volume,0≤g x) →
      (∫⁻ x,(ENNReal.ofReal (g x))^s)<∞ →
      (∀ δ : ℝ,0<δ → δ≤1 → ∀ L : ℝ,0<L →
        volume {x | ENNReal.ofReal ((A : ℝ)*L)<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x ∧
          dyadicBallMaximal (fun y=>ENNReal.ofReal (g y)) x≤ENNReal.ofReal (δ*L)}≤
          ENNReal.ofReal ((D : ℝ)*δ)*volume {x | ENNReal.ofReal L<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x}) →
      (∫⁻ x,(ENNReal.ofReal (f x))^s)≤ENNReal.ofReal (uniformGoodLambdaMomentMajorant n N A D : ℝ)*(∫⁻ x,(ENNReal.ofReal (g x))^s) ∧
        (∫⁻ x,(ENNReal.ofReal (f x))^s)<∞ := by
  let δ : ℝ := 1/(uniformGoodLambdaDenominator N A D : ℝ)
  obtain ⟨hδ,hδOne,hAbsorb,hCoeff⟩ := uniformGoodLambda_numeric_parameter_bounds n N A D s hs hsN hA
  have hsOne : 1<s := by linarith
  have H := original_moment_bound_of_uniform_maximal_goodLambda_parameter
    n s (A : ℝ) (D : ℝ) δ hsOne hA hD hδ hδOne hAbsorb
  intro f g hf hg hf0 hg0 hGMoment hGood
  obtain ⟨hBound,hFinite⟩ := H f g hf hg hf0 hg0 hGMoment hGood
  refine ⟨hBound.trans ?_,hFinite⟩
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hCoeff) zero_le

theorem exists_original_moment_bound_of_uniform_maximal_goodLambda_explicit
    (n : ℕ) (s A D : ℝ) (hs : 1<s) (hA : 1≤A) (hD : 0<D) :
    ∃ C : ℝ,0<C ∧ C = uniformGoodLambdaMomentConstant n s A D ∧ ∀ (f g : Domain n → ℝ),
      Integrable f volume → Integrable g volume →
      (∀ᵐ x ∂volume,0≤f x) → (∀ᵐ x ∂volume,0≤g x) →
      (∫⁻ x,(ENNReal.ofReal (g x))^s)<∞ →
      (∀ δ : ℝ,0<δ → δ≤1 → ∀ L : ℝ,0<L →
        volume {x | ENNReal.ofReal (A*L)<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x ∧
          dyadicBallMaximal (fun y=>ENNReal.ofReal (g y)) x≤ENNReal.ofReal (δ*L)}≤
          ENNReal.ofReal (D*δ)*volume {x | ENNReal.ofReal L<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x}) →
      (∫⁻ x,(ENNReal.ofReal (f x))^s)≤ENNReal.ofReal C*(∫⁻ x,(ENNReal.ofReal (g x))^s) ∧
        (∫⁻ x,(ENNReal.ofReal (f x))^s)<∞ := by
  have hA0 : 0<A := zero_lt_one.trans_le hA
  let δ := uniformGoodLambdaParameter s A D
  have hδ : 0<δ := lt_min zero_lt_one (by positivity)
  have hδOne : δ≤1 := min_le_left _ _
  have hδSmall : δ≤1/(2*D*A^s) := min_le_right _ _
  have hAbsorb : (D*δ)*A^s<1 := by
    have H := (le_div_iff₀ (show 0<2*D*A^s by positivity)).mp hδSmall
    nlinarith only [H]
  exact ⟨uniformGoodLambdaMomentConstant n s A D,
    uniformGoodLambdaCoefficient_pos n s A D δ hs hA hδ hAbsorb,rfl,
    original_moment_bound_of_uniform_maximal_goodLambda_parameter n s A D δ hs hA hD hδ hδOne hAbsorb⟩

theorem exists_original_moment_bound_of_uniform_maximal_goodLambda
    (n : ℕ) (s A D : ℝ) (hs : 1<s) (hA : 1≤A) (hD : 0<D) :
    ∃ C : ℝ,0<C ∧ ∀ (f g : Domain n → ℝ),
      Integrable f volume → Integrable g volume →
      (∀ᵐ x ∂volume,0≤f x) → (∀ᵐ x ∂volume,0≤g x) →
      (∫⁻ x,(ENNReal.ofReal (g x))^s)<∞ →
      (∀ δ : ℝ,0<δ → δ≤1 → ∀ L : ℝ,0<L →
        volume {x | ENNReal.ofReal (A*L)<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x ∧
          dyadicBallMaximal (fun y=>ENNReal.ofReal (g y)) x≤ENNReal.ofReal (δ*L)}≤
          ENNReal.ofReal (D*δ)*volume {x | ENNReal.ofReal L<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x}) →
      (∫⁻ x,(ENNReal.ofReal (f x))^s)≤ENNReal.ofReal C*(∫⁻ x,(ENNReal.ofReal (g x))^s) ∧
        (∫⁻ x,(ENNReal.ofReal (f x))^s)<∞ := by
  obtain ⟨C,hC,_hCEq,H⟩ :=
    exists_original_moment_bound_of_uniform_maximal_goodLambda_explicit n s A D hs hA hD
  exact ⟨C,hC,H⟩


@[expose] noncomputable def effectiveUniformGoodLambdaMomentConstant
    (n N A D : ℕ) (s : ℝ) : ℝ :=
  if 2≤s ∧ s≤(N : ℝ) then (uniformGoodLambdaMomentMajorant n N A D : ℝ)
  else uniformGoodLambdaMomentConstant n s A D

theorem effectiveUniformGoodLambdaMomentConstant_eq_majorant
    (n N A D : ℕ) (s : ℝ) (hs : 2≤s) (hsN : s≤(N : ℝ)) :
    effectiveUniformGoodLambdaMomentConstant n N A D s =
      (uniformGoodLambdaMomentMajorant n N A D : ℝ) := by
  exact if_pos ⟨hs,hsN⟩

theorem effectiveUniformGoodLambdaMomentConstant_pos
    (n N A D : ℕ) (s : ℝ) (hN : 0<N) (hs : 1<s)
    (hA : 1≤(A : ℝ)) (hD : 0<(D : ℝ)) :
    0 < effectiveUniformGoodLambdaMomentConstant n N A D s := by
  unfold effectiveUniformGoodLambdaMomentConstant
  split_ifs
  · exact uniformGoodLambdaMomentMajorant_pos n N A D hN
  · obtain ⟨C,hC,hCEq,_H⟩ :=
      exists_original_moment_bound_of_uniform_maximal_goodLambda_explicit n s A D hs hA hD
    rwa [hCEq] at hC

theorem effective_uniform_maximal_goodLambda_moment_bound
    (n N A D : ℕ) (s : ℝ) (hs : 1<s)
    (hA : 1≤(A : ℝ)) (hD : 0<(D : ℝ)) :
    ∀ (f g : Domain n → ℝ),
      Integrable f volume → Integrable g volume →
      (∀ᵐ x ∂volume,0≤f x) → (∀ᵐ x ∂volume,0≤g x) →
      (∫⁻ x,(ENNReal.ofReal (g x))^s)<∞ →
      (∀ δ : ℝ,0<δ → δ≤1 → ∀ L : ℝ,0<L →
        volume {x | ENNReal.ofReal ((A : ℝ)*L)<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x ∧
          dyadicBallMaximal (fun y=>ENNReal.ofReal (g y)) x≤ENNReal.ofReal (δ*L)}≤
          ENNReal.ofReal ((D : ℝ)*δ)*volume {x | ENNReal.ofReal L<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x}) →
      (∫⁻ x,(ENNReal.ofReal (f x))^s)≤ENNReal.ofReal (effectiveUniformGoodLambdaMomentConstant n N A D s)*(∫⁻ x,(ENNReal.ofReal (g x))^s) ∧
        (∫⁻ x,(ENNReal.ofReal (f x))^s)<∞ := by
  by_cases hWindow : 2≤s ∧ s≤(N : ℝ)
  · rw [effectiveUniformGoodLambdaMomentConstant,if_pos hWindow]
    exact effective_original_moment_bound_of_uniform_maximal_goodLambda n N A D s
      hWindow.1 hWindow.2 hA hD
  · obtain ⟨C,_hC,hCEq,H⟩ :=
      exists_original_moment_bound_of_uniform_maximal_goodLambda_explicit n s A D hs hA hD
    rw [hCEq] at H
    simpa only [effectiveUniformGoodLambdaMomentConstant,if_neg hWindow] using H

end StationaryHarmonicMaps.Analysis

end

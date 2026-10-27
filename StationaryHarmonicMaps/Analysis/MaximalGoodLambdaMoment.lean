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

/-- Uniform actual maximal good-lambda levels give a genuine original density moment bound, with no original output moment premise. -/
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
  have hs0 : 0<s := zero_lt_one.trans hs
  have hA0 : 0<A := zero_lt_one.trans_le hA
  let δ := min 1 (1/(2*D*A^s))
  have hδ : 0<δ := lt_min zero_lt_one (by positivity)
  have hδOne : δ≤1 := min_le_left _ _
  have hδSmall : δ≤1/(2*D*A^s) := min_le_right _ _
  have hAbsorb : (D*δ)*A^s<1 := by
    have H := (le_div_iff₀ (show 0<2*D*A^s by positivity)).mp hδSmall
    nlinarith only [H]
  let K := A^s*δ^(-s)/(1-(D*δ)*A^s)
  let H := (((2 : ℝ)^s*s/(s-1))*(5 : ℝ)^n)
  let C := K*H
  have hK : 0<K := by dsimp only [K];positivity
  have hH : 0<H := by dsimp only [H];positivity
  have hC : 0<C := mul_pos hK hH
  refine ⟨C,hC,?_⟩
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

end StationaryHarmonicMaps.Analysis

end

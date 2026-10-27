module

public import StationaryHarmonicMaps.Analysis.WeakTailTruncation
public import StationaryHarmonicMaps.Analysis.DyadicMaximalFinite

/-!
# Finite-cap good-lambda absorption

The original weak L1 tail supplies a genuinely finite capped moment.
The displayed good-lambda inequality is integrated at positive real
levels for that actual cap. Finite scalar absorption gives a bound
uniform in the cap. Real representatives of the original G are used
only after its finite moment has supplied genuine AE finiteness.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem moment_le_of_real_level_inequality {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g h : X → ℝ)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hh : AEMeasurable h μ)
    (hf0 : ∀ᵐ x ∂μ,0≤f x) (hg0 : ∀ᵐ x ∂μ,0≤g x) (hh0 : ∀ᵐ x ∂μ,0≤h x)
    {s : ℝ} (hs : 0<s) (e : ℝ)
    (hLevel : ∀ t : ℝ,0<t → μ {x | t<f x}≤μ {x | t<g x}+ENNReal.ofReal e*μ {x | t<h x}) :
    (∫⁻ x,ENNReal.ofReal ((f x)^s) ∂μ)≤
      (∫⁻ x,ENNReal.ofReal ((g x)^s) ∂μ)+ENNReal.ofReal e*(∫⁻ x,ENNReal.ofReal ((h x)^s) ∂μ) := by
  have hLf := lintegral_rpow_eq_lintegral_meas_lt_mul μ hf0 hf hs
  have hLg := lintegral_rpow_eq_lintegral_meas_lt_mul μ hg0 hg hs
  have hLh := lintegral_rpow_eq_lintegral_meas_lt_mul μ hh0 hh hs
  have hTailG : Measurable (fun t : ℝ=>μ {x | t<g x}) :=
    Antitone.measurable (fun _ _ hst=>measure_mono (fun _ hx=>hst.trans_lt hx))
  have hWeight : Measurable (fun t : ℝ=>ENNReal.ofReal (t^(s-1))) :=
    (measurable_id.pow_const (s-1)).ennreal_ofReal
  have hWeighted : Measurable (fun t : ℝ=>μ {x | t<g x}*ENNReal.ofReal (t^(s-1))) := hTailG.mul hWeight
  rw [hLf,hLg,hLh]
  calc
    _ ≤ ENNReal.ofReal s*∫⁻ t in Ioi (0 : ℝ),
        (μ {x | t<g x}+ENNReal.ofReal e*μ {x | t<h x})*ENNReal.ofReal (t^(s-1)) := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_le_mul_of_nonneg_right (hLevel t ht) zero_le
    _ = ENNReal.ofReal s*((∫⁻ t in Ioi (0 : ℝ),μ {x | t<g x}*ENNReal.ofReal (t^(s-1)))+
        ENNReal.ofReal e*(∫⁻ t in Ioi (0 : ℝ),μ {x | t<h x}*ENNReal.ofReal (t^(s-1)))) := by
      simp_rw [add_mul,mul_assoc]
      rw [lintegral_add_left hWeighted,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by rw [mul_add];ac_rfl

private theorem finite_moment_absorption (I J : ℝ≥0∞) (hI : I≠∞) (hJ : J≠∞)
    (K e : ℝ) (hK : 0≤K) (he : 0≤e) (he1 : e<1)
    (h : I≤ENNReal.ofReal K*J+ENNReal.ofReal e*I) :
    I≤ENNReal.ofReal (K/(1-e))*J := by
  have hRhs : ENNReal.ofReal K*J+ENNReal.ofReal e*I≠∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI⟩
  have H := ENNReal.toReal_mono hRhs h
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI),ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hK,ENNReal.toReal_ofReal he] at H
  have hDen : 0<1-e := sub_pos.mpr he1
  have hReal : I.toReal≤(K/(1-e))*J.toReal := by
    rw [div_mul_eq_mul_div,le_div_iff₀ hDen]
    nlinarith only [H]
  rw [← ENNReal.ofReal_toReal hI,← ENNReal.ofReal_toReal hJ,
    ← ENNReal.ofReal_mul (div_nonneg hK hDen.le)]
  exact ENNReal.ofReal_le_ofReal hReal

/-- Original weak-L1 and good-lambda tails give a uniform bound on every actual finite cap; the original F moment is not assumed finite. -/
theorem lintegral_min_rpow_le_of_goodLambda {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F G : X → ℝ≥0∞) (hF : AEMeasurable F μ) (hG : AEMeasurable G μ)
    (W : ℝ) (hW : 0≤W)
    (hWeak : ∀ t : ℝ,0<t → μ {x | ENNReal.ofReal t<F x}≤ENNReal.ofReal (W/t))
    (s A δ ε : ℝ) (hs : 1<s) (hA : 1≤A) (hδ : 0<δ) (hε : 0≤ε)
    (hAbsorb : ε*A^s<1)
    (hGood : ∀ t : ℝ,0<t →
      μ {x | ENNReal.ofReal (A*t)<F x ∧ G x≤ENNReal.ofReal (δ*t)}≤
        ENNReal.ofReal ε*μ {x | ENNReal.ofReal t<F x})
    (hGMoment : (∫⁻ x,(G x)^s ∂μ)<∞) (T : ℝ) (hT : 0<T) :
    (∫⁻ x,(min (F x) (ENNReal.ofReal T))^s ∂μ)≤
      ENNReal.ofReal (A^s*δ^(-s)/(1-ε*A^s))*(∫⁻ x,(G x)^s ∂μ) := by
  have hs0 : 0<s := zero_lt_one.trans hs
  have hA0 : 0<A := zero_lt_one.trans_le hA
  let H := fun x=>min (F x) (ENNReal.ofReal T)
  let f := fun x=>(H x).toReal
  let g := fun x=>(G x).toReal
  have hHFinite (x : X) : H x≠∞ := ne_of_lt ((min_le_right _ _).trans_lt ENNReal.ofReal_lt_top)
  have hf : AEMeasurable f μ := (hF.min aemeasurable_const).ennreal_toReal
  have hg : AEMeasurable g μ := hG.ennreal_toReal
  have hf0 (x : X) : 0≤f x := ENNReal.toReal_nonneg
  have hg0 (x : X) : 0≤g x := ENNReal.toReal_nonneg
  have hfT (x : X) : f x≤T := by
    have Hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_right (F x) (ENNReal.ofReal T))
    simpa only [ENNReal.toReal_ofReal hT.le] using Hle
  have hGFinite : ∀ᵐ x ∂μ,G x≠∞ := ae_ne_top_of_finite_positive_moment μ G hG hs0 hGMoment
  have hLevel (t : ℝ) (ht : 0<t) :
      μ {x | t<f x/A}≤μ {x | t<g x/δ}+ENNReal.ofReal ε*μ {x | t<f x} := by
    by_cases htT : t<T
    · have hSetF : {x | ENNReal.ofReal t<F x}={x | t<f x} := by
        ext x
        have hToReal := ENNReal.ofReal_lt_iff_lt_toReal ht.le (hHFinite x)
        change ENNReal.ofReal t<F x ↔ t<(H x).toReal
        rw [← hToReal]
        change ENNReal.ofReal t<F x ↔ ENNReal.ofReal t<min (F x) (ENNReal.ofReal T)
        rw [lt_min_iff]
        exact ⟨fun hx=>⟨hx,ENNReal.ofReal_lt_ofReal_iff hT |>.mpr htT⟩,And.left⟩
      have hSetG : μ {x | ENNReal.ofReal (δ*t)<G x}=μ {x | t<g x/δ} := by
        apply measure_congr
        filter_upwards [hGFinite] with x hx
        change (ENNReal.ofReal (δ*t)<G x)=(t<g x/δ)
        apply propext
        rw [ENNReal.ofReal_lt_iff_lt_toReal (mul_pos hδ ht).le hx,lt_div_iff₀ hδ]
        change δ*t<g x ↔ t*δ<g x
        rw [mul_comm δ t]
      have hSub : {x | t<f x/A}⊆
          {x | ENNReal.ofReal (δ*t)<G x}∪
            {x | ENNReal.ofReal (A*t)<F x ∧ G x≤ENNReal.ofReal (δ*t)} := by
        intro x hx
        have htf : A*t<f x := by simpa only [mul_comm] using (lt_div_iff₀ hA0).mp hx
        have hFlt : ENNReal.ofReal (A*t)<F x :=
          ((ENNReal.ofReal_lt_iff_lt_toReal (mul_pos hA0 ht).le (hHFinite x)).mpr htf).trans_le (min_le_left _ _)
        by_cases hxG : ENNReal.ofReal (δ*t)<G x
        · exact Or.inl hxG
        · exact Or.inr ⟨hFlt,le_of_not_gt hxG⟩
      calc
        _ ≤ μ ({x | ENNReal.ofReal (δ*t)<G x}∪
            {x | ENNReal.ofReal (A*t)<F x ∧ G x≤ENNReal.ofReal (δ*t)}) := measure_mono hSub
        _ ≤ μ {x | ENNReal.ofReal (δ*t)<G x}+
            μ {x | ENNReal.ofReal (A*t)<F x ∧ G x≤ENNReal.ofReal (δ*t)} := measure_union_le _ _
        _ ≤ _ := by rw [hSetG];exact add_le_add le_rfl (by simpa only [hSetF] using hGood t ht)
    · have hEmpty : {x | t<f x/A}=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hDiv : f x/A≤f x := (div_le_self (hf0 x) hA).trans le_rfl
        exact not_lt_of_ge (hDiv.trans ((hfT x).trans (le_of_not_gt htT))) hx
      rw [hEmpty,measure_empty]
      exact zero_le
  have hLayer := moment_le_of_real_level_inequality μ (fun x=>f x/A) (fun x=>g x/δ) f
    (hf.div_const A) (hg.div_const δ) hf
    (Eventually.of_forall fun x=>div_nonneg (hf0 x) hA0.le)
    (Eventually.of_forall fun x=>div_nonneg (hg0 x) hδ.le)
    (Eventually.of_forall hf0) hs0 ε hLevel
  have hCapMoment : (∫⁻ x,(H x)^s ∂μ)=∫⁻ x,ENNReal.ofReal ((f x)^s) ∂μ := by
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_rpow_of_nonneg (hf0 x) hs0.le,ENNReal.ofReal_toReal (hHFinite x)]
  have hGMomentEq : (∫⁻ x,(G x)^s ∂μ)=∫⁻ x,ENNReal.ofReal ((g x)^s) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hGFinite] with x hx
    rw [← ENNReal.ofReal_rpow_of_nonneg (hg0 x) hs0.le,ENNReal.ofReal_toReal hx]
  have hScaled (v : X → ℝ) (hv : ∀ x,0≤v x) (a : ℝ) (ha : 0<a) :
      (∫⁻ x,ENNReal.ofReal ((v x/a)^s) ∂μ)=
        ENNReal.ofReal (a^(-s))*(∫⁻ x,ENNReal.ofReal ((v x)^s) ∂μ) := by
    have hPoint (x : X) : (v x/a)^s=a^(-s)*(v x)^s := by
      rw [Real.div_rpow (hv x) ha.le,Real.rpow_neg ha.le,div_eq_mul_inv,mul_comm]
    simp_rw [hPoint,ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [hScaled f hf0 A hA0,hScaled g hg0 δ hδ,← hCapMoment,← hGMomentEq] at hLayer
  have hAPower : A^s*A^(-s)=1 := by
    rw [Real.rpow_neg hA0.le,mul_inv_cancel₀ (Real.rpow_pos_of_pos hA0 s).ne']
  have hAE : ENNReal.ofReal (A^s)*ENNReal.ofReal (A^(-s))=1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hA0.le _),hAPower,ENNReal.ofReal_one]
  have hAbs := mul_le_mul_of_nonneg_left hLayer (show 0≤ENNReal.ofReal (A^s) from zero_le)
  rw [← mul_assoc,hAE,one_mul,mul_add] at hAbs
  have hCoeff :
      ENNReal.ofReal (A^s)*(ENNReal.ofReal (δ^(-s))*(∫⁻ x,(G x)^s ∂μ))+
        ENNReal.ofReal (A^s)*(ENNReal.ofReal ε*(∫⁻ x,(H x)^s ∂μ))=
      ENNReal.ofReal (A^s*δ^(-s))*(∫⁻ x,(G x)^s ∂μ)+
        ENNReal.ofReal (ε*A^s)*(∫⁻ x,(H x)^s ∂μ) := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hA0.le _),ENNReal.ofReal_mul hε]
    ac_rfl
  rw [hCoeff] at hAbs
  have hCapFinite : (∫⁻ x,(H x)^s ∂μ)≠∞ :=
    (lintegral_min_rpow_lt_top_of_weak_one μ F hF W hW hWeak hs T hT).ne
  exact finite_moment_absorption _ _ hCapFinite hGMoment.ne _ _ (by positivity)
    (mul_nonneg hε (Real.rpow_nonneg hA0.le _)) hAbsorb hAbs

end StationaryHarmonicMaps.Analysis

end

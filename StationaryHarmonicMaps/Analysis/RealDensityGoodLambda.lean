module

public import StationaryHarmonicMaps.Analysis.DyadicMaximalWhitney
public import StationaryHarmonicMaps.Analysis.DyadicMaximalNearFar
public import StationaryHarmonicMaps.Analysis.MaximalGoodPointBallEnergyReal

/-!
# Good-lambda control from genuine real near and far densities

The local decomposition supplies actual integrable nonnegative densities.
Nearby good points control their original ball averages, and the actual
Whitney cover aggregates the resulting weak maximal estimates.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

@[expose] def densityGoodLambdaAmplitudeReal (n : ℕ) (C : ℝ) : ℝ :=
  1 + (64 : ℝ)^n + 16*C*(64 : ℝ)^n

@[expose] def densityGoodLambdaAmplitude (n c : ℕ) : ℕ :=
  1 + 64^n + 16*c*64^n

@[expose] def densityGoodLambdaTailFactor (n : ℕ) : ℕ :=
  1 + 4*5^n*64^n*1536^n

theorem densityGoodLambdaAmplitude_cast (n c : ℕ) :
    (densityGoodLambdaAmplitude n c : ℝ) = densityGoodLambdaAmplitudeReal n c := by
  simp only [densityGoodLambdaAmplitude, densityGoodLambdaAmplitudeReal,
    Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul]

theorem densityGoodLambdaAmplitude_one_lt (n : ℕ) (C : ℝ) (hC : 0<C) :
    1 < densityGoodLambdaAmplitudeReal n C := by
  unfold densityGoodLambdaAmplitudeReal
  have hPow : 0 < (64 : ℝ)^n := pow_pos (by norm_num) _
  nlinarith

theorem densityGoodLambdaTailFactor_pos (n : ℕ) :
    0 < (densityGoodLambdaTailFactor n : ℝ) := by
  unfold densityGoodLambdaTailFactor
  positivity

/-- A real nonnegative near/far factory produces an actual full-scale good-lambda estimate, with dimensional constants fixed before the densities. -/
theorem exists_real_density_goodLambda_constants_explicit (n : ℕ) (hn : 0<n) (C : ℝ) (hC : 0<C) :
    ∃A D : ℝ,1<A ∧ 0<D ∧
      A = densityGoodLambdaAmplitudeReal n C ∧ D = (densityGoodLambdaTailFactor n : ℝ) ∧
      ∀(f k : Domain n → ℝ),
      Integrable f volume → Integrable k volume → (∀x,0≤f x) → (∀x,0≤k x) →
      (∀(a : Domain n) (R : ℝ),0<R → ∃g h : Domain n → ℝ,
        Integrable g volume ∧ Integrable h volume ∧ (∀x,0≤g x) ∧ (∀x,0≤h x) ∧
        (∀ᵐx∂volume,f x≤2*g x+2*h x) ∧
        (∫x,g x)≤∫x in ball a (256*R),k x ∧
        ∀ᵐx∂volume.restrict (ball a R),h x≤2*C*(volume.real (ball a (256*R)))⁻¹*
          ((∫y in ball a (256*R),f y)+(∫y in ball a (256*R),k y))) →
      ∀(L δ : ℝ),0<L → 0≤δ → δ≤1 →
        volume {x | ENNReal.ofReal (A*L)<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x ∧
          dyadicBallMaximal (fun y=>ENNReal.ofReal (k y)) x≤ENNReal.ofReal (δ*L)}≤
        ENNReal.ofReal (D*δ)*volume {x | ENNReal.ofReal L<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x} := by
  let a₀ : ℝ := (64:ℝ)^n
  let b₀ : ℝ := 4*C*a₀
  let A : ℝ := 1+a₀+4*b₀
  let D : ℝ := 1+4*(5:ℝ)^n*a₀*(1536:ℝ)^n
  have ha : 0<a₀ := pow_pos (by norm_num) _
  have hb : 0<b₀ := by dsimp [b₀];positivity
  have hA : 1<A := by dsimp [A];linarith
  have hD : 0<D := by dsimp [D];positivity
  refine ⟨A,D,hA,hD,?_,?_,?_⟩
  · dsimp only [A,b₀,a₀,densityGoodLambdaAmplitudeReal]
    ring
  · simp only [D,a₀,densityGoodLambdaTailFactor,Nat.cast_add,Nat.cast_one,
      Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
  intro f k hf hk hf0 hk0 Hresponse L δ hL hδ hδ1
  let fE := fun x=>ENNReal.ofReal (f x)
  let kE := fun x=>ENNReal.ofReal (k x)
  have hfE : AEMeasurable fE volume := hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hFinite : (∫⁻x,fE x)≠∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hf0)]
    exact ENNReal.ofReal_ne_top
  apply dyadic_goodLambda_of_whitney_local_measure n hn fE kE hfE hFinite L A δ hL hA.le _
  intro a y r hr hy hGood hNonempty
  obtain ⟨z,hzB,_hzHigh,hzGood⟩ := hNonempty
  have hzDist : dist z a≤20*r := by have H : dist z a<5*r := hzB;linarith
  obtain ⟨g,h,hg,_hh,hg0,hh0,hSplit,hNear,hFar⟩ := Hresponse a (6*r) (by positivity)
  have hRad : 256*(6*r)=1536*r := by ring
  rw [hRad] at hNear hFar
  have hR : r≤1536*r := by linarith
  obtain ⟨hFk,hFavg⟩ := ball_integral_average_le_of_dyadic_maximal_goodpoint f hf
    (Eventually.of_forall hf0) a y r (1536*r) hr hy hR L hL.le hGood
  obtain ⟨hKk,hKavg⟩ := ball_integral_average_le_of_dyadic_maximal_goodpoint k hk
    (Eventually.of_forall hk0) a z r (1536*r) hr hzDist hR (δ*L) (mul_nonneg hδ hL.le) hzGood
  have hFarReal : ∀ᵐx∂volume.restrict (ball a (6*r)),h x≤b₀*L := by
    filter_upwards [hFar] with x hx
    have hSum : (volume.real (ball a (1536*r)))⁻¹*
        ((∫y in ball a (1536*r),f y)+(∫y in ball a (1536*r),k y))≤2*a₀*L := by
      rw [mul_add]
      have HD := mul_le_mul_of_nonneg_right hδ1 (mul_nonneg ha.le hL.le)
      dsimp only [a₀] at HD ⊢
      nlinarith only [hFavg,hKavg,HD]
    calc
      _ ≤ 2*C*((volume.real (ball a (1536*r)))⁻¹*
          ((∫y in ball a (1536*r),f y)+(∫y in ball a (1536*r),k y))) := by nlinarith only [hx]
      _ ≤ 2*C*(2*a₀*L) := mul_le_mul_of_nonneg_left hSum (by positivity)
      _ = _ := by dsimp only [b₀];ring
  have hSplitE : ∀ᵐx∂volume.restrict (ball a (6*r)),fE x≤2*ENNReal.ofReal (g x)+2*ENNReal.ofReal (h x) := by
    filter_upwards [ae_restrict_of_ae hSplit] with x hx
    calc
      _ ≤ ENNReal.ofReal (2*g x+2*h x) := ENNReal.ofReal_le_ofReal hx
      _ = _ := by rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) (hg0 x)) (mul_nonneg (by norm_num) (hh0 x)),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)];norm_num
  have hFarE : ∀ᵐx∂volume.restrict (ball a (6*r)),ENNReal.ofReal (h x)≤ENNReal.ofReal (b₀*L) :=
    hFarReal.mono (fun _ hx=>ENNReal.ofReal_le_ofReal hx)
  have hAA : (64:ℝ)^n≤A := by change a₀≤A;dsimp only [A];linarith
  have hAB : 4*b₀≤A := by dsimp only [A];linarith
  have hLocal := (local_dyadic_maximal_superlevel_measure_of_near_far fE
    (fun x=>ENNReal.ofReal (g x)) (fun x=>ENNReal.ofReal (h x))
    hg.aestronglyMeasurable.aemeasurable.ennreal_ofReal a y r hr hy L A b₀ hL hb.le hAA hAB hGood hSplitE hFarE).2
  have hSub : (ball a (5*r)∩{x | ENNReal.ofReal (A*L)<dyadicBallMaximal fE x ∧
      dyadicBallMaximal kE x≤ENNReal.ofReal (δ*L)})⊆
      (ball a (5*r)∩{x | ENNReal.ofReal (A*L)<dyadicBallMaximal fE x}) := fun _ hx=>⟨hx.1,hx.2.1⟩
  have hNearE : (∫⁻x,ENNReal.ofReal (g x))≤
      ENNReal.ofReal (a₀*(δ*L))*volume (ball a (1536*r)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall hg0)]
    calc
      _ ≤ ENNReal.ofReal (a₀*(δ*L)*volume.real (ball a (1536*r))) :=
        ENNReal.ofReal_le_ofReal (hNear.trans hKk)
      _ = _ := by
        change ENNReal.ofReal (_ * (volume _).toReal)=_
        rw [ENNReal.ofReal_mul (mul_nonneg ha.le (mul_nonneg hδ hL.le)),ENNReal.ofReal_toReal measure_ball_ne_top]
  have hVol : volume (ball a (1536*r))=ENNReal.ofReal ((1536:ℝ)^n)*volume (ball a r) := by
    rw [Measure.addHaar_ball_of_pos volume a (by positivity : 0<1536*r),Measure.addHaar_ball_of_pos volume a hr]
    simp only [finrank_euclideanSpace,Fintype.card_fin,mul_pow,
      ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0:ℝ)≤1536) n),mul_assoc]
  have hCoefficient : 4*(5:ℝ)^n/(A*L)*(a₀*(δ*L))*(1536:ℝ)^n≤D*δ := by
    have hA0 : 0<A := lt_trans (by norm_num) hA
    have hCancel : 4*(5:ℝ)^n/(A*L)*(a₀*(δ*L))*(1536:ℝ)^n=
        (4*(5:ℝ)^n*a₀*(1536:ℝ)^n)*δ/A := by field_simp
    rw [hCancel]
    apply (div_le_iff₀ hA0).mpr
    have hNonneg : 0≤4*(5:ℝ)^n*a₀*(1536:ℝ)^n := by positivity
    dsimp only [D]
    have hBase : (4*(5:ℝ)^n*a₀*(1536:ℝ)^n)*δ≤(1+4*(5:ℝ)^n*a₀*(1536:ℝ)^n)*δ := by nlinarith only [hδ]
    exact hBase.trans (le_mul_of_one_le_right (mul_nonneg (by positivity) hδ) hA.le)
  calc
    _ ≤ volume (ball a (5*r)∩{x | ENNReal.ofReal (A*L)<dyadicBallMaximal fE x}) := measure_mono hSub
    _ ≤ ENNReal.ofReal (4*(5:ℝ)^n/(A*L))*(∫⁻x,ENNReal.ofReal (g x)) := hLocal
    _ ≤ ENNReal.ofReal (4*(5:ℝ)^n/(A*L))*(ENNReal.ofReal (a₀*(δ*L))*volume (ball a (1536*r))) :=
      mul_le_mul_of_nonneg_left hNearE zero_le
    _ = ENNReal.ofReal (4*(5:ℝ)^n/(A*L)*(a₀*(δ*L))*(1536:ℝ)^n)*volume (ball a r) := by
      rw [hVol,ENNReal.ofReal_mul (by positivity : 0≤4*(5:ℝ)^n/(A*L)*(a₀*(δ*L))),
        ENNReal.ofReal_mul (by positivity : 0≤4*(5:ℝ)^n/(A*L))]
      ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hCoefficient) zero_le

theorem exists_real_density_goodLambda_constants (n : ℕ) (hn : 0<n) (C : ℝ) (hC : 0<C) :
    ∃A D : ℝ,1<A ∧ 0<D ∧ ∀(f k : Domain n → ℝ),
      Integrable f volume → Integrable k volume → (∀x,0≤f x) → (∀x,0≤k x) →
      (∀(a : Domain n) (R : ℝ),0<R → ∃g h : Domain n → ℝ,
        Integrable g volume ∧ Integrable h volume ∧ (∀x,0≤g x) ∧ (∀x,0≤h x) ∧
        (∀ᵐx∂volume,f x≤2*g x+2*h x) ∧
        (∫x,g x)≤∫x in ball a (256*R),k x ∧
        ∀ᵐx∂volume.restrict (ball a R),h x≤2*C*(volume.real (ball a (256*R)))⁻¹*
          ((∫y in ball a (256*R),f y)+(∫y in ball a (256*R),k y))) →
      ∀(L δ : ℝ),0<L → 0≤δ → δ≤1 →
        volume {x | ENNReal.ofReal (A*L)<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x ∧
          dyadicBallMaximal (fun y=>ENNReal.ofReal (k y)) x≤ENNReal.ofReal (δ*L)}≤
        ENNReal.ofReal (D*δ)*volume {x | ENNReal.ofReal L<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x} := by
  obtain ⟨A,D,hA,hD,_hAEq,_hDEq,H⟩ :=
    exists_real_density_goodLambda_constants_explicit n hn C hC
  exact ⟨A,D,hA,hD,H⟩

theorem effective_real_density_goodLambda_constants
    (n : ℕ) (hn : 0<n) (c : ℕ) (hc : 0<(c : ℝ)) :
    let A : ℝ := densityGoodLambdaAmplitude n c
    let D : ℝ := densityGoodLambdaTailFactor n
    ∀(f k : Domain n → ℝ),
      Integrable f volume → Integrable k volume → (∀x,0≤f x) → (∀x,0≤k x) →
      (∀(a : Domain n) (R : ℝ),0<R → ∃g h : Domain n → ℝ,
        Integrable g volume ∧ Integrable h volume ∧ (∀x,0≤g x) ∧ (∀x,0≤h x) ∧
        (∀ᵐx∂volume,f x≤2*g x+2*h x) ∧
        (∫x,g x)≤∫x in ball a (256*R),k x ∧
        ∀ᵐx∂volume.restrict (ball a R),h x≤2*(c : ℝ)*(volume.real (ball a (256*R)))⁻¹*
          ((∫y in ball a (256*R),f y)+(∫y in ball a (256*R),k y))) →
      ∀(L δ : ℝ),0<L → 0≤δ → δ≤1 →
        volume {x | ENNReal.ofReal (A*L)<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x ∧
          dyadicBallMaximal (fun y=>ENNReal.ofReal (k y)) x≤ENNReal.ofReal (δ*L)}≤
        ENNReal.ofReal (D*δ)*volume {x | ENNReal.ofReal L<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x} := by
  obtain ⟨A,D,_hA,_hD,hAEq,hDEq,H⟩ :=
    exists_real_density_goodLambda_constants_explicit n hn (c : ℝ) hc
  rw [hAEq,hDEq,← densityGoodLambdaAmplitude_cast] at H
  exact H

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.SobolevOrthogonalFrame
public import StationaryHarmonicMaps.Analysis.ZeroEnergyRepresentative
public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Constant orientation signs of actual Sobolev maps

A native W1,2 map into the two points of the real unit sphere has zero
actual weak gradient. Whole-ball Poincare then gives one almost-everywhere
constant sign, including a zero-dimensional native domain.
-/

public section

open HarmonicMaps MeasureTheory Filter
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- An actual two-point-valued native Sobolev map has zero original weak columns. -/
theorem ae_zero_gradient_of_sign_values {n : ℕ} {Ω : OpenDomain n}
    (u : Domain n → Ambient 1) (Du : Domain n → Gradient n 1)
    (hu : MemW12Loc Ω u Du)
    (hsign : ∀ᵐ x ∂volume.restrict Ω.val,
      u x = EuclideanSpace.single (0 : Fin 1) 1 ∨ u x = -EuclideanSpace.single (0 : Fin 1) 1) :
    ∀ᵐ x ∂volume.restrict Ω.val, ∀ i, Du x i = 0 := by
  let e : Ambient 1 := EuclideanSpace.single (0 : Fin 1) 1
  let C : Ambient 1 → Ambient 1 := fun z => ((z 0)^2 - 1) • e
  let π : Ambient 1 →L[ℝ] ℝ := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0
  have hπ : ContDiff ℝ 1 (fun z : Ambient 1 => z (0 : Fin 1)) := π.contDiff
  have hC : ContDiff ℝ 1 C := ((hπ.pow 2).sub contDiff_const).smul contDiff_const
  have hDC (z v : Ambient 1) : fderiv ℝ C z v = ((2 * z 0) * v 0) • e := by
    have H := congrArg (fun D : Ambient 1 →L[ℝ] Ambient 1 => D v)
      ((((π.hasFDerivAt (x := z)).pow 2).sub_const 1).smul_const e).fderiv
    simpa [C, π, pow_one] using H
  let χ : ContDiffBump (0 : Ambient 1) :=
    { rIn := 2, rOut := 3, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let F : Ambient 1 → Ambient 1 := fun z => χ z • C z
  have hF : ContDiff ℝ 1 F := χ.contDiff.smul hC
  have hcF : HasCompactSupport F := χ.hasCompactSupport.smul_right
  have hz : ∀ᵐ x ∂volume.restrict Ω.val, F (u x) = 0 := by
    filter_upwards [hsign] with x hx
    rcases hx with hx | hx
    · simp only [F, C, hx, PiLp.single_apply, ite_true, one_pow, sub_self, zero_smul, smul_zero]
    · simp only [F, C, hx, PiLp.neg_apply, PiLp.single_apply, ite_true, neg_sq, one_pow,
        sub_self, zero_smul, smul_zero]
  have hzero := ae_fderiv_eq_zero_of_comp_eq_zero hu F hF hcF hz
  filter_upwards [hzero, hsign] with x hx hs i
  have hnorm : ‖u x‖ = 1 := by
    rcases hs with hs | hs <;> simp only [hs, norm_neg, PiLp.norm_single, norm_one]
  have hball : u x ∈ Metric.ball (0 : Ambient 1) χ.rIn := by
    change dist (u x) 0 < 2
    rw [dist_zero_right, hnorm]
    norm_num
  have hEq : F =ᶠ[𝓝 (u x)] C :=
    (χ.eventuallyEq_one_of_mem_ball hball).mono fun z hz => by
      change χ z = (1 : ℝ) at hz
      change χ z • C z = C z
      rw [hz, one_smul]
  have HD := hx i
  rw [hEq.fderiv_eq, hDC] at HD
  have hc := congrArg (fun v : Ambient 1 => v (0 : Fin 1)) HD
  have hprod : (2 * (u x) 0) * (Du x i) 0 = 0 := by
    simpa only [e, PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul, mul_one,
      PiLp.zero_apply] using hc
  have hu0 : (u x) 0 ≠ 0 := by
    rcases hs with hs | hs <;> simp only [hs, PiLp.neg_apply, PiLp.single_apply, ite_true] <;> norm_num
  have hd0 : (Du x i) 0 = 0 := (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero (by norm_num) hu0)
  apply PiLp.ext
  intro j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  simpa only [hj, PiLp.zero_apply] using hd0

/-- On a positive-radius native ball the actual sign is one constant almost everywhere. -/
theorem exists_constant_sign_of_memW12 {n : ℕ} (a : Domain n) {R : ℝ} (hR : 0 < R)
    (u : Domain n → Ambient 1) (Du : Domain n → Gradient n 1)
    (hu : MemW12 (ballDomain a R) u Du)
    (hsign : ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      u x = EuclideanSpace.single (0 : Fin 1) 1 ∨ u x = -EuclideanSpace.single (0 : Fin 1) 1) :
    ∃ c : Ambient 1,
      (c = EuclideanSpace.single (0 : Fin 1) 1 ∨ c = -EuclideanSpace.single (0 : Fin 1) 1) ∧
      u =ᵐ[volume.restrict (Metric.ball a R)] (fun _ => c) := by
  have hD := ae_zero_gradient_of_sign_values u Du hu.to_memW12Loc hsign
  have henergy : (∫ x in Metric.ball a R, hsNormSq (Du x)) = 0 := by
    have H : (fun x => hsNormSq (Du x)) =ᵐ[volume.restrict (Metric.ball a R)] (fun _ => (0 : ℝ)) := by
      filter_upwards [hD] with x hx
      simp only [hsNormSq, hx, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
    rw [integral_congr_ae H, integral_zero]
  have hmean := ae_eq_ballMean_of_zero_energy a hR hu henergy
  let c := ⨍ y in Metric.ball a R, u y
  have hne : volume.restrict (Metric.ball a R) ≠ (0 : Measure (Domain n)) :=
    (Measure.restrict_eq_zero).not.mpr (Metric.measure_ball_pos volume a hR).ne'
  letI : (ae (volume.restrict (Metric.ball a R))).NeBot := ae_neBot.mpr hne
  obtain ⟨x, hs, hc⟩ := (hsign.and hmean).exists
  refine ⟨c, ?_, hmean⟩
  rcases hs with hs | hs
  · exact Or.inl (hc.symm.trans hs)
  · exact Or.inr (hc.symm.trans hs)


/-- A genuine bounded native map has a constant sign under any C1 two-point-valued observable. -/
theorem exists_constant_sign_of_c1_observable {n m : ℕ}
    (a : Domain n) {R : ℝ} (hR : 0 < R)
    (p : Domain n → Ambient m) (Dp : Domain n → Gradient n m)
    (hp : MemW12 (ballDomain a R) p Dp) (M : ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (Metric.ball a R), ‖p x‖ ≤ M)
    (f : Ambient m → Ambient 1) (hf : ContDiff ℝ 1 f)
    (hsign : ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      f (p x) = EuclideanSpace.single (0 : Fin 1) 1 ∨
      f (p x) = -EuclideanSpace.single (0 : Fin 1) 1) :
    ∃ c : Ambient 1,
      (c = EuclideanSpace.single (0 : Fin 1) 1 ∨ c = -EuclideanSpace.single (0 : Fin 1) 1) ∧
      (f ∘ p) =ᵐ[volume.restrict (Metric.ball a R)] (fun _ => c) := by
  let χ : ContDiffBump (0 : Ambient m) :=
    { rIn := |M| + 1, rOut := |M| + 2,
      rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let F : Ambient m → Ambient 1 := fun z => χ z • f z
  have hF : ContDiff ℝ 1 F := χ.contDiff.smul hf
  have hcF : HasCompactSupport F := χ.hasCompactSupport.smul_right
  obtain ⟨L, hL⟩ := (hcF.fderiv ℝ).exists_bound_of_continuous
    (hF.continuous_fderiv (by norm_num))
  have hW := memW12_postcompose_c1 hR hp F hF L hL
  have heq : (F ∘ p) =ᵐ[volume.restrict (Metric.ball a R)] (f ∘ p) := by
    filter_upwards [hb] with x hx
    have hball : p x ∈ Metric.ball (0 : Ambient m) χ.rIn := by
      change dist (p x) 0 < |M| + 1
      rw [dist_zero_right]
      exact lt_of_le_of_lt (hx.trans (le_abs_self M)) (lt_add_one _)
    have hχ := (χ.eventuallyEq_one_of_mem_ball hball).eq_of_nhds
    change χ (p x) = (1 : ℝ) at hχ
    change χ (p x) • f (p x) = f (p x)
    rw [hχ, one_smul]
  have hs : ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      (F ∘ p) x = EuclideanSpace.single (0 : Fin 1) 1 ∨
      (F ∘ p) x = -EuclideanSpace.single (0 : Fin 1) 1 := by
    filter_upwards [hsign, heq] with x hx he
    exact he.symm ▸ hx
  obtain ⟨c, hc, hconst⟩ := exists_constant_sign_of_memW12 a hR _ _ hW hs
  exact ⟨c, hc, heq.symm.trans hconst⟩

end StationaryHarmonicMaps.Analysis

end

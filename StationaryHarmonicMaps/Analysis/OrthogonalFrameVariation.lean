module

public import StationaryHarmonicMaps.Geometry.SkewExponential
public import StationaryHarmonicMaps.Analysis.SobolevOperatorTest
public import StationaryHarmonicMaps.Analysis.OrthogonalOperatorBounds

/-!
# Actual native Sobolev right variations of orthogonal frames

An actual domain cutoff equal to one near the closed unit ball gives
compact smooth multiplier data for the native operator product rule.
The original finite L2 data supply the full finite Sobolev graph of the
literal right product, with its actual spatial Frechet derivative.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem memLp_two_compact_operator_apply {n m q : ℕ} {μ : Measure (Domain n)}
    (L : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (f : Domain n → Ambient m) (hf : MemLp f 2 μ)
    (ψ : Domain n → Ambient q) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    MemLp (fun x => L (f x) (ψ x)) 2 μ := by
  obtain ⟨B, hB⟩ := hcψ.exists_bound_of_continuous hψ
  have hLf := L.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have hm := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (hLf.prodMk hψ.aestronglyMeasurable)
  apply hf.of_le_mul (c := ‖L‖ * B) hm
  exact Eventually.of_forall fun x => by
    calc
      _ ≤ ‖L (f x)‖ * ‖ψ x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖L‖ * ‖f x‖) * B := mul_le_mul (L.le_opNorm _) (hB x) (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- A bounded finite native Sobolev operator field times a compact smooth map has its actual finite product graph. -/
theorem memW12_operator_test {n m q : ℕ} {Ω : OpenDomain n}
    {p : Domain n → Ambient m} {Dp : Domain n → Gradient n m}
    (hp : MemW12 Ω p Dp) {M : ℝ}
    (hb : ∀ᵐ x ∂volume.restrict Ω.val, ‖p x‖ ≤ M)
    (L : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    MemW12 Ω (fun x => L (p x) (ψ x)) (fun x i =>
      L (Dp x i) (ψ x) + L (p x) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
  have hloc := memW12Loc_operator_test hp.to_memW12Loc hb L ψ hψ hcψ
  refine ⟨hloc.1, memLp_two_compact_operator_apply L p hp.2.1 ψ hψ.continuous hcψ, ?_⟩
  intro i
  have hfirst := memLp_two_compact_operator_apply L (fun x => Dp x i) (hp.2.2 i) ψ hψ.continuous hcψ
  have hdψ : Continuous (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdψ : HasCompactSupport (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)) :=
    hcψ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  exact hfirst.add (memLp_two_compact_operator_apply L p hp.2.1 _ hdψ hcdψ)

private theorem exists_encoded_operator_multiplication {q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q)) :
    ∃ L : Ambient (q*q) →L[ℝ] (Ambient (q*q) →L[ℝ] Ambient (q*q)),
      ∀ z w, L z w = E (R z * R w) := by
  let M := ContinuousLinearMap.compL ℝ (Ambient q) (Ambient q) (Ambient q)
  let L0 : Ambient (q*q) →ₗ[ℝ] (Ambient (q*q) →L[ℝ] Ambient (q*q)) :=
    { toFun := fun z => E.comp ((M (R z)).comp R)
      map_add' := by
        intro z w
        apply ContinuousLinearMap.ext
        intro v
        change E (R (z+w) * R v) = E (R z * R v) + E (R w * R v)
        rw [map_add, add_mul, map_add]
      map_smul' := by
        intro c z
        apply ContinuousLinearMap.ext
        intro v
        change E (R (c • z) * R v) = c • E (R z * R v)
        rw [map_smul]
        change E ((c • R z).comp (R v)) = c • E ((R z).comp (R v))
        rw [ContinuousLinearMap.smul_comp, map_smul] }
  exact ⟨L0.toContinuousLinearMap, fun _ _ => rfl⟩

/-- The same native orthogonal frame has an actual right-exponential Sobolev variation, with no test-support requirement. -/
theorem orthogonal_frame_right_exp_variation {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀ T, R (E T) = T) (hER : ∀ z, E (R z) = z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
    (hp : MemW12 (ballDomain (0 : Domain n) 1) p Dp)
    (horth : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), star (R (p x)) * R (p x) = 1)
    (S : Domain n → (Ambient q →L[ℝ] Ambient q)) (hS : ContDiff ℝ ∞ S)
    (hskew : ∀ x, star (S x) = -S x) (t : ℝ) :
    let Q := fun x => NormedSpace.exp (t • S x)
    let pt := fun x => E (R (p x) * Q x)
    let Dpt := fun x i => E (R (Dp x i) * Q x + R (p x) * fderiv ℝ Q x (EuclideanSpace.single i 1))
    MemW12 (ballDomain (0 : Domain n) 1) pt Dpt ∧
      (∀ x, R (pt x) = R (p x) * Q x) ∧
      (∀ x i, R (Dpt x i) = R (Dp x i) * Q x + R (p x) * fderiv ℝ Q x (EuclideanSpace.single i 1)) ∧
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), star (R (pt x)) * R (pt x) = 1 := by
  intro Q pt Dpt
  have hQ : ContDiff ℝ ∞ Q := contDiff_operator_exp_field S hS t
  let χ : ContDiffBump (0 : Domain n) :=
    { rIn := 2, rOut := 3, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let ψ := fun x => χ x • E (Q x)
  have hψ : ContDiff ℝ ∞ ψ := by
    convert χ.contDiff.smul (E.contDiff.comp hQ) using 1
    funext x
    rfl
  have hcψ : HasCompactSupport ψ := χ.hasCompactSupport.smul_right
  have hEq (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) 1) :
      ψ x = E (Q x) ∧ ∀ i : Fin n,
        fderiv ℝ ψ x (EuclideanSpace.single i 1) = E (fderiv ℝ Q x (EuclideanSpace.single i 1)) := by
    have hxχ : x ∈ Metric.ball (0 : Domain n) χ.rIn := by
      have hxnorm : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      change dist x 0 < 2
      rw [dist_zero_right]
      linarith only [hxnorm]
    have H : ψ =ᶠ[𝓝 x] (fun y => E (Q y)) :=
      (χ.eventuallyEq_one_of_mem_ball hxχ).mono fun y hy => by
        change χ y = (1 : ℝ) at hy
        change χ y • E (Q y) = E (Q y)
        rw [hy, one_smul]
    refine ⟨H.eq_of_nhds, ?_⟩
    intro i
    rw [H.fderiv_eq]
    change fderiv ℝ (E ∘ Q) x (EuclideanSpace.single i 1) = _
    rw [fderiv_comp x E.differentiableAt (hQ.differentiable (by simp) x), E.fderiv]
    rfl
  obtain ⟨L, hL⟩ := exists_encoded_operator_multiplication E R
  have hb := ae_orthogonal_coordinates_bound (Ω := ballDomain (0 : Domain n) 1) E R hER hE p
    (by simpa only [ballDomain] using horth)
  have hW := memW12_operator_test hp hb L ψ hψ hcψ
  have hpt : MemW12 (ballDomain (0 : Domain n) 1) pt Dpt := by
    apply hW.congr_ae
    · filter_upwards [ae_restrict_mem (ballDomain (0 : Domain n) 1).property.measurableSet] with x hx
      have hx' : x ∈ Metric.ball (0 : Domain n) 1 := by simpa only [ballDomain] using hx
      change L (p x) (ψ x) = E (R (p x) * Q x)
      rw [hL, (hEq x hx').1, hRE]
    · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      funext i
      rw [hL, hL, (hEq x hx).1, (hEq x hx).2 i, hRE, hRE, ← map_add]
  refine ⟨hpt, fun x => hRE _, fun x i => hRE _, ?_⟩
  filter_upwards [horth] with x hx
  change star (R (E (R (p x) * Q x))) * R (E (R (p x) * Q x)) = 1
  rw [hRE, star_mul]
  calc
    _ = star (Q x) * (star (R (p x)) * R (p x)) * Q x := by simp only [mul_assoc]
    _ = 1 := by rw [hx, mul_one]; exact (operator_exp_orthogonal_of_skew (S x) (hskew x) t).1


/-- At parameter zero the literal variation recovers the original map and every original weak column. -/
theorem orthogonal_frame_right_exp_variation_zero {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀ z, E (R z) = z)
    (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
    (S : Domain n → (Ambient q →L[ℝ] Ambient q)) :
    (fun x => E (R (p x) * NormedSpace.exp ((0 : ℝ) • S x))) = p ∧
      (fun x i => E (R (Dp x i) * NormedSpace.exp ((0 : ℝ) • S x) +
        R (p x) * fderiv ℝ (fun y => NormedSpace.exp ((0 : ℝ) • S y)) x
          (EuclideanSpace.single i 1))) = Dp := by
  have hQ0 : (fun y => NormedSpace.exp ((0 : ℝ) • S y)) = (fun _ : Domain n => (1 : Ambient q →L[ℝ] Ambient q)) := by
    funext y
    rw [zero_smul ℝ (S y), NormedSpace.exp_zero]
  constructor
  · funext x
    rw [zero_smul ℝ (S x), NormedSpace.exp_zero, mul_one, hER]
  · funext x i
    rw [zero_smul ℝ (S x), NormedSpace.exp_zero, mul_one, hQ0,
      fderiv_const_apply, zero_apply, mul_zero, add_zero, hER]

end StationaryHarmonicMaps.Analysis

end

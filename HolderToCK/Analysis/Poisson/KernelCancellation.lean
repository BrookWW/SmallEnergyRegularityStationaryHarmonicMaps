module

public import HolderToCK.Analysis.Poisson.FundamentalSolution
public import HarmonicMaps.Analysis.PoissonMeasureInvariance
public import HarmonicMaps.Analysis.AnnularPolarIntegral

/-! # Sphere moments and annular cancellation of the Newtonian Hessian kernel -/

public section

open HarmonicMaps MeasureTheory Set
open scoped Topology

namespace HolderToCK

@[expose] noncomputable def hessianKernelExpression {n : ℕ} (i j : Fin n)
    (z : Domain n) : ℝ :=
  (euclideanSphereArea n)⁻¹ *
    ((if i = j then 1 else 0) * ‖z‖ ^ (-(n : ℝ)) -
      (n : ℝ) * z i * z j * ‖z‖ ^ (-(n : ℝ) - 2))

theorem hessianKernelExpression_eq {n : ℕ} (i j : Fin n)
    (z : {z : Domain n // z ≠ 0}) :
    hessianKernelExpression i j z.val = fundamentalHessianKernel i j z := rfl

theorem canonicalSphere_integral_orthogonal {n : ℕ}
    (T : Domain n ≃ₗᵢ[ℝ] Domain n) (f : Domain n → ℝ) (hf : Continuous f) :
    (∫ θ : Metric.sphere (0 : Domain n) 1, f (T θ.val)
      ∂(volume : Measure (Domain n)).toSphere) =
    ∫ θ : Metric.sphere (0 : Domain n) 1, f θ.val
      ∂(volume : Measure (Domain n)).toSphere := by
  let μ : Measure (Domain n) :=
    Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => θ.val)
      (volume : Measure (Domain n)).toSphere
  have hT : MeasurePreserving T μ μ := ⟨T.continuous.measurable, by
    simpa only [one_pow, ENNReal.ofReal_one, one_smul]
      using poisson_scaledPolar_rotationInvariant (⟨1, one_pos⟩ : PositiveRadius) T⟩
  have ht := hT.integral_comp T.toHomeomorph.measurableEmbedding f
  dsimp only [μ] at ht
  rw [integral_map_of_stronglyMeasurable (f := fun x => f (T x)) measurable_subtype_coe
      (hf.comp T.continuous).stronglyMeasurable,
    integral_map_of_stronglyMeasurable measurable_subtype_coe hf.stronglyMeasurable] at ht
  exact ht

theorem sphereCoordinateProduct_integrable {n : ℕ} (i j : Fin n) :
    Integrable (fun θ : Metric.sphere (0 : Domain n) 1 => θ.val i * θ.val j)
      (volume : Measure (Domain n)).toSphere := by
  have hc : Continuous (fun θ : Metric.sphere (0 : Domain n) 1 => θ.val i * θ.val j) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp continuous_subtype_val).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_subtype_val)
  exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)

theorem sphereCoordinateProduct_offDiagonal {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (∫ θ : Metric.sphere (0 : Domain n) 1, θ.val i * θ.val j
      ∂(volume : Measure (Domain n)).toSphere) = 0 := by
  let T : Domain n ≃ₗᵢ[ℝ] Domain n := LinearIsometryEquiv.piLpCongrRight 2
    (fun k : Fin n => if k = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  have hTi (z : Domain n) : T z i = -z i := by
    simp only [T, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply, if_true]
    rfl
  have hTj (z : Domain n) : T z j = z j := by
    simp only [T, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply,
      if_neg (Ne.symm hij)]
    rfl
  have ht := canonicalSphere_integral_orthogonal T (fun z => z i * z j)
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).mul
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j))
  simp_rw [hTi, hTj, neg_mul] at ht
  rw [integral_neg] at ht
  linarith only [ht]

theorem sphereCoordinateSquare_eq {n : ℕ} (i j : Fin n) :
    (∫ θ : Metric.sphere (0 : Domain n) 1, θ.val i * θ.val i
      ∂(volume : Measure (Domain n)).toSphere) =
    ∫ θ : Metric.sphere (0 : Domain n) 1, θ.val j * θ.val j
      ∂(volume : Measure (Domain n)).toSphere := by
  let T : Domain n ≃ₗᵢ[ℝ] Domain n :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have hTi (z : Domain n) : T z i = z j := by
    simp [T, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  have ht := canonicalSphere_integral_orthogonal T (fun z => z i * z i)
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).mul
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i))
  simp_rw [hTi] at ht
  exact ht.symm

theorem sphereCoordinateProduct_moment {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    (∫ θ : Metric.sphere (0 : Domain n) 1, θ.val i * θ.val j
      ∂(volume : Measure (Domain n)).toSphere) =
      euclideanSphereArea n * (if i = j then 1 else 0) / n := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, mul_one]
    have hsum : (∑ k : Fin n,
        ∫ θ : Metric.sphere (0 : Domain n) 1, θ.val k * θ.val k
          ∂(volume : Measure (Domain n)).toSphere) = euclideanSphereArea n := by
      rw [← integral_finsetSum Finset.univ
        (fun k _ => sphereCoordinateProduct_integrable k k)]
      have heq : (fun θ : Metric.sphere (0 : Domain n) 1 =>
          ∑ k : Fin n, θ.val k * θ.val k) = fun _ => 1 := by
        funext θ
        simp_rw [← pow_two]
        rw [← EuclideanSpace.real_norm_sq_eq]
        have hθ : ‖θ.val‖ = 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
        rw [hθ, one_pow]
      rw [heq, integral_const, smul_eq_mul, mul_one]
      rfl
    have heq : (∑ k : Fin n,
        ∫ θ : Metric.sphere (0 : Domain n) 1, θ.val k * θ.val k
          ∂(volume : Measure (Domain n)).toSphere) =
        (n : ℝ) * (∫ θ : Metric.sphere (0 : Domain n) 1, θ.val i * θ.val i
          ∂(volume : Measure (Domain n)).toSphere) := by
      simp_rw [sphereCoordinateSquare_eq (j := i)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [heq] at hsum
    exact (eq_div_iff (Nat.cast_ne_zero.mpr hn.ne')).mpr (by
      rw [mul_comm]
      exact hsum)
  · rw [if_neg hij, mul_zero, zero_div]
    exact sphereCoordinateProduct_offDiagonal i j hij

theorem hessianKernelExpression_on_sphere {n : ℕ} (i j : Fin n)
    {r : ℝ} (hr : 0 < r) (θ : Metric.sphere (0 : Domain n) 1) :
    hessianKernelExpression i j (r • θ.val) =
      ((euclideanSphereArea n)⁻¹ * r ^ (-(n : ℝ))) *
        ((if i = j then 1 else 0) - (n : ℝ) * θ.val i * θ.val j) := by
  have hθ : ‖θ.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  have hpow : r ^ (-(n : ℝ) - 2) * r ^ 2 = r ^ (-(n : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_add hr]
    congr 1
    ring
  rw [hessianKernelExpression, norm_smul, Real.norm_of_nonneg hr.le, hθ, mul_one]
  simp only [PiLp.smul_apply, smul_eq_mul]
  calc
    _ = (euclideanSphereArea n)⁻¹ *
        ((if i = j then 1 else 0) * r ^ (-(n : ℝ)) -
          (n : ℝ) * θ.val i * θ.val j * (r ^ (-(n : ℝ) - 2) * r ^ 2)) := by ring
    _ = _ := by rw [hpow]; ring

theorem hessianKernelExpression_sphere_cancellation {n : ℕ} (hn : 0 < n)
    (i j : Fin n) {r : ℝ} (hr : 0 < r) :
    (∫ θ : Metric.sphere (0 : Domain n) 1, hessianKernelExpression i j (r • θ.val)
      ∂(volume : Measure (Domain n)).toSphere) = 0 := by
  simp_rw [hessianKernelExpression_on_sphere i j hr, mul_assoc (n : ℝ)]
  rw [integral_const_mul,
    integral_sub (integrable_const _) ((sphereCoordinateProduct_integrable i j).const_mul n),
    integral_const, smul_eq_mul]
  rw [integral_const_mul, sphereCoordinateProduct_moment hn i j]
  change (euclideanSphereArea n)⁻¹ * r ^ (-(n : ℝ)) *
    (euclideanSphereArea n * (if i = j then 1 else 0) -
      (n : ℝ) * (euclideanSphereArea n * (if i = j then 1 else 0) / n)) = 0
  field_simp
  ring

theorem hessianKernelExpression_continuousAt {n : ℕ} (i j : Fin n)
    (x : Domain n) (hx : x ≠ 0) : ContinuousAt (hessianKernelExpression i j) x := by
  have hp (a : ℝ) : ContinuousAt (fun z : Domain n => ‖z‖ ^ a) x :=
    continuous_norm.continuousAt.rpow_const (Or.inl (norm_ne_zero_iff.mpr hx))
  exact continuousAt_const.mul
    ((continuousAt_const.mul (hp _)).sub
      (((continuousAt_const.mul (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).continuousAt).mul
        (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).continuousAt).mul (hp _)))

theorem hessianKernelExpression_integrableOn_annulus {n : ℕ} (i j : Fin n)
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (hessianKernelExpression i j)
      (Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) a) := by
  have hc : ContinuousOn (hessianKernelExpression i j)
      (Metric.closedBall (0 : Domain n) b \ Metric.ball (0 : Domain n) a) := by
    intro x hx
    apply (hessianKernelExpression_continuousAt i j x ?_).continuousWithinAt
    intro hzero
    exact hx.2 (by rw [hzero]; exact Metric.mem_ball_self ha)
  exact (hc.integrableOn_compact ((isCompact_closedBall _ _).diff Metric.isOpen_ball)).mono_set
    (fun _ hx => ⟨Metric.ball_subset_closedBall hx.1, hx.2⟩)

theorem hessianKernelExpression_annulus_cancellation {n : ℕ} (hn : 0 < n)
    (i j : Fin n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ z in Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) a,
      hessianKernelExpression i j z) = 0 := by
  rw [integral_annulus_eq_polar hn ha hab
    (hessianKernelExpression_integrableOn_annulus i j ha)]
  calc
    _ = ∫ _ in a..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ Icc a b := by simpa only [uIcc_of_le hab] using hr
      simp only [zero_add]
      rw [hessianKernelExpression_sphere_cancellation hn i j (ha.trans_le hr'.1), mul_zero]
    _ = 0 := intervalIntegral.integral_zero

theorem hessianKernelExpression_strictAnnulus_cancellation {n : ℕ} (hn : 0 < n)
    (i j : Fin n) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫ z in {z : Domain n | a < ‖z‖ ∧ ‖z‖ < b}, hessianKernelExpression i j z) = 0 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have heq : {z : Domain n | a < ‖z‖ ∧ ‖z‖ < b} =ᵐ[volume]
      Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) a := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp
      (Measure.addHaar_sphere (volume : Measure (Domain n)) (0 : Domain n) a)] with z hz
    have hnz : ‖z‖ ≠ a := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz
    apply propext
    change z ∈ {z : Domain n | a < ‖z‖ ∧ ‖z‖ < b} ↔
      z ∈ Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) a
    simp only [mem_setOf_eq, mem_sdiff, Metric.mem_ball, dist_zero_right, not_lt]
    exact ⟨fun h => ⟨h.2, h.1.le⟩, fun h => ⟨lt_of_le_of_ne h.2 (Ne.symm hnz), h.1⟩⟩
  rw [setIntegral_congr_set heq]
  exact hessianKernelExpression_annulus_cancellation hn i j ha hab.le

end HolderToCK
end

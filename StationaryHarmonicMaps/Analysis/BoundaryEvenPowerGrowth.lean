module

public import StationaryHarmonicMaps.Analysis.BoundaryCriticalEvenMorrey
public import StationaryHarmonicMaps.Analysis.UniformPowerGrowthBounds

/-!
# Power growth of the literal even inversion graph

The original truncated-ball energy growth bounds the same even inversion
on every truncated query in the double ball. The query center may lie on
the sphere or outside the double ball. The displayed factor depends only
on the domain dimension and growth exponent.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set Metric
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original power growth gives complete all-center growth of the same literal even inversion gradient. -/
theorem even_inversion_power_growth_unitBall {n q : ℕ} (hn : 2 ≤ n)
    (ν : ℝ) (u : Domain n → Ambient q) (D : Domain n → Gradient n q)
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u D)
    (K : ℝ) (hK : 0 ≤ K)
    (hGrowth : ∀ x ∈ ball (0 : Domain n) 1, ∀ r : ℝ, 0 < r →
      (∫ y in ball x r ∩ ball (0 : Domain n) 1, hsNormSq (D y)) ≤ K * r ^ ν) :
    let I := inversion (0 : Domain n) 1
    let T := fun x i => ∑ j : Fin n,
      (fderiv ℝ I x (EuclideanSpace.single i 1)) j • D (I x) j
    let DU := fun x i => if ‖x‖ ≤ 1 then D x i else T x i
    ∀ (a : Domain n) (r : ℝ), 0 < r →
      (∫ x in ball a r ∩ ball (0 : Domain n) 2, hsNormSq (DU x)) ≤
        ((2 : ℝ) ^ ν * (1 + (2 : ℝ) ^ (2 * n))) * K * r ^ ν := by
  classical
  intro I T DU a r hr
  let B := ball (0 : Domain n) 1
  let B₂ := ball (0 : Domain n) 2
  let D₀ := B.indicator D
  let C := (2 : ℝ) ^ ν * (1 + (2 : ℝ) ^ (2 * n))
  have hNative := memW12_even_inversion_extension_ball_two hn u D hu
  have hDUInt : IntegrableOn (fun x => hsNormSq (DU x)) B₂ volume := hNative.integrable_hsNormSq
  have hD₀ (i : Fin n) : MemLp (fun x => D₀ x i) 2 volume := by
    have hEq : (fun x => D₀ x i) = B.indicator (fun x => D x i) := by
      funext x
      by_cases hx : x ∈ B
      · simp only [D₀, indicator_of_mem hx]
      · simp only [D₀, indicator_of_notMem hx, Pi.zero_apply]
    rw [hEq]
    exact (memLp_indicator_iff_restrict measurableSet_ball).mpr (hu.2.2 i)
  have hD₀I : Integrable (fun x => hsNormSq (D₀ x)) volume :=
    integrable_hsNormSq_of_columns D₀ hD₀
  have hSphere : ∀ᵐ x : Domain n ∂volume, ‖x‖ ≠ 1 := by
    filter_upwards [HarmonicMaps.ball_ae_eq_closedBall (0 : Domain n)
      (by norm_num : (0 : ℝ) < 1)] with x hx
    intro hxNorm
    have hCB : x ∈ closedBall (0 : Domain n) 1 := by rw [mem_closedBall, dist_zero_right, hxNorm]
    have hBall : x ∈ B := Eq.mpr hx hCB
    rw [mem_ball, dist_zero_right, hxNorm] at hBall
    exact (lt_irrefl (1 : ℝ)) hBall
  have hQuery (a : Domain n) (r : ℝ) (hr : 0 < r) :
      (∫ x in ball a r ∩ B₂, hsNormSq (DU x)) ≤ C * K * r ^ ν := by
    let Q := ball a r ∩ B₂
    let S := Q ∩ {x : Domain n | 1 < ‖x‖}
    let μ := volume.restrict Q
    let σ := volume.restrict S
    have hQ : MeasurableSet Q := measurableSet_ball.inter measurableSet_ball
    have hS : MeasurableSet S := hQ.inter (measurableSet_lt measurable_const measurable_norm)
    have hImageB : I '' S ⊆ B := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_ball_zero_iff, norm_unit_inversion]
      exact (inv_lt_one₀ (zero_lt_one.trans hx.2)).mpr hx.2
    have hImageD (j : Fin n) : MemLp (fun y => D y j) 2 (volume.restrict (I '' S)) :=
      (hu.2.2 j).mono_measure (Measure.restrict_mono_set volume hImageB)
    obtain ⟨hT, hTEnergy⟩ := unit_inversion_L2_gradient_columns_transport S hS 1 2
      (by norm_num) (by norm_num) (fun _ hx => hx.2.le)
      (fun x hx => (show ‖x‖ < 2 from by
        simpa only [B₂, mem_ball, dist_zero_right] using hx.1.2).le) D hImageD
    have hTI : Integrable (fun x => hsNormSq (T x)) σ := integrable_hsNormSq_of_columns T hT
    have hImageEnergy : (∫ y in I '' S, hsNormSq (D y)) ≤
        (2 : ℝ) ^ ν * K * r ^ ν := by
      by_cases hEmpty : S = ∅
      · rw [hEmpty, image_empty, setIntegral_empty]
        positivity
      · obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
        have hsub : I '' S ⊆ ball (I x₀) (2 * r) ∩ B := by
          rintro _ ⟨x, hx, rfl⟩
          refine ⟨?_, hImageB ⟨x, hx, rfl⟩⟩
          have hDist := dist_unit_inversion_le_dist_exterior x x₀ hx.2.le hx₀.2.le
          have hxD : dist x a < r := hx.1.1
          have hx₀D : dist x₀ a < r := hx₀.1.1
          have hTri := dist_triangle x a x₀
          rw [dist_comm a x₀] at hTri
          change dist (I x) (I x₀) < 2 * r
          linarith only [hDist, hxD, hx₀D, hTri]
        have hDI : IntegrableOn (fun y => hsNormSq (D y))
            (ball (I x₀) (2 * r) ∩ B) volume :=
          hu.integrable_hsNormSq.mono_set inter_subset_right
        calc
          _ ≤ ∫ y in ball (I x₀) (2 * r) ∩ B, hsNormSq (D y) :=
            setIntegral_mono_set hDI (Eventually.of_forall fun _ => hsNormSq_nonneg _)
              (Eventually.of_forall fun _ hy => hsub hy)
          _ ≤ K * (2 * r) ^ ν := hGrowth (I x₀) (hImageB ⟨x₀, hx₀, rfl⟩)
            (2 * r) (mul_pos (by norm_num : (0 : ℝ) < 2) hr)
          _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le]; ring
    have hOuterEnergy : (∫ x, hsNormSq (T x) ∂σ) ≤
        (2 : ℝ) ^ (2 * n) * ((2 : ℝ) ^ ν * K * r ^ ν) := by
      have H : (∫ x, hsNormSq (T x) ∂σ) ≤
          (2 : ℝ) ^ (2 * n) * (∫ y in I '' S, hsNormSq (D y)) := by
        simpa only [one_pow, inv_one, one_mul] using hTEnergy
      exact H.trans (mul_le_mul_of_nonneg_left hImageEnergy (by positivity))
    have hIndI : Integrable (S.indicator (fun x => hsNormSq (T x))) μ :=
      ((integrable_indicator_iff hS).mpr hTI).mono_measure Measure.restrict_le_self
    have hD₀Q : Integrable (fun x => hsNormSq (D₀ x)) μ := hD₀I.restrict
    have hDUQ : Integrable (fun x => hsNormSq (DU x)) μ :=
      hDUInt.mono_set inter_subset_right
    have hPoint : ∀ᵐ x ∂μ, hsNormSq (DU x) ≤ hsNormSq (D₀ x) +
        S.indicator (fun x => hsNormSq (T x)) x := by
      filter_upwards [ae_restrict_mem hQ, ae_restrict_of_ae hSphere] with x hxQ hxSphere
      by_cases hx : ‖x‖ < 1
      · have hxB : x ∈ B := by
          simpa only [B, mem_ball, dist_zero_right] using hx
        have hxS : x ∉ S := fun h => not_lt_of_ge hx.le h.2
        simp only [DU, if_pos hx.le, D₀, indicator_of_mem hxB,
          indicator_of_notMem hxS, add_zero, le_refl]
      · have hxOut : 1 < ‖x‖ := lt_of_le_of_ne (le_of_not_gt hx) hxSphere.symm
        have hxB : x ∉ B := by
          simpa only [B, mem_ball, dist_zero_right] using not_lt_of_ge hxOut.le
        simp only [DU, if_neg (not_le.mpr hxOut), D₀, indicator_of_notMem hxB,
          indicator_of_mem (show x ∈ S from ⟨hxQ, hxOut⟩), hsNormSq, Pi.zero_apply,
          norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, zero_add, le_refl]
    have hIndEq : (∫ x, S.indicator (fun x => hsNormSq (T x)) x ∂μ) =
        ∫ x, hsNormSq (T x) ∂σ := by
      rw [integral_indicator hS, show μ.restrict S = σ from by
        rw [Measure.restrict_restrict hS, inter_eq_left.mpr inter_subset_left]]
    have hInnerEnergy : (∫ x, hsNormSq (D₀ x) ∂μ) ≤
        (2 : ℝ) ^ ν * K * r ^ ν := by
      have hScalar : (fun x => hsNormSq (D₀ x)) = B.indicator (fun x => hsNormSq (D x)) := by
        funext x
        by_cases hx : x ∈ B
        · simp only [D₀, indicator_of_mem hx]
        · simp only [D₀, indicator_of_notMem hx, hsNormSq, Pi.zero_apply, norm_zero,
            zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
      have hSet : B ∩ Q = ball a r ∩ B := by
        ext x
        constructor
        · intro hx; exact ⟨hx.2.1, hx.1⟩
        · intro hx; exact ⟨hx.2, hx.1, (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hx.2⟩
      rw [hScalar, integral_indicator measurableSet_ball,
        show μ.restrict B = volume.restrict (ball a r ∩ B) from by
          rw [Measure.restrict_restrict measurableSet_ball, hSet]]
      exact integral_hsNormSq_inter_le_of_uniform_power_growth D B hu.2.2 K ν hK hGrowth a hr
    calc
      _ ≤ ∫ x, hsNormSq (D₀ x) + S.indicator (fun x => hsNormSq (T x)) x ∂μ :=
        integral_mono_ae hDUQ (hD₀Q.add hIndI) hPoint
      _ = (∫ x, hsNormSq (D₀ x) ∂μ) + ∫ x, hsNormSq (T x) ∂σ := by
        rw [integral_add hD₀Q hIndI, hIndEq]
      _ ≤ _ := (add_le_add hInnerEnergy hOuterEnergy).trans_eq (by dsimp only [C]; ring)
  exact hQuery a r hr

/-- One native even graph satisfies every allowed power-growth bound, with the positive constant function selected before all original fields. -/
theorem exists_same_even_inversion_native_all_power_growth_unitBall (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : {ν : ℝ // 0 ≤ ν ∧ ν < n} → ℝ,
      (∀ ν, 0 < C ν) ∧
      ∀ (q : ℕ) (u : Domain n → Ambient q) (D : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) u D →
        let I := inversion (0 : Domain n) 1
        let U := fun x => if ‖x‖ ≤ 1 then u x else u (I x)
        let T := fun x i => ∑ j : Fin n,
          (fderiv ℝ I x (EuclideanSpace.single i 1)) j • D (I x) j
        let DU := fun x i => if ‖x‖ ≤ 1 then D x i else T x i
        MemW12 (ballDomain (0 : Domain n) 2) U DU ∧
          ∀ (ν : {ν : ℝ // 0 ≤ ν ∧ ν < n}) (K : ℝ), 0 ≤ K →
            (∀ x ∈ ball (0 : Domain n) 1, ∀ r : ℝ, 0 < r →
              (∫ y in ball x r ∩ ball (0 : Domain n) 1, hsNormSq (D y)) ≤ K * r ^ ν.val) →
            ∀ (a : Domain n) (r : ℝ), 0 < r →
              (∫ x in ball a r ∩ ball (0 : Domain n) 2, hsNormSq (DU x)) ≤
                C ν * K * r ^ ν.val := by
  refine ⟨fun ν => (2 : ℝ) ^ ν.val * (1 + (2 : ℝ) ^ (2 * n)), ?_, ?_⟩
  · intro ν
    positivity
  · intro q u D hu I U T DU
    refine ⟨memW12_even_inversion_extension_ball_two hn u D hu, ?_⟩
    intro ν K hK hGrowth
    exact even_inversion_power_growth_unitBall hn ν.val u D hu K hK hGrowth

end StationaryHarmonicMaps.Analysis

end

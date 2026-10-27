module

public import StationaryHarmonicMaps.Analysis.BoundaryNativeEvenExtension
public import StationaryHarmonicMaps.Analysis.ZeroExtensionCriticalMorrey

/-!
# Complete critical Morrey control of even inversion

Inversion contracts distances between exterior points. Each nonempty exterior
query therefore maps into a doubled ball centered at an actual original
point. The genuine annular chain rule and Jacobian transport preserve the
critical scale on every truncated ball, including boundary queries.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set Metric
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Unit inversion is nonexpansive between exterior points. -/
theorem dist_unit_inversion_le_dist_exterior {n : ℕ} (x y : Domain n)
    (hx : 1 ≤ ‖x‖) (hy : 1 ≤ ‖y‖) :
    dist (inversion (0 : Domain n) 1 x) (inversion (0 : Domain n) 1 y) ≤ dist x y := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hx)
  have hy0 : y ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hy)
  rw [dist_inversion_inversion hx0 hy0, one_pow, dist_zero_right, dist_zero_right]
  have hprod : 1 ≤ ‖x‖ * ‖y‖ := one_le_mul_of_one_le_of_one_le hx hy
  have hInv : 1 / (‖x‖ * ‖y‖) ≤ 1 := (div_le_one (lt_of_lt_of_le zero_lt_one hprod)).mpr hprod
  exact (mul_le_mul_of_nonneg_right hInv dist_nonneg).trans_eq (one_mul _)

/-- The same literal even graph has the complete critical bound on the double ball, with a constant depending only on the dimension. -/
theorem even_inversion_criticalMorrey_bound_unitBall {n q : ℕ} (hn : 2 ≤ n)
    (u : Domain n → Ambient q) (D : Domain n → Gradient n q)
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u D)
    (K : ℝ) (hK : 0 ≤ K)
    (hCritical : criticalGradientMorreySquare D (ball (0 : Domain n) 1) ≤ ENNReal.ofReal K) :
    let I := inversion (0 : Domain n) 1
    let T := fun x i => ∑ j : Fin n,
      (fderiv ℝ I x (EuclideanSpace.single i 1)) j • D (I x) j
    let DU := fun x i => if ‖x‖ ≤ 1 then D x i else T x i
    criticalGradientMorreySquare DU (ball (0 : Domain n) 2) ≤
      ENNReal.ofReal (((2 : ℝ) ^ ((n : ℝ) - 2) * (1 + (2 : ℝ) ^ (2 * n))) * K) := by
  classical
  intro I T DU
  let B := ball (0 : Domain n) 1
  let B₂ := ball (0 : Domain n) 2
  let D₀ := B.indicator D
  let C := (2 : ℝ) ^ ((n : ℝ) - 2) * (1 + (2 : ℝ) ^ (2 * n))
  have hNative := memW12_even_inversion_extension_ball_two hn u D hu
  have hDUInt : IntegrableOn (fun x => hsNormSq (DU x)) B₂ volume := hNative.integrable_hsNormSq
  have hD₀ (i : Fin n) : MemLp (fun x => D₀ x i) 2 volume :=
    (indicator_criticalMorrey_univ_bound D B measurableSet_ball hu.2.2 K hK hCritical).1 i
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
      (∫ x in ball a r ∩ B₂, hsNormSq (DU x)) ≤ C * K * r ^ ((n : ℝ) - 2) := by
    let Q := ball a r ∩ B₂
    let S := Q ∩ {x : Domain n | 1 < ‖x‖}
    let μ := volume.restrict Q
    let ν := volume.restrict S
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
    have hTI : Integrable (fun x => hsNormSq (T x)) ν := integrable_hsNormSq_of_columns T hT
    have hImageEnergy : (∫ y in I '' S, hsNormSq (D y)) ≤
        (2 : ℝ) ^ ((n : ℝ) - 2) * K * r ^ ((n : ℝ) - 2) := by
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
        have H := integral_hsNormSq_le_of_criticalMorrey D
          (hImageB ⟨x₀, hx₀, rfl⟩) (mul_pos (by norm_num : (0 : ℝ) < 2) hr)
          hK hsub hImageD hCritical
        exact H.trans_eq (by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le]; ring)
    have hOuterEnergy : (∫ x, hsNormSq (T x) ∂ν) ≤
        (2 : ℝ) ^ (2 * n) * ((2 : ℝ) ^ ((n : ℝ) - 2) * K * r ^ ((n : ℝ) - 2)) := by
      have H : (∫ x, hsNormSq (T x) ∂ν) ≤
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
        ∫ x, hsNormSq (T x) ∂ν := by
      rw [integral_indicator hS, show μ.restrict S = ν from by
        rw [Measure.restrict_restrict hS, inter_eq_left.mpr inter_subset_left]]
    have hInnerEnergy : (∫ x, hsNormSq (D₀ x) ∂μ) ≤
        (2 : ℝ) ^ ((n : ℝ) - 2) * K * r ^ ((n : ℝ) - 2) := by
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
      exact integral_hsNormSq_inter_le_of_criticalMorrey D B hu.2.2 K hK hCritical a hr
    calc
      _ ≤ ∫ x, hsNormSq (D₀ x) + S.indicator (fun x => hsNormSq (T x)) x ∂μ :=
        integral_mono_ae hDUQ (hD₀Q.add hIndI) hPoint
      _ = (∫ x, hsNormSq (D₀ x) ∂μ) + ∫ x, hsNormSq (T x) ∂ν := by
        rw [integral_add hD₀Q hIndI, hIndEq]
      _ ≤ _ := (add_le_add hInnerEnergy hOuterEnergy).trans_eq (by dsimp only [C]; ring)
  unfold criticalGradientMorreySquare
  refine iSup_le fun a => iSup_le fun r => ?_
  have hInt := hDUInt.mono_set
    (inter_subset_right : ball a.val r.val ∩ B₂ ⊆ B₂)
  rw [dirichletEnergy_eq_ofReal_integral hInt]
  have hCancel : r.val ^ ((n : ℝ) - 2) * r.val ^ (2 - (n : ℤ)) = 1 := by
    rw [← Real.rpow_intCast, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast,
      ← Real.rpow_add r.property]
    norm_num
  calc
    _ ≤ ENNReal.ofReal (r.val ^ (2 - (n : ℤ))) *
        ENNReal.ofReal (C * K * r.val ^ ((n : ℝ) - 2)) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal (hQuery a.val r.val r.property)) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (zpow_nonneg r.property.le _)]
      congr 1
      change _ = C * K
      calc
        _ = C * K * (r.val ^ ((n : ℝ) - 2) * r.val ^ (2 - (n : ℤ))) := by ring
        _ = _ := by rw [hCancel, mul_one]

end StationaryHarmonicMaps.Analysis

end

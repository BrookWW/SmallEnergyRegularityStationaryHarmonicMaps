module

public import StationaryHarmonicMaps.Analysis.EffectiveSmoothTransition
public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

/-! # An explicit smooth cutoff between the two-thirds and three-quarters balls -/

@[expose] public section

open HarmonicMaps Real MeasureTheory Set
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

noncomputable section

/-- The fixed rational quadratic argument of the explicit ball cutoff. -/
def effectiveBallCutoffArgument {n : Nat} (x : Domain n) : Real :=
  ((9 : Real) / 16 - ‖x‖ ^ 2) / ((17 : Real) / 144)

/-- A literal smooth transition of the squared Euclidean norm. -/
def effectiveBallCutoff {n : Nat} (x : Domain n) : Real :=
  Real.smoothTransition (effectiveBallCutoffArgument x)

theorem effectiveBallCutoff_contDiff {n : Nat} :
    ContDiff Real ∞ (effectiveBallCutoff (n := n)) := by
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub (contDiff_norm_sq Real)).div_const _)

theorem effectiveBallCutoff_mem_Icc {n : Nat} (x : Domain n) :
    effectiveBallCutoff x ∈ Icc (0 : Real) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem effectiveBallCutoff_eq_one {n : Nat} {x : Domain n}
    (hx : ‖x‖ <= (2 : Real) / 3) : effectiveBallCutoff x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  change 1 <= ((9 : Real) / 16 - ‖x‖ ^ 2) / ((17 : Real) / 144)
  apply (le_div_iff₀ (by norm_num : (0 : Real) < 17 / 144)).mpr
  nlinarith only [hx, norm_nonneg x]

theorem effectiveBallCutoff_eq_zero {n : Nat} {x : Domain n}
    (hx : (3 : Real) / 4 <= ‖x‖) : effectiveBallCutoff x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  change ((9 : Real) / 16 - ‖x‖ ^ 2) / ((17 : Real) / 144) <= 0
  apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
  nlinarith only [hx, norm_nonneg x]

private theorem argument_hasFDerivAt {n : Nat} (x : Domain n) :
    HasFDerivAt effectiveBallCutoffArgument
      ((-(288 : Real) / 17) • innerSL Real x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_sub ((9 : Real) / 16)).const_smul
    (((17 : Real) / 144)⁻¹)
  have hfun : (((17 : Real) / 144)⁻¹ • fun y : Domain n => (9 : Real) / 16 - ‖y‖ ^ 2) =
      effectiveBallCutoffArgument := by
    funext y
    dsimp only [effectiveBallCutoffArgument, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun] at h
  apply h.congr_fderiv
  ext y
  simp only [smul_apply, neg_apply,
    innerSL_apply_apply, smul_eq_mul]
  ring

theorem effectiveBallCutoff_fderiv_apply {n : Nat} (x v : Domain n) :
    fderiv Real effectiveBallCutoff x v =
      (-(288 : Real) / 17) * deriv Real.smoothTransition (effectiveBallCutoffArgument x) *
        inner Real x v := by
  have hs : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (effectiveBallCutoffArgument x))
      (effectiveBallCutoffArgument x) :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _ |>.hasDerivAt
  change fderiv Real (Real.smoothTransition ∘ effectiveBallCutoffArgument) x v = _
  rw [(hs.comp_hasFDerivAt x (argument_hasFDerivAt x)).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

/-- The rational quadratic argument for a prescribed pair of radii. -/
def effectiveRadialArgument {n : Nat} (rIn rOut : Real) (x : Domain n) : Real :=
  (rOut ^ 2 - ‖x‖ ^ 2) / (rOut ^ 2 - rIn ^ 2)

/-- The explicit squared-norm smooth cutoff at prescribed radii. -/
def effectiveRadialCutoff {n : Nat} (rIn rOut : Real) (x : Domain n) : Real :=
  Real.smoothTransition (effectiveRadialArgument rIn rOut x)

theorem effectiveRadialCutoff_contDiff {n : Nat} (rIn rOut : Real) :
    ContDiff Real ∞ (effectiveRadialCutoff (n := n) rIn rOut) :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub (contDiff_norm_sq Real)).div_const _)

theorem effectiveRadialCutoff_mem_Icc {n : Nat} (rIn rOut : Real) (x : Domain n) :
    effectiveRadialCutoff rIn rOut x ∈ Icc (0 : Real) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem radius_square_gap_pos {rIn rOut : Real} (hi : 0 <= rIn)
    (hio : rIn < rOut) : 0 < rOut ^ 2 - rIn ^ 2 := by
  have ho : 0 < rOut := lt_of_le_of_lt hi hio
  have h := mul_pos (sub_pos.mpr hio) (add_pos_of_pos_of_nonneg ho hi)
  nlinarith only [h]

theorem effectiveRadialCutoff_eq_one {n : Nat} {rIn rOut : Real}
    (hi : 0 <= rIn) (hio : rIn < rOut) {x : Domain n} (hx : ‖x‖ <= rIn) :
    effectiveRadialCutoff rIn rOut x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  change 1 <= (rOut ^ 2 - ‖x‖ ^ 2) / (rOut ^ 2 - rIn ^ 2)
  apply (le_div_iff₀ (radius_square_gap_pos hi hio)).mpr
  have hs : ‖x‖ ^ 2 <= rIn ^ 2 := (sq_le_sq₀ (norm_nonneg x) hi).mpr hx
  nlinarith only [hs]

private theorem effectiveRadialArgument_nonpos {n : Nat} {rIn rOut : Real}
    (hi : 0 <= rIn) (hio : rIn < rOut) {x : Domain n} (hx : rOut <= ‖x‖) :
    effectiveRadialArgument rIn rOut x <= 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ (radius_square_gap_pos hi hio).le
  have hs : rOut ^ 2 <= ‖x‖ ^ 2 :=
    (sq_le_sq₀ (hi.trans hio.le) (norm_nonneg x)).mpr hx
  linarith only [hs]

theorem effectiveRadialCutoff_eq_zero {n : Nat} {rIn rOut : Real}
    (hi : 0 <= rIn) (hio : rIn < rOut) {x : Domain n} (hx : rOut <= ‖x‖) :
    effectiveRadialCutoff rIn rOut x = 0 :=
  Real.smoothTransition.zero_of_nonpos (effectiveRadialArgument_nonpos hi hio hx)

theorem effectiveRadialCutoff_tsupport_subset {n : Nat} {rIn rOut : Real}
    (hi : 0 <= rIn) (hio : rIn < rOut) :
    tsupport (effectiveRadialCutoff (n := n) rIn rOut) ⊆ Metric.closedBall 0 rOut := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hx (effectiveRadialCutoff_eq_zero hi hio (lt_of_not_ge h).le)

theorem effectiveRadialCutoff_hasCompactSupport {n : Nat} {rIn rOut : Real}
    (hi : 0 <= rIn) (hio : rIn < rOut) :
    HasCompactSupport (effectiveRadialCutoff (n := n) rIn rOut) :=
  (isCompact_closedBall (0 : Domain n) rOut).of_isClosed_subset
    (isClosed_tsupport _) (effectiveRadialCutoff_tsupport_subset hi hio)

private theorem radialArgument_hasFDerivAt {n : Nat} (rIn rOut : Real) (x : Domain n) :
    HasFDerivAt (effectiveRadialArgument rIn rOut)
      ((-2 / (rOut ^ 2 - rIn ^ 2)) • innerSL Real x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_sub (rOut ^ 2)).const_smul
    ((rOut ^ 2 - rIn ^ 2)⁻¹)
  have hfun : ((rOut ^ 2 - rIn ^ 2)⁻¹ • fun y : Domain n => rOut ^ 2 - ‖y‖ ^ 2) =
      effectiveRadialArgument rIn rOut := by
    funext y
    dsimp only [effectiveRadialArgument, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun] at h
  apply h.congr_fderiv
  ext y
  simp only [smul_apply, neg_apply, innerSL_apply_apply, smul_eq_mul]
  ring

theorem effectiveRadialCutoff_fderiv_apply {n : Nat} (rIn rOut : Real) (x v : Domain n) :
    fderiv Real (effectiveRadialCutoff rIn rOut) x v =
      (-2 / (rOut ^ 2 - rIn ^ 2)) *
        deriv Real.smoothTransition (effectiveRadialArgument rIn rOut x) * inner Real x v := by
  have hs : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (effectiveRadialArgument rIn rOut x))
      (effectiveRadialArgument rIn rOut x) :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _ |>.hasDerivAt
  change fderiv Real (Real.smoothTransition ∘ effectiveRadialArgument rIn rOut) x v = _
  rw [(hs.comp_hasFDerivAt x (radialArgument_hasFDerivAt rIn rOut x)).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

theorem effectiveRadialCutoff_fderiv_bound {n : Nat} {rIn rOut : Real}
    (hi : 0 <= rIn) (hio : rIn < rOut) (x : Domain n) :
    ‖fderiv Real (effectiveRadialCutoff rIn rOut) x‖ <=
      2 * rOut * (2 : Real) ^ 20 / (rOut ^ 2 - rIn ^ 2) := by
  have hg := radius_square_gap_pos hi hio
  have ho : 0 < rOut := lt_of_le_of_lt hi hio
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [Real.norm_eq_abs, effectiveRadialCutoff_fderiv_apply]
  by_cases hx : ‖x‖ <= rOut
  · have hs := smoothTransition_abs_deriv_le (effectiveRadialArgument rIn rOut x)
    have hinner : |inner Real x v| <= rOut * ‖v‖ :=
      (abs_real_inner_le_norm x v).trans
        (mul_le_mul_of_nonneg_right hx (norm_nonneg v))
    have hcoef : |(-2 : Real) / (rOut ^ 2 - rIn ^ 2)| =
        2 / (rOut ^ 2 - rIn ^ 2) := by
      rw [abs_div, abs_of_pos hg]
      norm_num
    calc
      _ = (2 / (rOut ^ 2 - rIn ^ 2)) *
          |deriv Real.smoothTransition (effectiveRadialArgument rIn rOut x)| *
          |inner Real x v| := by rw [abs_mul, abs_mul, hcoef]
      _ <= (2 / (rOut ^ 2 - rIn ^ 2)) * (2 : Real) ^ 20 * (rOut * ‖v‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) hinner
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [smoothTransition_deriv_eq_zero_of_nonpos
      (effectiveRadialArgument_nonpos hi hio (lt_of_not_ge hx).le)]
    simp only [mul_zero, zero_mul, abs_zero]
    positivity

theorem effectiveRadialCutoff_second_fderiv_apply {n : Nat} (rIn rOut : Real)
    (x v w : Domain n) :
    fderiv Real (fun z => fderiv Real (effectiveRadialCutoff rIn rOut) z v) x w =
      (-2 / (rOut ^ 2 - rIn ^ 2)) ^ 2 *
          deriv (deriv Real.smoothTransition) (effectiveRadialArgument rIn rOut x) *
          inner Real x v * inner Real x w +
        (-2 / (rOut ^ 2 - rIn ^ 2)) *
          deriv Real.smoothTransition (effectiveRadialArgument rIn rOut x) * inner Real v w := by
  let c : Real := -2 / (rOut ^ 2 - rIn ^ 2)
  let g : Domain n → Real := fun z => deriv Real.smoothTransition (effectiveRadialArgument rIn rOut z)
  have hs : HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) (effectiveRadialArgument rIn rOut x))
      (effectiveRadialArgument rIn rOut x) :=
    (Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two _ |>.hasDerivAt
  have hg : HasFDerivAt g
      (deriv (deriv Real.smoothTransition) (effectiveRadialArgument rIn rOut x) •
        (c • innerSL Real x)) x :=
    hs.comp_hasFDerivAt x (radialArgument_hasFDerivAt rIn rOut x)
  have hlin : HasFDerivAt (fun z : Domain n => inner Real z v) (innerSL Real v) x := by
    have h : HasFDerivAt (innerSL Real v) (innerSL Real v) x :=
      (innerSL Real v).hasFDerivAt
    have hfun : (innerSL Real v : Domain n → Real) = (fun z => inner Real z v) := by
      funext z
      simp only [innerSL_apply_apply, real_inner_comm]
    rw [hfun] at h
    exact h
  have hd := (hg.mul hlin).const_mul c
  have hfun : (fun z => c * (g z * inner Real z v)) =
      (fun z => fderiv Real (effectiveRadialCutoff rIn rOut) z v) := by
    funext z
    rw [effectiveRadialCutoff_fderiv_apply]
    dsimp only [c, g]
    ring
  change HasFDerivAt (fun z => c * (g z * inner Real z v)) _ x at hd
  rw [hfun] at hd
  rw [hd.fderiv]
  simp only [smul_apply, add_apply,
    innerSL_apply_apply, smul_eq_mul, c, g]
  rw [real_inner_comm v x]
  ring

private theorem radial_laplacian_coordinate_sum {n : Nat}
    (f : Domain n → Real) (hf : ContDiff Real ∞ f) (x : Domain n) :
    Laplacian.laplacian f x = ∑ i : Fin n,
      fderiv Real (fun z => fderiv Real f z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  have hDf : ContDiffOn Real ∞ (fderiv Real f) univ :=
    hf.contDiffOn.fderiv_of_isOpen isOpen_univ (by simp)
  have hdiff : DifferentiableAt Real (fderiv Real f) x :=
    (hDf.contDiffAt (isOpen_univ.mem_nhds (mem_univ x))).differentiableAt (by simp)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin n) Real)]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
    fderiv_clm_apply hdiff (differentiableAt_const _)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

theorem effectiveRadialCutoff_laplacian_formula {n : Nat} (rIn rOut : Real) (x : Domain n) :
    Laplacian.laplacian (effectiveRadialCutoff rIn rOut) x =
      (-2 / (rOut ^ 2 - rIn ^ 2)) ^ 2 *
          deriv (deriv Real.smoothTransition) (effectiveRadialArgument rIn rOut x) * ‖x‖ ^ 2 +
        (-2 / (rOut ^ 2 - rIn ^ 2)) *
          deriv Real.smoothTransition (effectiveRadialArgument rIn rOut x) * n := by
  rw [radial_laplacian_coordinate_sum _ (effectiveRadialCutoff_contDiff _ _) x]
  simp only [effectiveRadialCutoff_second_fderiv_apply,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul, mul_one,
    PiLp.single_apply, ite_true]
  simp_rw [mul_assoc, ← sq]
  simp only [Finset.sum_add_distrib]
  have hx : (∑ i : Fin n, (x i) ^ 2) = ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => Real) x).symm
  rw [← hx]
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem effectiveRadialCutoff_laplacian_bound {n : Nat} {rIn rOut : Real}
    (hi : 0 <= rIn) (hio : rIn < rOut) (x : Domain n) :
    |Laplacian.laplacian (effectiveRadialCutoff rIn rOut) x| <=
      4 * rOut ^ 2 * (2 : Real) ^ 40 / (rOut ^ 2 - rIn ^ 2) ^ 2 +
        2 * n * (2 : Real) ^ 20 / (rOut ^ 2 - rIn ^ 2) := by
  have ho : 0 < rOut := lt_of_le_of_lt hi hio
  have hg := radius_square_gap_pos hi hio
  rw [effectiveRadialCutoff_laplacian_formula]
  by_cases hx : ‖x‖ <= rOut
  · have hs1 := smoothTransition_abs_deriv_le (effectiveRadialArgument rIn rOut x)
    have hs2 := smoothTransition_abs_deriv_deriv_le (effectiveRadialArgument rIn rOut x)
    have hsq : ‖x‖ ^ 2 <= rOut ^ 2 := (sq_le_sq₀ (norm_nonneg x) ho.le).mpr hx
    have hc : |(-2 : Real) / (rOut ^ 2 - rIn ^ 2)| = 2 / (rOut ^ 2 - rIn ^ 2) := by
      rw [abs_div, abs_of_pos hg]
      norm_num
    calc
      _ <= |(-2 / (rOut ^ 2 - rIn ^ 2)) ^ 2 *
          deriv (deriv Real.smoothTransition) (effectiveRadialArgument rIn rOut x) * ‖x‖ ^ 2| +
          |(-2 / (rOut ^ 2 - rIn ^ 2)) *
          deriv Real.smoothTransition (effectiveRadialArgument rIn rOut x) * n| := abs_add_le _ _
      _ = (2 / (rOut ^ 2 - rIn ^ 2)) ^ 2 *
          |deriv (deriv Real.smoothTransition) (effectiveRadialArgument rIn rOut x)| * ‖x‖ ^ 2 +
          (2 / (rOut ^ 2 - rIn ^ 2)) *
          |deriv Real.smoothTransition (effectiveRadialArgument rIn rOut x)| * n := by
        simp only [abs_mul, abs_pow, hc, abs_of_nonneg (sq_nonneg ‖x‖),
          abs_of_nonneg (show (0 : Real) <= (n : Real) by positivity)]
      _ <= (2 / (rOut ^ 2 - rIn ^ 2)) ^ 2 * (2 : Real) ^ 40 * rOut ^ 2 +
          (2 / (rOut ^ 2 - rIn ^ 2)) * (2 : Real) ^ 20 * n :=
        add_le_add
          (mul_le_mul (mul_le_mul_of_nonneg_left hs2 (sq_nonneg _)) hsq
            (sq_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs1 (by positivity))
            (Nat.cast_nonneg n))
      _ = _ := by field_simp [ne_of_gt hg]; ring
  · rw [smoothTransition_deriv_eq_zero_of_nonpos
      (effectiveRadialArgument_nonpos hi hio (lt_of_not_ge hx).le),
      smoothTransition_deriv_deriv_eq_zero_of_nonpos
      (effectiveRadialArgument_nonpos hi hio (lt_of_not_ge hx).le)]
    simp only [mul_zero, zero_mul, zero_add, abs_zero]
    positivity

/-- The fixed main cutoff is the corresponding member of the explicit radial family. -/
theorem effectiveBallCutoff_eq_radial {n : Nat} :
    effectiveBallCutoff (n := n) = effectiveRadialCutoff (2/3) (3/4) := by
  funext x
  apply congrArg Real.smoothTransition
  dsimp only [effectiveBallCutoffArgument, effectiveRadialArgument]
  ring

theorem effectiveBallCutoff_tsupport_subset {n : Nat} :
    tsupport (effectiveBallCutoff (n := n)) ⊆ Metric.closedBall 0 (3/4 : Real) := by
  rw [effectiveBallCutoff_eq_radial]
  exact effectiveRadialCutoff_tsupport_subset (by norm_num) (by norm_num)

theorem effectiveBallCutoff_hasCompactSupport {n : Nat} :
    HasCompactSupport (effectiveBallCutoff (n := n)) := by
  rw [effectiveBallCutoff_eq_radial]
  exact effectiveRadialCutoff_hasCompactSupport (by norm_num) (by norm_num)

theorem effectiveBallCutoff_fderiv_bound {n : Nat} (x : Domain n) :
    ‖fderiv Real effectiveBallCutoff x‖ <= (2 : Real)^24 := by
  rw [effectiveBallCutoff_eq_radial]
  exact (effectiveRadialCutoff_fderiv_bound (by norm_num) (by norm_num) x).trans (by norm_num)

theorem effectiveBallCutoff_laplacian_bound {n : Nat} (x : Domain n) :
    |Laplacian.laplacian effectiveBallCutoff x| <=
      (2 : Real)^48 + (2 : Real)^25 * n := by
  rw [effectiveBallCutoff_eq_radial]
  apply (effectiveRadialCutoff_laplacian_bound (by norm_num) (by norm_num) x).trans
  norm_num
  nlinarith only [show (0 : Real) <= (n : Real) by positivity]

end

end StationaryHarmonicMaps.Analysis

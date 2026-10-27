module

public import StationaryHarmonicMaps.Analysis.BallSuperlevelMeasure
public import HolderToCK.Foundation.BallVolume
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Actual extended dyadic ball averages

The dyadic supremum uses every integer scale, including arbitrarily small
radii. Its values remain extended nonnegative reals. Finite windows cover
the integer interval from minus N to N, and increase to the literal full
supremum. Actual global AE equality preserves every ball integral.
-/

@[expose] public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The actual extended average over a positive-radius Euclidean ball. -/
noncomputable def centeredBallAverageENN {n : ℕ}
    (f : Domain n → ℝ≥0∞) (x : Domain n) (r : PositiveRadius) : ℝ≥0∞ :=
  (volume (Metric.ball x r.val))⁻¹ * ∫⁻ y in Metric.ball x r.val, f y

/-- The literal extended supremum over every integer dyadic radius. -/
noncomputable def dyadicBallMaximal {n : ℕ} (f : Domain n → ℝ≥0∞) (x : Domain n) : ℝ≥0∞ :=
  ⨆ j : ℤ, centeredBallAverageENN f x ⟨(2 : ℝ)^j, zpow_pos (by norm_num) j⟩

/-- The actual finite dyadic window containing all integer exponents from -N to N. -/
noncomputable def dyadicBallMaximalWindow {n : ℕ}
    (f : Domain n → ℝ≥0∞) (N : ℕ) (x : Domain n) : ℝ≥0∞ :=
  (Finset.Icc (-(N : ℤ)) (N : ℤ)).sup
    (fun j => centeredBallAverageENN f x ⟨(2 : ℝ)^j, zpow_pos (by norm_num) j⟩)

private theorem volume_ball_center_eq {n : ℕ} (x : Domain n) (r : PositiveRadius) :
    volume (Metric.ball x r.val) = volume (Metric.ball (0 : Domain n) r.val) := by
  rw [Measure.addHaar_ball_of_pos volume x r.property,
    Measure.addHaar_ball_of_pos volume (0 : Domain n) r.property]

/-- A single global AE equality preserves every actual centered ball average at every point. -/
theorem centeredBallAverageENN_congr_ae {n : ℕ} {f g : Domain n → ℝ≥0∞}
    (hfg : f =ᵐ[volume] g) (x : Domain n) (r : PositiveRadius) :
    centeredBallAverageENN f x r = centeredBallAverageENN g x r := by
  unfold centeredBallAverageENN
  rw [lintegral_congr_ae (ae_restrict_of_ae hfg)]

private theorem measurable_ball_average_of_measurable {n : ℕ}
    (f : Domain n → ℝ≥0∞) (hf : Measurable f) (r : PositiveRadius) :
    Measurable (fun x => centeredBallAverageENN f x r) := by
  let S : Set (Domain n × Domain n) := {p | p.2 ∈ Metric.ball p.1 r.val}
  have hS : MeasurableSet S :=
    (isOpen_lt (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  have hJoint : Measurable (S.indicator (fun p : Domain n × Domain n => f p.2)) :=
    (hf.comp measurable_snd).indicator hS
  have hI : Measurable (fun x => ∫⁻ y in Metric.ball x r.val, f y) := by
    convert hJoint.lintegral_prod_right' (ν := (volume : Measure (Domain n))) using 1
    funext x
    rw [← lintegral_indicator measurableSet_ball]
    rfl
  unfold centeredBallAverageENN
  simp_rw [volume_ball_center_eq]
  exact measurable_const.mul hI

/-- Actual AE measurability suffices for measurable pointwise ball averages. -/
theorem measurable_centeredBallAverageENN {n : ℕ}
    (f : Domain n → ℝ≥0∞) (hf : AEMeasurable f volume) (r : PositiveRadius) :
    Measurable (fun x => centeredBallAverageENN f x r) := by
  have hEq : (fun x => centeredBallAverageENN f x r) =
      (fun x => centeredBallAverageENN (hf.mk f) x r) :=
    funext (fun x => centeredBallAverageENN_congr_ae hf.ae_eq_mk x r)
  rw [hEq]
  exact measurable_ball_average_of_measurable (hf.mk f) hf.measurable_mk r

/-- The literal full dyadic supremum is measurable, with infinite values permitted. -/
theorem measurable_dyadicBallMaximal {n : ℕ}
    (f : Domain n → ℝ≥0∞) (hf : AEMeasurable f volume) :
    Measurable (dyadicBallMaximal f) :=
  Measurable.iSup (fun j : ℤ => measurable_centeredBallAverageENN f hf
    ⟨(2 : ℝ)^j, zpow_pos (by norm_num) j⟩)

/-- Every genuine finite dyadic window is measurable. -/
theorem measurable_dyadicBallMaximalWindow {n : ℕ}
    (f : Domain n → ℝ≥0∞) (hf : AEMeasurable f volume) (N : ℕ) :
    Measurable (dyadicBallMaximalWindow f N) := by
  unfold dyadicBallMaximalWindow
  simp_rw [Finset.sup_eq_iSup]
  exact Measurable.iSup (fun j : ℤ => Measurable.iSup (fun _ =>
    measurable_centeredBallAverageENN f hf ⟨(2 : ℝ)^j, zpow_pos (by norm_num) j⟩))

/-- Each finite window is bounded by the literal full dyadic supremum. -/
theorem dyadicBallMaximalWindow_le {n : ℕ}
    (f : Domain n → ℝ≥0∞) (N : ℕ) (x : Domain n) :
    dyadicBallMaximalWindow f N x ≤ dyadicBallMaximal f x := by
  apply Finset.sup_le_iff.mpr
  intro j _hj
  exact le_iSup (fun j : ℤ => centeredBallAverageENN f x
    ⟨(2 : ℝ)^j, zpow_pos (by norm_num) j⟩) j

/-- Increasing the true two-sided window adds scales without changing any original average. -/
theorem dyadicBallMaximalWindow_monotone {n : ℕ}
    (f : Domain n → ℝ≥0∞) (x : Domain n) : Monotone (fun N => dyadicBallMaximalWindow f N x) := by
  intro N M hNM
  apply Finset.sup_mono
  intro j hj
  have H := Finset.mem_Icc.mp hj
  apply Finset.mem_Icc.mpr
  constructor <;> omega

/-- The increasing finite windows recover the full integer-scale supremum exactly. -/
theorem iSup_dyadicBallMaximalWindow {n : ℕ} (f : Domain n → ℝ≥0∞) (x : Domain n) :
    (⨆ N : ℕ, dyadicBallMaximalWindow f N x) = dyadicBallMaximal f x := by
  apply le_antisymm
  · exact iSup_le (fun N => dyadicBallMaximalWindow_le f N x)
  · refine iSup_le fun j => ?_
    have hj : j ∈ Finset.Icc (-(j.natAbs : ℤ)) (j.natAbs : ℤ) := by
      apply Finset.mem_Icc.mpr
      have hp := Int.le_natAbs (a := j)
      have hn := Int.le_natAbs (a := -j)
      simp only [Int.natAbs_neg] at hn
      constructor <;> omega
    apply le_iSup_of_le j.natAbs
    change centeredBallAverageENN f x ⟨(2 : ℝ)^j, zpow_pos (by norm_num) j⟩ ≤
      (Finset.Icc (-(j.natAbs : ℤ)) (j.natAbs : ℤ)).sup
        (fun k => centeredBallAverageENN f x ⟨(2 : ℝ)^k, zpow_pos (by norm_num) k⟩)
    exact Finset.le_sup (f := fun k : ℤ => centeredBallAverageENN f x
      ⟨(2 : ℝ)^k, zpow_pos (by norm_num) k⟩) hj

private theorem volume_ball_two_mul {n : ℕ} (x : Domain n) {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball x (2*r)) = ENNReal.ofReal ((2 : ℝ)^n) * volume (Metric.ball x r) := by
  rw [Measure.addHaar_ball_of_pos volume x (by positivity : 0 < 2*r),
    Measure.addHaar_ball_of_pos volume x hr]
  simp only [finrank_euclideanSpace, Fintype.card_fin, mul_pow,
    ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n), mul_assoc]

private theorem inverse_ball_volume_le {a b C : ℝ≥0∞}
    (ha : a ≠ 0) (ha' : a ≠ ∞) (hb : b ≠ 0) (hb' : b ≠ ∞)
    (hba : b ≤ C*a) : a⁻¹ ≤ C*b⁻¹ := by
  calc
    _ = b*(a⁻¹*b⁻¹) := by
      calc
        _ = a⁻¹*(b*b⁻¹) := by rw [ENNReal.mul_inv_cancel hb hb',mul_one]
        _ = _ := by ac_rfl
    _ ≤ (C*a)*(a⁻¹*b⁻¹) := mul_le_mul_of_nonneg_right hba zero_le
    _ = C*b⁻¹ := by
      calc
        _ = C*(a*a⁻¹)*b⁻¹ := by ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel ha ha',mul_one]

/-- Every real positive radius is controlled by the actual dyadic supremum, at every center, with infinite values allowed. -/
theorem centeredBallAverageENN_le_dyadicBallMaximal {n : ℕ}
    (f : Domain n → ℝ≥0∞) (x : Domain n) (r : PositiveRadius) :
    centeredBallAverageENN f x r ≤ ENNReal.ofReal ((2 : ℝ)^n) * dyadicBallMaximal f x := by
  obtain ⟨j,hj⟩ := exists_mem_Ioc_zpow r.property (by norm_num : (1 : ℝ)<2)
  have hq : 0 < (2 : ℝ)^(j+1) := zpow_pos (by norm_num) _
  have hqr : (2 : ℝ)^(j+1) ≤ 2*r.val := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ)≠0),zpow_one]
    linarith only [hj.1]
  have hvol : volume (Metric.ball x ((2 : ℝ)^(j+1))) ≤
      ENNReal.ofReal ((2 : ℝ)^n) * volume (Metric.ball x r.val) :=
    (measure_mono (Metric.ball_subset_ball hqr)).trans_eq (volume_ball_two_mul x r.property)
  have hInv := inverse_ball_volume_le
    (Metric.measure_ball_pos volume x r.property).ne' measure_ball_ne_top
    (Metric.measure_ball_pos volume x hq).ne' measure_ball_ne_top hvol
  have hInt : (∫⁻ y in Metric.ball x r.val, f y) ≤
      ∫⁻ y in Metric.ball x ((2 : ℝ)^(j+1)), f y :=
    lintegral_mono_set (Metric.ball_subset_ball hj.2)
  calc
    _ ≤ (ENNReal.ofReal ((2 : ℝ)^n) * (volume (Metric.ball x ((2 : ℝ)^(j+1))))⁻¹) *
        ∫⁻ y in Metric.ball x ((2 : ℝ)^(j+1)), f y :=
      mul_le_mul hInv hInt zero_le zero_le
    _ = ENNReal.ofReal ((2 : ℝ)^n) * centeredBallAverageENN f x ⟨(2 : ℝ)^(j+1),hq⟩ := by
      rw [centeredBallAverageENN,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (le_iSup (fun j : ℤ => centeredBallAverageENN f x
        ⟨(2 : ℝ)^j,zpow_pos (by norm_num) j⟩) (j+1)) zero_le

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.GrandKernelLocalization
public import HolderToCK.Foundation.BallVolume

/-!
# Actual mass-normalized Whitney kernel pairings

The original grand maximal good point, the actual high-scale derivative
and support bounds, and the proved normalized Whitney mass lower bound
control the original kernel integral divided by that mass. No average
or compensation-coefficient bound is assumed.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual nearby grand-good data and a true Whitney mass lower bound produce the original normalized kernel pairing estimate uniformly over centers and scales. -/
theorem exists_whitney_mass_normalized_kernel_bound (n : ℕ) (B : ℝ) (hB : 0<B) :
    ∃ D : ℝ,0<D ∧ ∀ (f : Domain n → ℝ),Integrable f volume →
      let J := fun a => ⨆ s : PositiveRadius, ⨆ κ : Domain n → ℝ,
        ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
        ⨆ (_ : tsupport κ⊆Metric.ball a s.val),
        ⨆ (_ : ∀ x∈Metric.ball a s.val,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤s.val^(-(n : ℝ)-1)),
          ENNReal.ofReal |∫ x,κ x*f x|
      ∀ (b y : Domain n) (r L m : ℝ),0<r → 0≤L → dist y b≤20*r →
        J y≤ENNReal.ofReal (2*L) →
        volume.real (Metric.ball b (5*r))/(60 : ℝ)^n≤m →
        ∀ (κ : Domain n → ℝ),ContDiff ℝ ∞ κ → HasCompactSupport κ →
          tsupport κ⊆Metric.ball b (10*r) →
          (∀ x,‖fderiv ℝ κ x‖≤B/r) →
          0<m ∧ Integrable (fun x => κ x*f x) volume ∧
            |∫ x,κ x*f x|/m≤D*L := by
  let V : ℝ := volume.real (Metric.ball (0 : Domain n) 1)
  have hV : 0<V := HolderToCK.ball_volume_real_pos 0 (by norm_num : (0 : ℝ)<1)
  let D : ℝ := (2*B*(40 : ℝ)^(n+1)*(60 : ℝ)^n)/((5 : ℝ)^n*V)
  have hD : 0<D := by dsimp only [D];positivity
  refine ⟨D,hD,?_⟩
  intro f hf J b y r L m hr hL hDist hGood hMass κ hκ hcκ hsκ hDκ
  have hMassPos : 0<m :=
    (div_pos (HolderToCK.ball_volume_real_pos b (by positivity : 0<5*r))
      (pow_pos (by norm_num : (0 : ℝ)<60) n)).trans_le hMass
  have hSupp : tsupport κ⊆Metric.ball y (40*r) := by
    intro x hx
    have hxb : dist x b<10*r := hsκ hx
    have H := dist_triangle x b y
    rw [dist_comm b y] at H
    change dist x y<40*r
    linarith only [H,hxb,hDist,hr]
  have hDerivative (x : Domain n) (_hx : x∈Metric.ball y (40*r)) (i : Fin n) :
      |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤B/r := by
    calc
      _ ≤ ‖fderiv ℝ κ x‖*‖EuclideanSpace.single i (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ κ x‖ := by simp only [PiLp.norm_single,norm_one,mul_one]
      _ ≤ _ := hDκ x
  have hRaw := smooth_grand_kernel_localized_pairing_le f y (40*r) (B/r)
    (by positivity) (div_pos hB hr) κ hκ hcκ hSupp hDerivative
  have hRawR : |∫ x,κ x*f x|≤((B/r)*(40*r)^(n+1))*(2*L) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0≤((B/r)*(40*r)^(n+1))*(2*L))).mp
    calc
      _ ≤ ENNReal.ofReal ((B/r)*(40*r)^(n+1))*J y := hRaw
      _ ≤ ENNReal.ofReal ((B/r)*(40*r)^(n+1))*ENNReal.ofReal (2*L) :=
        mul_le_mul_of_nonneg_left hGood zero_le
      _ = _ := (ENNReal.ofReal_mul (by positivity : 0≤(B/r)*(40*r)^(n+1))).symm
  have hScale : D*L*(volume.real (Metric.ball b (5*r))/(60 : ℝ)^n)=
      ((B/r)*(40*r)^(n+1))*(2*L) := by
    rw [HolderToCK.ball_volume_real b (by positivity : 0<5*r)]
    change ((2*B*(40 : ℝ)^(n+1)*(60 : ℝ)^n)/((5 : ℝ)^n*V))*L*
      (((5*r)^n*V)/(60 : ℝ)^n)=_
    rw [mul_pow,pow_succ]
    field_simp [hr.ne',hV.ne']
    ring
  obtain ⟨M,hM⟩ := hcκ.exists_bound_of_continuous hκ.continuous
  have hI : Integrable (fun x => κ x*f x) volume := hf.bdd_mul hκ.continuous.aestronglyMeasurable
    (Eventually.of_forall hM)
  refine ⟨hMassPos,hI,(div_le_iff₀ hMassPos).mpr ?_⟩
  calc
    _ ≤ ((B/r)*(40*r)^(n+1))*(2*L) := hRawR
    _ = D*L*(volume.real (Metric.ball b (5*r))/(60 : ℝ)^n) := hScale.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hMass (mul_nonneg hD.le hL)

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.GrandKernelLocalization
public import StationaryHarmonicMaps.Analysis.ScaledBallCutoff
public import HolderToCK.Foundation.BallVolume

/-!
# Actual cancellation pieces from a nearby grand maximal good point

Uniform scaled cutoffs are produced from their fixed smooth profile.
Their original integrals and positive masses define the cutoff averages.
A nearby good point of the literal grand maximal field bounds those
averages at the original level. The resulting original cutoff pieces
are integrable and have exactly zero integral.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The actual cutoff average gives a genuine integrable zero-mean piece on an arbitrary measure space. -/
theorem integrable_zero_mean_cutoff_piece {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f η : X → ℝ) (hη : Integrable η μ) (hηf : Integrable (fun x=>η x*f x) μ)
    (hmass : (∫ x,η x ∂μ)≠0) :
    let c := (∫ x,η x*f x ∂μ)/(∫ x,η x ∂μ)
    Integrable (fun x=>η x*(f x-c)) μ ∧ (∫ x,η x*(f x-c) ∂μ)=0 := by
  intro c
  have hI : Integrable (fun x=>η x*f x-η x*c) μ := hηf.sub (hη.mul_const c)
  have hEq : (fun x=>η x*(f x-c))=(fun x=>η x*f x-η x*c) := by funext x;ring
  refine ⟨hEq.symm ▸ hI,?_⟩
  rw [hEq,integral_sub hηf (hη.mul_const c),integral_mul_const]
  dsimp only [c]
  field_simp [hmass]
  ring

/-- Original integrable data and one actual nearby grand-maximal good point produce a scaled cutoff, its controlled original average and its true zero-mean local piece. -/
theorem exists_grand_good_point_cutoff_piece (n : ℕ) :
    ∃ D : ℝ,0<D ∧ ∀ (f : Domain n → ℝ),Integrable f volume →
      let J := fun a => ⨆ r : PositiveRadius, ⨆ κ : Domain n → ℝ,
        ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
        ⨆ (_ : tsupport κ⊆Metric.ball a r.val),
        ⨆ (_ : ∀ x∈Metric.ball a r.val,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤r.val^(-(n : ℝ)-1)),
          ENNReal.ofReal |∫ x,κ x*f x|
      ∀ (a y : Domain n) (r L : ℝ),0<r → 0≤L → dist y a≤8*r → J y≤ENNReal.ofReal L →
        ∃ η : Domain n → ℝ,ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
          tsupport η⊆Metric.ball a (2*r) ∧
          (∀ x∈Metric.closedBall a r,η x=1) ∧ (∀ x,0≤η x ∧ η x≤1) ∧
          let c := (∫ x,η x*f x)/(∫ x,η x)
          |c|≤D*L ∧ Integrable (fun x=>η x*(f x-c)) volume ∧
            (∫ x,η x*(f x-c))=0 ∧
            Function.support (fun x=>η x*(f x-c))⊆Metric.ball a (2*r) := by
  obtain ⟨C,hC,Hcut⟩ := exists_scaled_ball_cutoff n
  let V : ℝ := volume.real (Metric.ball (0 : Domain n) 1)
  have hV : 0<V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume (0 : Domain n) (by norm_num : (0 : ℝ)<1)).ne' measure_ball_ne_top
  let D : ℝ := (C*(10 : ℝ)^(n+1))/V
  have hD : 0<D := div_pos (mul_pos hC (pow_pos (by norm_num) _)) hV
  refine ⟨D,hD,?_⟩
  intro f hf J a y r L hr hL hya hGood
  obtain ⟨η,hη,hcη,hsη,hOne,hηBound,hDη⟩ := Hcut a r hr
  have hηI : Integrable η volume := hη.continuous.integrable_of_hasCompactSupport hcη
  have hηfI : Integrable (fun x=>η x*f x) volume := hf.bdd_mul hη.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x=>by rw [Real.norm_of_nonneg (hηBound x).1];exact (hηBound x).2)
  have hMass : r^n*V≤∫ x,η x := by
    have hMono := integral_mono_measure (Measure.restrict_le_self (s := Metric.ball a r))
      (Eventually.of_forall fun x=>(hηBound x).1) hηI
    have hBall : (∫ x in Metric.ball a r,η x)=volume.real (Metric.ball a r) := by
      rw [setIntegral_congr_fun measurableSet_ball (fun x hx=>hOne x (Metric.ball_subset_closedBall hx))]
      simp only [integral_const,smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply MeasurableSet.univ,univ_inter]
    rw [hBall,HolderToCK.ball_volume_real a hr] at hMono
    exact hMono
  have hMassPos : 0<∫ x,η x := (mul_pos (pow_pos hr _) hV).trans_le hMass
  have hSupportY : tsupport η⊆Metric.ball y (10*r) := by
    intro x hx
    have hxy : dist x y≤dist x a+dist a y := dist_triangle _ _ _
    have hxa : dist x a<2*r := hsη hx
    have hay : dist a y≤8*r := by simpa only [dist_comm] using hya
    change dist x y<10*r
    linarith only [hxy,hxa,hay]
  have hCoordinate (x : Domain n) (_hx : x∈Metric.ball y (10*r)) (i : Fin n) :
      |fderiv ℝ η x (EuclideanSpace.single i 1)|≤C/r := by
    calc
      _ = ‖fderiv ℝ η x (EuclideanSpace.single i 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ η x‖*‖EuclideanSpace.single i (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ η x‖ := by simp
      _ ≤ _ := hDη x
  have hPair := smooth_grand_kernel_localized_pairing_le f y (10*r) (C/r)
    (by positivity) (div_pos hC hr) η hη hcη hSupportY hCoordinate
  have hENN : ENNReal.ofReal |∫ x,η x*f x|≤ENNReal.ofReal (((C/r)*(10*r)^(n+1))*L) := by
    calc
      _ ≤ ENNReal.ofReal ((C/r)*(10*r)^(n+1))*J y := hPair
      _ ≤ ENNReal.ofReal ((C/r)*(10*r)^(n+1))*ENNReal.ofReal L :=
        mul_le_mul_of_nonneg_left hGood zero_le
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hRaw : |∫ x,η x*f x|≤((C/r)*(10*r)^(n+1))*L :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hENN
  have hScale : ((C/r)*(10*r)^(n+1))*L=(D*L)*(r^n*V) := by
    dsimp only [D]
    rw [mul_pow,pow_succ r]
    field_simp [hr.ne',hV.ne']
  rw [hScale] at hRaw
  have hAverage : |(∫ x,η x*f x)/(∫ x,η x)|≤D*L := by
    rw [abs_div,abs_of_pos hMassPos,div_le_iff₀ hMassPos]
    exact hRaw.trans (mul_le_mul_of_nonneg_left hMass (mul_nonneg hD.le hL))
  obtain ⟨hBadI,hZero⟩ := integrable_zero_mean_cutoff_piece volume f η hηI hηfI hMassPos.ne'
  refine ⟨η,hη,hcη,hsη,hOne,hηBound,hAverage,hBadI,hZero,?_⟩
  intro x hx
  apply hsη
  apply subset_tsupport η
  intro hηx
  exact hx (by dsimp only;rw [hηx,zero_mul])

end StationaryHarmonicMaps.Analysis

end

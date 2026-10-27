module

public import StationaryHarmonicMaps.Analysis.WhitneyNestedScales
public import StationaryHarmonicMaps.Analysis.WhitneyNormalizedKernel

/-!
# The actual compensation coefficient of two Whitney levels

The original high average and the mixed low/high numerator are both
estimated against the same actual nearby high-level grand-good point.
Nested bad-set geometry supplies the product derivative estimate. The
actual positive high mass normalizes both integrals; no desired average
or compensation bound is an input.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original L1 function, actual nested Whitney cutoffs and original high good point produce the true high average and compensation-coefficient bounds. -/
theorem exists_whitney_compensation_coefficient_bound (n : ℕ) (B : ℝ) (hB : 0<B) :
    ∃ C : ℝ,0<C ∧ ∀ (f : Domain n → ℝ),Integrable f volume →
      let J := fun a => ⨆ s : PositiveRadius, ⨆ κ : Domain n → ℝ,
        ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
        ⨆ (_ : tsupport κ⊆Metric.ball a s.val),
        ⨆ (_ : ∀ x∈Metric.ball a s.val,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤s.val^(-(n : ℝ)-1)),
          ENNReal.ofReal |∫ x,κ x*f x|
      ∀ (Slo Shi : Set (Domain n)),Shi⊆Slo → Sloᶜ.Nonempty →
        ∀ (a b : Domain n),
          let rlo := Metric.infDist a Sloᶜ/20
          let rhi := Metric.infDist b Shiᶜ/20
          0<rhi → ∀ (y : Domain n) (L : ℝ),0≤L → dist y b≤20*rhi →
            J y≤ENNReal.ofReal (2*L) →
            ∀ (θlo θhi : Domain n → ℝ),
              ContDiff ℝ ∞ θlo → HasCompactSupport θlo →
              ContDiff ℝ ∞ θhi → HasCompactSupport θhi →
              tsupport θlo⊆Metric.ball a (10*rlo) →
              tsupport θhi⊆Metric.ball b (10*rhi) →
              (∀ x,0≤θlo x ∧ θlo x≤1) → (∀ x,0≤θhi x ∧ θhi x≤1) →
              (∀ x,‖fderiv ℝ θlo x‖≤B/rlo) → (∀ x,‖fderiv ℝ θhi x‖≤B/rhi) →
              volume.real (Metric.ball b (5*rhi))/(60 : ℝ)^n≤∫ x,θhi x →
              let m := ∫ x,θhi x
              let c := (∫ x,θhi x*f x)/m
              let d := (∫ x,θlo x*(θhi x*(f x-c)))/m
              0<m ∧ |c|≤C*L ∧
                (∀ x,‖fderiv ℝ (fun z => θlo z*θhi z) x‖≤4*B/rhi) ∧
                Integrable (fun x => θlo x*(θhi x*(f x-c))) volume ∧ |d|≤C*L := by
  obtain ⟨D,hD,Hkernel⟩ := exists_whitney_mass_normalized_kernel_bound n (4*B) (by positivity)
  let C : ℝ := 2*D
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro f hf J Slo Shi hNested hComp a b rlo rhi hrhi y L hL hDist hGood
    θlo θhi hLo hcLo hHi hcHi hsLo hsHi hLoBound hHiBound hDLo hDHi hMass m c d
  let κ := fun x => θlo x*θhi x
  have hκ : ContDiff ℝ ∞ κ := hLo.mul hHi
  have hcκ : HasCompactSupport κ := hcLo.mul_right
  have hsκ : tsupport κ⊆Metric.ball b (10*rhi) :=
    (tsupport_mul_subset_right (f := θlo) (g := θhi)).trans hsHi
  have hProductD : ∀ x,‖fderiv ℝ κ x‖≤4*B/rhi := by
    by_cases hOverlap : (Metric.ball a (10*rlo)∩Metric.ball b (10*rhi)).Nonempty
    · obtain ⟨hrlo,_hrhi,hRatio,_hCenter,_hSub⟩ :=
        nested_whitney_tenfold_geometry Slo Shi hNested hComp a b hOverlap
      exact norm_fderiv_nested_cutoff_product_le θlo θhi hLo hHi hLoBound hHiBound
        B rlo rhi hB hrlo hrhi hRatio hDLo hDHi
    · have hZero : κ=fun _ => 0 := by
        funext x
        by_cases hx : x∈Metric.ball a (10*rlo)
        · have hxHi : x∉tsupport θhi := fun H => hOverlap ⟨x,hx,hsHi H⟩
          change θlo x*θhi x=0
          rw [image_eq_zero_of_notMem_tsupport hxHi,mul_zero]
        · have hxLo : x∉tsupport θlo := fun H => hx (hsLo H)
          change θlo x*θhi x=0
          rw [image_eq_zero_of_notMem_tsupport hxLo,zero_mul]
      intro x
      rw [hZero,fderiv_const_apply,norm_zero]
      positivity
  have hHiD4 (x : Domain n) : ‖fderiv ℝ θhi x‖≤4*B/rhi := by
    apply (hDHi x).trans
    calc
      B/rhi ≤ 4*(B/rhi) := by have H := div_pos hB hrhi;linarith
      _ = _ := by ring
  obtain ⟨hMassPos,hHiF,hCraw⟩ := Hkernel f hf b y rhi L m hrhi hL hDist hGood hMass
    θhi hHi hcHi hsHi hHiD4
  have hcD : |c|≤D*L := by
    change |(∫ x,θhi x*f x)/m|≤D*L
    rw [abs_div,abs_of_pos hMassPos]
    exact hCraw
  obtain ⟨_hMassPos,hκF,hκRaw⟩ := Hkernel f hf b y rhi L m hrhi hL hDist hGood hMass
    κ hκ hcκ hsκ hProductD
  have hκI : Integrable κ volume := hκ.continuous.integrable_of_hasCompactSupport hcκ
  have hHiI : Integrable θhi volume := hHi.continuous.integrable_of_hasCompactSupport hcHi
  have hκNonneg (x : Domain n) : 0≤κ x := mul_nonneg (hLoBound x).1 (hHiBound x).1
  have hκLe (x : Domain n) : κ x≤θhi x :=
    mul_le_of_le_one_left (hHiBound x).1 (hLoBound x).2
  have hIMass : 0≤∫ x,κ x := integral_nonneg hκNonneg
  have hMassLe : (∫ x,κ x)≤m := integral_mono hκI hHiI hκLe
  have hRatio : (∫ x,κ x)/m≤1 := (div_le_iff₀ hMassPos).mpr (by simpa only [one_mul] using hMassLe)
  have hFun : (fun x => θlo x*(θhi x*(f x-c)))=(fun x => κ x*f x-c*κ x) := by
    funext x
    dsimp only [κ]
    ring
  have hNumerator : (∫ x,θlo x*(θhi x*(f x-c)))=(∫ x,κ x*f x)-c*(∫ x,κ x) := by
    rw [hFun,integral_sub hκF (hκI.const_mul c),integral_const_mul]
  have hNumI : Integrable (fun x => θlo x*(θhi x*(f x-c))) volume := by
    rw [hFun]
    exact hκF.sub (hκI.const_mul c)
  have hCC : |c|≤C*L := hcD.trans (by dsimp only [C];nlinarith only [hD,hL])
  refine ⟨hMassPos,hCC,hProductD,hNumI,?_⟩
  change |(∫ x,θlo x*(θhi x*(f x-c)))/m|≤C*L
  rw [abs_div,abs_of_pos hMassPos,hNumerator]
  calc
    _ ≤ (|∫ x,κ x*f x|+|c*(∫ x,κ x)|)/m :=
      div_le_div_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using norm_sub_le (∫ x,κ x*f x) (c*(∫ x,κ x))) hMassPos.le
    _ = |∫ x,κ x*f x|/m+|c| * ((∫ x,κ x)/m) := by
      rw [abs_mul,abs_of_nonneg hIMass]
      ring
    _ ≤ D*L+|c| := add_le_add hκRaw (mul_le_of_le_one_right (abs_nonneg c) hRatio)
    _ ≤ D*L+D*L := add_le_add le_rfl hcD
    _ = _ := by dsimp only [C];ring

end StationaryHarmonicMaps.Analysis

end

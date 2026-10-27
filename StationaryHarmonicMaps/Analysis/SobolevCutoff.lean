module

public import StationaryHarmonicMaps.Analysis.SobolevLinearOperations
public import HarmonicMaps.Analysis.SobolevCutoff
public import HarmonicMaps.SobolevRestriction
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Actual compact Sobolev cutoffs on the full source space

Local data on the compact cutoff support give global L² and L¹ products.
Testing the original weak gradient with χφ proves the full-space weak
product rule. The literal function χ(u-c) already vanishes off the domain;
no boundedness of u or of the product is asserted.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- A compact continuous scalar multiplier turns local L¹ data into a genuine global L¹ product. -/
theorem integrable_compact_smul_of_locallyIntegrableOn {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : OpenDomain n} {f : Domain n → E}
    (hf : LocallyIntegrableOn f Ω.val volume) {χ : Domain n → ℝ}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω.val) :
    Integrable (fun x => χ x • f x) volume := by
  have hK := hf.integrableOn_compact_subset hsχ hcχ
  have hχK := hχ.memLp_top_of_hasCompactSupport hcχ (volume.restrict (tsupport χ))
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp (hK.smul_of_top_right hχK)
  intro x hx
  by_contra hnot
  apply hx
  change χ x • f x = 0
  rw [image_eq_zero_of_notMem_tsupport hnot, zero_smul]

/-- Compact scalar multiplication produces actual global L² data from the local L² predicate. -/
theorem memLp_compact_smul_of_locallyMemL2 {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : OpenDomain n} {f : Domain n → E}
    (hf : LocallyMemL2 Ω f) {χ : Domain n → ℝ}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω.val) :
    MemLp (fun x => χ x • f x) 2 volume := by
  have hK := hf (tsupport χ) hcχ hsχ
  have hχK := hχ.memLp_top_of_hasCompactSupport hcχ (volume.restrict (tsupport χ))
  have hprod : MemLp (fun x => χ x • f x) 2 (volume.restrict (tsupport χ)) := hK.smul hχK
  have H := (memLp_indicator_iff_restrict (isClosed_tsupport χ).measurableSet).mpr hprod
  have heq : (tsupport χ).indicator (fun x => χ x • f x) = (fun x => χ x • f x) := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_smul]
  rw [heq] at H
  exact H

/-- Subtracting a constant preserves the original displayed local weak gradient. -/
theorem memW12Loc_sub_const {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (c : Ambient q) :
    MemW12Loc Ω (fun x => u x - c) Du := by
  have H := memW12Loc_add hu (memW12Loc_of_c1 Ω (f := fun _ : Domain n => -c) contDiff_const)
  have hmap : (u + fun _ : Domain n => -c) = (fun x => u x - c) := by
    funext x
    rfl
  have hgrad : (fun x i => Du x i + fderiv ℝ (fun _ : Domain n => -c) x
      (EuclideanSpace.single i 1)) = Du := by
    funext x i
    have hz : fderiv ℝ (fun _ : Domain n => -c) x = 0 := (hasFDerivAt_const (-c) x).fderiv
    rw [hz, zero_apply, add_zero]
  rw [hmap, hgrad] at H
  exact H

/-- The literal compact cutoff has a genuine finite Sobolev graph on the full source space. -/
theorem memW12_smoothCutoff_univ {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (χ : Domain n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω.val) :
    MemW12 (⟨Set.univ, isOpen_univ⟩ : OpenDomain n) (fun x => χ x • u x)
      (fun x i => χ x • Du x i + fderiv ℝ χ x (EuclideanSpace.single i 1) • u x) := by
  let dχ (i : Fin n) (x : Domain n) := fderiv ℝ χ x (EuclideanSpace.single i 1)
  have hdχ (i : Fin n) : ContDiff ℝ ∞ (dχ i) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcdχ (i : Fin n) : HasCompactSupport (dχ i) :=
    hcχ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hsdχ (i : Fin n) : tsupport (dχ i) ⊆ Ω.val :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsχ
  have hmapL := memLp_compact_smul_of_locallyMemL2 hu.2.1 hχ.continuous hcχ hsχ
  have hmapI := integrable_compact_smul_of_locallyIntegrableOn hu.1.1 hχ.continuous hcχ hsχ
  have hfirstL (i : Fin n) := memLp_compact_smul_of_locallyMemL2 (hu.2.2 i) hχ.continuous hcχ hsχ
  have hfirstI (i : Fin n) := integrable_compact_smul_of_locallyIntegrableOn
    (hu.1.2.1 i) hχ.continuous hcχ hsχ
  have hsecondL (i : Fin n) := memLp_compact_smul_of_locallyMemL2 hu.2.1
    (hdχ i).continuous (hcdχ i) (hsdχ i)
  have hsecondI (i : Fin n) := integrable_compact_smul_of_locallyIntegrableOn hu.1.1
    (hdχ i).continuous (hcdχ i) (hsdχ i)
  refine ⟨⟨hmapI.locallyIntegrable.locallyIntegrableOn Set.univ,
    (fun i => ((hfirstI i).add (hsecondI i)).locallyIntegrable.locallyIntegrableOn Set.univ), ?_⟩,
    ?_, ?_⟩
  · intro i φ hφ hcφ _hsφ
    have hprod := hφ.mul hχ
    have hcprod : HasCompactSupport (fun x => φ x * χ x) := hcχ.mul_left
    have hsprod : tsupport (fun x => φ x * χ x) ⊆ Ω.val := tsupport_mul_subset_right.trans hsχ
    have H := hu.1.2.2 i (fun x => φ x * χ x) hprod hcprod hsprod
    have hφL := hφ.continuous.memLp_top_of_hasCompactSupport hcφ volume
    have hdφL := ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport (hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)) volume
    have hA : Integrable (fun x => coordinateDerivative φ hφ i x • (χ x • u x)) volume :=
      hmapI.smul_of_top_right hdφL
    have hB : Integrable (fun x => φ x • (dχ i x • u x)) volume :=
      (hsecondI i).smul_of_top_right hφL
    have hC : Integrable (fun x => φ x • (χ x • Du x i)) volume :=
      (hfirstI i).smul_of_top_right hφL
    simp_rw [coordinateDerivative_mul hφ hχ, add_smul, mul_smul] at H
    change (∫ x in Ω.val, coordinateDerivative φ hφ i x • (χ x • u x) +
      φ x • (dχ i x • u x)) = -(∫ x in Ω.val, φ x • (χ x • Du x i)) at H
    have hzχ (x : Domain n) (hx : x ∉ Ω.val) : χ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hsχ h))
    have hzdχ (x : Domain n) (hx : x ∉ Ω.val) : dχ i x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hsdχ i h))
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      simp only [hzχ x hx, hzdχ x hx, zero_smul, smul_zero, add_zero]),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [hzχ x hx, zero_smul, smul_zero])] at H
    rw [integral_add hA hB] at H
    simp only [Measure.restrict_univ]
    change (∫ x, coordinateDerivative φ hφ i x • (χ x • u x)) =
      -(∫ x, φ x • (χ x • Du x i + dχ i x • u x))
    simp_rw [smul_add]
    rw [integral_add hC hB]
    apply eq_neg_iff_add_eq_zero.mpr
    calc
      _ = ((∫ x, coordinateDerivative φ hφ i x • (χ x • u x)) +
        ∫ x, φ x • (dχ i x • u x)) + ∫ x, φ x • (χ x • Du x i) := by abel
      _ = 0 := by rw [H, neg_add_cancel]
  · simpa only [Measure.restrict_univ] using hmapL
  · intro i
    change MemLp (fun x => χ x • Du x i + dχ i x • u x) 2 (volume.restrict Set.univ)
    rw [Measure.restrict_univ]
    exact (hfirstL i).add (hsecondL i)

/-- Subtracting any constant and multiplying by the actual cutoff gives the full-space Sobolev map. -/
theorem memW12_cutoff_sub_const_univ {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (c : Ambient q)
    (χ : Domain n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω.val) :
    MemW12 (⟨Set.univ, isOpen_univ⟩ : OpenDomain n) (fun x => χ x • (u x - c))
      (fun x i => χ x • Du x i + fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x - c)) :=
  memW12_smoothCutoff_univ (memW12Loc_sub_const hu c) χ hχ hcχ hsχ

/-- The same literal cutoff has finite Sobolev membership on the original open domain. -/
theorem memW12_cutoff_sub_const {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (c : Ambient q)
    (χ : Domain n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω.val) :
    MemW12 Ω (fun x => χ x • (u x - c))
      (fun x i => χ x • Du x i + fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x - c)) := by
  have H := memW12_cutoff_sub_const_univ hu c χ hχ hcχ hsχ
  have hm : MemLp (fun x => χ x • (u x - c)) 2 volume := by
    simpa only [Measure.restrict_univ] using H.2.1
  have hd (i : Fin n) : MemLp (fun x => χ x • Du x i +
      fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x - c)) 2 volume := by
    simpa only [Measure.restrict_univ] using H.2.2 i
  exact ⟨H.1.mono (subset_univ Ω.val), hm.restrict _, fun i => (hd i).restrict _⟩

end StationaryHarmonicMaps.Analysis

end

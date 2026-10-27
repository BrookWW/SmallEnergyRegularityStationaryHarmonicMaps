module

public import StationaryHarmonicMaps.Analysis.SobolevCutoff
public import StationaryHarmonicMaps.Analysis.ScalarVectorWeakEquation
public import StationaryHarmonicMaps.Analysis.OperatorFluxIntegrability
public import HolderToCK.Analysis.WeakPoissonLocality
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# The actual signed weak Poisson cutoff equation

For Δu=F the literal cutoff v=χ(u-c) has forcing
χF + 2 Σᵢ(∂ᵢχ)Duᵢ + (Δχ)(u-c). Compact support inside the original
open domain supplies full-space integrability and permits the original weak
identities to be tested with cutoff products.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem scalar_laplacian_eq_sum {n : ℕ} (χ : Domain n → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (x : Domain n) :
    Laplacian.laplacian χ x = ∑ i : Fin n,
      fderiv ℝ (fun y => fderiv ℝ χ y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right (m := ∞) (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ χ) x := hdf.differentiable (by simp) x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis χ
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

private theorem weak_gradient_compact_pairing_zero {n q : ℕ} {Ω : OpenDomain n}
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : HasWeakGradient Ω w Dw) (i : Fin n)
    (φ : Domain n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ Ω.val) (v : Ambient q) :
    Integrable (fun x => inner ℝ
      (fderiv ℝ φ x (EuclideanSpace.single i 1) • w x + φ x • Dw x i) v) volume ∧
    (∫ x, inner ℝ
      (fderiv ℝ φ x (EuclideanSpace.single i 1) • w x + φ x • Dw x i) v) = 0 := by
  have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdφ := hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hsdφ := (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsφ
  have hD := integrable_compact_smul_of_locallyIntegrableOn hw.1 hdφ hcdφ hsdφ
  have hG := integrable_compact_smul_of_locallyIntegrableOn (hw.2.1 i) hφ.continuous hcφ hsφ
  have H := hw.2.2 i φ hφ hcφ hsφ
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      change fderiv ℝ φ x (EuclideanSpace.single i 1) • w x = 0
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsdφ h)), zero_smul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsφ h)), zero_smul])] at H
  have hZero : (∫ x, fderiv ℝ φ x (EuclideanSpace.single i 1) • w x + φ x • Dw x i) = 0 := by
    rw [integral_add hD hG]
    change (∫ x, coordinateDerivative φ hφ i x • w x) + (∫ x, φ x • Dw x i) = 0
    rw [H, neg_add_cancel]
  refine ⟨(hD.add hG).inner_const v, ?_⟩
  calc
    _ = ∫ x, inner ℝ v
        (fderiv ℝ φ x (EuclideanSpace.single i 1) • w x + φ x • Dw x i) :=
      integral_congr_ae (Eventually.of_forall fun x => real_inner_comm _ _)
    _ = inner ℝ v (∫ x,
        fderiv ℝ φ x (EuclideanSpace.single i 1) • w x + φ x • Dw x i) := integral_inner (hD.add hG) v
    _ = 0 := by rw [hZero, inner_zero_right]

private theorem poisson_compact_pairing_zero {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {F : Domain n → Ambient q}
    (hP : HolderToCK.WeakPoissonOn Ω Du F)
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Ω.val) :
    Integrable (fun x => (∑ i : Fin n, inner ℝ (Du x i)
      (fderiv ℝ ψ x (EuclideanSpace.single i 1))) + inner ℝ (F x) (ψ x)) volume ∧
    (∫ x, (∑ i : Fin n, inner ℝ (Du x i)
      (fderiv ℝ ψ x (EuclideanSpace.single i 1))) + inner ℝ (F x) (ψ x)) = 0 := by
  have hL := integrable_locallyL2_vector_test Du hu.2.2 ψ hψ hcψ hsψ
  have hR := integrable_locallyL1_vector_test hP.1 ψ hψ.continuous hcψ hsψ
  have H := (hP.2 ψ hψ hcψ hsψ).2.2
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hnot : x ∉ tsupport ψ := fun h => hx (hsψ h)
      simp only [fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot, zero_apply,
        inner_zero_right, Finset.sum_const_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsψ h)), inner_zero_right])] at H
  exact ⟨hL.add hR, by rw [integral_add hL hR, H, neg_add_cancel]⟩

/-- The native cutoff forcing is genuinely integrable on the whole source space. -/
theorem integrable_poisson_cutoff_forcing {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {F : Domain n → Ambient q}
    (hF : LocallyIntegrableOn F Ω.val volume) (c : Ambient q)
    (χ : Domain n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω.val) :
    Integrable (fun x => χ x • F x +
      (2 : ℝ) • (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • Du x i) +
      Laplacian.laplacian χ x • (u x - c)) volume := by
  let dχ (i : Fin n) (x : Domain n) := fderiv ℝ χ x (EuclideanSpace.single i 1)
  let ddχ (i : Fin n) (x : Domain n) := fderiv ℝ (dχ i) x (EuclideanSpace.single i 1)
  have hdχ (i : Fin n) : ContDiff ℝ ∞ (dχ i) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hddχ (i : Fin n) : ContDiff ℝ ∞ (ddχ i) :=
    ((hdχ i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcdχ (i : Fin n) : HasCompactSupport (dχ i) :=
    hcχ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hcddχ (i : Fin n) : HasCompactSupport (ddχ i) :=
    (hcdχ i).fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hsdχ (i : Fin n) : tsupport (dχ i) ⊆ Ω.val :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsχ
  have hsddχ (i : Fin n) : tsupport (ddχ i) ⊆ Ω.val :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans (hsdχ i)
  have hχF := integrable_compact_smul_of_locallyIntegrableOn hF hχ.continuous hcχ hsχ
  have hcross (i : Fin n) := integrable_compact_smul_of_locallyIntegrableOn
    (hu.1.2.1 i) (hdχ i).continuous (hcdχ i) (hsdχ i)
  have hsecond (i : Fin n) := integrable_compact_smul_of_locallyIntegrableOn
    (memW12Loc_sub_const hu c).1.1 (hddχ i).continuous (hcddχ i) (hsddχ i)
  have H : Integrable (fun x => χ x • F x +
      (2 : ℝ) • (∑ i : Fin n, dχ i x • Du x i) +
      (∑ i : Fin n, ddχ i x • (u x - c))) volume :=
    (hχF.add ((integrable_finsetSum Finset.univ (fun i _ => hcross i)).smul (2 : ℝ))).add
      (integrable_finsetSum Finset.univ (fun i _ => hsecond i))
  apply H.congr
  filter_upwards [] with x
  rw [scalar_laplacian_eq_sum χ hχ x, Finset.sum_smul]

/-- The original signed PDE gives the genuine full-space cutoff equation with cross coefficient two. -/
theorem weakPoissonOn_cutoff_sub_const_univ {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {F : Domain n → Ambient q}
    (hP : HolderToCK.WeakPoissonOn Ω Du F) (c : Ambient q)
    (χ : Domain n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω.val) :
    HolderToCK.WeakPoissonOn (⟨Set.univ, isOpen_univ⟩ : OpenDomain n)
      (fun x i => χ x • Du x i + fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x - c))
      (fun x => χ x • F x +
        (2 : ℝ) • (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • Du x i) +
        Laplacian.laplacian χ x • (u x - c)) := by
  let w (x : Domain n) := u x - c
  let dχ (i : Fin n) (x : Domain n) := fderiv ℝ χ x (EuclideanSpace.single i 1)
  let ddχ (i : Fin n) (x : Domain n) := fderiv ℝ (dχ i) x (EuclideanSpace.single i 1)
  let Dv (x : Domain n) (i : Fin n) := χ x • Du x i + dχ i x • w x
  let Fv (x : Domain n) := χ x • F x +
    (2 : ℝ) • (∑ i : Fin n, dχ i x • Du x i) + Laplacian.laplacian χ x • w x
  have hcut := memW12_cutoff_sub_const_univ hu c χ hχ hcχ hsχ
  have hFI : Integrable Fv volume := integrable_poisson_cutoff_forcing hu hP.1 c χ hχ hcχ hsχ
  have hshift := memW12Loc_sub_const hu c
  have hdχ (i : Fin n) : ContDiff ℝ ∞ (dχ i) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcdχ (i : Fin n) : HasCompactSupport (dχ i) := hcχ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hsdχ (i : Fin n) : tsupport (dχ i) ⊆ Ω.val :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsχ
  have Hfinal : HolderToCK.WeakPoissonOn (⟨Set.univ, isOpen_univ⟩ : OpenDomain n) Dv
      (fun x => -(-Fv x)) := by
    apply weakPoissonOn_neg_of_separated (⟨Set.univ, isOpen_univ⟩ : OpenDomain n) Dv
      (fun x => -Fv x)
    · exact hFI.neg.locallyIntegrable.locallyIntegrableOn Set.univ
    · intro η hη hcη _hsη v
      let Ψ (x : Domain n) := (χ x * η x) • v
      have hΨ : ContDiff ℝ ∞ Ψ := (hχ.mul hη).smul contDiff_const
      have hcΨ : HasCompactSupport Ψ := (hcχ.mul_right).smul_right
      have hsΨ : tsupport Ψ ⊆ Ω.val :=
        (tsupport_smul_subset_left _ _).trans (tsupport_mul_subset_left.trans hsχ)
      have hPD := poisson_compact_pairing_zero hu hP Ψ hΨ hcΨ hsΨ
      let α (i : Fin n) (x : Domain n) := η x * dχ i x
      have hα (i : Fin n) : ContDiff ℝ ∞ (α i) := hη.mul (hdχ i)
      have hcα (i : Fin n) : HasCompactSupport (α i) := (hcdχ i).mul_left
      have hsα (i : Fin n) : tsupport (α i) ⊆ Ω.val := tsupport_mul_subset_right.trans (hsdχ i)
      have hIBP (i : Fin n) := weak_gradient_compact_pairing_zero hshift.1 i
        (α i) (hα i) (hcα i) (hsα i) v
      have hDα (i : Fin n) (x : Domain n) :
          fderiv ℝ (α i) x (EuclideanSpace.single i 1) =
          fderiv ℝ η x (EuclideanSpace.single i 1) * dχ i x + η x * ddχ i x :=
        coordinateDerivative_mul hη (hdχ i) i x
      have hDΨ (x : Domain n) (i : Fin n) :
          fderiv ℝ Ψ x (EuclideanSpace.single i 1) =
          (dχ i x * η x + χ x * fderiv ℝ η x (EuclideanSpace.single i 1)) • v := by
        have H := congrArg (fun D : Domain n →L[ℝ] Ambient q => D (EuclideanSpace.single i 1))
          (((hχ.mul hη).differentiable (by simp) x).hasFDerivAt.smul (hasFDerivAt_const v x)).fderiv
        simp only [smul_zero, zero_add, ContinuousLinearMap.smulRight_apply] at H
        change fderiv ℝ Ψ x (EuclideanSpace.single i 1) =
          fderiv ℝ (fun y => χ y * η y) x (EuclideanSpace.single i 1) • v at H
        have hd := coordinateDerivative_mul hχ hη i x
        change fderiv ℝ (fun y => χ y * η y) x (EuclideanSpace.single i 1) = _ at hd
        rw [hd] at H
        exact H
      have hFpoint (x : Domain n) : Fv x = χ x • F x + ∑ i : Fin n,
          ((2 : ℝ) • (dχ i x • Du x i) + ddχ i x • w x) := by
        dsimp only [Fv]
        rw [scalar_laplacian_eq_sum χ hχ x, Finset.sum_smul, Finset.smul_sum,
          Finset.sum_add_distrib]
        abel
      have hterm (i : Fin n) (x : Domain n) :
          inner ℝ (Dv x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v) +
            η x * inner ℝ ((2 : ℝ) • (dχ i x • Du x i) + ddχ i x • w x) v =
          inner ℝ (Du x i) (fderiv ℝ Ψ x (EuclideanSpace.single i 1)) +
            inner ℝ (fderiv ℝ (α i) x (EuclideanSpace.single i 1) • w x + α i x • Du x i) v := by
        rw [hDΨ, hDα]
        simp only [Dv, α, inner_add_left, real_inner_smul_left, real_inner_smul_right]
        ring
      have hpoint (x : Domain n) :
          (∑ i : Fin n, inner ℝ (Dv x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) +
            η x * inner ℝ (Fv x) v =
          ((∑ i : Fin n, inner ℝ (Du x i) (fderiv ℝ Ψ x (EuclideanSpace.single i 1))) +
            inner ℝ (F x) (Ψ x)) + ∑ i : Fin n,
              inner ℝ (fderiv ℝ (α i) x (EuclideanSpace.single i 1) • w x + α i x • Du x i) v := by
        have H := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl
          (fun (i : Fin n) _ => hterm i x)
        simp only [Finset.sum_add_distrib] at H
        have hFinner : inner ℝ (Fv x) v = χ x * inner ℝ (F x) v + ∑ i : Fin n,
            inner ℝ ((2 : ℝ) • (dχ i x • Du x i) + ddχ i x • w x) v := by
          calc
            _ = inner ℝ (χ x • F x) v + inner ℝ (∑ i : Fin n,
                ((2 : ℝ) • (dχ i x • Du x i) + ddχ i x • w x)) v := by
              rw [hFpoint, inner_add_left]
            _ = _ := by rw [real_inner_smul_left, sum_inner]
        have hFtest : inner ℝ (F x) (Ψ x) = (χ x * η x) * inner ℝ (F x) v := by
          exact real_inner_smul_right _ _ _
        rw [hFinner, mul_add, Finset.mul_sum, hFtest]
        linear_combination H
      have hcol (i : Fin n) : MemLp (fun x => Dv x i) 2 volume := by
        simpa only [Measure.restrict_univ] using hcut.2.2 i
      have htest (i : Fin n) : MemLp
          (fun x => fderiv ℝ η x (EuclideanSpace.single i 1) • v) 2 volume :=
        (((hη.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const).memLp_of_hasCompactSupport
          ((hcη.fderiv_apply ℝ (EuclideanSpace.single i 1)).smul_right)
      have hL : Integrable (fun x => ∑ i : Fin n,
          inner ℝ (Dv x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) volume :=
        integrable_finsetSum _ (fun i _ => HolderToCK.integrable_inner_of_memLp_two (hcol i) (htest i))
      have hηTop := hη.continuous.memLp_top_of_hasCompactSupport hcη volume
      have hR : Integrable (fun x => η x * inner ℝ (Fv x) v) volume :=
        ((hFI.smul_of_top_right hηTop).inner_const v).congr (Eventually.of_forall fun x => by
          change inner ℝ (η x • Fv x) v = η x * inner ℝ (Fv x) v
          exact real_inner_smul_left _ _ _)
      have hBsum : Integrable (fun x => ∑ i : Fin n,
          inner ℝ (fderiv ℝ (α i) x (EuclideanSpace.single i 1) • w x + α i x • Du x i) v) volume :=
        integrable_finsetSum _ (fun i _ => (hIBP i).1)
      have hzero : (∫ x, (∑ i : Fin n,
          inner ℝ (Dv x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) +
            η x * inner ℝ (Fv x) v) = 0 := by
        rw [integral_congr_ae (Eventually.of_forall hpoint), integral_add hPD.1 hBsum,
          integral_finsetSum _ (fun i _ => (hIBP i).1), hPD.2]
        simp only [fun i => (hIBP i).2, Finset.sum_const_zero, zero_add]
      rw [integral_add hL hR] at hzero
      have heq : (∫ x, ∑ i : Fin n,
          inner ℝ (Dv x i) (fderiv ℝ η x (EuclideanSpace.single i 1) • v)) =
          -(∫ x, η x * inner ℝ (Fv x) v) := eq_neg_iff_add_eq_zero.mpr hzero
      have hneg : (fun x => -(η x * inner ℝ (Fv x) v)) =
          (fun x => η x * inner ℝ (-Fv x) v) := by
        funext x
        rw [inner_neg_left, mul_neg]
      have hRN : Integrable (fun x => η x * inner ℝ (-Fv x) v) volume := by
        rw [← hneg]
        exact hR.neg
      refine ⟨hL.integrableOn, hRN.integrableOn, ?_⟩
      simp only [Measure.restrict_univ]
      rw [← hneg, integral_neg]
      exact heq
  simpa only [neg_neg] using Hfinal

/-- Restriction gives the same signed cutoff PDE on the original open domain. -/
theorem weakPoissonOn_cutoff_sub_const {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {F : Domain n → Ambient q}
    (hP : HolderToCK.WeakPoissonOn Ω Du F) (c : Ambient q)
    (χ : Domain n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω.val) :
    HolderToCK.WeakPoissonOn Ω
      (fun x i => χ x • Du x i + fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x - c))
      (fun x => χ x • F x +
        (2 : ℝ) • (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • Du x i) +
        Laplacian.laplacian χ x • (u x - c)) :=
  (weakPoissonOn_cutoff_sub_const_univ hu hP c χ hχ hcχ hsχ).mono (subset_univ Ω.val)

end StationaryHarmonicMaps.Analysis

end

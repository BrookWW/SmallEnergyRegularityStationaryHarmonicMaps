module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyValueGrowth
public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds
public import StationaryHarmonicMaps.Analysis.CutoffGradientHSBound
public import StationaryHarmonicMaps.Analysis.SobolevCutoff
public import StationaryHarmonicMaps.Analysis.AffineMorreyScaling

/-!
# Complete critical Morrey control of the actual Sobolev cutoff

The displayed Leibniz columns are the genuine full-space weak gradient.
Their actual support localizes every queried ball to the fixed interior
ball. Recentered gradient energy and the all-radius value estimate control
all centers and all positive radii of the complete critical supremum.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem gradient_integral_on_interior_inter_le {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du) {η : ℝ}
    (hcritical : criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤
      ENNReal.ofReal (η ^ 2)) (x : Domain n) {r : ℝ} (hr : 0 < r) :
    (∫ y in Metric.ball x r ∩ Metric.ball (0 : Domain n) (7 / 8 : ℝ), hsNormSq (Du y)) ≤
      ((2 : ℝ) ^ ((n : ℝ) - 2)) * η ^ 2 * r ^ ((n : ℝ) - 2) := by
  let S : Set (Domain n) := Metric.ball x r ∩ Metric.ball (0 : Domain n) (7 / 8 : ℝ)
  have hSB : S ⊆ Metric.ball (0 : Domain n) 1 :=
    inter_subset_right.trans (Metric.ball_subset_ball (by norm_num))
  by_cases hempty : S = ∅
  · change (∫ y in S, hsNormSq (Du y)) ≤ _
    rw [hempty, setIntegral_empty]
    positivity
  · obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    have hsub : S ⊆ Metric.ball y (2 * r) ∩ Metric.ball (0 : Domain n) 1 := by
      intro z hz
      refine ⟨?_, hSB hz⟩
      have hzx : dist z x < r := hz.1
      have hyx : dist y x < r := hy.1
      have hdist := dist_triangle z x y
      rw [dist_comm x y] at hdist
      change dist z y < 2 * r
      linarith
    have hcols (i : Fin n) : MemLp (fun z => Du z i) 2 (volume.restrict S) :=
      (hu.2.2 i).mono_measure (Measure.restrict_mono_set volume hSB)
    have h := integral_hsNormSq_le_of_criticalMorrey Du (hSB hy)
      (mul_pos (by norm_num : (0 : ℝ) < 2) hr) (sq_nonneg η) hsub hcols hcritical
    calc
      _ ≤ η ^ 2 * (2 * r) ^ ((n : ℝ) - 2) := h
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le]; ring

private theorem cutoff_columns_indicator_interior {n q : ℕ}
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (c : Ambient q)
    (χ : Domain n → ℝ)
    (hsχ : tsupport χ ⊆ Metric.closedBall (0 : Domain n) (3 / 4 : ℝ)) :
    (Metric.ball (0 : Domain n) (7 / 8 : ℝ)).indicator
      (fun x i => χ x • Du x i + fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x - c)) =
      (fun x i => χ x • Du x i + fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x - c)) := by
  classical
  have hs : tsupport χ ⊆ Metric.ball (0 : Domain n) (7 / 8 : ℝ) :=
    hsχ.trans (Metric.closedBall_subset_ball (by norm_num))
  funext x
  by_cases hx : x ∈ Metric.ball (0 : Domain n) (7 / 8 : ℝ)
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx]
    have hnot : x ∉ tsupport χ := fun hmem => hx (hs hmem)
    funext i
    rw [image_eq_zero_of_notMem_tsupport hnot,
      fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot, zero_apply, zero_smul, zero_smul, zero_add]
    rfl

/-- The actual full-space cutoff has a uniform bound on the complete critical L2 supremum. -/
theorem exists_cutoff_criticalMorrey_bound (n : ℕ) (hn : 2 ≤ n)
    (A B : ℝ) (_hA : 0 ≤ A) (_hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤
        ENNReal.ofReal (η ^ 2) →
      ∀ (χ : Domain n → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Metric.closedBall (0 : Domain n) (3 / 4 : ℝ) →
      (∀ x, |χ x| ≤ A) →
      (∀ (x : Domain n) (i : Fin n), |fderiv ℝ χ x (EuclideanSpace.single i 1)| ≤ B) →
      let c := ⨍ y in Metric.ball (0 : Domain n) 1, u y
      let v := fun x => χ x • (u x - c)
      let Dv := fun x i => χ x • Du x i + fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x - c)
      MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain n) v Dv ∧
      criticalGradientMorreySquare Dv univ ≤ ENNReal.ofReal (C * η ^ 2) := by
  obtain ⟨V, hV, hvalue⟩ := exists_all_radius_value_growth_of_criticalMorrey n hn
  let K : ℝ := 2 * A ^ 2 * (2 : ℝ) ^ ((n : ℝ) - 2) + 2 * (n : ℝ) * B ^ 2 * V
  let C : ℝ := 1 + K
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hKC : K ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro q u Du η hu hη hcritical χ hχ hcχ hsχ hχA hDχB
  dsimp only
  let c := ⨍ y in Metric.ball (0 : Domain n) 1, u y
  let Dv : Domain n → Gradient n q := fun x i =>
    χ x • Du x i + fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x - c)
  have hsχB : tsupport χ ⊆ (ballDomain (0 : Domain n) 1).val :=
    hsχ.trans (Metric.closedBall_subset_ball (by norm_num))
  have hW : MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain n) (fun x => χ x • (u x - c)) Dv :=
    memW12_cutoff_sub_const_univ hu.to_memW12Loc c χ hχ hcχ hsχB
  refine ⟨hW, ?_⟩
  change criticalGradientMorreySquare Dv univ ≤ _
  have hind : (Metric.ball (0 : Domain n) (7 / 8 : ℝ)).indicator Dv = Dv :=
    cutoff_columns_indicator_interior u Du c χ hsχ
  unfold criticalGradientMorreySquare
  refine iSup_le fun x => iSup_le fun r => ?_
  rw [inter_univ]
  let S : Set (Domain n) := Metric.ball x.val r.val ∩ Metric.ball (0 : Domain n) (7 / 8 : ℝ)
  have hSB : S ⊆ Metric.ball (0 : Domain n) 1 :=
    inter_subset_right.trans (Metric.ball_subset_ball (by norm_num))
  have hDuI : IntegrableOn (fun y => hsNormSq (Du y)) S volume :=
    hu.integrable_hsNormSq.mono_set hSB
  have hDvI : IntegrableOn (fun y => hsNormSq (Dv y)) S volume :=
    hW.integrable_hsNormSq.mono_set (subset_univ S)
  obtain ⟨_haL2, haI, havalue⟩ := hvalue q u Du η hu hη hcritical x.val r.val r.property
  have hgrad := gradient_integral_on_interior_inter_le hu hcritical x.val r.property
  have hInt : (∫ y in S, hsNormSq (Dv y)) ≤ C * η ^ 2 * r.val ^ ((n : ℝ) - 2) := by
    have hpoint (y : Domain n) : hsNormSq (Dv y) ≤
        2 * A ^ 2 * hsNormSq (Du y) + (2 * (n : ℝ) * B ^ 2) * ‖u y - c‖ ^ 2 :=
      cutoff_gradient_hsNormSq_le (Du y) (u y - c) (χ y)
        (fun i => fderiv ℝ χ y (EuclideanSpace.single i 1)) (hχA y) (hDχB y)
    calc
      _ ≤ ∫ y in S, (2 * A ^ 2 * hsNormSq (Du y) +
          (2 * (n : ℝ) * B ^ 2) * ‖u y - c‖ ^ 2) :=
        integral_mono hDvI ((hDuI.const_mul _).add (haI.const_mul _)) hpoint
      _ = 2 * A ^ 2 * (∫ y in S, hsNormSq (Du y)) +
          (2 * (n : ℝ) * B ^ 2) * (∫ y in S, ‖u y - c‖ ^ 2) := by
        rw [integral_add (hDuI.const_mul _) (haI.const_mul _),
          integral_const_mul, integral_const_mul]
      _ ≤ 2 * A ^ 2 * ((2 : ℝ) ^ ((n : ℝ) - 2) * η ^ 2 * r.val ^ ((n : ℝ) - 2)) +
          (2 * (n : ℝ) * B ^ 2) * (V * η ^ 2 * r.val ^ ((n : ℝ) - 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hgrad (by positivity))
          (mul_le_mul_of_nonneg_left havalue (by positivity))
      _ = K * η ^ 2 * r.val ^ ((n : ℝ) - 2) := by dsimp only [K]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKC (sq_nonneg η)) (Real.rpow_nonneg r.property.le _)
  have henergyEq : dirichletEnergy Dv (Metric.ball x.val r.val) = dirichletEnergy Dv S := by
    have H := dirichletEnergy_indicator_eq_inter Dv
      (D := Metric.ball (0 : Domain n) (7 / 8 : ℝ)) measurableSet_ball (Metric.ball x.val r.val)
    rw [hind] at H
    exact H
  have hcancel : r.val ^ ((n : ℝ) - 2) * r.val ^ (2 - (n : ℤ)) = 1 := by
    rw [← Real.rpow_intCast, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast,
      ← Real.rpow_add r.property]
    norm_num
  rw [henergyEq, dirichletEnergy_eq_ofReal_integral hDvI]
  calc
    _ ≤ ENNReal.ofReal (r.val ^ (2 - (n : ℤ))) *
        ENNReal.ofReal (C * η ^ 2 * r.val ^ ((n : ℝ) - 2)) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal hInt) _
    _ = ENNReal.ofReal (C * η ^ 2) := by
      rw [← ENNReal.ofReal_mul (zpow_nonneg r.property.le _)]
      congr 1
      calc
        _ = C * η ^ 2 * (r.val ^ ((n : ℝ) - 2) * r.val ^ (2 - (n : ℤ))) := by ring
        _ = _ := by rw [hcancel, mul_one]

end StationaryHarmonicMaps.Analysis

end

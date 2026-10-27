module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds
public import StationaryHarmonicMaps.Analysis.AffineMorreyScaling
public import HarmonicMaps.Analysis.SobolevMollificationGradient

/-!
# Complete critical Morrey control of actual zero-extended fields

An arbitrary external ball meeting the original set lies, on that set, in
a doubled ball centered at an actual point of the intersection. Empty
intersections have zero energy. The field is only required to have actual
L2 columns; no weak-gradient or zero-boundary hypothesis is used.
-/

public section

open HarmonicMaps MeasureTheory Set

namespace StationaryHarmonicMaps.Analysis

/-- Original complete critical control bounds every externally centered truncated real energy. -/
theorem integral_hsNormSq_inter_le_of_criticalMorrey {n q : ℕ}
    (F : Domain n → Gradient n q) (D : Set (Domain n))
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict D))
    (K : ℝ) (hK : 0 ≤ K)
    (hcritical : criticalGradientMorreySquare F D ≤ ENNReal.ofReal K)
    (a : Domain n) {r : ℝ} (hr : 0 < r) :
    (∫ x in Metric.ball a r ∩ D, hsNormSq (F x)) ≤
      (2 : ℝ) ^ ((n : ℝ)-2) * K * r ^ ((n : ℝ)-2) := by
  let S : Set (Domain n) := Metric.ball a r ∩ D
  by_cases hempty : S = ∅
  · change (∫ x in S, hsNormSq (F x)) ≤ _
    rw [hempty, setIntegral_empty]
    positivity
  · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    have hsub : S ⊆ Metric.ball x (2*r) ∩ D := by
      intro y hy
      refine ⟨?_, hy.2⟩
      have hya : dist y a < r := hy.1
      have hxa : dist x a < r := hx.1
      have hdist := dist_triangle y a x
      rw [dist_comm a x] at hdist
      change dist y x < 2*r
      linarith
    have hcols (i : Fin n) : MemLp (fun y => F y i) 2 (volume.restrict S) :=
      (hF i).mono_measure (Measure.restrict_mono_set volume inter_subset_right)
    have H := integral_hsNormSq_le_of_criticalMorrey F hx.2
      (mul_pos (by norm_num : (0 : ℝ)<2) hr) hK hsub hcols hcritical
    calc
      _ ≤ K * (2*r) ^ ((n : ℝ)-2) := H
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤2) hr.le]; ring

/-- Literal indicator extension has genuine global L2 columns and the complete all-center, all-radius critical bound. -/
theorem indicator_criticalMorrey_univ_bound {n q : ℕ}
    (F : Domain n → Gradient n q) (D : Set (Domain n)) (hD : MeasurableSet D)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict D))
    (K : ℝ) (hK : 0 ≤ K)
    (hcritical : criticalGradientMorreySquare F D ≤ ENNReal.ofReal K) :
    (∀ i, MemLp (fun x => D.indicator F x i) 2 volume) ∧
    criticalGradientMorreySquare (D.indicator F) univ ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ)-2) * K) := by
  classical
  have hcols (i : Fin n) : MemLp (fun x => D.indicator F x i) 2 volume := by
    have heq : (fun x => D.indicator F x i) = D.indicator (fun x => F x i) := by
      funext x
      by_cases hx : x∈D
      · simp only [indicator_of_mem hx]
      · simp only [indicator_of_notMem hx, Pi.zero_apply]
    rw [heq]
    exact (memLp_indicator_iff_restrict hD).mpr (hF i)
  refine ⟨hcols, ?_⟩
  unfold criticalGradientMorreySquare
  refine iSup_le fun a => iSup_le fun r => ?_
  rw [inter_univ, dirichletEnergy_indicator_eq_inter F hD]
  have hInt : IntegrableOn (fun x => hsNormSq (F x)) (Metric.ball a.val r.val ∩ D) volume :=
    integrable_hsNormSq_of_columns F (fun i =>
      (hF i).mono_measure (Measure.restrict_mono_set volume inter_subset_right))
  rw [dirichletEnergy_eq_ofReal_integral hInt]
  have H := integral_hsNormSq_inter_le_of_criticalMorrey F D hF K hK hcritical a.val r.property
  have hcancel : r.val ^ ((n : ℝ)-2) * r.val ^ (2-(n : ℤ)) = 1 := by
    rw [← Real.rpow_intCast, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast,
      ← Real.rpow_add r.property]
    norm_num
  calc
    _ ≤ ENNReal.ofReal (r.val ^ (2-(n : ℤ))) *
        ENNReal.ofReal ((2 : ℝ)^((n : ℝ)-2) * K * r.val^((n : ℝ)-2)) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal H) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (zpow_nonneg r.property.le _)]
      congr 1
      calc
        _ = ((2 : ℝ)^((n : ℝ)-2) * K) * (r.val^((n : ℝ)-2) * r.val^(2-(n : ℤ))) := by ring
        _ = _ := by rw [hcancel, mul_one]

/-- Columnwise literal zeroExtensionOn from the unit ball has the exact constant 2^(n-2) on the full space. -/
theorem zeroExtension_unitBall_criticalMorrey_bound {n q : ℕ} (hn : 2 ≤ n)
    (F : Domain n → Gradient n q)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (K : ℝ) (hK : 0 ≤ K)
    (hcritical : criticalGradientMorreySquare F (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal K) :
    (∀ i, MemLp (zeroExtensionOn (ballDomain (0 : Domain n) 1) (fun x => F x i)) 2 volume) ∧
    criticalGradientMorreySquare
      (fun x i => zeroExtensionOn (ballDomain (0 : Domain n) 1) (fun y => F y i) x) univ ≤
      ENNReal.ofReal ((2 : ℝ) ^ (n-2) * K) := by
  classical
  have heq : (fun x i => zeroExtensionOn (ballDomain (0 : Domain n) 1) (fun y => F y i) x) =
      (Metric.ball (0 : Domain n) 1).indicator F := by
    funext x i
    by_cases hx : x∈Metric.ball (0 : Domain n) 1
    · simp only [zeroExtensionOn, ballDomain, indicator_of_mem hx]
    · simp only [zeroExtensionOn, ballDomain, indicator_of_notMem hx, Pi.zero_apply]
  have H := indicator_criticalMorrey_univ_bound F (Metric.ball (0 : Domain n) 1)
    measurableSet_ball hF K hK hcritical
  have hexp : (n : ℝ)-2 = ((n-2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn]
    norm_num
  rw [hexp, Real.rpow_natCast] at H
  refine ⟨?_, ?_⟩
  · intro i
    have Hi := H.1 i
    change MemLp (fun x => (fun y j => zeroExtensionOn (ballDomain (0 : Domain n) 1) (fun z => F z j) y) x i) 2 volume
    rw [heq]
    exact Hi
  · rw [heq]
    exact H.2

end StationaryHarmonicMaps.Analysis

end

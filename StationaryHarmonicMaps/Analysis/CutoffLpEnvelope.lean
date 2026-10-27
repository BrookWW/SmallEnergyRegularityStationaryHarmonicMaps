module

public import StationaryHarmonicMaps.Analysis.CutoffCriticalMorrey
public import StationaryHarmonicMaps.Analysis.ForwardMorreyLpGrowth
public import StationaryHarmonicMaps.Analysis.EffectiveEuclideanVolume
public import StationaryHarmonicMaps.Analysis.EffectiveElementaryPowers

/-!
# Actual initial Lp envelope for the compact Sobolev cutoff

The same produced cutoff has full-space W¹,² data and complete critical
L² Morrey control. Forward Hölder comparison then gives the normalized
Lp bound for every center and every positive radius.
-/

@[expose] public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

def effectiveCutoffLpEnvelopeConstant (n A B : ℕ) : ℕ :=
  (1+2^n)*(1+effectiveCutoffCriticalConstant n A B)

/-- The actual cutoff produces the bounded initial normalized Lp envelope, with all data uniform. -/
theorem exists_cutoff_lp_envelope_bound (n : ℕ) (hn : 2 ≤ n)
    (p : ℝ) (hp : 0 < p) (hpTwo : p ≤ 2) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal (η ^ 2) →
      ∀ (χ : Domain n → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Metric.closedBall (0 : Domain n) (3 / 4 : ℝ) →
      (∀ x, |χ x| ≤ A) →
      (∀ (x : Domain n) (i : Fin n), |fderiv ℝ χ x (EuclideanSpace.single i 1)| ≤ B) →
      let c := ⨍ y in Metric.ball (0 : Domain n) 1, u y
      let v := fun x => χ x • (u x - c)
      let Dv := fun x i => χ x • Du x i + fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x - c)
      MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain n) v Dv ∧
      ∀ (x : Domain n) (r : ℝ), 0 < r →
        IntegrableOn (fun y => (Real.sqrt (hsNormSq (Dv y))) ^ p) (Metric.ball x r) volume ∧
        r ^ (p - (n : ℝ)) * (∫ y in Metric.ball x r, (Real.sqrt (hsNormSq (Dv y))) ^ p) ≤
          C * η ^ p := by
  obtain ⟨D, hD, hcutoff⟩ := exists_cutoff_criticalMorrey_bound n hn A B hA hB
  let V := volume.real (Metric.ball (0 : Domain n) 1)
  let C := V ^ (1 - p / 2) * D ^ (p / 2)
  have hV : 0 < V := HolderToCK.ball_volume_real_pos 0 (by norm_num : (0 : ℝ) < 1)
  have hC : 0 < C := mul_pos (Real.rpow_pos_of_pos hV _) (Real.rpow_pos_of_pos hD _)
  refine ⟨C, hC, ?_⟩
  intro q u Du η hu hη hcritical χ hχ hcχ hsχ hχA hDχB
  obtain ⟨hW, hcrit⟩ := hcutoff q u Du η hu hη hcritical χ hχ hcχ hsχ hχA hDχB
  refine ⟨hW, ?_⟩
  intro x r hr
  have hforward := integral_hs_rpow_le_of_global_criticalMorrey _ hW.to_memW12Loc.2.2
    (mul_nonneg hD.le (sq_nonneg η)) hp hpTwo hcrit x hr
  have hamp : (D * η ^ 2) ^ (p / 2) = D ^ (p / 2) * η ^ p := by
    rw [Real.mul_rpow hD.le (sq_nonneg η), ← Real.rpow_natCast η 2, ← Real.rpow_mul hη]
    congr 1
    congr 1
    ring
  have hgrowth : (∫ y in Metric.ball x r,
      (Real.sqrt (hsNormSq (fun i => χ y • Du y i +
        fderiv ℝ χ y (EuclideanSpace.single i 1) • (u y - (⨍ z in Metric.ball 0 1, u z))))) ^ p) ≤
      C * η ^ p * r ^ ((n : ℝ) - p) := by
    exact hforward.2.trans_eq (by rw [hamp]; dsimp only [C, V]; ring)
  refine ⟨hforward.1, ?_⟩
  calc
    _ ≤ r ^ (p - (n : ℝ)) * (C * η ^ p * r ^ ((n : ℝ) - p)) :=
      mul_le_mul_of_nonneg_left hgrowth (Real.rpow_nonneg hr.le _)
    _ = C * η ^ p * (r ^ (p - (n : ℝ)) * r ^ ((n : ℝ) - p)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hr]
      have he : p - (n : ℝ) + ((n : ℝ) - p) = 0 := by ring
      rw [he, Real.rpow_zero, mul_one]

theorem exists_cutoff_lp_envelope_bound_effective (n : ℕ) (hn : 2 ≤ n)
    (p : ℝ) (hp : 0 < p) (hpTwo : p ≤ 2) (A B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ C=(effectiveCutoffLpEnvelopeConstant n A B:ℝ) ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal (η ^ 2) →
      ∀ (χ : Domain n → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Metric.closedBall (0 : Domain n) (3 / 4 : ℝ) →
      (∀ x, |χ x| ≤ (A:ℝ)) →
      (∀ (x : Domain n) (i : Fin n), |fderiv ℝ χ x (EuclideanSpace.single i 1)| ≤ (B:ℝ)) →
      let c := ⨍ y in Metric.ball (0 : Domain n) 1, u y
      let v := fun x => χ x • (u x - c)
      let Dv := fun x i => χ x • Du x i + fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x - c)
      MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain n) v Dv ∧
      ∀ (x : Domain n) (r : ℝ), 0 < r →
        IntegrableOn (fun y => (Real.sqrt (hsNormSq (Dv y))) ^ p) (Metric.ball x r) volume ∧
        r ^ (p - (n : ℝ)) * (∫ y in Metric.ball x r, (Real.sqrt (hsNormSq (Dv y))) ^ p) ≤
          C * η ^ p := by
  let D : ℝ := (effectiveCutoffCriticalConstant n A B:ℝ)
  have hD : 0<D := effectiveCutoffCriticalConstant_pos n A B
  have hcutoff := effective_cutoff_criticalMorrey_bound n hn A B
  let V := volume.real (Metric.ball (0 : Domain n) 1)
  let C : ℝ := (effectiveCutoffLpEnvelopeConstant n A B:ℝ)
  have hV : 0 < V := HolderToCK.ball_volume_real_pos 0 (by norm_num : (0 : ℝ) < 1)
  have hMajorant : V^(1-p/2)*D^(p/2)≤C := by
    have hVPow := rpow_le_one_add_self_of_unit_exponent V (1-p/2) hV.le (by linarith only [hpTwo]) (by linarith only [hp])
    have hDPow := rpow_le_one_add_self_of_unit_exponent D (p/2) hD.le (by linarith only [hp]) (by linarith only [hpTwo])
    calc
      _≤(1+V)*(1+D) := mul_le_mul hVPow hDPow (Real.rpow_nonneg hD.le _) (by positivity)
      _≤(1+(2:ℝ)^n)*(1+D) := by gcongr;exact euclidean_unit_ball_volume_upper_bound n
      _=C := by dsimp only [C,D,effectiveCutoffLpEnvelopeConstant];push_cast;rfl
  have hC : 0<C := (mul_pos (Real.rpow_pos_of_pos hV _) (Real.rpow_pos_of_pos hD _)).trans_le hMajorant
  refine ⟨C, hC, rfl, ?_⟩
  intro q u Du η hu hη hcritical χ hχ hcχ hsχ hχA hDχB
  obtain ⟨hW, hcrit⟩ := hcutoff q u Du η hu hη hcritical χ hχ hcχ hsχ hχA hDχB
  refine ⟨hW, ?_⟩
  intro x r hr
  have hforward := integral_hs_rpow_le_of_global_criticalMorrey _ hW.to_memW12Loc.2.2
    (mul_nonneg hD.le (sq_nonneg η)) hp hpTwo hcrit x hr
  have hamp : (D * η ^ 2) ^ (p / 2) = D ^ (p / 2) * η ^ p := by
    rw [Real.mul_rpow hD.le (sq_nonneg η), ← Real.rpow_natCast η 2, ← Real.rpow_mul hη]
    congr 1
    congr 1
    ring
  have hgrowth : (∫ y in Metric.ball x r,
      (Real.sqrt (hsNormSq (fun i => χ y • Du y i +
        fderiv ℝ χ y (EuclideanSpace.single i 1) • (u y - (⨍ z in Metric.ball 0 1, u z))))) ^ p) ≤
      C * η ^ p * r ^ ((n : ℝ) - p) := by
    calc
      _≤V^(1-p/2)*D^(p/2)*η^p*r^((n:ℝ)-p) :=
        hforward.2.trans_eq (by rw [hamp];dsimp only [V];ring)
      _≤_ := by gcongr
  refine ⟨hforward.1, ?_⟩
  calc
    _ ≤ r ^ (p - (n : ℝ)) * (C * η ^ p * r ^ ((n : ℝ) - p)) :=
      mul_le_mul_of_nonneg_left hgrowth (Real.rpow_nonneg hr.le _)
    _ = C * η ^ p * (r ^ (p - (n : ℝ)) * r ^ ((n : ℝ) - p)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hr]
      have he : p - (n : ℝ) + ((n : ℝ) - p) = 0 := by ring
      rw [he, Real.rpow_zero, mul_one]

end StationaryHarmonicMaps.Analysis

end

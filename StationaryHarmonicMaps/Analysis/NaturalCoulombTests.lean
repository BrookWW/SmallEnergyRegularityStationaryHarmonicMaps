module

public import StationaryHarmonicMaps.Analysis.SkewConnectionAndTests
public import HarmonicMaps.Analysis.SobolevSmoothDensity
public import HolderToCK.Analysis.L2PairingContinuity

/-!
# Whole-ball Sobolev tests for an actual skew connection

The HS skew-part identity converts all ambient smooth skew tests into all
ambient smooth encoded tests. Genuine smooth density on the whole ball
then preserves every native W1,2 test, including its boundary values.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

private theorem continuous_memLp_unitBall {n q : ℕ}
    (f : Domain n → Ambient q) (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Metric.ball (0 : Domain n) 1)) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Domain n) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Domain n) 1).exists_bound_of_continuousOn
    hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable B
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact hB x (Metric.ball_subset_closedBall hx)

/-- A genuine L2 column pairing is integrable against every actual L2 test gradient. -/
theorem integrable_column_pairing {n q : ℕ} (μ : Measure (Domain n))
    (F D : Domain n → Gradient n q)
    (hF : ∀ i, MemLp (fun x => F x i) 2 μ)
    (hD : ∀ i, MemLp (fun x => D x i) 2 μ) :
    Integrable (fun x => ∑ i : Fin n, inner ℝ (F x i) (D x i)) μ :=
  integrable_finsetSum _ fun i _ => HolderToCK.integrable_inner_of_memLp_two (hF i) (hD i)

/-- Actual whole-ball smooth graph density extends all smooth tests to every native Sobolev graph. -/
theorem native_tests_of_all_smooth_tests {n q : ℕ}
    (F : Domain n → Gradient n q)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (hzero : ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
      (∫ x in Metric.ball (0 : Domain n) 1,
        ∑ i : Fin n, inner ℝ (F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) = 0)
    (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q)
    (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
    IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (F x i) (Dψ x i))
      (Metric.ball (0 : Domain n) 1) volume ∧
    (∫ x in Metric.ball (0 : Domain n) 1, ∑ i : Fin n, inner ℝ (F x i) (Dψ x i)) = 0 := by
  let μ := volume.restrict (Metric.ball (0 : Domain n) 1)
  have hI := integrable_column_pairing μ F Dψ hF hψ.2.2
  obtain ⟨m, hm, _hmL, hmD, _hconv, hDconv⟩ := hψ.smoothDensity_ball (by norm_num)
  have hlim (i : Fin n) : Tendsto (fun k => ∫ x, inner ℝ (F x i)
      (coordinateDerivative (m k) (hm k) i x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (F x i) (Dψ x i) ∂μ)) := by
    apply HolderToCK.tendsto_integral_inner_of_L2 (fun k => hmD k i) (hψ.2.2 i) (hF i)
    exact hDconv i
  have hsum : Tendsto (fun k => ∑ i : Fin n, ∫ x, inner ℝ (F x i)
      (coordinateDerivative (m k) (hm k) i x) ∂μ) atTop
      (𝓝 (∑ i : Fin n, ∫ x, inner ℝ (F x i) (Dψ x i) ∂μ)) :=
    tendsto_finsetSum _ fun i _ => hlim i
  have hmzero (k : ℕ) : (∑ i : Fin n, ∫ x, inner ℝ (F x i)
      (coordinateDerivative (m k) (hm k) i x) ∂μ) = 0 := by
    rw [← integral_finsetSum _ (fun i _ =>
      HolderToCK.integrable_inner_of_memLp_two (hF i) (hmD k i))]
    exact hzero (m k) (hm k)
  have hfun : (fun k => ∑ i : Fin n, ∫ x, inner ℝ (F x i)
      (coordinateDerivative (m k) (hm k) i x) ∂μ) = (fun _ : ℕ => (0 : ℝ)) :=
    funext hmzero
  rw [hfun] at hsum
  have H := tendsto_nhds_unique hsum tendsto_const_nhds
  refine ⟨hI, ?_⟩
  rw [integral_finsetSum _ (fun i _ =>
    HolderToCK.integrable_inner_of_memLp_two (hF i) (hψ.2.2 i))]
  exact H

/-- Every smooth encoded test follows from the genuine pairing equation for all smooth skew operator tests. -/
theorem encoded_connection_smooth_tests_of_skew_tests {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀ z, E (R z) = z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (Z : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q))
    (hZ : ∀ i, MemLp (fun x => Z x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (hskew : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), ∀ i, star (Z x i) = -Z x i)
    (hzero : ∀ (S : Domain n → (Ambient q →L[ℝ] Ambient q)), ContDiff ℝ ∞ S →
      (∀ x, star (S x) = -S x) →
      (∫ x in Metric.ball (0 : Domain n) 1,
        ∑ i : Fin n, inner ℝ (E (Z x i)) (E (fderiv ℝ S x (EuclideanSpace.single i 1)))) = 0)
    (ψ : Domain n → Ambient (q*q)) (hψ : ContDiff ℝ ∞ ψ) :
    IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (E (Z x i)) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))
      (Metric.ball (0 : Domain n) 1) volume ∧
    (∫ x in Metric.ball (0 : Domain n) 1, ∑ i : Fin n,
      inner ℝ (E (Z x i)) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) = 0 := by
  let J : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q) :=
    (1 / 2 : ℝ) • (R - (starL' ℝ : (Ambient q →L[ℝ] Ambient q) ≃L[ℝ]
      (Ambient q →L[ℝ] Ambient q)).toContinuousLinearMap.comp R)
  have hJ (z : Ambient (q*q)) : J z = (1 / 2 : ℝ) • (R z - star (R z)) := rfl
  have hJs (z : Ambient (q*q)) : star (J z) = -J z := by
    rw [hJ]
    change ContinuousLinearMap.adjoint ((1 / 2 : ℝ) • (R z - ContinuousLinearMap.adjoint (R z))) = _
    rw [map_smul, map_sub, ContinuousLinearMap.adjoint_adjoint]
    apply ContinuousLinearMap.ext
    intro v
    change (1 / 2 : ℝ) • (star (R z) v - R z v) =
      -((1 / 2 : ℝ) • (R z v - star (R z) v))
    rw [smul_sub, smul_sub]
    abel
  let S := J ∘ ψ
  have hS : ContDiff ℝ ∞ S := J.contDiff.comp hψ
  have hDs (x : Domain n) (i : Fin n) :
      fderiv ℝ S x (EuclideanSpace.single i 1) = J (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    rw [fderiv_comp x J.differentiableAt (hψ.differentiable (by simp) x), J.fderiv]
    rfl
  have hZE (i : Fin n) : MemLp (fun x => E (Z x i)) 2
      (volume.restrict (Metric.ball (0 : Domain n) 1)) :=
    E.lipschitz.comp_memLp (map_zero E) (hZ i)
  have hDψ (i : Fin n) : MemLp (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)) 2
      (volume.restrict (Metric.ball (0 : Domain n) 1)) :=
    continuous_memLp_unitBall _ ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hpair : (fun x => ∑ i : Fin n, inner ℝ (E (Z x i))
      (E (fderiv ℝ S x (EuclideanSpace.single i 1)))) =ᵐ[volume.restrict (Metric.ball (0 : Domain n) 1)]
      (fun x => ∑ i : Fin n, inner ℝ (E (Z x i)) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
    filter_upwards [hskew] with x hx
    apply Finset.sum_congr rfl
    intro i _
    rw [hDs, hJ, encoded_inner_skew_part_eq E hE _ _ (hx i), hER]
  refine ⟨integrable_column_pairing _ _ _ hZE hDψ, ?_⟩
  exact (integral_congr_ae hpair).symm.trans (hzero S hS fun x => hJs (ψ x))

/-- All native whole-ball tests, with arbitrary boundary values, follow from the actual smooth skew-test equation. -/
theorem encoded_connection_native_tests_of_skew_tests {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀ z, E (R z) = z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (Z : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q))
    (hZ : ∀ i, MemLp (fun x => Z x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (hskew : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), ∀ i, star (Z x i) = -Z x i)
    (hzero : ∀ (S : Domain n → (Ambient q →L[ℝ] Ambient q)), ContDiff ℝ ∞ S →
      (∀ x, star (S x) = -S x) →
      (∫ x in Metric.ball (0 : Domain n) 1,
        ∑ i : Fin n, inner ℝ (E (Z x i)) (E (fderiv ℝ S x (EuclideanSpace.single i 1)))) = 0)
    (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q))
    (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
    IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (E (Z x i)) (Dψ x i))
      (Metric.ball (0 : Domain n) 1) volume ∧
    (∫ x in Metric.ball (0 : Domain n) 1, ∑ i : Fin n, inner ℝ (E (Z x i)) (Dψ x i)) = 0 := by
  apply native_tests_of_all_smooth_tests (fun x i => E (Z x i))
    (fun i => E.lipschitz.comp_memLp (map_zero E) (hZ i))
  · intro φ hφ
    exact (encoded_connection_smooth_tests_of_skew_tests E R hER hE Z hZ hskew hzero φ hφ).2
  · exact hψ


/-- The original native frame and all its actual connection coefficients preserve every whole-ball Sobolev test. -/
theorem native_frame_connection_tests {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀ z, E (R z) = z)
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
    (hp : MemW12 (ballDomain (0 : Domain n) 1) p Dp)
    (horth : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), star (R (p x)) * R (p x) = 1)
    (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q))
    (hA : ∀ i, MemLp (fun x => A x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (hAskew : ∀ i, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), star (A x i) = -A x i)
    (hzero : ∀ (S : Domain n → (Ambient q →L[ℝ] Ambient q)), ContDiff ℝ ∞ S →
      (∀ x, star (S x) = -S x) →
      (∫ x in Metric.ball (0 : Domain n) 1,
        ∑ i : Fin n, inner ℝ
          (E (star (R (p x)) * (R (Dp x i) + A x i * R (p x))))
          (E (fderiv ℝ S x (EuclideanSpace.single i 1)))) = 0)
    (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q))
    (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
    IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (E (star (R (p x)) * R (Dp x i) +
        star (R (p x)) * A x i * R (p x))) (Dψ x i))
      (Metric.ball (0 : Domain n) 1) volume ∧
    (∫ x in Metric.ball (0 : Domain n) 1, ∑ i : Fin n,
      inner ℝ (E (star (R (p x)) * R (Dp x i) +
        star (R (p x)) * A x i * R (p x))) (Dψ x i)) = 0 := by
  obtain ⟨hZ, _hEZ, hZskew⟩ := frame_connection_memLp_and_skew E R hER hE p Dp hp horth A hA hAskew
  apply encoded_connection_native_tests_of_skew_tests E R hER hE _ hZ hZskew
  · intro S hS hs
    simpa only [mul_add, mul_assoc] using hzero S hS hs
  · exact hψ

end StationaryHarmonicMaps.Analysis

end

module

public import StationaryHarmonicMaps.Analysis.NeumannKelvinWeakPoisson
public import StationaryHarmonicMaps.Analysis.NeumannKelvinLocalEnergy
public import StationaryHarmonicMaps.Analysis.NativeHarmonicGradient
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Effective boundary Neumann gradient bound

The natural-number coefficient controls the original zero-extended
Neumann gradient through the native Kelvin extension and its local energy.
-/

public section

open HarmonicMaps MeasureTheory Set Metric

namespace StationaryHarmonicMaps.Analysis.EffectiveCoulomb

@[expose] def neumannBoundaryBound (n : ℕ) : ℕ :=
  1 + 2 * 2 ^ (2 * n) + 2 * (n - 2) ^ 2 * 2 ^ (2 * (n - 2)) * 4 ^ n

theorem neumannBoundaryBound_pos (n : ℕ) : 0 < neumannBoundaryBound n := by
  unfold neumannBoundaryBound
  positivity

theorem neumannBoundaryBound_cast (n : ℕ) (hn : 2 ≤ n) :
    (neumannBoundaryBound n : ℝ) =
      1 + 2 * (2 : ℝ) ^ (2 * n) +
        2 * ((n : ℝ) - 2) ^ 2 * (2 : ℝ) ^ (2 * (n - 2)) * (4 : ℝ) ^ n := by
  have hSub : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := Nat.cast_sub hn
  simp only [neumannBoundaryBound, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, hSub]

theorem native_neumann_boundary_gradient_le (n : ℕ) (hn : 2 ≤ n)
    (q : ℕ) (a : Domain n) (ha : ‖a‖ = 1) (r : ℝ) (hr : 0 < r) (hrHalf : r ≤ 1 / 2)
    (u : Domain n → Ambient q) (Du F : Domain n → Gradient n q)
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hTests : ∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
      (∫ x in ball (0 : Domain n) 1, ∑ i : Fin n, inner ℝ (Du x i) (Dψ x i)) =
        ∫ x in ball (0 : Domain n) 1, ∑ i : Fin n, inner ℝ (F x i) (Dψ x i))
    (hZero : F =ᵐ[volume.restrict (ball (0 : Domain n) 1 ∩ ball a r)]
      (fun _ => (0 : Gradient n q))) :
    let D₀ := fun x i => (ball (0 : Domain n) 1).indicator (fun y => Du y i) x
    ∀ᵐ x ∂volume.restrict (ball a (r / 2)),
      hsNormSq (D₀ x) ≤ (neumannBoundaryBound n : ℝ) *
        (volume.real (ball a (r / 2)))⁻¹ * (∫ y in ball a r, hsNormSq (D₀ y)) := by
  classical
  intro D₀
  let K : ℝ := neumannBoundaryBound n
  let M := K * (volume.real (ball a (r / 2)))⁻¹ * (∫ y in ball a r, hsNormSq (D₀ y))
  let I := EuclideanGeometry.inversion (0 : Domain n) 1
  let V := fun x => ‖x‖ ^ (n - 2) •
    (∫ t in (‖x‖⁻¹) ^ 2..‖x‖⁻¹, t ^ (n - 3) • u (t • x))
  let B := fun x j => ‖x‖ ^ (n - 2) •
    (∫ t in (‖x‖⁻¹) ^ 2..‖x‖⁻¹, t ^ (n - 2) • Du (t • x) j)
  let O := fun x => ‖x‖ ^ (2 - (n : ℝ)) • u (I x) + ((n : ℝ) - 2) • V x
  let DO := fun x i => ‖x‖ ^ (2 - (n : ℝ)) •
    (∑ j : Fin n, (fderiv ℝ I x (EuclideanSpace.single i 1)) j • Du (I x) j) +
      ((n : ℝ) - 2) • (∑ j : Fin n,
        ((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j • B x j)
  let U := fun x => if ‖x‖ ≤ 1 then u x else O x
  let Dext := fun x i => if ‖x‖ ≤ 1 then Du x i else DO x i
  obtain ⟨hNative, hHarmonic⟩ := neumann_kelvin_native_weak_harmonic_boundary_ball hn a ha r hr hrHalf
    u Du F hu hF hTests hZero
  change MemW12 (ballDomain a r) U Dext at hNative
  change HolderToCK.WeakPoissonOn (ballDomain a r) Dext (fun _ => (0 : Ambient q)) at hHarmonic
  obtain ⟨_W, _hW, _hAE, _hLap, _hGrad, _hCols, _hPoint, hBound, _hTop, _hAll⟩ :=
    exists_smooth_harmonic_representative_with_original_gradient_ball hn a ⟨r, hr⟩ U Dext hNative hHarmonic
  have hEnergy : (∫ x in ball a r, hsNormSq (Dext x)) ≤ K *
      (∫ x in ball (0 : Domain n) 1 ∩ ball a r, hsNormSq (Du x)) := by
    rw [show K = _ from neumannBoundaryBound_cast n hn]
    exact (neumann_kelvin_local_gradient_energy hn Du hu.2.2 a ha r hr hrHalf).2
  have hOriginalIntegral : (∫ x in ball a r, hsNormSq (D₀ x)) =
      ∫ x in ball (0 : Domain n) 1 ∩ ball a r, hsNormSq (Du x) := by
    have hPoint : (fun x => hsNormSq (D₀ x)) =
        (ball (0 : Domain n) 1).indicator (fun x => hsNormSq (Du x)) := by
      funext x
      by_cases hx : x ∈ ball (0 : Domain n) 1
      · simp only [D₀, indicator_of_mem hx]
      · simp only [D₀, indicator_of_notMem hx, hsNormSq, norm_zero,
          zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
    rw [hPoint, setIntegral_indicator measurableSet_ball, inter_comm]
  rw [← hOriginalIntegral] at hEnergy
  have hM : (volume.real (ball a (r / 2)))⁻¹ * (∫ x in ball a r, hsNormSq (Dext x)) ≤ M := by
    exact (mul_le_mul_of_nonneg_left hEnergy (inv_nonneg.mpr ENNReal.toReal_nonneg)).trans_eq
      (by dsimp only [M]; simp only [measureReal_def]; ring)
  have hOriginalPoint (x : Domain n) : hsNormSq (D₀ x) ≤ hsNormSq (Dext x) := by
    by_cases hx : x ∈ ball (0 : Domain n) 1
    · have hxNorm : ‖x‖ ≤ 1 := (by simpa only [mem_ball, dist_zero_right] using hx : ‖x‖ < 1).le
      simp only [D₀, Dext, indicator_of_mem hx, if_pos hxNorm, le_refl]
    · simp only [D₀, indicator_of_notMem hx, hsNormSq, norm_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact hBound.mono fun x hx => (hOriginalPoint x).trans (hx.trans hM)

end StationaryHarmonicMaps.Analysis.EffectiveCoulomb

end

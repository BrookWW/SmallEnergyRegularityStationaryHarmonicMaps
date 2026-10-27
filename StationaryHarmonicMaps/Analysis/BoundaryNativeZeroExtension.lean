module

public import StationaryHarmonicMaps.Analysis.NaturalCoexactResidual
public import StationaryHarmonicMaps.Analysis.AffineMorreyScaling
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Literal zero extension of natural solenoidal fields

Orthogonality to every native gradient on the ball is the weak zero normal
boundary condition. It makes the literal zero extension distributionally
solenoidal on the whole space, with exactly the original full HS energy.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The original all-native gradient orthogonality gives a whole-space solenoidal literal zero extension and exact energy. -/
theorem natural_solenoidal_zeroExtension_unitBall {n q : ℕ}
    (Z : Domain n → Gradient n q)
    (hZ : ∀ i, MemLp (fun x => Z x i) 2
      (volume.restrict (ball (0 : Domain n) 1)))
    (hNatural : ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 1) w Dw →
      (∫ x in ball (0 : Domain n) 1, ∑ i : Fin n, inner ℝ (Z x i) (Dw x i)) = 0) :
    let B := ball (0 : Domain n) 1
    let G := B.indicator Z
    (∀ i, MemLp (fun x => G x i) 2 volume) ∧
      (∀ x ∈ B, G x = Z x) ∧
      (∀ x ∉ B, G x = 0) ∧
      (∫ x, hsNormSq (G x)) = (∫ x in B, hsNormSq (Z x)) ∧
      HolderToCK.WeakPoissonOn (⟨univ, isOpen_univ⟩ : OpenDomain n) G
        (fun _ => (0 : Ambient q)) := by
  classical
  intro B G
  have hGI (i : Fin n) : MemLp (fun x => G x i) 2 volume := by
    have H := (memLp_indicator_iff_restrict measurableSet_ball).mpr (hZ i)
    convert H using 1
    funext x
    by_cases hx : x ∈ B
    · simp only [G, indicator_of_mem hx]
      exact (indicator_of_mem hx (fun x => Z x i)).symm
    · simp only [G, indicator_of_notMem hx, Pi.zero_apply]
      exact (indicator_of_notMem hx (fun x => Z x i)).symm
  have hIn (x : Domain n) (hx : x ∈ B) : G x = Z x := indicator_of_mem hx Z
  have hOut (x : Domain n) (hx : x ∉ B) : G x = 0 := indicator_of_notMem hx Z
  have hEnergy : (fun x => hsNormSq (G x)) = B.indicator (fun x => hsNormSq (Z x)) := by
    funext x
    by_cases hx : x ∈ B
    · rw [hIn x hx, indicator_of_mem hx]
    · rw [hOut x hx, indicator_of_notMem hx]
      simp only [hsNormSq, Pi.zero_apply, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
        Finset.sum_const_zero]
  refine ⟨hGI, hIn, hOut, ?_, ?_⟩
  · rw [hEnergy, integral_indicator measurableSet_ball]
  · refine ⟨locallyIntegrableOn_zero, ?_⟩
    intro ψ hψ _hc _hs
    let Dψ := fun x i => fderiv ℝ ψ x (EuclideanSpace.single i 1)
    have hW := memW12_ball_of_ambient_c1 (0 : Domain n) 1 ψ (hψ.of_le (by simp))
    have hI : IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (Z x i) (Dψ x i)) B volume :=
      integrable_finsetSum _ (fun i _ =>
        HolderToCK.integrable_inner_of_memLp_two (hZ i) (hW.2.2 i))
    have hScalar : (fun x => ∑ i : Fin n, inner ℝ (G x i) (Dψ x i)) =
        B.indicator (fun x => ∑ i : Fin n, inner ℝ (Z x i) (Dψ x i)) := by
      funext x
      by_cases hx : x ∈ B
      · rw [hIn x hx, indicator_of_mem hx]
      · rw [hOut x hx, indicator_of_notMem hx]
        simp only [Pi.zero_apply, inner_zero_left, Finset.sum_const_zero]
    have hGlobalI : Integrable (fun x => ∑ i : Fin n, inner ℝ (G x i) (Dψ x i)) volume := by
      rw [hScalar]
      exact (integrable_indicator_iff measurableSet_ball).mpr hI
    refine ⟨?_, ?_, ?_⟩
    · change Integrable (fun x => ∑ i : Fin n, inner ℝ (G x i) (Dψ x i))
        (volume.restrict univ)
      simpa only [Measure.restrict_univ] using hGlobalI
    · simp only [inner_zero_left]
      exact integrable_zero _ _ _
    · change (∫ x in univ, ∑ i : Fin n, inner ℝ (G x i) (Dψ x i)) = _
      rw [setIntegral_univ, hScalar, integral_indicator measurableSet_ball,
        hNatural ψ Dψ hW]
      simp only [inner_zero_left, integral_zero, neg_zero]

end StationaryHarmonicMaps.Analysis

end

module

public import HolderToCK.Analysis.WeakPoissonLocality
public import HolderToCK.Analysis.WeakPoissonZeroBoundaryGreen
public import HarmonicMaps.EnergyLemmas

/-! # Signed gradient-error energy for an actual harmonic difference

The difference weak equation and its genuine zero-boundary test give the exact
negative forcing identity. A pointwise bound for that same difference yields
its energy bound by the L1 norm of the forcing. This applies to the smooth
auxiliaries in the replacement proof, where the forcing has native L2 data.
-/

public section

open HarmonicMaps MeasureTheory

namespace HolderToCK

theorem weak_harmonic_difference_error_identity {n q : ℕ} {Ω : OpenDomain n}
    {u w F : Domain n → Ambient q} {Du Dw : Domain n → Gradient n q}
    (hEq : WeakPoissonOn Ω Du F) (hHarmonic : WeakPoissonOn Ω Dw (fun _ => 0))
    (hF : MemLp F 2 (volume.restrict Ω.val))
    (hzero : HasZeroBoundaryValues Ω (u - w) (fun x i => Du x i - Dw x i)) :
    (∫ x in Ω.val, hsNormSq (fun i => Du x i - Dw x i)) =
      -(∫ x in Ω.val, inner ℝ (F x) ((u - w) x)) := by
  have hDiff : WeakPoissonOn Ω (fun x i => Du x i - Dw x i) F := by
    simpa only [sub_zero] using hEq.sub hHarmonic
  have hGreen := hDiff.zeroBoundary_green hzero.1.2.2 hF hzero
  simpa only [hsNormSq, real_inner_self_eq_norm_sq] using hGreen.2.2

theorem weak_harmonic_difference_error_le {n q : ℕ} {Ω : OpenDomain n}
    [IsFiniteMeasure (volume.restrict Ω.val)]
    {u w F : Domain n → Ambient q} {Du Dw : Domain n → Gradient n q}
    (hEq : WeakPoissonOn Ω Du F) (hHarmonic : WeakPoissonOn Ω Dw (fun _ => 0))
    (hF : MemLp F 2 (volume.restrict Ω.val))
    (hzero : HasZeroBoundaryValues Ω (u - w) (fun x i => Du x i - Dw x i))
    (M : ℝ) (hBound : ∀ x ∈ Ω.val, ‖(u - w) x‖ ≤ M) :
    (∫ x in Ω.val, hsNormSq (fun i => Du x i - Dw x i)) ≤
      M * ∫ x in Ω.val, ‖F x‖ := by
  have hForceInt := hF.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hPairInt := integrable_inner_of_memLp_two hF hzero.1.2.1
  have hpoint : ∀ x ∈ Ω.val, -inner ℝ (F x) ((u - w) x) ≤ ‖F x‖ * M := by
    intro x hx
    exact (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hBound x hx) (norm_nonneg _)))
  rw [weak_harmonic_difference_error_identity hEq hHarmonic hF hzero, ← integral_neg]
  calc
    _ ≤ ∫ x in Ω.val, ‖F x‖ * M :=
      setIntegral_mono_on hPairInt.neg (hForceInt.norm.mul_const M) Ω.property.measurableSet hpoint
    _ = _ := by rw [integral_mul_const, mul_comm]

end HolderToCK
end

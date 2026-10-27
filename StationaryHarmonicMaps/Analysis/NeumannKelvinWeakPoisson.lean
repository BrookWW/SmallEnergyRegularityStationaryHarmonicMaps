module

public import StationaryHarmonicMaps.Analysis.NeumannKelvinNativeExtension
public import StationaryHarmonicMaps.Analysis.NeumannKelvinNaturalPairing
import StationaryHarmonicMaps.Analysis.SobolevLinearOperations

/-!
# Actual weak harmonicity of the native Neumann reflection

The original all-native Neumann response and the original forcing vanishing
on a boundary cap produce weak harmonicity of the same reflected graph.
The true natural adjoint test has arbitrary sphere values; its actual
localized derivative removes the forcing outside that same cap.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Set Filter Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Original native Neumann data produce the same literal native reflected graph and its weak harmonic equation on each off-support sphere-centered cap. -/
theorem neumann_kelvin_native_weak_harmonic_boundary_ball {n q : ℕ} (hn : 2 ≤ n)
    (a : Domain n) (ha : ‖a‖ = 1) (r : ℝ) (hr : 0 < r) (hrHalf : r ≤ 1/2)
    (u : Domain n → Ambient q) (Du F : Domain n → Gradient n q)
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (hF : ∀ j, MemLp (fun x => F x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hTests : ∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
      (∫ x in ball (0 : Domain n) 1, ∑ i : Fin n, inner ℝ (Du x i) (Dψ x i)) =
        ∫ x in ball (0 : Domain n) 1, ∑ i : Fin n, inner ℝ (F x i) (Dψ x i))
    (hZero : F =ᵐ[volume.restrict (ball (0 : Domain n) 1 ∩ ball a r)]
      (fun _ => (0 : Gradient n q))) :
    let I := inversion (0 : Domain n) 1
    let V := fun (f : Domain n → Ambient q) x => ‖x‖^(n-2) •
      (∫ t in (‖x‖⁻¹)^2..‖x‖⁻¹, t^(n-3) • f (t • x))
    let B := fun (G : Domain n → Gradient n q) x j => ‖x‖^(n-2) •
      (∫ t in (‖x‖⁻¹)^2..‖x‖⁻¹, t^(n-2) • G (t • x) j)
    let O := fun (f : Domain n → Ambient q) x => ‖x‖^(2-(n : ℝ)) • f (I x) + ((n : ℝ)-2) • V f x
    let DO := fun (G : Domain n → Gradient n q) x i => ‖x‖^(2-(n : ℝ)) •
      (∑ j : Fin n, (fderiv ℝ I x (EuclideanSpace.single i 1)) j • G (I x) j) +
      ((n : ℝ)-2) • (∑ j : Fin n,
        ((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j • B G x j)
    let U := fun x => if ‖x‖ ≤ 1 then u x else O u x
    let DU := fun x i => if ‖x‖ ≤ 1 then Du x i else DO Du x i
    MemW12 (ballDomain a r) U DU ∧
      HolderToCK.WeakPoissonOn (ballDomain a r) DU (fun _ => (0 : Ambient q)) := by
  classical
  intro I V B O DO U DU
  let ν := volume.restrict (ball (0 : Domain n) 1)
  have hLarge : MemW12 (ballDomain (0 : Domain n) 2) U DU :=
    memW12_neumann_kelvin_extension_ball_two hn u Du hu
  have hSub : ball a r ⊆ ball (0 : Domain n) 2 := by
    intro x hx
    have H := dist_triangle x a (0 : Domain n)
    have hxDist : dist x a < r := hx
    have haDist : dist a (0 : Domain n) = 1 := by simpa only [dist_zero_right] using ha
    rw [haDist] at H
    exact mem_ball.mpr (by linarith only [H, hxDist, hrHalf])
  have hNative : MemW12 (ballDomain a r) U DU :=
    ⟨hLarge.1.mono hSub,
      hLarge.2.1.mono_measure (Measure.restrict_mono_set volume hSub),
      fun i => (hLarge.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)⟩
  refine ⟨hNative, locallyIntegrableOn_zero, ?_⟩
  intro ψ hψ hcψ hsψ
  have hsDouble : tsupport ψ ⊆ ball (0 : Domain n) 2 := hsψ.trans hSub
  obtain ⟨φ, _hφ, hφW, hφSupport, hPairI, hPair⟩ :=
    exists_neumann_kelvin_natural_pairing hn Du hu.2.2 ψ hψ hcψ hsDouble
  let Dtest := fun x i => fderiv ℝ ψ x (EuclideanSpace.single i 1) +
    fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hψW := memW12_ball_of_ambient_c1 (0 : Domain n) 1 ψ (hψ.of_le (by simp))
  have hTest : MemW12 (ballDomain (0 : Domain n) 1) (ψ+φ) Dtest :=
    ⟨hasWeakGradient_add hψW.1 hφW.1, hψW.2.1.add hφW.2.1,
      fun i => (hψW.2.2 i).add (hφW.2.2 i)⟩
  have hNat := hTests (ψ+φ) Dtest hTest
  have _hFPairI : Integrable (fun x => ∑ i : Fin n, inner ℝ (F x i) (Dtest x i)) ν :=
    integrable_finsetSum _ (fun i _ => HolderToCK.integrable_inner_of_memLp_two (hF i) (hTest.2.2 i))
  obtain ⟨s, hs, hSupportSmall⟩ := exists_pos_lt_subset_ball hr (isClosed_tsupport ψ) hsψ
  have hZeroPoint : ∀ᵐ x : Domain n ∂volume,
      x ∈ ball (0 : Domain n) 1 ∩ ball a r → F x = 0 :=
    (ae_restrict_iff' (measurableSet_ball.inter measurableSet_ball)).mp hZero
  have hFPairZero : (fun x => ∑ i : Fin n, inner ℝ (F x i) (Dtest x i)) =ᵐ[ν] (fun _ => 0) := by
    filter_upwards [hZeroPoint.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_ball] with x hxZero hxBall
    by_cases hxCap : x ∈ ball a r
    · have hFx : F x = 0 := hxZero ⟨hxBall,hxCap⟩
      simp only [hFx, Pi.zero_apply, inner_zero_left, Finset.sum_const_zero]
    · have hNotSupport : x ∉ tsupport ψ := fun h => hxCap (hsψ h)
      have hDψ : fderiv ℝ ψ x = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hNotSupport
      have hDist : r ≤ dist x a := le_of_not_gt hxCap
      have hDφ : fderiv ℝ φ x = 0 := hφSupport a s ha hSupportSmall x
        (mem_ball_zero_iff.mp hxBall) (hs.2.trans_le hDist)
      simp only [Dtest, hDψ, hDφ, zero_apply, add_zero, inner_zero_right, Finset.sum_const_zero]
  have hIntegralZero : (∫ x, ∑ i : Fin n, inner ℝ (F x i) (Dtest x i) ∂ν) = 0 := by
    rw [integral_congr_ae hFPairZero, integral_zero]
  have hNatZero : (∫ x in ball (0 : Domain n) 1, ∑ i : Fin n, inner ℝ (Du x i) (Dtest x i)) = 0 :=
    hNat.trans hIntegralZero
  have hGlobalZero : (∫ x in ball (0 : Domain n) 2, ∑ i : Fin n, inner ℝ (DU x i)
      (fderiv ℝ ψ x (EuclideanSpace.single i 1))) = 0 := hPair.trans hNatZero
  have hCapEq : (∫ x in ball a r, ∑ i : Fin n, inner ℝ (DU x i)
      (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      ∫ x in ball (0 : Domain n) 2, ∑ i : Fin n, inner ℝ (DU x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hSub
    intro x hx
    have hNotSupport : x ∉ tsupport ψ := fun h => hx.2 (hsψ h)
    have hDψ : fderiv ℝ ψ x = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hNotSupport
    simp only [hDψ, zero_apply, inner_zero_right, Finset.sum_const_zero]
  refine ⟨hPairI.mono_set hSub, ?_, ?_⟩
  · simp only [inner_zero_left]
    exact integrable_zero _ _ _
  · change (∫ x in ball a r, ∑ i : Fin n, inner ℝ (DU x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
        -(∫ x in ball a r, inner ℝ (0 : Ambient q) (ψ x))
    rw [hCapEq, hGlobalZero]
    simp only [inner_zero_left, integral_zero, neg_zero]

end StationaryHarmonicMaps.Analysis

end

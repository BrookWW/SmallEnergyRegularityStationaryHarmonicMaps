module

public import StationaryHarmonicMaps.Analysis.DistributionHarmonicMollification
public import HolderToCK.Analysis.WeakPoissonAffine

/-!
# Actual affine transport of relative Hodge harmonic identities

A compact smooth vector test has the literal squared dilation factor in
its Laplacian. Its true inverse affine test transports every original
coefficient-harmonic pairing and its ordinary integrability. Multiplying
a zero-forcing native divergence equation preserves that equation.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The Laplacian of an actual smooth affine test has the squared
physical dilation multiplier. -/
theorem affineBallTest_laplacian {n q : ℕ} (ψ : Domain n → Ambient q)
    (hψ : ContDiff ℝ ∞ ψ) (a b : Domain n) (t : ℝ) (x : Domain n) :
    Laplacian.laplacian (fun y=>ψ (a+t • (y-b))) x=
      t^2 • Laplacian.laplacian ψ (a+t • (x-b)) := by
  let Φ := fun y=>ψ (a+t • (y-b))
  have hΦ : ContDiff ℝ ∞ Φ := hψ.comp (affineBall_contDiff a b t)
  let d := fun (i : Fin n) y=>fderiv ℝ ψ y (EuclideanSpace.single i 1)
  have hd (i : Fin n) : ContDiff ℝ ∞ (d i) :=
    (hψ.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hFirst (i : Fin n) : (fun y=>fderiv ℝ Φ y (EuclideanSpace.single i 1))=
      (fun y=>t • d i (a+t • (y-b))) := by
    funext y
    simpa only [coordinateDerivative,Φ,d] using affineBallTest_coordinateDerivative hψ a b t i y
  have hSecond (i : Fin n) : fderiv ℝ (fun y=>fderiv ℝ Φ y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)=t^2 • fderiv ℝ (d i) (a+t • (x-b)) (EuclideanSpace.single i 1) := by
    rw [hFirst]
    have HD := ((((hd i).comp (affineBall_contDiff a b t)).differentiable (by simp) x).hasFDerivAt.const_smul t).fderiv
    have HE := congrArg (fun L : Domain n →L[ℝ] Ambient q=>L (EuclideanSpace.single i 1)) HD
    change fderiv ℝ (fun y=>t • d i (a+t • (y-b))) x (EuclideanSpace.single i 1)=
      t • fderiv ℝ (fun y=>d i (a+t • (y-b))) x (EuclideanSpace.single i 1) at HE
    rw [HE]
    have H := affineBallTest_coordinateDerivative (hd i) a b t i x
    simp only [coordinateDerivative] at H
    rw [H,smul_smul,pow_two]
  rw [laplacian_eq_sum_second_coordinate Φ hΦ,laplacian_eq_sum_second_coordinate ψ hψ]
  simp_rw [hSecond]
  rw [Finset.smul_sum]

/-- Original ordinary vector Laplacian tests transport to the entire
actual affine ball, with the same field amplitude. -/
theorem coefficient_harmonic_vector_tests_affineBall {n q : ℕ}
    (a b : Domain n) {t : ℝ} (ht : 0<t) (r : ℝ)
    (F : Domain n → Gradient n q)
    (hTests : ∀(j : Fin n) (ψ : Domain n → Ambient q),ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ⊆ball a r →
      IntegrableOn (fun x=>inner ℝ (F x j) (Laplacian.laplacian ψ x)) (ball a r) volume ∧
      (∫x in ball a r,inner ℝ (F x j) (Laplacian.laplacian ψ x))=0) :
    ∀(j : Fin n) (ψ : Domain n → Ambient q),ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ⊆ball b (r/t) →
      IntegrableOn (fun x=>inner ℝ (F (a+t • (x-b)) j) (Laplacian.laplacian ψ x)) (ball b (r/t)) volume ∧
      (∫x in ball b (r/t),inner ℝ (F (a+t • (x-b)) j) (Laplacian.laplacian ψ x))=0 := by
  intro j ψ hψ hc hs
  let Φ := fun x=>ψ (b+t⁻¹ • (x-a))
  have hΦ : ContDiff ℝ ∞ Φ := hψ.comp (affineBall_contDiff b a t⁻¹)
  have hcΦ : HasCompactSupport Φ := affineBallTest_hasCompactSupport hc b a (inv_ne_zero ht.ne')
  have hRadius : r/t/t⁻¹=r := by field_simp
  have hsΦ : tsupport Φ⊆ball a r := by
    simpa only [hRadius,Φ] using affineBallTest_tsupport_subset b a (inv_pos.mpr ht) (r/t) hs
  obtain ⟨hI,hZero⟩ := hTests j Φ hΦ hcΦ hsΦ
  have hPoint (x : Domain n) : inner ℝ (F (a+t • (x-b)) j) (Laplacian.laplacian Φ (a+t • (x-b)))=
      (t⁻¹)^2*inner ℝ (F (a+t • (x-b)) j) (Laplacian.laplacian ψ x) := by
    rw [affineBallTest_laplacian ψ hψ b a t⁻¹]
    simp only [add_sub_cancel_left,smul_smul,inv_mul_cancel₀ ht.ne',one_smul,add_sub_cancel,
      real_inner_smul_right]
  have hAffineI := HolderToCK.integrable_affineBall a b ht r hI
  have hScale : t^2*(t⁻¹)^2=1 := by rw [←mul_pow,mul_inv_cancel₀ ht.ne',one_pow]
  simp_rw [hPoint] at hAffineI
  have hOrdinary := hAffineI.const_mul (t^2)
  simp only [←mul_assoc,hScale,one_mul] at hOrdinary
  refine ⟨hOrdinary,?_⟩
  have H := integral_affineBall a b ht r (fun x=>inner ℝ (F x j) (Laplacian.laplacian Φ x))
  rw [hZero,smul_zero] at H
  simp_rw [hPoint] at H
  rw [integral_const_mul] at H
  exact (mul_eq_zero.mp H).resolve_left (pow_ne_zero 2 (inv_ne_zero ht.ne'))

/-- Constant multiplication of the original one-form preserves its
actual zero-forcing weak divergence equation and pairing integrability. -/
theorem weakPoissonOn_zero_const_smul {n q : ℕ} {Ω : OpenDomain n}
    {F : Domain n → Gradient n q}
    (hEq : HolderToCK.WeakPoissonOn Ω F (fun _=>(0:Ambient q))) (c : ℝ) :
    HolderToCK.WeakPoissonOn Ω (fun x i=>c • F x i) (fun _=>(0:Ambient q)) := by
  refine ⟨locallyIntegrableOn_zero,?_⟩
  intro ψ hψ hc hs
  obtain ⟨hI,hZeroI,hZero⟩ := hEq.2 ψ hψ hc hs
  simp only [inner_zero_left,integral_zero,neg_zero] at hZero
  have hPoint (x : Domain n) : (∑i : Fin n,inner ℝ (c • F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=
      c*(∑i : Fin n,inner ℝ (F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
    simp only [real_inner_smul_left,Finset.mul_sum]
  refine ⟨(hI.const_mul c).congr (Eventually.of_forall fun x=>(hPoint x).symm),hZeroI,?_⟩
  rw [integral_congr_ae (Eventually.of_forall hPoint),integral_const_mul,hZero]
  simp only [mul_zero,inner_zero_left,integral_zero,neg_zero]

end StationaryHarmonicMaps.Analysis

end

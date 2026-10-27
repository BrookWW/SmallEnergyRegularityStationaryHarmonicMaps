module

public import StationaryHarmonicMaps.Foundation.DomainStationarity
public import HarmonicMaps.Analysis.InnerVariationStressIntegrability
public import HarmonicMaps.SobolevRestriction
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Locality and integrability of compactly supported stress tests -/

public section

open HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff

namespace StationaryHarmonicMaps

private theorem integrable_inner_memLp {n q : ℕ} {μ : Measure (Domain n)}
    {f g : Domain n → Ambient q} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

theorem domainStress_zero_of_notMem_tsupport {n q : ℕ}
    (Du : Domain n → Gradient n q) (X : Domain n → Domain n)
    {x : Domain n} (hx : x ∉ tsupport X) :
    hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ X x (EuclideanSpace.single i 1)) i) -
      2 * ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (fderiv ℝ X x (EuclideanSpace.single i 1)) j = 0 := by
  simp only [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx, zero_apply, WithLp.ofLp_zero,
    Pi.zero_apply, Finset.sum_const_zero, mul_zero, sub_zero]

theorem integrable_domainStress {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {X : Domain n → Domain n}
    (hX : ContDiff ℝ ∞ X) (hc : HasCompactSupport X)
    (hs : tsupport X ⊆ Ω.val) :
    Integrable (fun x => hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ X x (EuclideanSpace.single i 1)) i) -
      2 * ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (fderiv ℝ X x (EuclideanSpace.single i 1)) j) volume := by
  have hDu (i : Fin n) : MemLp (fun x => Du x i) 2 (volume.restrict (tsupport X)) :=
    hu.2.2 i (tsupport X) hc hs
  have hcoef (i j : Fin n) :
      Continuous (fun x => (fderiv ℝ X x (EuclideanSpace.single i 1)) j) :=
    (EuclideanSpace.proj j).continuous.comp
      ((hX.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hdiv : Continuous (fun x => ∑ i : Fin n,
      (fderiv ℝ X x (EuclideanSpace.single i 1)) i) :=
    continuous_finsetSum Finset.univ (fun i _ => hcoef i i)
  have he : IntegrableOn (fun x => hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ X x (EuclideanSpace.single i 1)) i)) (tsupport X) :=
    IntegrableOn.mul_continuousOn
      (integrable_hsNormSq_of_memLp_columns hDu) hdiv.continuousOn hc
  have hterm (i j : Fin n) : IntegrableOn (fun x =>
      inner ℝ (Du x i) (Du x j) *
        (fderiv ℝ X x (EuclideanSpace.single i 1)) j) (tsupport X) :=
    IntegrableOn.mul_continuousOn
      (integrable_inner_memLp (hDu i) (hDu j)) (hcoef i j).continuousOn hc
  have hstress := he.sub ((integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hterm i j))).const_mul 2)
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hstress
  intro x hx
  by_contra hnot
  exact hx (domainStress_zero_of_notMem_tsupport Du X hnot)

theorem isDomainStationary_iff_stress_integral_eq_zero {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) :
    IsDomainStationary Ω Du ↔
      ∀ (X : Domain n → Domain n), ContDiff ℝ ∞ X →
        HasCompactSupport X → tsupport X ⊆ Ω.val →
        (∫ x in Ω.val, hsNormSq (Du x) *
          (∑ i : Fin n, (fderiv ℝ X x (EuclideanSpace.single i 1)) i) -
          2 * ∑ i : Fin n, ∑ j : Fin n,
            inner ℝ (Du x i) (Du x j) *
              (fderiv ℝ X x (EuclideanSpace.single i 1)) j) = 0 := by
  constructor
  · intro h X hX hc hs
    exact (h X hX hc hs).2
  · intro h X hX hc hs
    exact ⟨(integrable_domainStress hu hX hc hs).integrableOn, h X hX hc hs⟩

theorem domainStress_integral_eq_of_support_subset {n q : ℕ}
    {Ω Ω' : OpenDomain n} (hsub : Ω'.val ⊆ Ω.val)
    (Du : Domain n → Gradient n q) (X : Domain n → Domain n)
    (hs : tsupport X ⊆ Ω'.val) :
    (∫ x in Ω.val, hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ X x (EuclideanSpace.single i 1)) i) -
      2 * ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (fderiv ℝ X x (EuclideanSpace.single i 1)) j) =
    (∫ x in Ω'.val, hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ X x (EuclideanSpace.single i 1)) i) -
      2 * ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (fderiv ℝ X x (EuclideanSpace.single i 1)) j) := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Ω.property.measurableSet hsub
  intro x hx
  exact domainStress_zero_of_notMem_tsupport Du X (fun h => hx.2 (hs h))

theorem IsDomainStationary.mono {n q : ℕ} {Ω Ω' : OpenDomain n}
    {Du : Domain n → Gradient n q} (h : IsDomainStationary Ω Du)
    (hsub : Ω'.val ⊆ Ω.val) : IsDomainStationary Ω' Du := by
  intro X hX hc hs
  obtain ⟨hi, heq⟩ := h X hX hc (hs.trans hsub)
  exact ⟨hi.mono_set hsub,
    (domainStress_integral_eq_of_support_subset hsub Du X hs).symm.trans heq⟩

theorem IsDomainStationary.congr_ae {n q : ℕ} {Ω : OpenDomain n}
    {Du Dv : Domain n → Gradient n q} (h : IsDomainStationary Ω Du)
    (hDu : Du =ᵐ[volume.restrict Ω.val] Dv) : IsDomainStationary Ω Dv := by
  intro X hX hc hs
  obtain ⟨hi, heq⟩ := h X hX hc hs
  have hd : (fun x => hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ X x (EuclideanSpace.single i 1)) i) -
      2 * ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (fderiv ℝ X x (EuclideanSpace.single i 1)) j) =ᵐ[volume.restrict Ω.val]
    (fun x => hsNormSq (Dv x) *
      (∑ i : Fin n, (fderiv ℝ X x (EuclideanSpace.single i 1)) i) -
      2 * ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Dv x i) (Dv x j) *
          (fderiv ℝ X x (EuclideanSpace.single i 1)) j) := by
    filter_upwards [hDu] with x hx
    rw [hx]
  exact ⟨hi.congr hd, (integral_congr_ae hd).symm.trans heq⟩

theorem IsDomainStationary.test_ball {n q : ℕ} {Ω : OpenDomain n}
    {Du : Domain n → Gradient n q} (h : IsDomainStationary Ω Du)
    {a : Domain n} {R : ℝ} (hball : Metric.closedBall a R ⊆ Ω.val)
    {X : Domain n → Domain n} (hX : ContDiff ℝ ∞ X)
    (hc : HasCompactSupport X) (hs : tsupport X ⊆ Metric.ball a R) :
    IntegrableOn (fun x => hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ X x (EuclideanSpace.single i 1)) i) -
      2 * ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (fderiv ℝ X x (EuclideanSpace.single i 1)) j) (Metric.ball a R) volume ∧
    (∫ x in Metric.ball a R, hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ X x (EuclideanSpace.single i 1)) i) -
      2 * ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (fderiv ℝ X x (EuclideanSpace.single i 1)) j) = 0 := by
  exact h.mono (Ω' := ballDomain a R)
    (Metric.ball_subset_closedBall.trans hball) X hX hc hs

end StationaryHarmonicMaps

end

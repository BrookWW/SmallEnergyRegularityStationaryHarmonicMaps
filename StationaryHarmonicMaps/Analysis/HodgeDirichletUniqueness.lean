module

public import StationaryHarmonicMaps.Analysis.HodgeDirichletPotential
public import StationaryHarmonicMaps.Analysis.ZeroBoundaryPoincare
import HarmonicMaps.Analysis.SobolevAECongruence

/-!
# Native zero-boundary tests and uniqueness of the Dirichlet gradient response

Actual L² pairing continuity extends compact smooth gradient tests to the
native W₀¹,² graph closure. Coercivity then gives uniqueness of both the map
and its explicit gradient almost everywhere on the ball.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- L² gradient pairings extend from compact smooth tests to every native W₀¹,² test. -/
theorem gradient_pairing_eq_on_zeroBoundary_of_smooth {n q : ℕ} (Ω : OpenDomain n)
    (G F : Domain n → Gradient n q)
    (hG : ∀ i : Fin n, MemLp (fun x => G x i) 2 (volume.restrict Ω.val))
    (hF : ∀ i : Fin n, MemLp (fun x => F x i) 2 (volume.restrict Ω.val))
    (hEq : ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Ω.val →
      (∫ x in Ω.val, ∑ i : Fin n, inner ℝ (G x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      ∫ x in Ω.val, ∑ i : Fin n, inner ℝ (F x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1)))
    {v : Domain n → Ambient q} {Dv : Domain n → Gradient n q}
    (hv : HasZeroBoundaryValues Ω v Dv) :
    IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (G x i) (Dv x i)) Ω.val volume ∧
    IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (F x i) (Dv x i)) Ω.val volume ∧
    (∫ x in Ω.val, ∑ i : Fin n, inner ℝ (G x i) (Dv x i)) =
      ∫ x in Ω.val, ∑ i : Fin n, inner ℝ (F x i) (Dv x i) := by
  obtain ⟨hvW, ψ, hψ, hcψ, _hmaplim, hDlim⟩ := hv
  let μ := volume.restrict Ω.val
  have hD (k : ℕ) (i : Fin n) : MemLp (coordinateDerivative (ψ k) (hψ k) i) 2 μ :=
    ((hψ k).continuous_fderiv (by simp) |>.clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hcψ k).1.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hpair (A : Domain n → Gradient n q)
      (hA : ∀ i : Fin n, MemLp (fun x => A x i) 2 μ) :
      Integrable (fun x => ∑ i : Fin n, inner ℝ (A x i) (Dv x i)) μ ∧
      Tendsto (fun k => ∫ x, ∑ i : Fin n, inner ℝ (A x i)
        (coordinateDerivative (ψ k) (hψ k) i x) ∂μ) atTop
        (𝓝 (∫ x, ∑ i : Fin n, inner ℝ (A x i) (Dv x i) ∂μ)) := by
    have hi (i : Fin n) := HolderToCK.integrable_inner_of_memLp_two (hA i) (hvW.2.2 i)
    refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
    have hs := tendsto_finsetSum Finset.univ (fun i _ =>
      HolderToCK.tendsto_integral_inner_of_L2 (fun k => hD k i) (hvW.2.2 i) (hA i) (hDlim i))
    have hsum (k : ℕ) : (∫ x, ∑ i : Fin n, inner ℝ (A x i)
        (coordinateDerivative (ψ k) (hψ k) i x) ∂μ) =
        ∑ i : Fin n, ∫ x, inner ℝ (A x i)
          (coordinateDerivative (ψ k) (hψ k) i x) ∂μ :=
      integral_finsetSum _ (fun i _ => HolderToCK.integrable_inner_of_memLp_two (hA i) (hD k i))
    have hsumV : (∫ x, ∑ i : Fin n, inner ℝ (A x i) (Dv x i) ∂μ) =
        ∑ i : Fin n, ∫ x, inner ℝ (A x i) (Dv x i) ∂μ :=
      integral_finsetSum _ (fun i _ => hi i)
    simpa only [hsum, hsumV] using hs
  obtain ⟨hGI, hGlim⟩ := hpair G hG
  obtain ⟨hFI, hFlim⟩ := hpair F hF
  refine ⟨hGI, hFI, ?_⟩
  apply tendsto_nhds_unique hGlim
  apply hFlim.congr
  intro k
  exact (hEq (ψ k) (hψ k) (hcψ k).1 (hcψ k).2).symm

/-- The actual Dirichlet gradient projection admits every native zero-boundary test. -/
theorem exists_dirichlet_gradient_projection_zeroBoundary_tests {n q : ℕ} (hn : 1 ≤ n)
    (a : Domain n) {R : ℝ} (hR : 0 < R)
    (F : Domain n → Gradient n q)
    (hF : ∀ i : Fin n, MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a R))) :
    ∃ (f : Domain n → Ambient q) (Df : Domain n → Gradient n q),
      HasZeroBoundaryValues (ballDomain a R) f Df ∧
      (∫ x in Metric.ball a R, hsNormSq (Df x)) ≤ ∫ x in Metric.ball a R, hsNormSq (F x) ∧
      ∀ (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
        HasZeroBoundaryValues (ballDomain a R) v Dv →
        IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (Df x i) (Dv x i))
          (Metric.ball a R) volume ∧
        IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (F x i) (Dv x i))
          (Metric.ball a R) volume ∧
        (∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (Df x i) (Dv x i)) =
          ∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (F x i) (Dv x i) := by
  obtain ⟨f, Df, hf, henergy, htests⟩ := exists_dirichlet_gradient_projection hn a hR F hF
  refine ⟨f, Df, hf, henergy, ?_⟩
  intro v Dv hv
  exact gradient_pairing_eq_on_zeroBoundary_of_smooth (ballDomain a R) Df F hf.1.2.2 hF
    (fun ψ hψ hcψ hsψ => (htests ψ hψ hcψ hsψ).2.2) hv

/-- The actual residual is orthogonal in energy to every native zero-boundary test gradient. -/
theorem residual_gradient_orthogonal_zeroBoundary {n q : ℕ} (Ω : OpenDomain n)
    (G F : Domain n → Gradient n q)
    (hG : ∀ i : Fin n, MemLp (fun x => G x i) 2 (volume.restrict Ω.val))
    (hF : ∀ i : Fin n, MemLp (fun x => F x i) 2 (volume.restrict Ω.val))
    (hEq : ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Ω.val →
      (∫ x in Ω.val, ∑ i : Fin n, inner ℝ (G x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      ∫ x in Ω.val, ∑ i : Fin n, inner ℝ (F x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1)))
    {v : Domain n → Ambient q} {Dv : Domain n → Gradient n q}
    (hv : HasZeroBoundaryValues Ω v Dv) :
    IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (F x i - G x i) (Dv x i)) Ω.val volume ∧
    (∫ x in Ω.val, ∑ i : Fin n, inner ℝ (F x i - G x i) (Dv x i)) = 0 := by
  obtain ⟨hGI, hFI, htest⟩ :=
    gradient_pairing_eq_on_zeroBoundary_of_smooth Ω G F hG hF hEq hv
  have heq : (fun x => ∑ i : Fin n, inner ℝ (F x i - G x i) (Dv x i)) =
      (fun x => ∑ i : Fin n, inner ℝ (F x i) (Dv x i)) -
      (fun x => ∑ i : Fin n, inner ℝ (G x i) (Dv x i)) := by
    funext x
    simp only [inner_sub_left, Finset.sum_sub_distrib, Pi.sub_apply]
  rw [heq]
  refine ⟨hFI.sub hGI, ?_⟩
  change (∫ x in Ω.val, (∑ i : Fin n, inner ℝ (F x i) (Dv x i)) -
    ∑ i : Fin n, inner ℝ (G x i) (Dv x i)) = 0
  rw [integral_sub hFI hGI, ← htest, sub_self]

/-- The map and explicit gradient response are unique almost everywhere inside the ball. -/
theorem dirichlet_gradient_response_unique_ae {n q : ℕ} (hn : 1 ≤ n)
    (a : Domain n) {R : ℝ} (hR : 0 < R)
    (F : Domain n → Gradient n q)
    (hF : ∀ i : Fin n, MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a R)))
    {f g : Domain n → Ambient q} {Df Dg : Domain n → Gradient n q}
    (hf : HasZeroBoundaryValues (ballDomain a R) f Df)
    (hg : HasZeroBoundaryValues (ballDomain a R) g Dg)
    (hEqf : ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball a R →
      (∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (Df x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      ∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (F x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1)))
    (hEqg : ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball a R →
      (∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (Dg x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      ∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (F x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) :
    f =ᵐ[volume.restrict (Metric.ball a R)] g ∧
      Df =ᵐ[volume.restrict (Metric.ball a R)] Dg := by
  have hw := zeroBoundary_sub hf hg
  have hTf := gradient_pairing_eq_on_zeroBoundary_of_smooth (ballDomain a R)
    Df F hf.1.2.2 hF hEqf hw
  have hTg := gradient_pairing_eq_on_zeroBoundary_of_smooth (ballDomain a R)
    Dg F hg.1.2.2 hF hEqg hw
  simp only [ballDomain] at hTf hTg
  have henergy : (∫ x in Metric.ball a R, hsNormSq (fun i => Df x i - Dg x i)) = 0 := by
    calc
      _ = (∫ x in Metric.ball a R, ∑ i : Fin n,
            inner ℝ (Df x i) (Df x i - Dg x i)) -
          ∫ x in Metric.ball a R, ∑ i : Fin n,
            inner ℝ (Dg x i) (Df x i - Dg x i) := by
        rw [← integral_sub hTf.1 hTg.1]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [hsNormSq, ← real_inner_self_eq_norm_sq, inner_sub_left,
            Finset.sum_sub_distrib]
      _ = 0 := by rw [hTf.2.2, hTg.2.2, sub_self]
  have hmapzero := zeroBoundary_ae_eq_zero_of_energy_eq_zero hn a hR hw henergy
  have hmap : f =ᵐ[volume.restrict (Metric.ball a R)] g := by
    filter_upwards [hmapzero] with x hx
    exact sub_eq_zero.mp hx
  exact ⟨hmap, hf.1.1.ae_eq_of_ae_eq_map hg.1.1 hmap⟩

end StationaryHarmonicMaps.Analysis

end

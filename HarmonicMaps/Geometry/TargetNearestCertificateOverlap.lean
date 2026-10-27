module

public import HarmonicMaps.Geometry.TargetUniformNearest
public import HarmonicMaps.Geometry.LocalCertificateDerivatives

/-!
# Agreement of genuine nearest-point certificates

The same uniform radius supports actual nearest-point certificates. Any other
smooth nearest-point certificate agrees on the open overlap, because every
global distance minimizer has the same value. Both actual first and second
derivatives consequently agree there.
-/

public section

open Set
open scoped ContDiff

namespace HarmonicMaps.CompactSmoothEmbeddedTarget

/-- Genuine nearest certificates agree on overlap with the same actual derivatives. -/
theorem exists_uniform_nearest_certificate_overlap {q : ℕ} (N : CompactSmoothEmbeddedTarget q) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ z : EuclideanSpace ℝ (Fin q), Metric.infDist z N.carrierSet < 2 * rho →
        ∃ epsilon : ℝ, 0 < epsilon ∧
          Metric.ball z epsilon ⊆ {w | Metric.infDist w N.carrierSet < 2 * rho} ∧
          ∃ g : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin q),
            ContDiffOn ℝ ∞ g (Metric.ball z epsilon) ∧
            (∀ w ∈ Metric.ball z epsilon,
              g w ∈ N.carrierSet ∧
              (∀ r : N.Carrier, dist w (g w) ≤ dist w r.val) ∧
              ∀ r : N.Carrier,
                (∀ s : N.Carrier, dist w r.val ≤ dist w s.val) → r.val = g w) ∧
            ∀ (W : Set (EuclideanSpace ℝ (Fin q)))
              (h : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin q)),
              IsOpen W → z ∈ W → ContDiffOn ℝ ∞ h W →
              (∀ w ∈ W, h w ∈ N.carrierSet ∧
                ∀ r : N.Carrier, dist w (h w) ≤ dist w r.val) →
              Set.EqOn g h (Metric.ball z epsilon ∩ W) ∧
              ContDiffAt ℝ ∞ g z ∧ ContDiffAt ℝ ∞ h z ∧
              fderiv ℝ g z = fderiv ℝ h z ∧
              fderiv ℝ (fderiv ℝ g) z = fderiv ℝ (fderiv ℝ h) z := by
  obtain ⟨rho, hrho, hUniform⟩ := N.exists_uniform_nearest_smooth_radius
  refine ⟨rho, hrho, ?_⟩
  intro z hz
  obtain ⟨epsilon, hepsilon, hBallTube, g, hg, hMinG⟩ := hUniform z hz
  refine ⟨epsilon, hepsilon, hBallTube, g, hg, hMinG, ?_⟩
  intro W h hWo hzW hh hMinH
  let U := Metric.ball z epsilon ∩ W
  have hUo : IsOpen U := Metric.isOpen_ball.inter hWo
  have hzBall : z ∈ Metric.ball z epsilon := Metric.mem_ball_self hepsilon
  have hzU : z ∈ U := ⟨hzBall, hzW⟩
  have hEq : Set.EqOn g h U := by
    intro w hw
    obtain ⟨hmem, hmin⟩ := hMinH w hw.2
    exact ((hMinG w hw.1).2.2 ⟨h w, hmem⟩ hmin).symm
  have hD := HarmonicMaps.localCertificate_derivatives_eq
    (fun w : U => g w.val) ⟨z, hzU⟩ U U g h hUo hUo hzU hzU
    Set.Subset.rfl Set.Subset.rfl (fun _ _ => rfl)
    (fun w _ => (hEq w.property).symm)
  exact ⟨hEq, hg.contDiffAt (Metric.isOpen_ball.mem_nhds hzBall),
    hh.contDiffAt (hWo.mem_nhds hzW), hD⟩

end HarmonicMaps.CompactSmoothEmbeddedTarget

end

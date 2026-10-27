/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.AlternatingCoexactPowerGrowth
public import StationaryHarmonicMaps.Analysis.SkewCoulombNearEnergy

/-!
# Full boundary power growth of the original logarithmic response

The original native orthogonality constraint supplies its differentiated
identity. It identifies the actual encoded logarithmic derivative with
the genuine alternating coefficient on the same weak gradient. Complete
alternating-response growth then applies to the original response and
its original native complement.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The same natural response of an original orthogonal logarithmic
derivative has complete boundary power growth from the original Dp growth. -/
theorem exists_coulomb_boundary_logarithmic_power_growth (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n:ℝ)) :
    ∃L : ℝ,0<L ∧ ∀(p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
      (η K : ℝ),MemW12 (ballDomain (0:Domain n) 1) p Dp →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (R (p x))*R (p x)=1) → 0≤η →
      criticalGradientMorreySquare Dp (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) → 0≤K →
      (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Dp x))≤K*r^ν) →
      ∀(Q : Domain n → Gradient n (q*q)) (v : Domain n → Ambient (q*q)),
        (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
        MemW12 (ballDomain (0:Domain n) 1) v
          (fun x i=>E (star (R (p x))*R (Dp x i))-Q x i) →
        (∀(ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) →
        ∀(a : Domain n) (r : ℝ),0<r →
          (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Q x))≤L*η^2*K*r^ν := by
  let Bs := skewLogarithmicAlternation E R
  obtain ⟨L,hL,H⟩ := exists_alternating_coexact_full_real_power_growth n hn (q*q) (q*q) Bs
    (skewLogarithmicAlternation_self E R) ν hν hνn
  refine ⟨L,hL,?_⟩
  intro p Dp η K hp hOrth hη hCritical hK hGrowth Q v hQ hv hNatural
  have hBound := ae_orthogonal_coordinates_bound (Ω:=ballDomain (0:Domain n) 1) E R hER hE p hOrth
  have hLog := ae_native_orthogonal_logarithmic_alternation E R p Dp hp.to_memW12Loc
    (Real.sqrt (q:ℝ)) hBound hOrth
  have hvAlt : MemW12 (ballDomain (0:Domain n) 1) v
      (fun x i=>Bs (p x) (Dp x i)-Q x i) := by
    apply hv.congr_ae (Eventually.of_forall fun _=>rfl)
    filter_upwards [hLog] with x hx
    funext i
    rw [hx i]
  exact H p Dp η (Real.sqrt (q:ℝ)) K hp hη hBound hCritical hK hGrowth Q v hQ hvAlt hNatural

end StationaryHarmonicMaps.Analysis

end

/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Geometry.SkewLogarithmicAlternation
public import StationaryHarmonicMaps.Analysis.AlternatingBoundaryNearEnergy
public import StationaryHarmonicMaps.Analysis.SobolevOrthogonalFrame
public import StationaryHarmonicMaps.Analysis.OrthogonalCoefficientBounds

/-!
# Actual skew logarithmic near responses of native orthogonal frames

Native differentiation of orthogonality identifies the original
logarithmic derivative with its genuine alternating bilinear coefficient.
The original critical bound and power growth then construct an actual
localized relative coexact response. The centering contribution remains
the displayed derivative of a genuine native linear graph.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Differentiating the original native orthogonality constraint produces
the alternating formula for every original weak derivative column. -/
theorem ae_native_orthogonal_logarithmic_alternation {n m k q : ℕ} {Ω : OpenDomain n}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient k)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (p : Domain n → Ambient m) (Dp : Domain n → Gradient n m)
    (hp : MemW12Loc Ω p Dp) (M : ℝ)
    (hBound : ∀ᵐx∂volume.restrict Ω.val,‖p x‖≤M)
    (hOrth : ∀ᵐx∂volume.restrict Ω.val,star (R (p x))*R (p x)=1) :
    ∀ᵐx∂volume.restrict Ω.val,∀i,
      E (star (R (p x))*R (Dp x i))=skewLogarithmicAlternation E R (p x) (Dp x i) := by
  have hDerivative := ae_orthogonal_frame_derivative hp R M hBound hOrth
  filter_upwards [hDerivative] with x hx i
  exact (skewLogarithmicAlternation_eq_logarithmic_of_constraint E R (p x) (Dp x i) (hx i)).symm

/-- For every fixed centering vector, its alternating contribution is
the actual gradient of the original native linear graph. -/
theorem native_constant_logarithmic_alternation_graph {n m k q : ℕ}
    (Ω : OpenDomain n)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient k)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (p : Domain n → Ambient m) (Dp : Domain n → Gradient n m)
    (hp : MemW12 Ω p Dp) (c : Ambient m) :
    MemW12 Ω (fun x=>skewLogarithmicAlternation E R c (p x))
      (fun x i=>skewLogarithmicAlternation E R c (Dp x i)) := by
  let L := skewLogarithmicAlternation E R c
  exact ⟨(memW12Loc_continuousLinearMap hp.to_memW12Loc L).1,
    L.lipschitz.comp_memLp (map_zero L) hp.2.1,
    fun i=>L.lipschitz.comp_memLp (map_zero L) (hp.2.2 i)⟩

/-- Original critical native orthogonal frame data and complete original
power growth produce an actual natural coexact response of the centered
localized logarithmic forcing, with its critical energy gain and explicit
native centering contribution. -/
theorem exists_skew_coulomb_logarithmic_near_coexact_energy
    (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (ν : ℝ) :
    ∃C : ℝ,0<C ∧ ∀(p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
      (η K : ℝ),MemW12 (ballDomain (0:Domain n) 1) p Dp →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (R (p x))*R (p x)=1) → 0≤η →
      criticalGradientMorreySquare Dp (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) → 0≤K →
      (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Dp x))≤K*r^ν) →
      ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r → r≤1/8 →
      ∃(χ : Domain n → ℝ) (c : Ambient (q*q)) (P : Domain n → Gradient n (q*q))
        (v : Domain n → Ambient (q*q)),
        ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ⊆ball a (2*r) ∧
        (∀x∈closedBall a r,χ x=1) ∧ (∀x,0≤χ x ∧ χ x≤1) ∧
        (∀i,MemLp (fun x=>P x i) 2 (volume.restrict (ball (0:Domain n) 1))) ∧
        MemW12 (ballDomain (0:Domain n) 1) v
          (fun x i=>χ x • (E (star (R (p x))*R (Dp x i))-
            skewLogarithmicAlternation E R c (Dp x i))-P x i) ∧
        (∀(ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (P x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (P x i) (Dψ x i))=0) ∧
        (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,
          E (star (R (p x))*R (Dp x i))=skewLogarithmicAlternation E R (p x) (Dp x i)) ∧
        MemW12 (ballDomain (0:Domain n) 1)
          (fun x=>skewLogarithmicAlternation E R c (p x))
          (fun x i=>skewLogarithmicAlternation E R c (Dp x i)) ∧
        (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,
          χ x • E (star (R (p x))*R (Dp x i))=
            χ x • skewLogarithmicAlternation E R (p x-c) (Dp x i)+
              χ x • skewLogarithmicAlternation E R c (Dp x i)) ∧
        (∀x i,star (R (χ x • skewLogarithmicAlternation E R (p x-c) (Dp x i)))=
          -R (χ x • skewLogarithmicAlternation E R (p x-c) (Dp x i))) ∧
        (∫x in ball (0:Domain n) 1,hsNormSq (P x))≤C*η^2*K*r^ν := by
  let B := skewLogarithmicAlternation E R
  obtain ⟨C,hC,Hnear⟩ := exists_alternating_boundary_near_coexact_energy n hn (q*q) (q*q) B
    (skewLogarithmicAlternation_self E R) ν
  refine ⟨C,hC,?_⟩
  intro p Dp η K hp hOrth hη hCritical hK hGrowth a ha r hr hrCap
  have hBound := ae_orthogonal_coordinates_bound (Ω:=ballDomain (0:Domain n) 1) E R hER hE p hOrth
  have hLog := ae_native_orthogonal_logarithmic_alternation E R p Dp hp.to_memW12Loc
    (Real.sqrt (q:ℝ)) hBound hOrth
  obtain ⟨χ,c,P,v,hχ,hcχ,hsχ,hOne,hBounds,hP,hv,hNatural,hEnergy⟩ :=
    Hnear p Dp η (Real.sqrt (q:ℝ)) K hp hη hBound hCritical hK hGrowth a ha r hr hrCap
  have hForce : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,
      χ x • (E (star (R (p x))*R (Dp x i))-B c (Dp x i))=
        χ x • B (p x-c) (Dp x i) := by
    filter_upwards [hLog] with x hx i
    rw [hx i,map_sub,sub_apply]
  have hvLog : MemW12 (ballDomain (0:Domain n) 1) v
      (fun x i=>χ x • (E (star (R (p x))*R (Dp x i))-B c (Dp x i))-P x i) := by
    apply hv.congr_ae (Eventually.of_forall fun _=>rfl)
    filter_upwards [hForce] with x hx
    funext i
    rw [hx i]
  have hSplit : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,
      χ x • E (star (R (p x))*R (Dp x i))=
        χ x • B (p x-c) (Dp x i)+χ x • B c (Dp x i) := by
    filter_upwards [hLog] with x hx i
    rw [hx i,map_sub,sub_apply,smul_sub,sub_add_cancel]
  have hSkew (x : Domain n) (i : Fin n) :
      star (R (χ x • B (p x-c) (Dp x i)))= -R (χ x • B (p x-c) (Dp x i)) := by
    rw [map_smul,star_smul,star_trivial,skewLogarithmicAlternation_range_skew E R hRE,smul_neg]
  exact ⟨χ,c,P,v,hχ,hcχ,hsχ,hOne,hBounds,hP,hvLog,hNatural,hLog,
    native_constant_logarithmic_alternation_graph _ E R p Dp hp c,hSplit,hSkew,hEnergy⟩

end StationaryHarmonicMaps.Analysis

end

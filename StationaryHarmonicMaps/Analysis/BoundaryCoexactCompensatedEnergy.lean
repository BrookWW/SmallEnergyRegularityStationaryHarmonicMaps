module

public import StationaryHarmonicMaps.Analysis.BoundaryCenteredCoexactEnergy

/-!
# Actual full-ball coexact energy of a critical bilinear gradient

The relative response of the original bilinear gradient is constructed
from its raw L2 columns. Its native gradient complement and natural tests
identify its energy with the original bilinear pairing. Boundary div-curl
compensation then gives the homogeneous quadratic smallness factor.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original bounded critical graph produces an actual closed normal
relative response of its bilinear gradient and its compensated full-ball
energy bound; no response or variational identity is assumed. -/
theorem exists_boundary_coexact_compensated_energy (n : ℕ) (hn : 2≤n)
    (m k : ℕ) (B : Ambient m →L[ℝ] (Ambient m →L[ℝ] Ambient k)) :
    ∃C : ℝ,0<C ∧ ∀ (u : Domain n → Ambient m) (Du : Domain n → Gradient n m)
      (η M : ℝ),MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M) →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∃ (b : Fin n → Fin n → Domain n → Ambient k)
        (Db : Fin n → Fin n → Domain n → Gradient n k)
        (Q : Domain n → Gradient n k) (v : Domain n → Ambient k)
        (Dv : Domain n → Gradient n k),
        MemW12 (ballDomain (0 : Domain n) 1) v Dv ∧
        (∀i j,MemW12 (ballDomain (0 : Domain n) 1) (b i j) (Db i j)) ∧
        (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i j,b i j x= -b j i x) ∧
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i j l,
          Db i j x l+Db j l x i+Db l i x j=0) ∧
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀j,(∑i : Fin n,Db i j x i)=Q x j) ∧
        (∀(j : Fin n) (ψ : Domain n → Ambient k) (Dψ : Domain n → Gradient n k),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (b i j x) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
          IntegrableOn (fun x=>inner ℝ (Q x j) (ψ x)) (ball (0 : Domain n) 1) volume ∧
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (b i j x) (Dψ x i))=
            -(∫x in ball (0 : Domain n) 1,inner ℝ (Q x j) (ψ x))) ∧
        (∀(ψ : Domain n → Ambient k) (Dψ : Domain n → Gradient n k),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) ∧
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i,
          B (u x) (Du x i)=Dv x i+Q x i) ∧
        (∫x in ball (0 : Domain n) 1,hsNormSq (Q x))≤
          C*η^2*(∫x in ball (0 : Domain n) 1,hsNormSq (Du x)) := by
  obtain ⟨C,hC,HC⟩ := exists_boundary_centered_coexact_compensated_energy n hn m k B
  refine ⟨C,hC,?_⟩
  intro u Du η M hu hη hBound hCritical
  simpa only [sub_zero] using HC u Du η M hu hη hBound hCritical u Du hu (0 : Ambient m)

end StationaryHarmonicMaps.Analysis

end

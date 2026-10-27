module

public import StationaryHarmonicMaps.Analysis.RelativeCoexactKernel
public import StationaryHarmonicMaps.Analysis.NaturalCoexactResidual

/-!
# Exact native relative coexact potentials on the unit ball

The original natural-solenoidal L2 field is the divergence of a genuine
closed normal H1 two-tensor. The residual of the actual Hilbert projection
vanishes by the relative kernel theorem. The original field appears in the
full native boundary identity and the quantitative H1 estimate.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Every actual natural-solenoidal L2 field has an exact native closed normal potential, with no residual, given potential or elliptic estimate as an input. -/
theorem exists_native_relative_coexact_potential_unitBall {n q : ℕ} (hn : 1≤n)
    (F : Domain n → Gradient n q)
    (hF : ∀j,MemLp (fun x=>F x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hNatural : ∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
      (∫x in ball (0 : Domain n) 1,∑j : Fin n,inner ℝ (F x j) (Dψ x j))=0) :
    ∃ (b : Fin n → Fin n → Domain n → Ambient q)
      (Db : Fin n → Fin n → Domain n → Gradient n q),
      (∀i j,MemW12 (ballDomain (0 : Domain n) 1) (b i j) (Db i j)) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀i j,b i j x= -b j i x) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀i j k,Db i j x k+Db j k x i+Db k i x j=0) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀j,(∑i : Fin n,Db i j x i)=F x j) ∧
      (∀ (j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (b i j x) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
        IntegrableOn (fun x=>inner ℝ (F x j) (ψ x)) (ball (0 : Domain n) 1) volume ∧
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (b i j x) (Dψ x i))=
          -(∫x in ball (0 : Domain n) 1,inner ℝ (F x j) (ψ x))) ∧
      ((∫x in ball (0 : Domain n) 1,∑j : Fin n,∑i : Fin n,‖b i j x‖^2)+
        (∫x in ball (0 : Domain n) 1,∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Db i j x k‖^2)≤
          (4*(2 : ℝ)^(n+1)+2*(n : ℝ)+2)*(∫x in ball (0 : Domain n) 1,hsNormSq (F x))) := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  obtain ⟨b,Db,P,h,hb,hP,hSkew,hClosed,hDiv,hNormal,_hPNatural,hDecomp,hHLp,hHNatural,
    _hHDiv,_hHarm,_hEnergy,hBEnergy,hCore⟩ :=
    exists_natural_closed_normal_harmonic_residual_unitBall F hF hNatural
  obtain ⟨_hEnergyZero,hZero⟩ := natural_coexact_kernel_eq_zero_unitBall hn h hHLp
    (fun ψ Dψ hψ=>(hHNatural ψ Dψ hψ).2)
    (fun C hC hCS hCD hCN=>(hCore C hC hCS hCD hCN).2)
  have hPF : P=ᵐ[μ]F := by
    filter_upwards [hZero] with x hx
    funext j
    have H := hDecomp x j
    rw [hx] at H
    simpa only [zero_add,add_zero] using H.symm
  refine ⟨b,Db,hb,hSkew,hClosed,?_,?_,hBEnergy⟩
  · filter_upwards [hDiv,hPF] with x hx hpx j
    exact (hx j).trans (congrFun hpx j)
  · intro j ψ Dψ hψ
    obtain ⟨hI,hJ,hEq⟩ := hNormal j ψ Dψ hψ
    have hPair : (fun x=>inner ℝ (P x j) (ψ x))=ᵐ[μ](fun x=>inner ℝ (F x j) (ψ x)) :=
      hPF.mono fun x hx=>by
        change inner ℝ (P x j) (ψ x)=inner ℝ (F x j) (ψ x)
        rw [hx]
    exact ⟨hI,hJ.congr hPair,hEq.trans (congrArg Neg.neg (integral_congr_ae hPair))⟩

end StationaryHarmonicMaps.Analysis

end

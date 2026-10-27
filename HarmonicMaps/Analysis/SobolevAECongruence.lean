module

public import HarmonicMaps.SobolevLemmas

/-!
# Almost-everywhere congruence of Sobolev data

The weak identities, local and finite L2 conditions, and compact smooth
graph-norm closure depend only on the map and gradient inside the domain.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace HarmonicMaps

/-- Changing a map and its columns almost everywhere preserves its weak gradient. -/
theorem HasWeakGradient.congr_ae {n q : ℕ} {Ω : OpenDomain n}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : HasWeakGradient Ω u Du)
    (huv : u =ᵐ[volume.restrict Ω.val] v)
    (hDuDv : Du =ᵐ[volume.restrict Ω.val] Dv) :
    HasWeakGradient Ω v Dv := by
  have hcol (i : Fin n) :
      (fun x => Du x i) =ᵐ[volume.restrict Ω.val] (fun x => Dv x i) :=
    hDuDv.mono fun x hx => congrFun hx i
  refine ⟨hu.1.congr huv, fun i => (hu.2.1 i).congr (hcol i), ?_⟩
  intro i φ hφ hcφ hsφ
  have hleft : (∫ x in Ω.val, coordinateDerivative φ hφ i x • v x) =
      ∫ x in Ω.val, coordinateDerivative φ hφ i x • u x := by
    apply integral_congr_ae
    exact huv.symm.mono fun x hx => congrArg (fun z => coordinateDerivative φ hφ i x • z) hx
  have hright : (∫ x in Ω.val, φ x • Dv x i) =
      ∫ x in Ω.val, φ x • Du x i := by
    apply integral_congr_ae
    exact (hcol i).symm.mono fun x hx => congrArg (fun z => φ x • z) hx
  rw [hleft, hright]
  exact hu.2.2 i φ hφ hcφ hsφ

/-- Weak gradients of almost-everywhere equal maps agree almost everywhere. -/
theorem HasWeakGradient.ae_eq_of_ae_eq_map {n q : ℕ} {Ω : OpenDomain n}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : HasWeakGradient Ω u Du) (hv : HasWeakGradient Ω v Dv)
    (huv : u =ᵐ[volume.restrict Ω.val] v) :
    Du =ᵐ[volume.restrict Ω.val] Dv :=
  (hu.congr_ae huv (Filter.EventuallyEq.refl _ _)).ae_eq hv

/-- Almost-everywhere changes preserve local L2 membership on an open domain. -/
theorem LocallyMemL2.congr_ae {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {Ω : OpenDomain n} {u v : Domain n → E} (hu : LocallyMemL2 Ω u)
    (huv : u =ᵐ[volume.restrict Ω.val] v) : LocallyMemL2 Ω v := by
  intro K hK hsK
  exact (hu K hK hsK).ae_eq (ae_restrict_of_ae_restrict_of_subset hsK huv)

/-- Local Sobolev membership depends only on the almost-everywhere graph. -/
theorem MemW12Loc.congr_ae {n q : ℕ} {Ω : OpenDomain n}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (huv : u =ᵐ[volume.restrict Ω.val] v)
    (hDuDv : Du =ᵐ[volume.restrict Ω.val] Dv) :
    MemW12Loc Ω v Dv := by
  refine ⟨hu.1.congr_ae huv hDuDv, hu.2.1.congr_ae huv, ?_⟩
  intro i
  exact (hu.2.2 i).congr_ae (hDuDv.mono fun x hx => congrFun hx i)

/-- Finite Sobolev membership depends only on the almost-everywhere graph. -/
theorem MemW12.congr_ae {n q : ℕ} {Ω : OpenDomain n}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du)
    (huv : u =ᵐ[volume.restrict Ω.val] v)
    (hDuDv : Du =ᵐ[volume.restrict Ω.val] Dv) : MemW12 Ω v Dv := by
  refine ⟨hu.1.congr_ae huv hDuDv, hu.2.1.ae_eq huv, ?_⟩
  intro i
  exact (hu.2.2 i).ae_eq (hDuDv.mono fun x hx => congrFun hx i)

/-- A compact smooth graph-norm approximation transfers across almost-everywhere
equality of the map and its gradient on the domain. -/
theorem HasZeroBoundaryValues.congr_ae {n q : ℕ} {Ω : OpenDomain n}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : HasZeroBoundaryValues Ω u Du)
    (huv : u =ᵐ[volume.restrict Ω.val] v)
    (hDuDv : Du =ᵐ[volume.restrict Ω.val] Dv) :
    HasZeroBoundaryValues Ω v Dv := by
  obtain ⟨hw, m, hm, hmc, hlim, hDlim⟩ := hu
  refine ⟨hw.congr_ae huv hDuDv, m, hm, hmc, ?_, ?_⟩
  · have heq (k : ℕ) : eLpNorm (m k - v) 2 (volume.restrict Ω.val) =
        eLpNorm (m k - u) 2 (volume.restrict Ω.val) := by
      apply eLpNorm_congr_ae
      exact huv.symm.mono fun x hx => congrArg (fun z => m k x - z) hx
    simp_rw [heq]
    exact hlim
  · intro i
    have heq (k : ℕ) : eLpNorm
        (fun x => coordinateDerivative (m k) (hm k) i x - Dv x i)
        2 (volume.restrict Ω.val) = eLpNorm
        (fun x => coordinateDerivative (m k) (hm k) i x - Du x i)
        2 (volume.restrict Ω.val) := by
      apply eLpNorm_congr_ae
      exact hDuDv.symm.mono fun x hx =>
        congrArg (fun z => coordinateDerivative (m k) (hm k) i x - z i) hx
    simp_rw [heq]
    exact hDlim i

end HarmonicMaps

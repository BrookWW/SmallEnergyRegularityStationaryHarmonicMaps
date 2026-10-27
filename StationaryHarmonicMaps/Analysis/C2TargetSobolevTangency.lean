module

public import StationaryHarmonicMaps.Geometry.C2LocalDefiningMap
public import StationaryHarmonicMaps.Analysis.C1SobolevPostcompositionLocal
import HarmonicMaps.Analysis.SobolevAECongruence
import HarmonicMaps.SobolevRestriction
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Tangency of the actual weak gradient of a target-valued map

Compact C¹ defining maps vanish on the actual C² target. The C¹ Sobolev chain
rule and uniqueness of weak gradients annihilate their differentials on each
displayed gradient column. A finite target cover then puts the same columns
in the actual tangent subspace almost everywhere.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace StationaryHarmonicMaps

/-- A compact C¹ map vanishing on the target annihilates each actual weak gradient column. -/
theorem ae_fderiv_apply_eq_zero_of_target_zero {n q k : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    (F : Ambient q → Ambient k) (hF : ContDiff ℝ 1 F) (hcF : HasCompactSupport F)
    (hFN : ∀ p : N.Carrier, F p.val = 0) :
    ∀ᵐ x ∂volume.restrict Ω.val, ∀ i : Fin n, fderiv ℝ F (u x) (Du x i) = 0 := by
  obtain ⟨L, hL⟩ := (hcF.fderiv ℝ).exists_bound_of_continuous
    (hF.continuous_fderiv (by norm_num))
  have hw := Analysis.memW12Loc_postcompose_c1 hu F hF L hL
  have hmap : F ∘ u =ᵐ[volume.restrict Ω.val] (0 : Domain n → Ambient k) :=
    hN.mono fun x hx => hFN ⟨u x, hx⟩
  have hD := hw.1.ae_eq_of_ae_eq_map (HasWeakGradient.zero Ω) hmap
  filter_upwards [hD] with x hx
  intro i
  simpa only [Pi.zero_apply] using congrFun hx i

/-- The given weak gradient of an almost-everywhere C² target-valued map is tangent a.e. -/
theorem memW12Loc_ae_tangent {n q : ℕ} (N : CompactC2EmbeddedTarget q)
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet) :
    ∀ᵐ x ∂volume.restrict Ω.val, ∀ hx : u x ∈ N.carrierSet,
      ∀ i : Fin n, Du x i ∈ N.tangentImage ⟨u x, hx⟩ := by
  classical
  have hlocal (p : N.Carrier) := N.exists_compact_local_defining_map p
  choose O F hOo hpO hFC1 hcF hFN hker using hlocal
  obtain ⟨t, ht⟩ := N.isCompact.elim_finite_subcover O hOo
    (fun y hy => mem_iUnion_of_mem ⟨y, hy⟩ (hpO ⟨y, hy⟩))
  have hzero (j : t) : ∀ᵐ x ∂volume.restrict Ω.val, ∀ i : Fin n,
      fderiv ℝ (F j.val) (u x) (Du x i) = 0 :=
    ae_fderiv_apply_eq_zero_of_target_zero N hu hN (F j.val)
      (hFC1 j.val) (hcF j.val) (hFN j.val)
  filter_upwards [hN, ae_all_iff.2 hzero] with x hxN hxzero
  intro hx i
  obtain ⟨p, hpt, huxO⟩ := mem_iUnion₂.mp (ht hxN)
  exact hker p ⟨u x, hx⟩ huxO (Du x i) (hxzero ⟨p, hpt⟩ i)

end StationaryHarmonicMaps

end

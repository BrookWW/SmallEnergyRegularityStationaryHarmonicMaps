module

public import HarmonicMaps.Analysis.ContinuousRepresentativeLocality
public import Mathlib.Topology.Compactness.Lindelof

/-! # Gluing continuous almost-everywhere representatives

Representatives agree on every open overlap by positivity of Euclidean
volume. A countable subcover makes their glued map agree almost everywhere
with the same original function.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace HolderToCK

theorem continuous_representatives_agree_on_overlap {n q : ℕ}
    {u v w : Domain n → Ambient q} {U V : Set (Domain n)}
    (hU : IsOpen U) (hV : IsOpen V)
    (hv : ContinuousOn v U) (hw : ContinuousOn w V)
    (hvu : v =ᵐ[volume.restrict U] u) (hwu : w =ᵐ[volume.restrict V] u) :
    EqOn v w (U ∩ V) := by
  have hvu' : v =ᵐ[volume.restrict (U ∩ V)] u :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hvu
  have hwu' : w =ᵐ[volume.restrict (U ∩ V)] u :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hwu
  exact Measure.eqOn_open_of_ae_eq (hvu'.trans hwu'.symm) (hU.inter hV)
    (hv.mono inter_subset_left) (hw.mono inter_subset_right)

theorem continuous_representatives_glue {n q : ℕ} {ι : Type*}
    (u : Domain n → Ambient q) (s : Set (Domain n)) (hs : IsOpen s)
    (U : ι → Set (Domain n)) (v : ι → Domain n → Ambient q)
    (hU : ∀ i, IsOpen (U i)) (hv : ∀ i, ContinuousOn (v i) (U i))
    (hvu : ∀ i, v i =ᵐ[volume.restrict (U i)] u)
    (hcover : s ⊆ ⋃ i, U i) :
    ∃ w : Domain n → Ambient q,
      ContinuousOn w s ∧ w =ᵐ[volume.restrict s] u ∧
        ∀ i, EqOn w (v i) (s ∩ U i) := by
  classical
  have hindex : ∀ x ∈ s, ∃ i, x ∈ U i := fun x hx => mem_iUnion.mp (hcover hx)
  choose I hI using hindex
  let w : Domain n → Ambient q := fun x => if hx : x ∈ s then v (I x hx) x else u x
  have hsame (i : ι) : EqOn w (v i) (s ∩ U i) := by
    intro x hx
    dsimp only [w]
    rw [dif_pos hx.1]
    exact continuous_representatives_agree_on_overlap
      (hU (I x hx.1)) (hU i) (hv (I x hx.1)) (hv i)
      (hvu (I x hx.1)) (hvu i) ⟨hI x hx.1, hx.2⟩
  have hwcont : ContinuousOn w s := by
    intro x hx
    let i := I x hx
    have hxi : x ∈ U i := hI x hx
    have heq : w =ᶠ[𝓝[s] x] v i := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ((hU i).mem_nhds hxi)]
        with y hy hyU
      exact hsame i ⟨hy, hyU⟩
    exact ((hv i).continuousAt ((hU i).mem_nhds hxi)).continuousWithinAt.congr_of_eventuallyEq
      heq (hsame i ⟨hx, hxi⟩)
  obtain ⟨t, ht, hsub⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover U hU hcover
  have hsub' : s ⊆ ⋃ i ∈ t, s ∩ U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hsub hx)
    exact mem_iUnion₂.mpr ⟨i, hi, hx, hxi⟩
  have hAE : w =ᵐ[volume.restrict (⋃ i ∈ t, s ∩ U i)] u := by
    apply (ae_eq_restrict_biUnion_iff (fun i => s ∩ U i) ht w u).mpr
    intro i _
    have heq : w =ᵐ[volume.restrict (s ∩ U i)] v i := by
      filter_upwards [ae_restrict_mem (hs.inter (hU i)).measurableSet] with x hx
      exact hsame i hx
    exact heq.trans (ae_restrict_of_ae_restrict_of_subset inter_subset_right (hvu i))
  exact ⟨w, hwcont, ae_restrict_of_ae_restrict_of_subset hsub' hAE, hsame⟩

end HolderToCK
end

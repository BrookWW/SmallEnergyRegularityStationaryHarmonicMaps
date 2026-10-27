module

public import HarmonicMaps.Geometry.TargetNormalCoordinates
public import HarmonicMaps.Geometry.NearestPointLocality

/-!
# Actual local nearest-point uniqueness and smoothness

One local normal-coordinate inverse identifies every genuine competing nearest
point near each target point. Compactness supplies an actual minimizer, while
the common normal-coordinate lift proves uniqueness and produces a smooth
ambient certificate on a positive ball.
-/

public section

open Filter Topology Set
open scoped Manifold ContDiff

namespace HarmonicMaps.CompactSmoothEmbeddedTarget

set_option backward.isDefEq.respectTransparency false in
/-- All actual nearest points near a target point agree with one smooth local certificate. -/
theorem exists_local_nearest_smooth_certificate {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (p : N.Carrier) :
    ∃ delta : ℝ, 0 < delta ∧
      ∃ g : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin q),
        ContDiffOn ℝ ∞ g (Metric.ball p.val delta) ∧
        ∀ z ∈ Metric.ball p.val delta,
          g z ∈ N.carrierSet ∧
          (∀ r : N.Carrier, dist z (g z) ≤ dist z r.val) ∧
          ∀ r : N.Carrier,
            (∀ s : N.Carrier, dist z r.val ≤ dist z s.val) → r.val = g z := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin q))
  let e := extChartAt I p
  let a := e p
  let gamma : EuclideanSpace ℝ (Fin N.dimension) → EuclideanSpace ℝ (Fin q) :=
    Subtype.val ∘ e.symm
  let A := fun t => fderiv ℝ gamma t
  let A0 : EuclideanSpace ℝ (Fin N.dimension) →L[ℝ] EuclideanSpace ℝ (Fin q) :=
    mfderiv I J (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) p
  let K := A0.rangeᗮ
  obtain ⟨V, hVo, haV, hVe, hgamma, L, hLd, _, hNormal,
    e0, _, _, Phi, hPhiBase, hSource, _, hpPhi, hPhiF, _, _, hPhiInv⟩ :=
    N.exists_smooth_normal_coordinates p
  let S : EuclideanSpace ℝ (Fin N.dimension) →
      ((EuclideanSpace ℝ (Fin N.dimension) × K) →L[ℝ] EuclideanSpace ℝ (Fin q)) :=
    fun t => (A t).coprod (L t)
  have hSinv : ∀ t ∈ V, (S t).IsInvertible := fun t ht => (hNormal t ht).2.2.2
  have hAd : ContDiffOn ℝ ∞ A V := hgamma.fderiv_of_isOpen hVo (by simp)
  have hSc : ContinuousAt S a :=
    (hAd.continuousOn.continuousLinearMapCoprod hLd.continuousOn).continuousAt
      (hVo.mem_nhds haV)
  have hSi : ContinuousAt (fun t => (S t).inverse) a :=
    ((hSinv a haV).contDiffAt_map_inverse (n := ∞)).continuousAt.comp hSc
  let lift : N.Carrier × EuclideanSpace ℝ (Fin q) →
      (EuclideanSpace ℝ (Fin N.dimension) × K) :=
    fun x => (e x.1, ((S (e x.1)).inverse (x.2 - x.1.val)).2)
  have hEc : ContinuousAt
      (fun x : N.Carrier × EuclideanSpace ℝ (Fin q) => e x.1) (p, p.val) :=
    (continuousAt_extChartAt (I := I) p).comp continuousAt_fst
  have hDiffc : ContinuousAt
      (fun x : N.Carrier × EuclideanSpace ℝ (Fin q) => x.2 - x.1.val) (p, p.val) :=
    continuousAt_snd.sub (continuous_subtype_val.continuousAt.comp continuousAt_fst)
  have hSiEc : ContinuousAt
      (fun x : N.Carrier × EuclideanSpace ℝ (Fin q) => (S (e x.1)).inverse) (p, p.val) :=
    hSi.comp_of_eq hEc rfl
  have hLiftc : ContinuousAt lift (p, p.val) :=
    hEc.prodMk ((hSiEc.clm_apply hDiffc).snd)
  have hLiftBase : lift (p, p.val) = (a, 0) := by
    dsimp only [lift]
    rw [sub_self, map_zero]
    rfl
  have hLiftNhd : lift ⁻¹' Phi.source ∈ 𝓝 (p, p.val) :=
    hLiftc.preimage_mem_nhds (Phi.open_source.mem_nhds (hLiftBase ▸ hPhiBase))
  obtain ⟨R, hRp, Z, hZp, hRZ⟩ := mem_nhds_prod_iff.mp hLiftNhd
  have hRneeded : R ∩ (e.source ∩ e ⁻¹' V) ∈ 𝓝 p :=
    inter_mem hRp (inter_mem (extChartAt_source_mem_nhds p)
      ((continuousAt_extChartAt (I := I) p).preimage_mem_nhds (hVo.mem_nhds haV)))
  obtain ⟨R0, hR0sub, hR0o, hpR0⟩ := mem_nhds_iff.mp hRneeded
  obtain ⟨U, hUo, hUeq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hR0o
  have hpU : p.val ∈ U := by
    change p ∈ (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) ⁻¹' U
    rw [hUeq]
    exact hpR0
  obtain ⟨d1, hd1, hLocal⟩ := N.nearest_points_localize p U hUo hpU
  have hZneeded : Z ∩ Phi.target ∈ 𝓝 p.val :=
    inter_mem hZp (Phi.open_target.mem_nhds hpPhi)
  obtain ⟨d2, hd2, hBallZ⟩ := Metric.mem_nhds_iff.mp hZneeded
  let delta := min d1 d2
  have hdelta : 0 < delta := lt_min hd1 hd2
  have hZ : ∀ z ∈ Metric.ball p.val delta, z ∈ Z ∩ Phi.target := by
    intro z hz
    apply hBallZ
    exact lt_of_lt_of_le hz (min_le_right d1 d2)
  have hRmin : ∀ z ∈ Metric.ball p.val delta, ∀ r : N.Carrier,
      (∀ s : N.Carrier, dist z r.val ≤ dist z s.val) → r ∈ R0 := by
    intro z hz r hr
    have hrU := (hLocal z (lt_of_lt_of_le hz (min_le_left d1 d2))).2 r hr
    change r ∈ (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) ⁻¹' U at hrU
    rwa [hUeq] at hrU
  let phi := chartAt (EuclideanSpace ℝ (Fin N.dimension)) p
  have hGamma : gamma = Subtype.val ∘ phi.symm := by
    simp only [gamma, e, I, phi, mfld_simps]
  have hChart : phi.MDifferentiable I I := mdifferentiable_chart p
  have hMinEq : ∀ z ∈ Metric.ball p.val delta, ∀ r : N.Carrier,
      (∀ s : N.Carrier, dist z r.val ≤ dist z s.val) →
      gamma (Phi.symm z).1 = r.val := by
    intro z hz r hr
    have hr0 := hRmin z hz r hr
    have hRparts := hR0sub hr0
    have hrs : r ∈ e.source := hRparts.2.1
    have htr : e r ∈ V := hRparts.2.2
    have hLift : lift (r, z) ∈ Phi.source := hRZ ⟨hRparts.1, (hZ z hz).1⟩
    have hGammaR : gamma (e r) = r.val := by
      exact congrArg Subtype.val (e.left_inv hrs)
    have hTarget : e r ∈ phi.target := by
      simpa only [e, I, phi, mfld_simps] using e.map_source hrs
    have hInvChart : phi.symm (e r) = r := by
      simpa only [e, I, phi, mfld_simps] using e.left_inv hrs
    have hi : MDifferentiableAt I J
        (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) (phi.symm (e r)) :=
      N.isSmoothEmbedding.contMDiff.mdifferentiableAt (by simp)
    have hAt : A (e r) =
        (mfderiv I J (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q))
          (phi.symm (e r))).comp (mfderiv I I phi.symm (e r)) := by
      change fderiv ℝ gamma (e r) = _
      rw [hGamma, ← mfderiv_eq_fderiv,
        mfderiv_comp (e r) hi (hChart.mdifferentiableAt_symm hTarget)]
    have hDisplacement : z - r.val ∈ (A (e r)).rangeᗮ := by
      apply ((A (e r)).range.mem_orthogonal' _).mpr
      intro y hy
      obtain ⟨v, rfl⟩ := hy
      rw [ContinuousLinearMap.coe_coe]
      have hAtv : A (e r) v =
          (mfderiv I J (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q))
            (phi.symm (e r))) ((mfderiv I I phi.symm (e r)) v) :=
        congrArg (fun T => T v) hAt
      rw [hAtv]
      have hrPhi : ∀ s : N.Carrier,
          dist z (phi.symm (e r)).val ≤ dist z s.val := by
        rw [hInvChart]
        exact hr
      have hVal : (phi.symm (e r)).val = r.val := congrArg Subtype.val hInvChart
      simpa only [hVal] using N.nearest_point_normal z (phi.symm (e r)) hrPhi
        ((mfderiv I I phi.symm (e r)) v)
    let uv := (S (e r)).inverse (z - r.val)
    have hSum : A (e r) uv.1 + L (e r) uv.2 = z - r.val :=
      (hSinv (e r) htr).self_apply_inverse _
    have hLNormal : L (e r) uv.2 ∈ (A (e r)).rangeᗮ := by
      rw [← (hNormal (e r) htr).2.2.1]
      exact ⟨uv.2, rfl⟩
    have hANormal : A (e r) uv.1 ∈ (A (e r)).rangeᗮ := by
      rw [eq_sub_of_add_eq hSum]
      exact Submodule.sub_mem _ hDisplacement hLNormal
    have hAzero : A (e r) uv.1 = 0 :=
      (Submodule.disjoint_def.mp (A (e r)).range.orthogonal_disjoint)
        (A (e r) uv.1) ⟨uv.1, rfl⟩ hANormal
    have hLvalue : L (e r) uv.2 = z - r.val := by
      simpa only [hAzero, zero_add] using hSum
    have hPhiLift : Phi (lift (r, z)) = z := by
      rw [hPhiF hLift]
      change gamma (e r) + L (e r) uv.2 = z
      rw [hGammaR, hLvalue, add_sub_cancel]
    have hInvLift : Phi.symm z = lift (r, z) := by
      calc
        Phi.symm z = Phi.symm (Phi (lift (r, z))) := congrArg Phi.symm hPhiLift.symm
        _ = lift (r, z) := Phi.left_inv hLift
    rw [hInvLift]
    exact hGammaR
  let g : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin q) :=
    fun z => gamma (Phi.symm z).1
  have hBallTarget : Metric.ball p.val delta ⊆ Phi.target := fun z hz => (hZ z hz).2
  have hg : ContDiffOn ℝ ∞ g (Metric.ball p.val delta) :=
    hgamma.comp (contDiff_fst.comp_contDiffOn (hPhiInv.mono hBallTarget))
      (fun z hz => (hSource (Phi.map_target (hBallTarget hz))).1)
  refine ⟨delta, hdelta, g, hg, ?_⟩
  intro z hz
  obtain ⟨r, _, hr⟩ := N.exists_nearest_point z
  have hgr : g z = r.val := hMinEq z hz r hr
  refine ⟨hgr ▸ r.property, ?_, ?_⟩
  · intro s
    rw [hgr]
    exact hr s
  · intro s hs
    exact (hMinEq z hz s hs).symm

end HarmonicMaps.CompactSmoothEmbeddedTarget

end

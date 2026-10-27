module

public import HarmonicMaps.Geometry.TargetSmoothNormal
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Genuine local normal addition coordinates

The actual chart parametrization and smooth normal family give a nonlinear
normal addition map. Its differential at the zero normal vector is the true
tangent and normal sum equivalence. The inverse function theorem gives smooth
local coordinates with an actually invertible differential on their source.
-/

public section

open Filter Topology
open scoped Manifold ContDiff

namespace HarmonicMaps.CompactSmoothEmbeddedTarget

set_option backward.isDefEq.respectTransparency false in
/-- Actual target geometry produces smooth local normal coordinates with a genuine smooth inverse. -/
theorem exists_smooth_normal_coordinates {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (p : N.Carrier) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) p
    let a := e p
    let gamma : EuclideanSpace ℝ (Fin N.dimension) → EuclideanSpace ℝ (Fin q) :=
      Subtype.val ∘ e.symm
    let A := fun t => fderiv ℝ gamma t
    let A0 : EuclideanSpace ℝ (Fin N.dimension) →L[ℝ] EuclideanSpace ℝ (Fin q) :=
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
        𝓘(ℝ, EuclideanSpace ℝ (Fin q))
        (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) p
    let K := A0.rangeᗮ
    ∃ V : Set (EuclideanSpace ℝ (Fin N.dimension)),
      IsOpen V ∧ a ∈ V ∧ V ⊆ e.target ∧ ContDiffOn ℝ ∞ gamma V ∧
      ∃ L : EuclideanSpace ℝ (Fin N.dimension) → (K →L[ℝ] EuclideanSpace ℝ (Fin q)),
        ContDiffOn ℝ ∞ L V ∧ L a = K.subtypeL ∧
        (∀ t ∈ V, Function.Injective (A t) ∧ Function.Injective (L t) ∧
          (L t).range = (A t).rangeᗮ ∧ ((A t).coprod (L t)).IsInvertible) ∧
        let F : (EuclideanSpace ℝ (Fin N.dimension) × K) → EuclideanSpace ℝ (Fin q) :=
          fun x => gamma x.1 + L x.1 x.2
        ∃ e0 : (EuclideanSpace ℝ (Fin N.dimension) × K) ≃L[ℝ] EuclideanSpace ℝ (Fin q),
          (∀ (v : EuclideanSpace ℝ (Fin N.dimension)) (w : K), e0 (v, w) = A0 v + w.val) ∧
          HasFDerivAt F (e0 : _ →L[ℝ] _) (a, 0) ∧
          ∃ Phi : OpenPartialHomeomorph
              (EuclideanSpace ℝ (Fin N.dimension) × K) (EuclideanSpace ℝ (Fin q)),
            (a, 0) ∈ Phi.source ∧ Phi.source ⊆ V ×ˢ Set.univ ∧
            Phi (a, 0) = p.val ∧ p.val ∈ Phi.target ∧
            Set.EqOn Phi F Phi.source ∧
            (∀ x ∈ Phi.source, (fderiv ℝ F x).IsInvertible) ∧
            ContDiffOn ℝ ∞ Phi Phi.source ∧ ContDiffOn ℝ ∞ Phi.symm Phi.target := by
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
  obtain ⟨V, hVo, haV, hVe, hgamma, L, hLd, hLa, hNormal⟩ :=
    N.exists_smooth_normal_family p
  have hLbase : L a = K.subtypeL := hLa
  let F : (EuclideanSpace ℝ (Fin N.dimension) × K) → EuclideanSpace ℝ (Fin q) :=
    fun x => gamma x.1 + L x.1 x.2
  have hgammaD : HasFDerivAt gamma A0 a := by
    have hi : MDifferentiableAt I J
        (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) p :=
      N.isSmoothEmbedding.contMDiff.mdifferentiableAt (by simp)
    simpa only [I, J, gamma, A0, a, e, writtenInExtChartAt, mfld_simps,
      hasFDerivWithinAt_univ, Function.comp_def] using hi.hasMFDerivAt.2
  obtain ⟨e0, he0⟩ :
      ∃ e0 : (EuclideanSpace ℝ (Fin N.dimension) × K) ≃L[ℝ]
        EuclideanSpace ℝ (Fin q),
        ∀ (v : EuclideanSpace ℝ (Fin N.dimension)) (w : K),
          e0 (v, w) = A0 v + w.val := N.exists_tangent_normal_equiv p
  have hLD : HasFDerivAt L (fderiv ℝ L a) a :=
    ((hLd.contDiffAt (hVo.mem_nhds haV)).differentiableAt (by simp)).hasFDerivAt
  have hSnd : HasFDerivAt
      (fun x : EuclideanSpace ℝ (Fin N.dimension) × K => x.2)
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin N.dimension)) K)
      (a, 0) := hasFDerivAt_snd
  have hFD : HasFDerivAt F (e0 : _ →L[ℝ] _) (a, 0) := by
    convert! (hgammaD.comp (a, 0) hasFDerivAt_fst).add
      ((hLD.comp (a, 0) hasFDerivAt_fst).clm_apply hSnd) using 1
    apply ContinuousLinearMap.ext
    intro x
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      Function.comp_apply, map_zero, add_zero]
    rw [hLbase]
    exact he0 x.1 x.2
  have hProdOpen : IsOpen (V ×ˢ (Set.univ : Set K)) := hVo.prod isOpen_univ
  have hbase : (a, (0 : K)) ∈ V ×ˢ Set.univ := ⟨haV, Set.mem_univ _⟩
  have hFp : ContDiffOn ℝ ∞ F (V ×ˢ Set.univ) :=
    (hgamma.comp contDiffOn_fst (fun x hx => hx.1)).add
      ((hLd.comp contDiffOn_fst (fun x hx => hx.1)).clm_apply contDiffOn_snd)
  have hFbase : ContDiffAt ℝ ∞ F (a, 0) := hFp.contDiffAt (hProdOpen.mem_nhds hbase)
  have hFvalue : F (a, 0) = p.val := by
    change gamma a + L a 0 = p.val
    rw [map_zero, add_zero]
    exact congrArg Subtype.val (extChartAt_to_inv (I := I) p)
  have hDFc : ContinuousOn (fderiv ℝ F) (V ×ˢ Set.univ) :=
    hFp.continuousOn_fderiv_of_isOpen hProdOpen (by simp)
  have hInvAt : {T : (EuclideanSpace ℝ (Fin N.dimension) × K) →L[ℝ]
      EuclideanSpace ℝ (Fin q) | T.IsInvertible} ∈ 𝓝 (fderiv ℝ F (a, 0)) := by
    rw [hFD.fderiv]
    exact e0.nhds
  have hInvNhd : {x | (fderiv ℝ F x).IsInvertible} ∈ 𝓝 (a, (0 : K)) :=
    (hDFc.continuousAt (hProdOpen.mem_nhds hbase)).preimage_mem_nhds hInvAt
  obtain ⟨O, hOI, hOo, haO⟩ := mem_nhds_iff.mp hInvNhd
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let basePhi := hFbase.toOpenPartialHomeomorph F hFD hn
  let Phi := basePhi.restrOpen ((V ×ˢ Set.univ) ∩ O) (hProdOpen.inter hOo)
  have hPhiBase : (a, (0 : K)) ∈ Phi.source :=
    ⟨hFbase.mem_toOpenPartialHomeomorph_source hFD hn, hbase, haO⟩
  have hSource : Phi.source ⊆ V ×ˢ Set.univ := fun x hx => hx.2.1
  have hPhiEq : (Phi : (EuclideanSpace ℝ (Fin N.dimension) × K) →
      EuclideanSpace ℝ (Fin q)) = F := by
    simp only [Phi, basePhi, OpenPartialHomeomorph.coe_restrOpen,
      ContDiffAt.toOpenPartialHomeomorph_coe]
  have hPhiD : ∀ x ∈ Phi.source, (fderiv ℝ F x).IsInvertible :=
    fun x hx => hOI hx.2.2
  have hPhiSmooth : ContDiffOn ℝ ∞ Phi Phi.source := by
    rw [hPhiEq]
    exact hFp.mono hSource
  have hPhiInvSmooth : ContDiffOn ℝ ∞ Phi.symm Phi.target := by
    intro z hz
    have hx := Phi.map_target hz
    obtain ⟨d, hd⟩ := hPhiD (Phi.symm z) hx
    have hfAt : ContDiffAt ℝ ∞ Phi (Phi.symm z) :=
      hPhiSmooth.contDiffAt (Phi.open_source.mem_nhds hx)
    have hfD : HasFDerivAt Phi (d : _ →L[ℝ] _) (Phi.symm z) := by
      rw [hPhiEq, hd]
      exact ((hFp.contDiffAt (hProdOpen.mem_nhds (hSource hx))).differentiableAt
        (by simp)).hasFDerivAt
    exact (Phi.contDiffAt_symm hz hfD hfAt).contDiffWithinAt
  refine ⟨V, hVo, haV, hVe, hgamma, L, hLd, hLa, hNormal, e0, he0, hFD,
    Phi, hPhiBase, hSource, ?_, ?_, ?_, hPhiD, hPhiSmooth, hPhiInvSmooth⟩
  · rw [hPhiEq]
    exact hFvalue
  · rw [← hFvalue, ← hPhiEq]
    exact Phi.map_source hPhiBase
  · intro x _
    exact congrFun hPhiEq x

end HarmonicMaps.CompactSmoothEmbeddedTarget

end

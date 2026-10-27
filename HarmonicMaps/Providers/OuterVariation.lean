module
public import HarmonicMaps.Frozen.TubularProjection
public import HarmonicMaps.Geometry.TargetNearestPoint
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import HarmonicMaps.Analysis.SobolevPostcomposition
public import HarmonicMaps.Analysis.SobolevAECollar
public import HarmonicMaps.Analysis.SobolevDifference
public import HarmonicMaps.Analysis.SmoothWeakGradient
public import HarmonicMaps.Analysis.DominatedEnergyDerivative
public import HarmonicMaps.SobolevRestriction
public import HarmonicMaps.Minimizer
public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.L2Space
public import HarmonicMaps.Analysis.SobolevPostcompositionLocal
public import HarmonicMaps.Analysis.SobolevAECongruence
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import HarmonicMaps.Sobolev
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
@[expose] public section
open MeasureTheory Filter Set
open scoped ContDiff Topology Manifold BigOperators
namespace HarmonicMaps


 private theorem outerCertificate_normal {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (V : Set (Ambient q)) (g : Ambient q → Ambient q)
    (hV : IsOpen V) (hsub : V ⊆ tubularTube q N)
    (hg : ContDiffOn ℝ ∞ g V)
    (hcert : ∀ w : tubularTube q N, w.val ∈ V →
      g w.val = (tubularProjection q N w).val)
    (z : Ambient q) (hz : z ∈ V) (v : Ambient q) :
    inner ℝ (z - g z) (fderiv ℝ g z v) = 0 := by
  have hmin : IsLocalMin (fun x => ‖z - g x‖ ^ 2) z := by
    filter_upwards [hV.mem_nhds hz] with x hx
    have hc := (tubularProjection_characterization q N).2.2.1
    have hm := (hc ⟨z, hsub hz⟩).1 (tubularProjection q N ⟨x, hsub hx⟩)
    rw [← hcert ⟨z, hsub hz⟩ hz, ← hcert ⟨x, hsub hx⟩ hx] at hm
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [dist_eq_norm] using hm) 2
  have hdg := ((hg z hz).contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)
  have hsq := ((hasFDerivAt_const z z).sub hdg.hasFDerivAt).norm_sq
  have he := congrArg (fun L => L v) (hmin.hasFDerivAt_eq_zero hsq)
  simp only [smul_apply, ContinuousLinearMap.comp_apply, zero_apply,
    Pi.sub_apply, innerSL_apply_apply, neg_apply, zero_sub, inner_neg_right,
    nsmul_eq_mul, Nat.cast_ofNat] at he
  exact neg_eq_zero.mp ((mul_eq_zero.mp he).resolve_left two_ne_zero)

 private theorem outerCertificate_potential {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (V : Set (Ambient q)) (g : Ambient q → Ambient q)
    (hV : IsOpen V) (hsub : V ⊆ tubularTube q N)
    (hg : ContDiffOn ℝ ∞ g V)
    (hcert : ∀ w : tubularTube q N, w.val ∈ V →
      g w.val = (tubularProjection q N w).val)
    (z : Ambient q) (hz : z ∈ V) :
    HasFDerivAt (fun x => (1 / 2 : ℝ) * ‖x‖ ^ 2 -
      (1 / 2 : ℝ) * (Metric.infDist x N.carrierSet) ^ 2)
      (innerSL ℝ (g z)) z := by
  have hdg := ((hg z hz).contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)
  have heq : (fun x => (1 / 2 : ℝ) * ‖x‖ ^ 2 -
        (1 / 2 : ℝ) * (Metric.infDist x N.carrierSet) ^ 2) =ᶠ[𝓝 z]
      (fun x => (1 / 2 : ℝ) * ‖x‖ ^ 2 - (1 / 2 : ℝ) * ‖x - g x‖ ^ 2) := by
    filter_upwards [hV.mem_nhds hz] with x hx
    have hp := ((tubularProjection_characterization q N).2.2.1 ⟨x, hsub hx⟩).1
    have he := (N.nearest_point_iff x (tubularProjection q N ⟨x, hsub hx⟩)).1 hp
    rw [← hcert ⟨x, hsub hx⟩ hx] at he
    rw [← he, dist_eq_norm]
  have hd := ((hasFDerivAt_id z).norm_sq.const_mul (1 / 2 : ℝ)).sub
    (((hasFDerivAt_id z).sub hdg.hasFDerivAt).norm_sq.const_mul (1 / 2 : ℝ))
  apply (hd.congr_of_eventuallyEq heq).congr_fderiv
  ext v
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    innerSL_apply_apply, Pi.sub_apply, id_eq, inner_sub_right, inner_sub_left,
    nsmul_eq_mul, Nat.cast_ofNat]
  have hn := outerCertificate_normal N V g hV hsub hg hcert z hz v
  simp only [inner_sub_left] at hn
  linarith only [hn]

 private theorem outerCertificate_derivative_symmetric {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (V : Set (Ambient q)) (g : Ambient q → Ambient q)
    (hV : IsOpen V) (hsub : V ⊆ tubularTube q N)
    (hg : ContDiffOn ℝ ∞ g V)
    (hcert : ∀ w : tubularTube q N, w.val ∈ V →
      g w.val = (tubularProjection q N w).val)
    (z : Ambient q) (hz : z ∈ V) (v w : Ambient q) :
    inner ℝ v (fderiv ℝ g z w) = inner ℝ w (fderiv ℝ g z v) := by
  have hdg := ((hg z hz).contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)
  have hf : ∀ᶠ x in 𝓝 z,
      HasFDerivAt (fun x => (1 / 2 : ℝ) * ‖x‖ ^ 2 -
        (1 / 2 : ℝ) * (Metric.infDist x N.carrierSet) ^ 2)
        (innerSL ℝ (g x)) x := by
    filter_upwards [hV.mem_nhds hz] with x hx
    exact outerCertificate_potential N V g hV hsub hg hcert x hx
  have hd := ((innerSL ℝ).hasFDerivAt).comp z hdg.hasFDerivAt
  have he := second_derivative_symmetric_of_eventually hf hd v w
  change inner ℝ (fderiv ℝ g z v) w = inner ℝ (fderiv ℝ g z w) v at he
  simpa only [real_inner_comm] using he.symm

 private theorem outerCertificate_hessian_symmetric {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (V : Set (Ambient q)) (g : Ambient q → Ambient q)
    (hV : IsOpen V) (hsub : V ⊆ tubularTube q N)
    (hg : ContDiffOn ℝ ∞ g V)
    (hcert : ∀ w : tubularTube q N, w.val ∈ V →
      g w.val = (tubularProjection q N w).val)
    (z : Ambient q) (hz : z ∈ V) (a v w : Ambient q) :
    inner ℝ a (fderiv ℝ (fderiv ℝ g) z v w) =
      inner ℝ w (fderiv ℝ (fderiv ℝ g) z v a) := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ g) V :=
    hg.fderiv_of_isOpen hV (by simp)
  have hdD := ((hD z hz).contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)
  have h₁ := ((innerSL ℝ a).hasFDerivAt).comp z
    (hdD.hasFDerivAt.clm_apply (hasFDerivAt_const w z))
  have h₂ := ((innerSL ℝ w).hasFDerivAt).comp z
    (hdD.hasFDerivAt.clm_apply (hasFDerivAt_const a z))
  have heq : (fun x => inner ℝ a (fderiv ℝ g x w)) =ᶠ[𝓝 z]
      (fun x => inner ℝ w (fderiv ℝ g x a)) := by
    filter_upwards [hV.mem_nhds hz] with x hx
    exact outerCertificate_derivative_symmetric N V g hV hsub hg hcert x hx a w
  have he := congrArg (fun L => L v) (h₁.fderiv.symm.trans
    (heq.fderiv_eq.trans h₂.fderiv))
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    add_apply, ContinuousLinearMap.apply_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero, zero_add] using he

 private theorem outerCertificate_hessian_argument_symmetry {q : ℕ}
    (V : Set (Ambient q)) (g : Ambient q → Ambient q)
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (z : Ambient q) (hz : z ∈ V) (v w : Ambient q) :
    fderiv ℝ (fderiv ℝ g) z v w = fderiv ℝ (fderiv ℝ g) z w v := by
  exact ((hg z hz).contDiffAt (hV.mem_nhds hz)).isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.mpr le_top) v w

 private theorem outerProjection_potential (q : ℕ) (N : CompactSmoothEmbeddedTarget q)
    (z : tubularTube q N) :
    HasFDerivAt (fun x => (1 / 2 : ℝ) * ‖x‖ ^ 2 -
      (1 / 2 : ℝ) * (Metric.infDist x N.carrierSet) ^ 2)
      (innerSL ℝ (tubularProjection q N z).val) z.val := by
  obtain ⟨V, hV, hz, hsub, g, hg, hcert, _⟩ :=
    (tubularProjectionDerivative_characterization q N).2.1 z
  rw [← hcert z hz]
  exact outerCertificate_potential N V g hV hsub hg hcert z.val hz

 private theorem outerProjection_derivative_symmetric (q : ℕ) (N : CompactSmoothEmbeddedTarget q)
    (z : tubularTube q N) (v w : Ambient q) :
    inner ℝ v (tubularProjectionDerivative q N z w) =
      inner ℝ w (tubularProjectionDerivative q N z v) := by
  obtain ⟨V, hV, hz, hsub, g, hg, hcert, _⟩ :=
    (tubularProjectionDerivative_characterization q N).2.1 z
  rw [← (tubularProjectionDerivative_characterization q N).1 z V g hV hz hsub hg hcert]
  exact outerCertificate_derivative_symmetric N V g hV hsub hg hcert z.val hz v w

 private theorem outerProjection_hessian_symmetric (q : ℕ) (N : CompactSmoothEmbeddedTarget q)
    (z : tubularTube q N) (a v w : Ambient q) :
    inner ℝ a (tubularProjectionSecondDerivative q N z v w) =
      inner ℝ w (tubularProjectionSecondDerivative q N z v a) := by
  obtain ⟨V, hV, hz, hsub, g, hg, hcert, _⟩ :=
    (tubularProjectionSecondDerivative_characterization q N).2.1 z
  rw [← (tubularProjectionSecondDerivative_characterization q N).1
    z V g hV hz hsub hg hcert]
  exact outerCertificate_hessian_symmetric N V g hV hsub hg hcert z.val hz a v w

 private theorem outerProjection_hessian_argument_symmetry (q : ℕ)
    (N : CompactSmoothEmbeddedTarget q) (z : tubularTube q N) (v w : Ambient q) :
    tubularProjectionSecondDerivative q N z v w =
      tubularProjectionSecondDerivative q N z w v := by
  obtain ⟨V, hV, hz, hsub, g, hg, hcert, _⟩ :=
    (tubularProjectionSecondDerivative_characterization q N).2.1 z
  rw [← (tubularProjectionSecondDerivative_characterization q N).1
    z V g hV hz hsub hg hcert]
  exact outerCertificate_hessian_argument_symmetry V g hV hg z.val hz v w

 private theorem outerExtension_jets {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (ρ : ℝ) (Q : Ambient q → Ambient q) (hQ : ContDiff ℝ ∞ Q)
    (hQeq : ∀ z : tubularTube q N, Metric.infDist z.val N.carrierSet < ρ →
      Q z.val = (tubularProjection q N z).val)
    (z : tubularTube q N) (hz : Metric.infDist z.val N.carrierSet < ρ) :
    fderiv ℝ Q z.val = tubularProjectionDerivative q N z ∧
    fderiv ℝ (fderiv ℝ Q) z.val = tubularProjectionSecondDerivative q N z := by
  let V : Set (Ambient q) := tubularTube q N ∩ {x | Metric.infDist x N.carrierSet < ρ}
  have hV : IsOpen V := (tubularProjection_characterization q N).2.1.inter
    (isOpen_lt (Metric.continuous_infDist_pt N.carrierSet) continuous_const)
  have hsub : V ⊆ tubularTube q N := inter_subset_left
  have hcert : ∀ w : tubularTube q N, w.val ∈ V →
      Q w.val = (tubularProjection q N w).val := fun w hw => hQeq w hw.2
  exact ⟨(tubularProjectionDerivative_characterization q N).1 z V Q hV
      ⟨z.property, hz⟩ hsub hQ.contDiffOn hcert,
    (tubularProjectionSecondDerivative_characterization q N).1 z V Q hV
      ⟨z.property, hz⟩ hsub hQ.contDiffOn hcert⟩

 private theorem outerExtension_target_jets {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (ρ : ℝ) (hρ : 0 < ρ) (Q : Ambient q → Ambient q) (hQ : ContDiff ℝ ∞ Q)
    (hQeq : ∀ z : tubularTube q N, Metric.infDist z.val N.carrierSet < ρ →
      Q z.val = (tubularProjection q N z).val)
    (p : N.Carrier) (hp : p.val ∈ tubularTube q N) :
    Q p.val = p.val ∧
    fderiv ℝ Q p.val = tubularProjectionDerivative q N ⟨p.val, hp⟩ ∧
    fderiv ℝ (fderiv ℝ Q) p.val = tubularProjectionSecondDerivative q N ⟨p.val, hp⟩ := by
  have hd : Metric.infDist p.val N.carrierSet < ρ := by
    rw [Metric.infDist_zero_of_mem p.property]
    exact hρ
  obtain ⟨hp', he⟩ := (tubularProjection_characterization q N).2.2.2.1 p
  have hid : tubularProjection q N ⟨p.val, hp⟩ = p := he
  exact ⟨(hQeq ⟨p.val, hp⟩ hd).trans (congrArg Subtype.val hid),
    outerExtension_jets N ρ Q hQ hQeq ⟨p.val, hp⟩ hd⟩

 private theorem outerProjection_exists_extension_jets (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ Q : Ambient q → Ambient q,
      ContDiff ℝ ∞ Q ∧
      (∀ z : tubularTube q N, Metric.infDist z.val N.carrierSet < ρ →
        Q z.val = (tubularProjection q N z).val) ∧
      ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
        (∀ z, ‖fderiv ℝ Q z‖ ≤ C₁) ∧
        (∀ z, ‖fderiv ℝ (fderiv ℝ Q) z‖ ≤ C₂) ∧
        (∀ z : tubularTube q N, Metric.infDist z.val N.carrierSet < ρ →
          fderiv ℝ Q z.val = tubularProjectionDerivative q N z ∧
          fderiv ℝ (fderiv ℝ Q) z.val = tubularProjectionSecondDerivative q N z) ∧
        ∀ p : N.Carrier, ∃ hp : p.val ∈ tubularTube q N,
          Q p.val = p.val ∧
          fderiv ℝ Q p.val = tubularProjectionDerivative q N ⟨p.val, hp⟩ ∧
          fderiv ℝ (fderiv ℝ Q) p.val = tubularProjectionSecondDerivative q N ⟨p.val, hp⟩ := by
  obtain ⟨ρ, hρ, _, hsub, _, _, _, _, _, _, _, _, _, Q, hQ, hQeq,
      C₁, C₂, hC₁, hC₂, hQD, hQH⟩ := tubularProjection_complete q N
  refine ⟨ρ, hρ, Q, hQ, hQeq, C₁, C₂, hC₁, hC₂, hQD, hQH,
    fun z hz => outerExtension_jets N ρ Q hQ hQeq z hz, ?_⟩
  intro p
  obtain ⟨hp, _⟩ := (tubularProjection_characterization q N).2.2.2.1 p
  exact ⟨hp, outerExtension_target_jets N ρ hρ Q hQ hQeq p hp⟩



/-- Weak-gradient addition retains the displayed original columns. -/
private theorem HasWeakGradient.add {n q : ℕ} {Ω : OpenDomain n}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : HasWeakGradient Ω u Du) (hv : HasWeakGradient Ω v Dv) :
    HasWeakGradient Ω (u + v) (fun x i => Du x i + Dv x i) := by
  refine ⟨hu.1.add hv.1, fun i => (hu.2.1 i).add (hv.2.1 i), ?_⟩
  intro i φ hφ hc hs
  simp only [Pi.add_apply, smul_add]
  rw [integral_add (hu.integrable_test_derivative i hφ hc hs)
      (hv.integrable_test_derivative i hφ hc hs),
    integral_add (hu.integrable_test_gradient i hφ hc hs)
      (hv.integrable_test_gradient i hφ hc hs),
    hu.2.2 i φ hφ hc hs, hv.2.2 i φ hφ hc hs]
  abel

/-- Addition of finite Sobolev maps uses the sum of the same weak columns. -/
private theorem MemW12.add {n q : ℕ} {Ω : OpenDomain n}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (hv : MemW12 Ω v Dv) :
    MemW12 Ω (u + v) (fun x i => Du x i + Dv x i) :=
  ⟨hu.1.add hv.1, hu.2.1.add hv.2.1, fun i => (hu.2.2 i).add (hv.2.2 i)⟩

/-- Smooth compact tests have the literal classical coordinate columns in W1,2. -/
private theorem memW12_const_smul_compactSmooth {n q : ℕ} (Ω : OpenDomain n)
    {ψ : Domain n → Ambient q} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (t : ℝ) :
    MemW12 Ω (fun x => t • ψ x)
      (fun x i => t • fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
  have htψ : ContDiff ℝ ∞ (fun x => t • ψ x) := hψ.const_smul t
  have hmem : MemLp (fun x => t • ψ x) 2 (volume.restrict Ω.val) :=
    (hψ.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict Ω.val |>.const_smul t
  have hcoord (i : Fin n) (x : Domain n) :
      coordinateDerivative (fun x => t • ψ x) htψ i x =
        t • fderiv ℝ ψ x (EuclideanSpace.single i 1) := by
    change (fderiv ℝ (fun y => t • ψ y) x) _ = _
    rw [fderiv_fun_const_smul (hψ.differentiable (by simp) x)]
    rfl
  have hd (i : Fin n) : MemLp (coordinateDerivative (fun x => t • ψ x) htψ i) 2
      (volume.restrict Ω.val) := by
    have hm : MemLp (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)) 2
        (volume.restrict Ω.val) :=
      (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (μ := volume) (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))).restrict Ω.val
    apply (hm.const_smul t).ae_eq
    filter_upwards [] with x
    exact (hcoord i x).symm
  have H := memW12_of_contDiff Ω htψ hmem hd
  have heq : (fun x i => coordinateDerivative (fun x => t • ψ x) htψ i x) =
      (fun x i => t • fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    funext x i
    exact hcoord i x
  rw [heq] at H
  exact H

/-- Projected outer variations are genuine Sobolev competitors for both signs
of a sufficiently small parameter. The zero boundary condition is the native
closure and follows from an almost-everywhere collar argument. -/
private theorem MemW12.projected_outerVariation_admissible {n q : ℕ}
    {a : Domain n} {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) {N : CompactSmoothEmbeddedTarget q}
    (hN : TakesValuesIn N (ballDomain a R) u)
    {Q : Ambient q → Ambient q} (hQ : ContDiff ℝ ∞ Q)
    (L : ℝ) (hDQ : ∀ z, ‖fderiv ℝ Q z‖ ≤ L)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hfix : ∀ p ∈ N.carrierSet, Q p = p)
    (hmap : ∀ z, Metric.infDist z N.carrierSet < ρ → Q z ∈ N.carrierSet)
    {ψ : Domain n → Ambient q} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Metric.ball a R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      MemW12 (ballDomain a R) (fun x => Q (u x + t • ψ x))
        (fun x i => fderiv ℝ Q (u x + t • ψ x)
          (Du x i + t • fderiv ℝ ψ x (EuclideanSpace.single i 1))) ∧
      TakesValuesIn N (ballDomain a R) (fun x => Q (u x + t • ψ x)) ∧
      HasZeroBoundaryDifference (ballDomain a R) u Du (fun x => Q (u x + t • ψ x))
        (fun x i => fderiv ℝ Q (u x + t • ψ x)
          (Du x i + t • fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hψ.continuous
  let M : ℝ := max 1 B
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hψbound (x : Domain n) : ‖ψ x‖ ≤ M := (hB x).trans (le_max_right _ _)
  have hK := hc.insert a
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨a, mem_insert a _⟩
    (continuous_id.dist (continuous_const (y := a))).continuousOn
  have hzR : dist z a < R := by
    rcases hz with rfl | hz
    · simpa only [dist_self] using hR
    · exact hs hz
  let r : ℝ := (dist z a + R) / 2
  have hr : 0 ≤ r := by dsimp [r]; linarith only [dist_nonneg (x := z) (y := a), hR]
  have hrR : r < R := by dsimp [r]; linarith only [hzR]
  have hsupp : tsupport ψ ⊆ Metric.closedBall a r := by
    intro x hx
    have hxle : dist x a ≤ dist z a := hmax (mem_insert_of_mem a hx)
    change dist x a ≤ r
    dsimp [r]
    linarith only [hxle, hzR]
  refine ⟨ρ / M, div_pos hρ hM, ?_⟩
  intro t ht
  have hv := (hu.add (memW12_const_smul_compactSmooth (ballDomain a R) hψ hc t)).postcompose
    hR Q hQ L hDQ
  have hv' : MemW12 (ballDomain a R) (fun x => Q (u x + t • ψ x))
      (fun x i => fderiv ℝ Q (u x + t • ψ x)
        (Du x i + t • fderiv ℝ ψ x (EuclideanSpace.single i 1))) := hv
  refine ⟨hv', ?_, ?_⟩
  · filter_upwards [hN] with x hx
    apply hmap
    calc
      Metric.infDist (u x + t • ψ x) N.carrierSet ≤ dist (u x + t • ψ x) (u x) :=
        Metric.infDist_le_dist_of_mem hx
      _ = |t| * ‖ψ x‖ := by rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      _ ≤ |t| * M := mul_le_mul_of_nonneg_left (hψbound x) (abs_nonneg t)
      _ < ρ := (lt_div_iff₀ hM).mp ht
  · apply (hv'.sub hu).zeroBoundary_of_ae_zero_collar_ball hR hr hrR
    have hNc : ∀ᵐ x ∂volume.restrict (Metric.ball a R \ Metric.closedBall a r),
        u x ∈ N.carrierSet := ae_restrict_of_ae_restrict_of_subset sdiff_subset hN
    have hxmem : ∀ᵐ x ∂volume.restrict (Metric.ball a R \ Metric.closedBall a r),
        x ∈ Metric.ball a R \ Metric.closedBall a r :=
      ae_restrict_mem (Metric.isOpen_ball.measurableSet.diff Metric.isClosed_closedBall.measurableSet)
    filter_upwards [hNc, hxmem] with x hx hxmem
    have hnot : x ∉ tsupport ψ := fun h => hxmem.2 (hsupp h)
    simp only [Pi.sub_apply, image_eq_zero_of_notMem_tsupport hnot, smul_zero, add_zero,
      hfix (u x) hx, sub_self]

/-- The difference of squared norms is bounded by the norm difference
and the sum of the two norms. -/
private theorem outerVariation_abs_norm_sq_sub_le {E : Type*} [NormedAddCommGroup E] (v w : E) :
    |‖v‖ ^ 2 - ‖w‖ ^ 2| ≤ ‖v - w‖ * (‖v‖ + ‖w‖) := by
  calc
    |‖v‖ ^ 2 - ‖w‖ ^ 2| = |‖v‖ - ‖w‖| * (‖v‖ + ‖w‖) := by
      rw [show ‖v‖ ^ 2 - ‖w‖ ^ 2 = (‖v‖ - ‖w‖) * (‖v‖ + ‖w‖) by ring,
        abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ _ := mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le v w)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The genuine derivative field is Lipschitz when its actual Hessian is bounded. -/
private theorem outerVariation_DQ_norm_sub_le {q : ℕ} {Q : Ambient q → Ambient q}
    (hQ : ContDiff ℝ ∞ Q) {K : ℝ}
    (hD2Q : ∀ z, ‖fderiv ℝ (fderiv ℝ Q) z‖ ≤ K) (z w : Ambient q) :
    ‖fderiv ℝ Q z - fderiv ℝ Q w‖ ≤ K * ‖z - w‖ := by
  have hG : ContDiff ℝ ∞ (fderiv ℝ Q) := hQ.fderiv_right (by simp)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (hG.differentiable (by simp)).differentiableAt)
    (fun x _ => hD2Q x) convex_univ (mem_univ w) (mem_univ z)

/-- Pointwise two-sided domination of the actual projected HS-energy slope.
The gradient factor is the literal sum of the two HS densities. -/
private theorem outerVariation_energy_density_difference_quotient_bound {n q : ℕ}
    {Q : Ambient q → Ambient q} (hQ : ContDiff ℝ ∞ Q)
    {L K M : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hDQ : ∀ z, ‖fderiv ℝ Q z‖ ≤ L)
    (hD2Q : ∀ z, ‖fderiv ℝ (fderiv ℝ Q) z‖ ≤ K)
    (p v : Ambient q) (hv : ‖v‖ ≤ M) (A B : Gradient n q)
    (t : ℝ) (ht : |t| < 1) (ht0 : t ≠ 0) :
    |(hsNormSq (fun i => fderiv ℝ Q (p + t • v) (A i + t • B i)) -
       hsNormSq (fun i => fderiv ℝ Q p (A i))) / t| ≤
      (4 * L * (K * M + L)) * (hsNormSq A + hsNormSq B) := by
  have ht1 : |t| ≤ 1 := ht.le
  have hcol (i : Fin n) :
      |‖fderiv ℝ Q (p + t • v) (A i + t • B i)‖ ^ 2 -
       ‖fderiv ℝ Q p (A i)‖ ^ 2| ≤
        |t| * (4 * L * (K * M + L)) * (‖A i‖ ^ 2 + ‖B i‖ ^ 2) := by
    let V := fderiv ℝ Q (p + t • v) (A i + t • B i)
    let W := fderiv ℝ Q p (A i)
    have hV : ‖V‖ ≤ L * (‖A i‖ + ‖B i‖) := by
      apply (ContinuousLinearMap.le_opNorm _ _).trans
      apply mul_le_mul (hDQ _) _ (norm_nonneg _) hL
      exact (norm_add_le _ _).trans (by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add_right (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right ht1 (norm_nonneg (B i))) _)
    have hW : ‖W‖ ≤ L * ‖A i‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hDQ _) (norm_nonneg _))
    have hG : ‖fderiv ℝ Q (p + t • v) - fderiv ℝ Q p‖ ≤ K * (|t| * M) := by
      have hh := outerVariation_DQ_norm_sub_le hQ hD2Q (p + t • v) p
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hv (abs_nonneg t)) hK)
    have hsplit : V - W =
        (fderiv ℝ Q (p + t • v) - fderiv ℝ Q p) (A i) +
          t • fderiv ℝ Q (p + t • v) (B i) := by
      dsimp only [V, W]
      rw [map_add, map_smul, sub_apply]
      abel
    have hdiff : ‖V - W‖ ≤ |t| * (K * M * ‖A i‖ + L * ‖B i‖) := by
      rw [hsplit]
      apply (norm_add_le _ _).trans
      have h1 := (ContinuousLinearMap.le_opNorm
        (fderiv ℝ Q (p + t • v) - fderiv ℝ Q p) (A i)).trans
          (mul_le_mul_of_nonneg_right hG (norm_nonneg _))
      have h2 := (ContinuousLinearMap.le_opNorm (fderiv ℝ Q (p + t • v)) (B i)).trans
          (mul_le_mul_of_nonneg_right (hDQ _) (norm_nonneg _))
      rw [norm_smul, Real.norm_eq_abs]
      calc
        _ ≤ K * (|t| * M) * ‖A i‖ + |t| * (L * ‖B i‖) :=
          add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg t))
        _ = _ := by ring
    have hsum : ‖V‖ + ‖W‖ ≤ 2 * L * (‖A i‖ + ‖B i‖) := by
      have hh := add_le_add hV hW
      have hLB : 0 ≤ L * ‖B i‖ := mul_nonneg hL (norm_nonneg _)
      nlinarith only [hh, hLB]
    have hc : K * M * ‖A i‖ + L * ‖B i‖ ≤ (K * M + L) * (‖A i‖ + ‖B i‖) := by
      have h1 : 0 ≤ K * M * ‖B i‖ := mul_nonneg (mul_nonneg hK hM) (norm_nonneg _)
      have h2 : 0 ≤ L * ‖A i‖ := mul_nonneg hL (norm_nonneg _)
      nlinarith only [h1, h2]
    have hs : (‖A i‖ + ‖B i‖) ^ 2 ≤ 2 * (‖A i‖ ^ 2 + ‖B i‖ ^ 2) := by
      nlinarith only [sq_nonneg (‖A i‖ - ‖B i‖)]
    calc
      _ ≤ ‖V - W‖ * (‖V‖ + ‖W‖) := outerVariation_abs_norm_sq_sub_le V W
      _ ≤ (|t| * (K * M * ‖A i‖ + L * ‖B i‖)) *
          (2 * L * (‖A i‖ + ‖B i‖)) :=
        mul_le_mul hdiff hsum (add_nonneg (norm_nonneg _) (norm_nonneg _))
          (by positivity)
      _ ≤ (|t| * ((K * M + L) * (‖A i‖ + ‖B i‖))) *
          (2 * L * (‖A i‖ + ‖B i‖)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (abs_nonneg t)) (by positivity)
      _ = (|t| * (2 * L * (K * M + L))) * (‖A i‖ + ‖B i‖) ^ 2 := by ring
      _ ≤ (|t| * (2 * L * (K * M + L))) *
          (2 * (‖A i‖ ^ 2 + ‖B i‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  rw [abs_div, div_le_iff₀ (abs_pos.mpr ht0)]
  calc
    |hsNormSq (fun i => fderiv ℝ Q (p + t • v) (A i + t • B i)) -
       hsNormSq (fun i => fderiv ℝ Q p (A i))| =
        |∑ i : Fin n, (‖fderiv ℝ Q (p + t • v) (A i + t • B i)‖ ^ 2 -
          ‖fderiv ℝ Q p (A i)‖ ^ 2)| := by rw [hsNormSq, hsNormSq, Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin n, |‖fderiv ℝ Q (p + t • v) (A i + t • B i)‖ ^ 2 -
          ‖fderiv ℝ Q p (A i)‖ ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, |t| * (4 * L * (K * M + L)) * (‖A i‖ ^ 2 + ‖B i‖ ^ 2) :=
      Finset.sum_le_sum (fun i _ => hcol i)
    _ = (4 * L * (K * M + L)) * (hsNormSq A + hsNormSq B) * |t| := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      dsimp only [hsNormSq]
      ring

/-- The projected coordinate columns have their genuine parameter derivatives. -/
private theorem outerVariation_energy_density_hasDerivAt {n q : ℕ}
    {Q : Ambient q → Ambient q} (hQ : ContDiff ℝ ∞ Q)
    (p v : Ambient q) (A B : Gradient n q)
    (htan : ∀ i, fderiv ℝ Q p (A i) = A i) :
    HasDerivAt (fun t : ℝ => hsNormSq
      (fun i => fderiv ℝ Q (p + t • v) (A i + t • B i)))
      (2 * ∑ i : Fin n, inner ℝ (A i)
        (fderiv ℝ Q p (B i) + fderiv ℝ (fderiv ℝ Q) p v (A i))) 0 := by
  have hG : ContDiff ℝ ∞ (fderiv ℝ Q) := hQ.fderiv_right (by simp)
  have hp : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa only [one_smul, zero_add, Pi.add_apply, Function.id_def] using!
      (hasDerivAt_const (0 : ℝ) p).add ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hGline := (hG.differentiable (by simp) (p + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 hp
  simp only [zero_smul, add_zero] at hGline
  have hcol (i : Fin n) : HasDerivAt
      (fun t : ℝ => fderiv ℝ Q (p + t • v) (A i + t • B i))
      (fderiv ℝ Q p (B i) + fderiv ℝ (fderiv ℝ Q) p v (A i)) 0 := by
    have hin : HasDerivAt (fun t : ℝ => A i + t • B i) (B i) 0 := by
      simpa only [one_smul, zero_add, Pi.add_apply, Function.id_def] using!
        (hasDerivAt_const (0 : ℝ) (A i)).add ((hasDerivAt_id (0 : ℝ)).smul_const (B i))
    simpa only [Function.comp_def, zero_smul, add_zero, add_comm] using! hGline.clm_apply hin
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => (hcol i).norm_sq)
  simp only [zero_smul, add_zero, htan, ← Finset.mul_sum] at hsum
  simpa only [hsNormSq, Finset.sum_fn] using hsum

/-- The genuine outer first-variation integrand is L1 on a ball. -/
private theorem MemW12.integrable_projected_outerVariation {n q : ℕ}
    {a : Domain n} {R : ℝ} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du)
    {Q : Ambient q → Ambient q} (hQ : ContDiff ℝ ∞ Q)
    {L K : ℝ} (hDQ : ∀ z, ‖fderiv ℝ Q z‖ ≤ L)
    (hD2Q : ∀ z, ‖fderiv ℝ (fderiv ℝ Q) z‖ ≤ K)
    {ψ : Domain n → Ambient q} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (Du x i)
      (fderiv ℝ Q (u x) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) +
        fderiv ℝ (fderiv ℝ Q) (u x) (ψ x) (Du x i))) (Metric.ball a R) := by
  let μ := volume.restrict (Metric.ball a R)
  have hG : ContDiff ℝ ∞ (fderiv ℝ Q) := hQ.fderiv_right (by simp)
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hψ.continuous
  have hum : AEStronglyMeasurable u μ := hu.2.1.aestronglyMeasurable
  have hHm : AEStronglyMeasurable
      (fun x => fderiv ℝ (fderiv ℝ Q) (u x) (ψ x)) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (((hG.continuous_fderiv (by simp)).comp_aestronglyMeasurable hum).prodMk
        hψ.continuous.aestronglyMeasurable)
  have hHcol (i : Fin n) : MemLp
      (fun x => fderiv ℝ (fderiv ℝ Q) (u x) (ψ x) (Du x i)) 2 μ := by
    apply (hu.2.2 i).of_le_mul
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hHm.prodMk (hu.2.2 i).aestronglyMeasurable))
    filter_upwards [] with x
    have hK : 0 ≤ K := (norm_nonneg (fderiv ℝ (fderiv ℝ Q) (u x))).trans (hD2Q (u x))
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ Q) (u x) (ψ x)‖ * ‖Du x i‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ Q) (u x)‖ * ‖ψ x‖) * ‖Du x i‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (K * M) * ‖Du x i‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul (hD2Q _) (hM x) (norm_nonneg _) hK)
          (norm_nonneg _)
  have hDψ (i : Fin n) : MemLp
      (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)) 2 μ :=
    (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (μ := volume) (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))).restrict (Metric.ball a R)
  apply integrable_finsetSum Finset.univ
  intro i _
  have hV := (memLp_postcomposition_column hum (hDψ i) hQ hDQ).add (hHcol i)
  have hA : MemLp (fun x => Du x i) 2 μ := hu.2.2 i
  apply (L2.integrable_inner (𝕜 := ℝ) (hA.toLp (fun x => Du x i))
    (hV.toLp _)).congr
  filter_upwards [hA.coeFn_toLp, hV.coeFn_toLp] with x hAx hVx
  rw [hAx, hVx]
  rfl

/-- A local minimizer gives the exact ball-supported outer first variation.
Every admissibility and dominated-slope obligation is discharged in the proof. -/
private theorem IsLocallyEnergyMinimizing.projected_outerVariation_first_integral_zero {n q : ℕ}
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val)
    {Q : Ambient q → Ambient q} (hQ : ContDiff ℝ ∞ Q)
    (L K : ℝ) (hDQ : ∀ z, ‖fderiv ℝ Q z‖ ≤ L)
    (hD2Q : ∀ z, ‖fderiv ℝ (fderiv ℝ Q) z‖ ≤ K)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hfix : ∀ p ∈ N.carrierSet, Q p = p)
    (hmap : ∀ z, Metric.infDist z N.carrierSet < ρ → Q z ∈ N.carrierSet)
    (htan : ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      ∀ i : Fin n, fderiv ℝ Q (u x) (Du x i) = Du x i)
    {ψ : Domain n → Ambient q} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Metric.ball a R) :
    IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (Du x i)
      (fderiv ℝ Q (u x) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) +
        fderiv ℝ (fderiv ℝ Q) (u x) (ψ x) (Du x i))) (Metric.ball a R) ∧
    (∫ x in Metric.ball a R, ∑ i : Fin n, inner ℝ (Du x i)
      (fderiv ℝ Q (u x) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) +
        fderiv ℝ (fderiv ℝ Q) (u x) (ψ x) (Du x i))) = 0 := by
  have hw := hu.memW12_ball hball
  have ht : TakesValuesIn N (ballDomain a R) u :=
    ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_closedBall.trans hball) hN
  have hi := hw.integrable_projected_outerVariation hQ hDQ hD2Q hψ hc
  refine ⟨hi, ?_⟩
  let μ := volume.restrict (Metric.ball a R)
  let F : ℝ → Domain n → ℝ := fun t x => hsNormSq
    (fun i => fderiv ℝ Q (u x + t • ψ x)
      (Du x i + t • fderiv ℝ ψ x (EuclideanSpace.single i 1)))
  let D : Domain n → ℝ := fun x => 2 * ∑ i : Fin n, inner ℝ (Du x i)
    (fderiv ℝ Q (u x) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) +
      fderiv ℝ (fderiv ℝ Q) (u x) (ψ x) (Du x i))
  have hF0 : F 0 =ᵐ[μ] (fun x => hsNormSq (Du x)) := by
    filter_upwards [htan] with x hx
    dsimp only [F]
    simp only [zero_smul, add_zero, hx]
  obtain ⟨ε, hε, hadm⟩ := hw.projected_outerVariation_admissible
    hR ht hQ L hDQ hρ hfix hmap hψ hc hs
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hψ.continuous
  let M : ℝ := max 1 B
  have hM : 0 ≤ M := (zero_lt_one.trans_le (le_max_left _ _)).le
  have hψbound (x : Domain n) : ‖ψ x‖ ≤ M := (hB x).trans (le_max_right _ _)
  have hL : 0 ≤ L := (norm_nonneg (fderiv ℝ Q 0)).trans (hDQ 0)
  have hK : 0 ≤ K := (norm_nonneg (fderiv ℝ (fderiv ℝ Q) 0)).trans (hD2Q 0)
  let C : ℝ := 4 * L * (K * M + L)
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, |t| < min ε 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (lt_min hε zero_lt_one)] with t ht
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
  have hFn : ∀ᶠ t : ℝ in 𝓝[≠] 0, Integrable (F t) μ := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with t ht
    exact (hadm t (ht.trans_le (min_le_left _ _))).1.integrable_hsNormSq
  have hDψ : Integrable
      (fun x => hsNormSq (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1))) μ := by
    apply integrable_hsNormSq_of_memLp_columns
    intro i
    exact (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (μ := volume) (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))).restrict (Metric.ball a R)
  have hb : Integrable (fun x => C *
      (hsNormSq (Du x) + hsNormSq (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1)))) μ :=
    (hw.integrable_hsNormSq.add hDψ).const_mul C
  have hbound : ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ᵐ x ∂μ,
      ‖t⁻¹ * (F t x - F 0 x)‖ ≤ C *
        (hsNormSq (Du x) + hsNormSq (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
    apply Filter.Eventually.of_forall
    intro x
    have hh := outerVariation_energy_density_difference_quotient_bound hQ hL hK hM hDQ hD2Q
      (u x) (ψ x) (hψbound x) (Du x)
      (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1)) t
      (ht.trans_le (min_le_right _ _)) ht0
    dsimp only [F]
    simp only [zero_smul, add_zero]
    rw [Real.norm_eq_abs, mul_comm t⁻¹, ← div_eq_mul_inv]
    exact hh
  have hder : ∀ᵐ x ∂μ, HasDerivAt (fun t => F t x) (D x) 0 := by
    filter_upwards [htan] with x hx
    exact outerVariation_energy_density_hasDerivAt hQ (u x) (ψ x) (Du x)
      (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1)) hx
  have hzI : Integrable (F 0) μ := hw.integrable_hsNormSq.congr hF0.symm
  have hderI := hasDerivAt_integral_of_dominated_slopes hzI hFn hb hbound hder
  have hlocal : IsLocalMin (fun t => ∫ x, F t x ∂μ) 0 := by
    filter_upwards [hnear] with t ht
    obtain ⟨hv, hNv, hzero⟩ := hadm t (ht.trans_le (min_le_left _ _))
    have hle := hmin a R hR hball _ _ hv hNv hzero
    have hreal := ENNReal.toReal_mono hv.dirichletEnergy_ne_top hle
    calc
      (∫ x, F 0 x ∂μ) = ∫ x in Metric.ball a R, hsNormSq (Du x) := integral_congr_ae hF0
      _ = (dirichletEnergy Du (Metric.ball a R)).toReal :=
        (dirichletEnergy_toReal (U := Metric.ball a R) hw.integrable_hsNormSq).symm
      _ ≤ _ := hreal
      _ = ∫ x, F t x ∂μ :=
        dirichletEnergy_toReal (U := Metric.ball a R) hv.integrable_hsNormSq
  have heq := hlocal.hasDerivAt_eq_zero hderI
  change (∫ x, 2 * _ ∂μ) = 0 at heq
  rw [integral_const_mul] at heq
  exact (mul_eq_zero.mp heq).resolve_left (by norm_num)



private theorem MemW12Loc.projected_gradient_fixed {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (N : CompactSmoothEmbeddedTarget q)
    (hN : TakesValuesIn N Ω u) (Q : Ambient q → Ambient q)
    (hQ : ContDiff ℝ ∞ Q) (C : ℝ) (hDQ : ∀ z, ‖fderiv ℝ Q z‖ ≤ C)
    (hfix : ∀ p : N.Carrier, Q p.val = p.val) :
    ∀ᵐ x ∂volume.restrict Ω.val, ∀ i : Fin n,
      fderiv ℝ Q (u x) (Du x i) = Du x i := by
  have hPost := hu.postcompose Q hQ C hDQ
  have hEq : (Q ∘ u) =ᵐ[volume.restrict Ω.val] u := by
    filter_upwards [hN] with x hx
    exact hfix ⟨u x, hx⟩
  have hgrad := hPost.1.ae_eq_of_ae_eq_map hu.1 hEq
  filter_upwards [hgrad] with x hx i
  exact congrFun hx i



private theorem outer_hessian_sum_norm_le {n q : ℕ}
    (A : Ambient q →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (D : Gradient n q) (K : ℝ) (hA : ‖A‖ ≤ K) :
    ‖∑ i : Fin n, A (D i) (D i)‖ ≤ K * hsNormSq D := by
  calc
    ‖∑ i : Fin n, A (D i) (D i)‖ ≤ ∑ i : Fin n, ‖A (D i) (D i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin n, K * ‖D i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ‖A (D i) (D i)‖ ≤ ‖A (D i)‖ * ‖D i‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖A‖ * ‖D i‖) * ‖D i‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ (K * ‖D i‖) * ‖D i‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hA (norm_nonneg _)) (norm_nonneg _)
        _ = K * ‖D i‖ ^ 2 := by ring
    _ = K * hsNormSq D := by rw [hsNormSq, Finset.mul_sum]

private theorem MemW12Loc.outer_curvature_locallyIntegrable {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {Q : Ambient q → Ambient q}
    (hQ : ContDiff ℝ ∞ Q) (K : ℝ)
    (hHQ : ∀ z, ‖fderiv ℝ (fderiv ℝ Q) z‖ ≤ K) :
    LocallyIntegrableOn (fun x => ∑ i : Fin n,
      fderiv ℝ (fderiv ℝ Q) (u x) (Du x i) (Du x i)) Ω.val volume := by
  apply (locallyIntegrableOn_iff Ω.property.isLocallyClosed).mpr
  intro A hAΩ hA
  have hDcont : ContDiff ℝ ∞ (fderiv ℝ Q) := hQ.fderiv_right (by simp)
  have hHcont : Continuous (fderiv ℝ (fderiv ℝ Q)) :=
    hDcont.continuous_fderiv (by simp)
  have hHmeas := hHcont.comp_aestronglyMeasurable (hu.2.1 A hA hAΩ).aestronglyMeasurable
  have hFmeas : AEStronglyMeasurable (fun x => ∑ i : Fin n,
      fderiv ℝ (fderiv ℝ Q) (u x) (Du x i) (Du x i)) (volume.restrict A) := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    have hDi := (hu.2.2 i A hA hAΩ).aestronglyMeasurable
    have hHD : AEStronglyMeasurable
        (fun x => fderiv ℝ (fderiv ℝ Q) (u x) (Du x i)) (volume.restrict A) :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hHmeas.prodMk hDi)
    exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hHD.prodMk hDi)
  have hEnergy := integrable_hsNormSq_of_memLp_columns (fun i => hu.2.2 i A hA hAΩ)
  apply (hEnergy.const_mul K).mono' hFmeas
  filter_upwards [] with x
  exact outer_hessian_sum_norm_le _ _ K (hHQ (u x))

private theorem outer_compact_inner_integrable {n q : ℕ} {Ω : OpenDomain n}
    {f : Domain n → Ambient q} {ψ : Domain n → Ambient q}
    (hf : LocallyIntegrableOn f Ω.val volume) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω.val) :
    Integrable (fun x => inner ℝ (f x) (ψ x)) volume := by
  have hfK := hf.integrableOn_compact_subset hs hc
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hψ
  have hInner : IntegrableOn (fun x => inner ℝ (f x) (ψ x)) (tsupport ψ) := by
    apply (hfK.norm.const_mul B).mono' (hfK.aestronglyMeasurable.inner hψ.aestronglyMeasurable)
    filter_upwards [] with x
    exact (norm_inner_le_norm (f x) (ψ x)).trans (by
      calc
        ‖f x‖ * ‖ψ x‖ ≤ ‖f x‖ * B := mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)
        _ = B * ‖f x‖ := mul_comm _ _)
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hInner
  intro x hx
  by_contra hnot
  exact hx (by
    change inner ℝ (f x) (ψ x) = 0
    rw [image_eq_zero_of_notMem_tsupport hnot, inner_zero_right])

private theorem MemW12Loc.outer_test_pairings_integrable {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {F : Domain n → Ambient q}
    (hF : LocallyIntegrableOn F Ω.val volume) {ψ : Domain n → Ambient q}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω.val) :
    Integrable (fun x => ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) volume ∧
    Integrable (fun x => inner ℝ (F x) (ψ x)) volume := by
  refine ⟨?_, outer_compact_inner_integrable hF hψ.continuous hc hs⟩
  apply integrable_finsetSum
  intro i _
  exact outer_compact_inner_integrable (hu.1.2.1 i)
    ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))
    ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hs)



private theorem outerTest_finite_ball_decomposition_generic {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : OpenDomain n) (ψ : Domain n → E)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω.val) :
    ∃ t : Finset (tsupport ψ), ∃ r : t → ℝ, ∃ η : t → Domain n → E,
      (∀ j : t, 0 < r j ∧ Metric.closedBall j.val.val (r j) ⊆ Ω.val ∧
        ContDiff ℝ ∞ (η j) ∧ HasCompactSupport (η j) ∧
        tsupport (η j) ⊆ Metric.ball j.val.val (r j)) ∧
      (∑ j : t, η j) = ψ := by
  classical
  have hballs (x : tsupport ψ) : ∃ r : ℝ, 0 < r ∧ Metric.closedBall x.val r ⊆ Ω.val := by
    obtain ⟨ε, hε, hinc⟩ := Metric.isOpen_iff.mp Ω.property x.val (hs x.property)
    exact ⟨ε / 2, half_pos hε,
      (Metric.closedBall_subset_ball (by linarith only [hε])).trans hinc⟩
  choose r hr hclosed using hballs
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover
    (fun x : tsupport ψ => Metric.ball x.val (r x)) (fun _ => Metric.isOpen_ball)
    (fun x hx => mem_iUnion_of_mem ⟨x, hx⟩ (Metric.mem_ball_self (hr ⟨x, hx⟩)))
  let U : t → Set (Domain n) := fun j => Metric.ball j.val.val (r j.val)
  have hcover : tsupport ψ ⊆ ⋃ j : t, U j := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion_of_mem ⟨j, hj⟩ hxj
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, Domain n) (isClosed_tsupport ψ) U (fun _ => Metric.isOpen_ball) hcover
  let η : t → Domain n → E := fun j x => ρ j x • ψ x
  have hη (j : t) : ContDiff ℝ ∞ (η j) := (ρ j).contMDiff.contDiff.smul hψ
  have hcη (j : t) : HasCompactSupport (η j) := hc.smul_left
  have hsη (j : t) : tsupport (η j) ⊆ U j := (tsupport_smul_subset_left (ρ j) ψ).trans (hρ j)
  have hsum : (∑ j : t, η j) = ψ := by
    funext x
    simp only [Finset.sum_apply, η]
    rw [← Finset.sum_smul]
    by_cases hx : x ∈ tsupport ψ
    · have H := ρ.sum_eq_one hx
      rw [finsum_eq_sum_of_fintype] at H
      rw [H, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]
  exact ⟨t, fun j => r j.val, η,
    fun j => ⟨hr j.val, hclosed j.val, hη j, hcη j, hsη j⟩, hsum⟩

private theorem outerTest_finite_ball_decomposition {n q : ℕ}
    (Ω : OpenDomain n) (ψ : Domain n → Ambient q)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω.val) :
    ∃ t : Finset (tsupport ψ), ∃ r : t → ℝ, ∃ η : t → Domain n → Ambient q,
      (∀ j : t, 0 < r j ∧ Metric.closedBall j.val.val (r j) ⊆ Ω.val ∧
        ContDiff ℝ ∞ (η j) ∧ HasCompactSupport (η j) ∧
        tsupport (η j) ⊆ Metric.ball j.val.val (r j)) ∧
      (∑ j : t, η j) = ψ :=
  outerTest_finite_ball_decomposition_generic Ω ψ hψ hc hs

private theorem outerTest_fderiv_sum_generic {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
    (η : ι → Domain n → E) (hη : ∀ j, ContDiff ℝ ∞ (η j))
    (ψ : Domain n → E) (hsum : (∑ j : ι, η j) = ψ) (x : Domain n) :
    (∑ j : ι, fderiv ℝ (η j) x) = fderiv ℝ ψ x := by
  classical
  have H := fderiv_sum (u := Finset.univ) (A := η) (x := x)
    (fun j _ => (hη j).differentiable (by simp) x)
  rw [hsum] at H
  exact H.symm

private theorem outerTest_fderiv_sum {n q : ℕ} {ι : Type*} [Fintype ι]
    (η : ι → Domain n → Ambient q) (hη : ∀ j, ContDiff ℝ ∞ (η j))
    (ψ : Domain n → Ambient q) (hsum : (∑ j : ι, η j) = ψ)
    (x : Domain n) (v : Domain n) :
    (∑ j : ι, fderiv ℝ (η j) x v) = fderiv ℝ ψ x v := by
  have H := outerTest_fderiv_sum_generic η hη ψ hsum x
  simpa only [sum_apply] using congrArg (fun L : Domain n →L[ℝ] Ambient q => L v) H

private theorem IsLocallyEnergyMinimizing.outerVariation_weakEquation_ball {n q : ℕ}
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val)
    {Q : Ambient q → Ambient q} (hQ : ContDiff ℝ ∞ Q)
    (L K : ℝ) (hDQ : ∀ z, ‖fderiv ℝ Q z‖ ≤ L)
    (hD2Q : ∀ z, ‖fderiv ℝ (fderiv ℝ Q) z‖ ≤ K)
    {ρ : ℝ} (hρ : 0 < ρ) (hρbase : ρ ≤ tubularBaseRadius q N)
    (hQeq : ∀ z : tubularTube q N, Metric.infDist z.val N.carrierSet < ρ →
      Q z.val = (tubularProjection q N z).val)
    {ψ : Domain n → Ambient q} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Metric.ball a R) :
    IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) (Metric.ball a R) ∧
    IntegrableOn (fun x => inner ℝ
      (∑ i : Fin n, fderiv ℝ (fderiv ℝ Q) (u x) (Du x i) (Du x i)) (ψ x)) (Metric.ball a R) ∧
    (∫ x in Metric.ball a R, ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      -(∫ x in Metric.ball a R, inner ℝ
        (∑ i : Fin n, fderiv ℝ (fderiv ℝ Q) (u x) (Du x i) (Du x i)) (ψ x)) := by
  have hfix (p : N.Carrier) : Q p.val = p.val := by
    obtain ⟨hp, _⟩ := (tubularProjection_characterization q N).2.2.2.1 p
    exact (outerExtension_target_jets N ρ hρ Q hQ hQeq p hp).1
  have hmap (z : Ambient q) (hz : Metric.infDist z N.carrierSet < ρ) : Q z ∈ N.carrierSet := by
    have hzbase : z ∈ tubularTube q N := by
      change Metric.infDist z N.carrierSet < 2 * tubularBaseRadius q N
      exact hz.trans_le (by linarith only [hρ, hρbase])
    rw [hQeq ⟨z, hzbase⟩ hz]
    exact (tubularProjection q N ⟨z, hzbase⟩).property
  have htan := hu.projected_gradient_fixed N hN Q hQ L hDQ hfix
  have htanball : ∀ᵐ x ∂volume.restrict (Metric.ball a R),
      ∀ i : Fin n, fderiv ℝ Q (u x) (Du x i) = Du x i :=
    ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_closedBall.trans hball) htan
  have hfirst := hmin.projected_outerVariation_first_integral_zero hu hN hR hball
    hQ L K hDQ hD2Q hρ (fun p hp => hfix ⟨p, hp⟩) hmap htanball hψ hc hs
  have hF := hu.outer_curvature_locallyIntegrable hQ K hD2Q
  have hpair := hu.outer_test_pairings_integrable hF hψ hc
    (hs.trans (Metric.ball_subset_closedBall.trans hball))
  have hleft : IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) (Metric.ball a R) := hpair.1.restrict
  have hright : IntegrableOn (fun x => inner ℝ
      (∑ i : Fin n, fderiv ℝ (fderiv ℝ Q) (u x) (Du x i) (Du x i)) (ψ x)) (Metric.ball a R) :=
    hpair.2.restrict
  refine ⟨hleft, hright, ?_⟩
  have hNball : TakesValuesIn N (ballDomain a R) u :=
    ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_closedBall.trans hball) hN
  have heq : (fun x => ∑ i : Fin n, inner ℝ (Du x i)
      (fderiv ℝ Q (u x) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) +
        fderiv ℝ (fderiv ℝ Q) (u x) (ψ x) (Du x i))) =ᵐ[volume.restrict (Metric.ball a R)]
      (fun x => (∑ i : Fin n, inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) +
        inner ℝ (∑ i : Fin n, fderiv ℝ (fderiv ℝ Q) (u x) (Du x i) (Du x i)) (ψ x)) := by
    filter_upwards [hNball, htanball] with x hxN hxTan
    let p : N.Carrier := ⟨u x, hxN⟩
    obtain ⟨hp, _⟩ := (tubularProjection_characterization q N).2.2.2.1 p
    have hj := outerExtension_target_jets N ρ hρ Q hQ hQeq p hp
    have hDj (i : Fin n) :
        inner ℝ (Du x i) (fderiv ℝ Q (u x) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
          inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
      have hsD : inner ℝ (Du x i)
          (fderiv ℝ Q (u x) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
          inner ℝ (fderiv ℝ ψ x (EuclideanSpace.single i 1)) (fderiv ℝ Q (u x) (Du x i)) := by
        rw [hj.2.1]
        exact outerProjection_derivative_symmetric q N ⟨p.val, hp⟩ (Du x i)
          (fderiv ℝ ψ x (EuclideanSpace.single i 1))
      rw [hsD, hxTan i, real_inner_comm]
    have hHj (i : Fin n) :
        inner ℝ (Du x i) (fderiv ℝ (fderiv ℝ Q) (u x) (ψ x) (Du x i)) =
          inner ℝ (fderiv ℝ (fderiv ℝ Q) (u x) (Du x i) (Du x i)) (ψ x) := by
      rw [hj.2.2, outerProjection_hessian_argument_symmetry q N ⟨p.val, hp⟩ (ψ x) (Du x i),
        outerProjection_hessian_symmetric q N ⟨p.val, hp⟩ (Du x i) (Du x i) (ψ x),
        real_inner_comm]
    calc
      _ = ∑ i : Fin n, (inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) +
          inner ℝ (fderiv ℝ (fderiv ℝ Q) (u x) (Du x i) (Du x i)) (ψ x)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [inner_add_right, hDj i, hHj i]
      _ = _ := by rw [Finset.sum_add_distrib, sum_inner]
  have hz := (integral_congr_ae heq).symm.trans hfirst.2
  rw [integral_add hleft hright] at hz
  exact eq_neg_of_add_eq_zero_left hz


private theorem outer_left_setIntegral_eq_integral {n q : ℕ}
    (Du : Domain n → Gradient n q) (ψ : Domain n → Ambient q)
    {s : Set (Domain n)} (hs : tsupport ψ ⊆ s) :
    (∫ x in s, ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
    ∫ x, ∑ i : Fin n,
      inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hD : fderiv ℝ ψ x = 0 := fderiv_of_notMem_tsupport ℝ (fun h => hx (hs h))
  simp only [hD, zero_apply, inner_zero_right, Finset.sum_const_zero]

private theorem outer_right_setIntegral_eq_integral {n q : ℕ}
    (F ψ : Domain n → Ambient q) {s : Set (Domain n)} (hs : tsupport ψ ⊆ s) :
    (∫ x in s, inner ℝ (F x) (ψ x)) = ∫ x, inner ℝ (F x) (ψ x) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), inner_zero_right]

private theorem MemW12Loc.outer_equation_of_ball_tests {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {F : Domain n → Ambient q}
    (hF : LocallyIntegrableOn F Ω.val volume)
    (hball : ∀ (a : Domain n) (R : ℝ), 0 < R → Metric.closedBall a R ⊆ Ω.val →
      ∀ ψ : Domain n → Ambient q, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Metric.ball a R →
        (∫ x in Metric.ball a R, ∑ i : Fin n,
          inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
          -(∫ x in Metric.ball a R, inner ℝ (F x) (ψ x))) :
    ∀ ψ : Domain n → Ambient q, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω.val →
      IntegrableOn (fun x => ∑ i : Fin n,
        inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) Ω.val ∧
      IntegrableOn (fun x => inner ℝ (F x) (ψ x)) Ω.val ∧
      (∫ x in Ω.val, ∑ i : Fin n,
        inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
        -(∫ x in Ω.val, inner ℝ (F x) (ψ x)) := by
  classical
  intro ψ hψ hc hs
  have hPair := hu.outer_test_pairings_integrable hF hψ hc hs
  refine ⟨hPair.1.integrableOn, hPair.2.integrableOn, ?_⟩
  obtain ⟨t, r, η, hparts, hsum⟩ := outerTest_finite_ball_decomposition Ω ψ hψ hc hs
  have hr (j : t) : 0 < r j := (hparts j).1
  have hclosed (j : t) : Metric.closedBall j.val.val (r j) ⊆ Ω.val := (hparts j).2.1
  have hη (j : t) : ContDiff ℝ ∞ (η j) := (hparts j).2.2.1
  have hcη (j : t) : HasCompactSupport (η j) := (hparts j).2.2.2.1
  have hsη (j : t) : tsupport (η j) ⊆ Metric.ball j.val.val (r j) := (hparts j).2.2.2.2
  have hsηΩ (j : t) : tsupport (η j) ⊆ Ω.val :=
    (hsη j).trans (Metric.ball_subset_closedBall.trans (hclosed j))
  have hDsum (x : Domain n) (i : Fin n) :
      (∑ j : t, fderiv ℝ (η j) x (EuclideanSpace.single i 1)) =
        fderiv ℝ ψ x (EuclideanSpace.single i 1) :=
    outerTest_fderiv_sum η hη ψ hsum x (EuclideanSpace.single i 1)
  have hLsum (x : Domain n) :
      (∑ j : t, ∑ i : Fin n, inner ℝ (Du x i)
        (fderiv ℝ (η j) x (EuclideanSpace.single i 1))) =
      ∑ i : Fin n, inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← inner_sum, hDsum]
  have hRsum (x : Domain n) :
      (∑ j : t, inner ℝ (F x) (η j x)) = inner ℝ (F x) (ψ x) := by
    rw [← inner_sum]
    have H := congrFun hsum x
    simpa only [Finset.sum_apply] using congrArg (fun v => inner ℝ (F x) v) H
  have hlocal (j : t) :
      (∫ x, ∑ i : Fin n, inner ℝ (Du x i)
        (fderiv ℝ (η j) x (EuclideanSpace.single i 1))) =
      -(∫ x, inner ℝ (F x) (η j x)) := by
    have H := hball j.val.val (r j) (hr j) (hclosed j)
      (η j) (hη j) (hcη j) (hsη j)
    rw [outer_left_setIntegral_eq_integral Du (η j) (hsη j),
      outer_right_setIntegral_eq_integral F (η j) (hsη j)] at H
    exact H
  have hEach (j : t) := hu.outer_test_pairings_integrable hF (hη j) (hcη j) (hsηΩ j)
  rw [outer_left_setIntegral_eq_integral Du ψ hs, outer_right_setIntegral_eq_integral F ψ hs]
  calc
    (∫ x, ∑ i : Fin n, inner ℝ (Du x i)
      (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      ∫ x, ∑ j : t, ∑ i : Fin n, inner ℝ (Du x i)
        (fderiv ℝ (η j) x (EuclideanSpace.single i 1)) := by
          congr 1
          funext x
          exact (hLsum x).symm
    _ = ∑ j : t, ∫ x, ∑ i : Fin n, inner ℝ (Du x i)
        (fderiv ℝ (η j) x (EuclideanSpace.single i 1)) :=
      integral_finsetSum _ (fun j _ => (hEach j).1)
    _ = ∑ j : t, -(∫ x, inner ℝ (F x) (η j x)) :=
      Finset.sum_congr rfl (fun j _ => hlocal j)
    _ = -(∫ x, ∑ j : t, inner ℝ (F x) (η j x)) := by
      rw [Finset.sum_neg_distrib, integral_finsetSum _ (fun j _ => (hEach j).2)]
    _ = -(∫ x, inner ℝ (F x) (ψ x)) := by
      congr 1
      congr 1
      funext x
      exact hRsum x
end HarmonicMaps
namespace HarmonicMaps.Providers.OuterVariation
theorem result (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
  let S : Set ℝ := {k | ∃ p : N.Carrier, ∃ hp : p.val ∈ tubularTube q N,
    k = ‖tubularProjectionSecondDerivative q N ⟨p.val, hp⟩‖}
  ∀ (n : ℕ) (hn : 2 ≤ n) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
    MemW12Loc Ω u Du → TakesValuesIn N Ω u →
    IsLocallyEnergyMinimizing N Ω u Du →
    ∃ F : Domain n → Ambient q,
      LocallyIntegrableOn F Ω.val volume ∧
      (∀ᵐ x ∂volume.restrict Ω.val, ∃ hx : u x ∈ tubularTube q N,
        F x = ∑ i : Fin n,
          tubularProjectionSecondDerivative q N ⟨u x, hx⟩ (Du x i) (Du x i) ∧
        ‖F x‖ ≤ sSup S * hsNormSq (Du x)) ∧
      ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
        HasCompactSupport ψ → tsupport ψ ⊆ Ω.val →
        IntegrableOn (fun x => ∑ i : Fin n,
          inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) Ω.val ∧
        IntegrableOn (fun x => inner ℝ (F x) (ψ x)) Ω.val ∧
        (∫ x in Ω.val, ∑ i : Fin n,
          inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
          -(∫ x in Ω.val, inner ℝ (F x) (ψ x)) :=
by
  classical
  dsimp only
  intro n _hn Ω u Du hu hN hmin
  obtain ⟨ρ, hρ, hρbase, hsub, hOpen, hnearest, hfixed, hlocal, hD,
    hSne, hSbdd, hSnonneg, hSbound, Q, hQ, hQeq, C₁, C₂, hC₁, hC₂, hQD, hQH⟩ :=
    tubularProjection_complete q N
  let F : Domain n → Ambient q := fun x => ∑ i : Fin n,
    fderiv ℝ (fderiv ℝ Q) (u x) (Du x i) (Du x i)
  have hFlocal : LocallyIntegrableOn F Ω.val volume :=
    hu.outer_curvature_locallyIntegrable hQ C₂ hQH
  refine ⟨F, hFlocal, ?_, ?_⟩
  · filter_upwards [hN] with x hxN
    let p : N.Carrier := ⟨u x, hxN⟩
    obtain ⟨hp, _⟩ := (tubularProjection_characterization q N).2.2.2.1 p
    have hjet := outerExtension_target_jets N ρ hρ Q hQ hQeq p hp
    have hH : fderiv ℝ (fderiv ℝ Q) (u x) =
        tubularProjectionSecondDerivative q N ⟨u x, hp⟩ := hjet.2.2
    have hFormula : F x = ∑ i : Fin n,
        tubularProjectionSecondDerivative q N ⟨u x, hp⟩ (Du x i) (Du x i) := by
      dsimp only [F]
      rw [hH]
    refine ⟨hp, hFormula, ?_⟩
    rw [hFormula]
    exact outer_hessian_sum_norm_le _ _ _ (hSbound p hp)
  · apply hu.outer_equation_of_ball_tests hFlocal
    intro a R hR hball ψ hψ hc hs
    exact (hmin.outerVariation_weakEquation_ball hu hN hR hball hQ C₁ C₂
      hQD hQH hρ hρbase hQeq hψ hc hs).2.2

end HarmonicMaps.Providers.OuterVariation
end

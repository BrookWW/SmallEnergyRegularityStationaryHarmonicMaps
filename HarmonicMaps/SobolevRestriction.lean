module

public import HarmonicMaps.SobolevLemmas

/-!
# Restriction and zero data for weak Sobolev interfaces

Weak derivatives restrict to smaller open domains. Local Sobolev data give
finite Sobolev data on every ball whose closed ball is contained in the domain.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace HarmonicMaps

private theorem setIntegral_smul_eq_integral {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : OpenDomain n} {φ : Domain n → ℝ} (f : Domain n → E)
    (hsupport : tsupport φ ⊆ Ω.val) :
    (∫ x in Ω.val, φ x • f x) = ∫ x, φ x • f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hnot : x ∉ tsupport φ := fun hmem => hx (hsupport hmem)
  simp [image_eq_zero_of_notMem_tsupport hnot]

/-- Weak gradients restrict to smaller open domains. -/
theorem HasWeakGradient.mono {n q : ℕ} {Ω Ω' : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hDu : HasWeakGradient Ω u Du) (hsubset : Ω'.val ⊆ Ω.val) :
    HasWeakGradient Ω' u Du := by
  refine ⟨hDu.1.mono_set hsubset, fun i => (hDu.2.1 i).mono_set hsubset, ?_⟩
  intro i φ hφ hcompact hsupport
  have hderiv_support : tsupport (coordinateDerivative φ hφ i) ⊆ Ω'.val :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsupport
  have hidentity := hDu.2.2 i φ hφ hcompact (hsupport.trans hsubset)
  rw [setIntegral_smul_eq_integral u (hderiv_support.trans hsubset),
    setIntegral_smul_eq_integral (fun x => Du x i) (hsupport.trans hsubset)] at hidentity
  rw [setIntegral_smul_eq_integral u hderiv_support,
    setIntegral_smul_eq_integral (fun x => Du x i) hsupport]
  exact hidentity

/-- Local Sobolev membership restricts to smaller open domains. -/
theorem MemW12Loc.mono {n q : ℕ} {Ω Ω' : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hsubset : Ω'.val ⊆ Ω.val) :
    MemW12Loc Ω' u Du := by
  refine ⟨hu.1.mono hsubset, ?_, ?_⟩
  · intro K hK hKsubset
    exact hu.2.1 K hK (hKsubset.trans hsubset)
  · intro i K hK hKsubset
    exact hu.2.2 i K hK (hKsubset.trans hsubset)

/-- Finite Sobolev membership implies local Sobolev membership. -/
theorem MemW12.to_memW12Loc {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) : MemW12Loc Ω u Du := by
  refine ⟨hu.1, ?_, ?_⟩
  · intro K _hK hsubset
    exact MemLp.mono_measure (Measure.restrict_mono_set volume hsubset) hu.2.1
  · intro i K _hK hsubset
    exact MemLp.mono_measure (Measure.restrict_mono_set volume hsubset) (hu.2.2 i)

/-- Local Sobolev data are finite on a ball with closed ball contained in the domain. -/
theorem MemW12Loc.memW12_ball {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) {a : Domain n} {r : ℝ}
    (hclosed : Metric.closedBall a r ⊆ Ω.val) :
    MemW12 (ballDomain a r) u Du := by
  have hball : (ballDomain a r).val ⊆ Ω.val :=
    Metric.ball_subset_closedBall.trans hclosed
  have hmeasure : volume.restrict (Metric.ball a r) ≤
      volume.restrict (Metric.closedBall a r) :=
    Measure.restrict_mono_set volume Metric.ball_subset_closedBall
  refine ⟨hu.1.mono hball, ?_, ?_⟩
  · exact MemLp.mono_measure hmeasure
      (hu.2.1 (Metric.closedBall a r) (isCompact_closedBall a r) hclosed)
  · intro i
    exact MemLp.mono_measure hmeasure
      (hu.2.2 i (Metric.closedBall a r) (isCompact_closedBall a r) hclosed)

/-- The zero map has the zero weak gradient on any open domain. -/
theorem HasWeakGradient.zero {n q : ℕ} (Ω : OpenDomain n) :
    HasWeakGradient Ω (0 : Domain n → Ambient q) (0 : Domain n → Gradient n q) := by
  refine ⟨locallyIntegrableOn_zero, ?_, ?_⟩
  · intro i
    exact locallyIntegrableOn_zero
  · intro i φ _hφ _hcompact _hsupport
    simp

/-- The zero map has finite Sobolev membership, including on unbounded domains. -/
theorem MemW12.zero {n q : ℕ} (Ω : OpenDomain n) :
    MemW12 Ω (0 : Domain n → Ambient q) (0 : Domain n → Gradient n q) := by
  refine ⟨HasWeakGradient.zero Ω, MemLp.zero, ?_⟩
  intro i
  exact MemLp.zero

/-- The zero map is approximated by the constant sequence of zero smooth maps. -/
theorem HasZeroBoundaryValues.zero {n q : ℕ} (Ω : OpenDomain n) :
    HasZeroBoundaryValues Ω (0 : Domain n → Ambient q)
      (0 : Domain n → Gradient n q) := by
  refine ⟨MemW12.zero Ω, fun _ => 0, fun _ => contDiff_const, ?_, ?_, ?_⟩
  · intro k
    exact ⟨HasCompactSupport.zero, by simp⟩
  · simp
  · intro i
    simp [coordinateDerivative]

/-- Every ambient map has zero Sobolev boundary difference with itself. -/
theorem HasZeroBoundaryDifference.self {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) :
    HasZeroBoundaryDifference Ω u Du u Du := by
  have hgradient : (fun x i => Du x i - Du x i) =
      (0 : Domain n → Gradient n q) := by
    funext x i
    simp
  unfold HasZeroBoundaryDifference
  rw [sub_self, hgradient]
  exact HasZeroBoundaryValues.zero Ω

end HarmonicMaps

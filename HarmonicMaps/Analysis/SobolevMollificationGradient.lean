module

public import HarmonicMaps.Analysis.MollificationTests
public import HarmonicMaps.Analysis.InteriorMollification
public import HarmonicMaps.SobolevLemmas

/-!
# Classical derivatives of mollified weak Sobolev maps

The reflected kernel is an admissible weak test whenever its translated
support remains in the open domain. Integration by parts identifies the
classical derivative of the smooth convolution with the convolution of the
same displayed weak gradient. Zero extension is used only for integrable data.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff Convolution Topology

namespace HarmonicMaps

noncomputable section

/-- The literal zero extension of a map restricted to an open domain. -/
def zeroExtensionOn {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) : Domain n → Ambient q := Ω.val.indicator u

theorem zeroExtensionOn_integrable {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val) :
    Integrable (zeroExtensionOn Ω u) volume :=
  hu.integrable_indicator Ω.property.measurableSet

theorem kernel_smul_zeroExtensionOn_integrable {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (x : Domain n) :
    Integrable (fun z => χ z • zeroExtensionOn Ω u (x - z)) volume :=
  (hcχ.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hχ.continuous
    (zeroExtensionOn_integrable Ω u hu).locallyIntegrable x).integrable

theorem kernelConvolution_contDiff {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    ContDiff ℝ ∞ (fun x => ∫ z, χ z • zeroExtensionOn Ω u (x - z)) :=
  hcχ.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hχ
    (zeroExtensionOn_integrable Ω u hu).locallyIntegrable

/-- Positive-radius Euclidean convolution of the literal domain zero extension. -/
def euclideanMollification {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (_hu : IntegrableOn u Ω.val)
    (h : PositiveRadius) (x : Domain n) : Ambient q :=
  ∫ z, scaledMollifierKernel n h z • zeroExtensionOn Ω u (x - z)

theorem euclideanMollification_integrable {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val)
    (h : PositiveRadius) (x : Domain n) :
    Integrable (fun z => scaledMollifierKernel n h z •
      zeroExtensionOn Ω u (x - z)) volume :=
  kernel_smul_zeroExtensionOn_integrable Ω u hu
    (scaledMollifierKernel_contDiff n h) (scaledMollifierKernel_hasCompactSupport n h) x

theorem euclideanMollification_contDiff {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val) (h : PositiveRadius) :
    ContDiff ℝ ∞ (euclideanMollification Ω u hu h) :=
  kernelConvolution_contDiff Ω u hu (scaledMollifierKernel_contDiff n h)
    (scaledMollifierKernel_hasCompactSupport n h)

theorem MemW12.integrable_domain {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (hΩ : volume Ω.val ≠ ⊤) : IntegrableOn u Ω.val := by
  letI : IsFiniteMeasure (volume.restrict Ω.val) := isFiniteMeasure_restrict.mpr hΩ
  exact hu.2.1.integrable (by norm_num)

theorem MemW12.column_integrable_domain {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (hΩ : volume Ω.val ≠ ⊤) (i : Fin n) :
    IntegrableOn (fun x => Du x i) Ω.val := by
  letI : IsFiniteMeasure (volume.restrict Ω.val) := isFiniteMeasure_restrict.mpr hΩ
  exact (hu.2.2 i).integrable (by norm_num)

theorem MemW12.integrable_ball {n q : ℕ} {a : Domain n} {R : ℝ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) : IntegrableOn u (Metric.ball a R) :=
  hu.integrable_domain measure_ball_ne_top

theorem MemW12.column_integrable_ball {n q : ℕ} {a : Domain n} {R : ℝ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) (i : Fin n) :
    IntegrableOn (fun x => Du x i) (Metric.ball a R) :=
  hu.column_integrable_domain measure_ball_ne_top i

/-- Domain L2 data give global L2 zero extension without a boundary derivative claim. -/
theorem MemW12.zeroExtensionOn_memLp {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) : MemLp (zeroExtensionOn Ω u) 2 volume :=
  (memLp_indicator_iff_restrict Ω.property.measurableSet).mpr hu.2.1

theorem MemW12.column_zeroExtensionOn_memLp {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (i : Fin n) :
    MemLp (zeroExtensionOn Ω (fun x => Du x i)) 2 volume :=
  (memLp_indicator_iff_restrict Ω.property.measurableSet).mpr (hu.2.2 i)

private theorem kernelConvolution_fderiv_apply {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (x v : Domain n) :
    fderiv ℝ (fun x => ∫ z, χ z • zeroExtensionOn Ω u (x - z)) x v =
      ∫ z, fderiv ℝ χ (x - z) v • zeroExtensionOn Ω u z := by
  let L : ℝ →L[ℝ] Ambient q →L[ℝ] Ambient q := ContinuousLinearMap.lsmul ℝ ℝ
  have hzero := (zeroExtensionOn_integrable Ω u hu).locallyIntegrable
  have hderiv := hcχ.hasFDerivAt_convolution_right L.flip hzero
    (hχ.of_le (by simp)) x
  rw [convolution_flip] at hderiv
  change fderiv ℝ (χ ⋆[L, volume] zeroExtensionOn Ω u) x v = _
  rw [hderiv.fderiv,
    convolution_precompR_apply L.flip hzero (hcχ.fderiv ℝ)
      (hχ.continuous_fderiv (by simp)) x v]
  rfl

/-- Both weak integration-by-parts pairings for the reflected kernel are integrable. -/
theorem HasWeakGradient.kernelConvolution_pairings_integrable {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : HasWeakGradient Ω u Du)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (x : Domain n) (hSample : ∀ y ∈ tsupport χ, x - y ∈ Ω.val) (i : Fin n) :
    IntegrableOn (fun z => fderiv ℝ χ (x - z) (EuclideanSpace.single i 1) • u z)
      Ω.val ∧ IntegrableOn (fun z => χ (x - z) • Du z i) Ω.val := by
  have hψ := translatedKernelTest_contDiff hχ x
  have hcψ := translatedKernelTest_hasCompactSupport hcχ x
  have hsψ := translatedKernelTest_tsupport_subset Ω x hSample
  constructor
  · apply (hu.integrable_test_derivative i hψ hcψ hsψ).neg.congr_fun _
      Ω.property.measurableSet
    intro z _
    change -(coordinateDerivative (translatedKernelTest χ x) hψ i z • u z) = _
    rw [translatedKernelTest_coordinateDerivative hχ, neg_smul, neg_neg]
  · exact hu.integrable_test_gradient i hψ hcψ hsψ

/-- The genuine weak test identity gives the classical convolution derivative. -/
theorem HasWeakGradient.kernelConvolution_coordinateDerivative {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : HasWeakGradient Ω u Du)
    (hInt : IntegrableOn u Ω.val) {χ : Domain n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (x : Domain n)
    (hSample : ∀ y ∈ tsupport χ, x - y ∈ Ω.val) (i : Fin n) :
    fderiv ℝ (fun x => ∫ z, χ z • zeroExtensionOn Ω u (x - z)) x
      (EuclideanSpace.single i 1) =
      ∫ z, χ z • zeroExtensionOn Ω (fun z => Du z i) (x - z) := by
  let ψ := translatedKernelTest χ x
  have hψ : ContDiff ℝ ∞ ψ := translatedKernelTest_contDiff hχ x
  have hcψ : HasCompactSupport ψ := translatedKernelTest_hasCompactSupport hcχ x
  have hsψ : tsupport ψ ⊆ Ω.val := translatedKernelTest_tsupport_subset Ω x hSample
  have hIBP := hu.2.2 i ψ hψ hcψ hsψ
  have hDerivative : (∫ z in Ω.val,
      fderiv ℝ χ (x - z) (EuclideanSpace.single i 1) • u z) =
      ∫ z in Ω.val, χ (x - z) • Du z i := by
    apply neg_injective
    calc
      -(∫ z in Ω.val, fderiv ℝ χ (x - z) (EuclideanSpace.single i 1) • u z) =
          ∫ z in Ω.val, coordinateDerivative ψ hψ i z • u z := by
        simp only [ψ, translatedKernelTest_coordinateDerivative hχ, neg_smul, integral_neg]
      _ = -(∫ z in Ω.val, χ (x - z) • Du z i) := hIBP
  calc
    fderiv ℝ (fun x => ∫ z, χ z • zeroExtensionOn Ω u (x - z)) x
        (EuclideanSpace.single i 1) =
        ∫ z, fderiv ℝ χ (x - z) (EuclideanSpace.single i 1) • zeroExtensionOn Ω u z :=
      kernelConvolution_fderiv_apply Ω u hInt hχ hcχ x _
    _ = ∫ z in Ω.val, fderiv ℝ χ (x - z) (EuclideanSpace.single i 1) • u z := by
      simp only [zeroExtensionOn, ← indicator_smul]
      exact integral_indicator Ω.property.measurableSet
    _ = ∫ z in Ω.val, χ (x - z) • Du z i := hDerivative
    _ = ∫ z, χ (x - z) • zeroExtensionOn Ω (fun z => Du z i) z := by
      simp only [zeroExtensionOn, ← indicator_smul]
      exact (integral_indicator Ω.property.measurableSet).symm
    _ = ∫ z, χ z • zeroExtensionOn Ω (fun z => Du z i) (x - z) := by
      rw [← integral_sub_left_eq_self
        (fun z => χ z • zeroExtensionOn Ω (fun z => Du z i) (x - z)) volume x]
      simp only [sub_sub_cancel]

/-- Finite Sobolev data make the convolved weak-gradient integrand integrable. -/
theorem MemW12.euclideanMollification_gradientIntegrand_integrable {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12 Ω u Du)
    (hΩ : volume Ω.val ≠ ⊤) (h : PositiveRadius) (x : Domain n) (i : Fin n) :
    Integrable (fun z => scaledMollifierKernel n h z •
      zeroExtensionOn Ω (fun z => Du z i) (x - z)) volume :=
  euclideanMollification_integrable Ω (fun z => Du z i)
    (hu.column_integrable_domain hΩ i) h x

/-- The classical coordinate derivative on any admissible interior kernel support. -/
theorem MemW12.euclideanMollification_coordinateDerivative {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12 Ω u Du)
    (hΩ : volume Ω.val ≠ ⊤) (h : PositiveRadius) (x : Domain n)
    (hSample : ∀ y ∈ tsupport (scaledMollifierKernel n h), x - y ∈ Ω.val)
    (i : Fin n) :
    coordinateDerivative (euclideanMollification Ω u (hu.integrable_domain hΩ) h)
      (euclideanMollification_contDiff Ω u (hu.integrable_domain hΩ) h) i x =
      ∫ z, scaledMollifierKernel n h z •
        zeroExtensionOn Ω (fun z => Du z i) (x - z) :=
  hu.1.kernelConvolution_coordinateDerivative (hu.integrable_domain hΩ)
    (scaledMollifierKernel_contDiff n h) (scaledMollifierKernel_hasCompactSupport n h)
    x hSample i

/-- The same derivative formula on an arbitrary open Euclidean ball. -/
theorem MemW12.euclideanMollification_ball_coordinateDerivative {n q : ℕ}
    {a : Domain n} {R : ℝ} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hu : MemW12 (ballDomain a R) u Du)
    (h : PositiveRadius) (x : Domain n)
    (hSample : ∀ y ∈ tsupport (scaledMollifierKernel n h), x - y ∈ Metric.ball a R)
    (i : Fin n) :
    coordinateDerivative
      (euclideanMollification (ballDomain a R) u hu.integrable_ball h)
      (euclideanMollification_contDiff (ballDomain a R) u hu.integrable_ball h) i x =
      ∫ z, scaledMollifierKernel n h z •
        zeroExtensionOn (ballDomain a R) (fun z => Du z i) (x - z) :=
  hu.euclideanMollification_coordinateDerivative measure_ball_ne_top h x hSample i

/-- At each source interior point the literal integral has an ordinary derivative. -/
theorem sourceMollification_differentiableAt {n q : ℕ}
    (u : Domain n → Ambient q) (hInt : IntegrableOn u (Metric.ball (0 : Domain n) 1))
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    DifferentiableAt ℝ (fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (x - h.val • y)) x := by
  have hlocal : (fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (x - h.val • y)) =ᶠ[𝓝 x]
      zeroExtendedMollification u hInt h := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    exact sourceMollification_eq_zeroExtended u hInt h hh z hz
  exact (((zeroExtendedMollification_contDiff u hInt h).differentiable (by simp)).differentiableAt).congr_of_eventuallyEq hlocal

/-- The smooth unit-ball convolution auxiliary has the source gradient formula
throughout the proved interior neighborhood. -/
theorem MemW12.zeroExtendedMollification_coordinateDerivative {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) (i : Fin n) :
    coordinateDerivative (zeroExtendedMollification u hu.integrable_unitBall h)
      (zeroExtendedMollification_contDiff u hu.integrable_unitBall h) i x =
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • Du (x - h.val • y) i := by
  have hDuInt := hu.column_integrable_ball i
  calc
    coordinateDerivative (zeroExtendedMollification u hu.integrable_unitBall h)
        (zeroExtendedMollification_contDiff u hu.integrable_unitBall h) i x =
        ∫ z, scaledMollifierKernel n h z •
          unitBallZeroExtension (fun z => Du z i) (x - z) :=
      hu.1.kernelConvolution_coordinateDerivative hu.integrable_unitBall
        (scaledMollifierKernel_contDiff n h) (scaledMollifierKernel_hasCompactSupport n h)
        x (scaledMollifierKernel_sampling_unitBall h hh hx) i
    _ = zeroExtendedMollification (fun z => Du z i) hDuInt h x := rfl
    _ = ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • Du (x - h.val • y) i :=
      (sourceMollification_eq_zeroExtended (fun z => Du z i) hDuInt h hh x hx).symm

/-- The classical derivative of the source integral is the mollification of its
actual displayed weak-gradient column. -/
theorem MemW12.sourceMollification_coordinateDerivative {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) (i : Fin n) :
    fderiv ℝ (fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (x - h.val • y)) x (EuclideanSpace.single i 1) =
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • Du (x - h.val • y) i := by
  have hInt := hu.integrable_unitBall
  have hDuInt := hu.column_integrable_ball i
  have hlocal : (fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (x - h.val • y)) =ᶠ[𝓝 x]
      zeroExtendedMollification u hInt h := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    exact sourceMollification_eq_zeroExtended u hInt h hh z hz
  calc
    fderiv ℝ (fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - h.val • y)) x (EuclideanSpace.single i 1) =
        fderiv ℝ (zeroExtendedMollification u hInt h) x (EuclideanSpace.single i 1) :=
      congrArg (fun L : Domain n →L[ℝ] Ambient q => L (EuclideanSpace.single i 1))
        hlocal.fderiv_eq
    _ = ∫ z, scaledMollifierKernel n h z •
        unitBallZeroExtension (fun z => Du z i) (x - z) :=
      hu.1.kernelConvolution_coordinateDerivative hInt (scaledMollifierKernel_contDiff n h)
        (scaledMollifierKernel_hasCompactSupport n h) x
        (scaledMollifierKernel_sampling_unitBall h hh hx) i
    _ = zeroExtendedMollification (fun z => Du z i) hDuInt h x := rfl
    _ = ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • Du (x - h.val • y) i :=
      (sourceMollification_eq_zeroExtended (fun z => Du z i) hDuInt h hh x hx).symm

/-- The source derivative integral is a genuine integrable pairing. -/
theorem MemW12.sourceMollification_gradientIntegrand_integrable {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) (i : Fin n) :
    IntegrableOn (fun y => fixedMollifierKernel n y • Du (x - h.val • y) i)
      (Metric.ball (0 : Domain n) 1) :=
  sourceMollification_integrableOn (fun z => Du z i) (hu.column_integrable_ball i)
    h hh x hx

end
end HarmonicMaps

end

module

public import HarmonicMaps.Analysis.PoissonRadialEulerIntegral
public import HarmonicMaps.Analysis.ClosedBallRadialPrimitive

/-!
# Continuous Euler derivatives on a closed positive collar

An actual smooth harmonic map and a continuous completion of its ordered
second angular derivative sum determine a continuous Euler derivative on the
closed outer collar. The construction uses the weighted radial identity with
an interior anchor, so continuity includes arbitrary approaches to the sphere.
This conditional calculus theorem does not construct the angular completion.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff BigOperators Topology

namespace HarmonicMaps

/-- Continuous closed-ball data for the actual second angular derivative sum
produce a continuous completion of the Euler derivative on the closed outer
collar. The prescribed coordinate formula identifies the same generators in
the angular datum and the radial integral identity. -/
theorem poisson_euler_continuous_closedCollar_of_angularSum {n q : ℕ}
    (A : Fin n → Fin n → (Domain n →L[ℝ] Domain n))
    (hA : ∀ i j (x : Domain n), A i j x =
      x i • EuclideanSpace.single j 1 - x j • EuclideanSpace.single i 1)
    (R : PositiveRadius) (f : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball (0 : Domain n) R.val))
    (hh : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian f x = 0)
    (w : Metric.closedBall (0 : Domain n) R.val → Ambient q)
    (hw : Continuous w)
    (heq : ∀ (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val),
      w ⟨x, Metric.ball_subset_closedBall hx⟩ =
        ∑ i : Fin n, ∑ j : Fin n,
          fderiv ℝ (fun y => fderiv ℝ f y (A i j y)) x (A i j x)) :
    ∃ e : {x : Domain n // R.val / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ R.val} → Ambient q,
      Continuous e ∧ ∀ x, ‖x.val‖ < R.val → e x = fderiv ℝ f x.val x.val := by
  obtain ⟨B, hB, hradial⟩ := poisson_weighted_radialEuler_integral n
  have hAB : A = B := by
    funext i j
    apply ContinuousLinearMap.ext
    intro x
    exact (hA i j x).trans ((hB i j).2 x).symm
  subst B
  let a : ℝ := R.val / 2
  have ha : 0 < a := half_pos R.property
  have haR : a < R.val := half_lt_self R.property
  let S := Metric.sphere (0 : Domain n) 1
  let C := {x : Domain n // a ≤ ‖x‖ ∧ ‖x‖ ≤ R.val}
  let k : ℤ := (n : ℤ) - 2
  let E : Domain n → Ambient q := fun x => fderiv ℝ f x x
  let L₂ : Domain n → Ambient q := fun x =>
    ∑ i : Fin n, ∑ j : Fin n,
      fderiv ℝ (fun y => fderiv ℝ f y (A i j y)) x (A i j x)
  have htheta (θ : S) : ‖θ.val‖ = 1 := by
    simpa only [S, Metric.mem_sphere, dist_zero_right] using θ.property
  have hanchor (θ : S) : a • θ.val ∈ Metric.ball (0 : Domain n) R.val := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ha.le,
      htheta, mul_one]
    exact haR
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ f) (Metric.ball (0 : Domain n) R.val) :=
    hf.fderiv_of_isOpen Metric.isOpen_ball (by simp)
  have hE : ContinuousOn E (Metric.ball (0 : Domain n) R.val) :=
    (hDf.clm_apply contDiffOn_id).continuousOn
  have hanchorCont : Continuous (fun θ : S => E (a • θ.val)) :=
    hE.comp_continuous (continuous_subtype_val.const_smul a) hanchor
  obtain ⟨J, _hJ, hJvalue, hprimitive⟩ :=
    closedBall_radial_primitive_joint_continuous R a ha haR.le ((n : ℤ) - 3) w hw
  let G : S × Icc a R.val → Ambient q := fun p =>
    p.2.val ^ (-k) •
      (a ^ k • E (a • p.1.val) - (1 / 2 : ℝ) • (∫ s in a..p.2.val, J p.1 s))
  have hG : Continuous G := by
    have hp : Continuous (fun p : S × Icc a R.val => p.2.val ^ (-k)) :=
      (continuous_subtype_val.comp continuous_snd).zpow₀ (-k)
        (fun p => Or.inl (ha.trans_le p.2.property.1).ne')
    exact hp.smul (((hanchorCont.comp continuous_fst).const_smul (a ^ k)).sub
        (hprimitive.const_smul (1 / 2 : ℝ)))
  have hnonzero (x : C) : ‖x.val‖ ≠ 0 := (ha.trans_le x.property.1).ne'
  have hnormalize (x : C) : ‖‖x.val‖⁻¹ • x.val‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (hnonzero x)]
  let θ : C → S := fun x => ⟨‖x.val‖⁻¹ • x.val, by
    simpa only [S, Metric.mem_sphere, dist_zero_right] using hnormalize x⟩
  have hθ : Continuous θ := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.norm.inv₀ hnonzero).smul continuous_subtype_val)
  let r : C → Icc a R.val := fun x => ⟨‖x.val‖, x.property⟩
  have hr : Continuous r := Continuous.subtype_mk continuous_subtype_val.norm _
  have hrecover (x : C) : ‖x.val‖ • (θ x).val = x.val := by
    change ‖x.val‖ • (‖x.val‖⁻¹ • x.val) = x.val
    rw [smul_smul, mul_inv_cancel₀ (hnonzero x), one_smul]
  refine ⟨fun x => G (θ x, r x), hG.comp (hθ.prodMk hr), ?_⟩
  intro x hx
  have hint : (∫ s in a..‖x.val‖, J (θ x) s) =
      ∫ s in a..‖x.val‖, s ^ ((n : ℤ) - 3) • L₂ (s • (θ x).val) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le x.property.1] at hs
    have hsR : s ∈ Icc a R.val := ⟨hs.1, hs.2.trans x.property.2⟩
    obtain ⟨hball, hvalue⟩ := hJvalue (θ x) s hsR
    have hsinside : s • (θ x).val ∈ Metric.ball (0 : Domain n) R.val := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (ha.le.trans hs.1), htheta, mul_one]
      exact hs.2.trans_lt hx
    rw [hvalue, heq _ hsinside]
  have hidentity := hradial q R f hf hh a ‖x.val‖ ha x.property.1 hx (θ x)
  change ‖x.val‖ ^ k • E (‖x.val‖ • (θ x).val) =
    a ^ k • E (a • (θ x).val) - (1 / 2 : ℝ) •
      (∫ s in a..‖x.val‖, s ^ ((n : ℤ) - 3) • L₂ (s • (θ x).val)) at hidentity
  change ‖x.val‖ ^ (-k) •
    (a ^ k • E (a • (θ x).val) - (1 / 2 : ℝ) • (∫ s in a..‖x.val‖, J (θ x) s)) = _
  rw [hint, ← hidentity, hrecover, smul_smul, ← zpow_add₀ (hnonzero x)]
  simp only [neg_add_cancel, zpow_zero, one_smul, E]

/-- A closed collar completion of the actual Euler derivative glues to its
interior values, giving a proof-local ambient representative continuous on
the entire closed ball. -/
theorem poisson_euler_continuousOn_closedBall_of_angularSum {n q : ℕ}
    (A : Fin n → Fin n → (Domain n →L[ℝ] Domain n))
    (hA : ∀ i j (x : Domain n), A i j x =
      x i • EuclideanSpace.single j 1 - x j • EuclideanSpace.single i 1)
    (R : PositiveRadius) (f : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball (0 : Domain n) R.val))
    (hh : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian f x = 0)
    (w : Metric.closedBall (0 : Domain n) R.val → Ambient q)
    (hw : Continuous w)
    (heq : ∀ (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val),
      w ⟨x, Metric.ball_subset_closedBall hx⟩ =
        ∑ i : Fin n, ∑ j : Fin n,
          fderiv ℝ (fun y => fderiv ℝ f y (A i j y)) x (A i j x)) :
    ∃ g : Domain n → Ambient q,
      ContinuousOn g (Metric.closedBall (0 : Domain n) R.val) ∧
      EqOn g (fun x => fderiv ℝ f x x) (Metric.ball (0 : Domain n) R.val) := by
  classical
  obtain ⟨e, he, hevalue⟩ :=
    poisson_euler_continuous_closedCollar_of_angularSum A hA R f hf hh w hw heq
  let a : ℝ := R.val / 2
  have haR : a < R.val := half_lt_self R.property
  let C : Set (Domain n) := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ R.val}
  let E : Domain n → Ambient q := fun x => fderiv ℝ f x x
  let g : Domain n → Ambient q := fun x => if hx : x ∈ C then e ⟨x, hx⟩ else E x
  have hvalue : EqOn g E (Metric.ball (0 : Domain n) R.val) := by
    intro x hx
    have hxR : ‖x‖ < R.val := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    change (if hx : x ∈ C then e ⟨x, hx⟩ else E x) = E x
    split_ifs with hc
    · exact hevalue ⟨x, hc⟩ hxR
    · rfl
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ f) (Metric.ball (0 : Domain n) R.val) :=
    hf.fderiv_of_isOpen Metric.isOpen_ball (by simp)
  have hE : ContinuousOn E (Metric.ball (0 : Domain n) R.val) :=
    (hDf.clm_apply contDiffOn_id).continuousOn
  have hinner : Metric.closedBall (0 : Domain n) a ⊆ Metric.ball (0 : Domain n) R.val := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    simpa only [dist_zero_right] using (Metric.mem_closedBall.mp hx).trans_lt haR
  have hinnerCont : ContinuousOn g (Metric.closedBall (0 : Domain n) a) :=
    hE.congr_mono (hvalue.mono hinner) hinner
  have hcollarCont : ContinuousOn g C := by
    rw [continuousOn_iff_continuous_restrict]
    have heqg : C.restrict g = e := by
      funext x
      exact dif_pos x.property
    rw [heqg]
    exact he
  have hclosed : IsClosed C :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hcover : Metric.closedBall (0 : Domain n) a ∪ C =
      Metric.closedBall (0 : Domain n) R.val := by
    ext x
    simp only [mem_union, Metric.mem_closedBall, dist_zero_right, C, mem_setOf_eq]
    constructor
    · rintro (hx | hx)
      · exact hx.trans haR.le
      · exact hx.2
    · intro hx
      by_cases hxa : ‖x‖ ≤ a
      · exact Or.inl hxa
      · exact Or.inr ⟨(le_of_not_ge hxa), hx⟩
  refine ⟨g, ?_, hvalue⟩
  rw [← hcover]
  exact hinnerCont.union_of_isClosed hcollarCont Metric.isClosed_closedBall hclosed

end HarmonicMaps
end

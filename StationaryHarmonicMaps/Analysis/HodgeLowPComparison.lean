module

public import StationaryHarmonicMaps.Analysis.DistributionHarmonicLpDecay
public import StationaryHarmonicMaps.Analysis.SupercriticalGradientGrowth

/-!
# Low-power comparison with the same actual harmonic remainder

Actual L2 fields supply every lower-power integral. The original
three-term decomposition controls its own harmonic remainder, whose
distributional equation gives the true small-ball decay. No estimate
of the component energies or an inverse lower-power comparison is input.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem norm_add_real_power_le {V : Type*} [NormedAddCommGroup V]
    (v w : V) (p : ℝ) (hp : 0≤p) :
    ‖v+w‖^p≤(2 : ℝ)^p*(‖v‖^p+‖w‖^p) := by
  by_cases h : ‖v‖≤‖w‖
  · have hTwo : ‖v+w‖≤2*‖w‖ := (norm_add_le _ _).trans (by linarith only [h])
    calc
      _≤(2*‖w‖)^p := Real.rpow_le_rpow (norm_nonneg _) hTwo hp
      _=(2 : ℝ)^p*‖w‖^p := Real.mul_rpow (by norm_num) (norm_nonneg _)
      _≤_ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _))
        (Real.rpow_nonneg (by norm_num) _)
  · have hTwo : ‖v+w‖≤2*‖v‖ := (norm_add_le _ _).trans (by linarith only [not_le.mp h])
    calc
      _≤(2*‖v‖)^p := Real.rpow_le_rpow (norm_nonneg _) hTwo hp
      _=(2 : ℝ)^p*‖v‖^p := Real.mul_rpow (by norm_num) (norm_nonneg _)
      _≤_ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))
        (Real.rpow_nonneg (by norm_num) _)

/-- The literal complete-HS density of three original fields has its
dimension-independent power triangle bound. -/
theorem hs_three_term_real_power_le {n q : ℕ} (A B C : Gradient n q) (p : ℝ) (hp : 0≤p) :
    (Real.sqrt (hsNormSq (A+B+C)))^p≤((2 : ℝ)^p)^2*
      ((Real.sqrt (hsNormSq A))^p+(Real.sqrt (hsNormSq B))^p+(Real.sqrt (hsNormSq C))^p) := by
  let L : Gradient n q →ₗ[ℝ] Ambient (n*q) :=
    { toFun := fun D=>WithLp.toLp 2 (fun k : Fin (n*q)=>D (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      map_add' := fun _ _=>by ext k;rfl
      map_smul' := fun _ _=>by ext k;rfl }
  have hNorm (D : Gradient n q) : ‖L D‖=Real.sqrt (hsNormSq D) := by
    rw [←hs_flatten_norm_sq D,Real.sqrt_sq (norm_nonneg _)]
    rfl
  have hTwo : 1≤(2 : ℝ)^p := Real.one_le_rpow (by norm_num) hp
  have hC : 0≤‖L C‖^p := Real.rpow_nonneg (norm_nonneg _) _
  have H : ‖L A+L B+L C‖^p≤((2 : ℝ)^p)^2*(‖L A‖^p+‖L B‖^p+‖L C‖^p) := by
    calc
      _≤(2 : ℝ)^p*(‖L A+L B‖^p+‖L C‖^p) := norm_add_real_power_le _ _ p hp
      _≤(2 : ℝ)^p*((2 : ℝ)^p*(‖L A‖^p+‖L B‖^p)+‖L C‖^p) := mul_le_mul_of_nonneg_left
        (add_le_add (norm_add_real_power_le _ _ p hp) le_rfl) (Real.rpow_nonneg (by norm_num) _)
      _≤_ := by nlinarith only [mul_nonneg (sub_nonneg.mpr hTwo) hC,hTwo]
  rw [←map_add,←map_add] at H
  simpa only [hNorm] using H

private theorem integrable_hs_real_power_of_columns {n q : ℕ}
    (a : Domain n) (r : ℝ) (F : Domain n → Gradient n q) (p : ℝ) (hp : 0≤p) (hpTwo : p≤2)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball a r))) :
    IntegrableOn (fun x=>(Real.sqrt (hsNormSq (F x)))^p) (ball a r) volume := by
  let μ := volume.restrict (ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hHS : MemLp (fun x=>Real.sqrt (hsNormSq (F x))) 2 μ := memLp_hsNorm_of_columns F 2 hF
  have H := integrable_norm_rpow_of_memLp_real (fun x=>Real.sqrt (hsNormSq (F x))) hp
    (memLp_real_of_memL2 _ hpTwo hHS)
  change Integrable (fun x=>(Real.sqrt (hsNormSq (F x)))^p) μ
  simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _)] using H

/-- The same actual three-field Hodge decomposition has its low-power
small-ball bound in terms of its two nonharmonic moments and original
input moment. The harmonic moment is eliminated internally. -/
theorem exists_hodge_low_power_small_ball_comparison (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1≤p) (hpTwo : p≤2) :
    ∃C : ℝ,0<C ∧ ∀(q : ℕ) (a : Domain n) (R : PositiveRadius)
      (F D P h : Domain n → Gradient n q),
      (∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball a R.val))) →
      (∀i,MemLp (fun x=>D x i) 2 (volume.restrict (ball a R.val))) →
      (∀i,MemLp (fun x=>P x i) 2 (volume.restrict (ball a R.val))) →
      (∀i,MemLp (fun x=>h x i) 2 (volume.restrict (ball a R.val))) →
      (∀ᵐx∂volume.restrict (ball a R.val),∀i,F x i=D x i+P x i+h x i) →
      (∀(i : Fin n) (ψ : Domain n → Ambient q),ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ⊆ball a R.val → (∫x in ball a R.val,inner ℝ (h x i) (Laplacian.laplacian ψ x))=0) →
      ∀θ : ℝ,0<θ → θ≤1/2 →
        IntegrableOn (fun x=>(Real.sqrt (hsNormSq (F x)))^p) (ball a (θ*R.val)) volume ∧
        (∫x in ball a (θ*R.val),(Real.sqrt (hsNormSq (F x)))^p)≤
          C*((∫x in ball a R.val,(Real.sqrt (hsNormSq (D x)))^p)+
            (∫x in ball a R.val,(Real.sqrt (hsNormSq (P x)))^p)+
            θ^n*(∫x in ball a R.val,(Real.sqrt (hsNormSq (F x)))^p)) := by
  have hp : 0≤p := zero_le_one.trans hpOne
  let K := ((2 : ℝ)^p)^2
  let B := K^2*(2 : ℝ)^n
  let C := K+B
  have hK : 0<K := sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _)
  have hB : 0≤B := mul_nonneg (sq_nonneg K) (pow_nonneg (by norm_num) n)
  have hC : 0<C := by dsimp only [C];linarith only [hK,hB]
  have hBC : B≤C := by dsimp only [C];linarith only [hK]
  refine ⟨C,hC,?_⟩
  intro q a R F D P h hF hD hP hh hDecomp hHarm θ hθ hθHalf
  have hFI := integrable_hs_real_power_of_columns a R.val F p hp hpTwo hF
  have hDI := integrable_hs_real_power_of_columns a R.val D p hp hpTwo hD
  have hPI := integrable_hs_real_power_of_columns a R.val P p hp hpTwo hP
  obtain ⟨_hHLp,hHI,Hdecay⟩ := distribution_harmonic_oneForm_lp_decay hn hpOne hpTwo a R h hh hHarm
  have hSub : ball a (θ*R.val)⊆ball a R.val := ball_subset_ball (by nlinarith only [hθHalf,R.property])
  let IF := ∫x in ball a R.val,(Real.sqrt (hsNormSq (F x)))^p
  let ID := ∫x in ball a R.val,(Real.sqrt (hsNormSq (D x)))^p
  let IP := ∫x in ball a R.val,(Real.sqrt (hsNormSq (P x)))^p
  let IH := ∫x in ball a R.val,(Real.sqrt (hsNormSq (h x)))^p
  have hID : 0≤ID := integral_nonneg fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hIP : 0≤IP := integral_nonneg fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hIF : 0≤IF := integral_nonneg fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hHBound : IH≤K*(IF+ID+IP) := by
    have hPoint : ∀ᵐx∂volume.restrict (ball a R.val),(Real.sqrt (hsNormSq (h x)))^p≤
        K*((Real.sqrt (hsNormSq (F x)))^p+(Real.sqrt (hsNormSq (D x)))^p+(Real.sqrt (hsNormSq (P x)))^p) := by
      filter_upwards [hDecomp] with x hx
      have hEq : F x+(-D x)+(-P x)=h x := by
        ext i
        dsimp only [Pi.add_apply,Pi.neg_apply]
        rw [hx i]
        abel_nf
      have H := hs_three_term_real_power_le (F x) (-D x) (-P x) p hp
      rw [hEq] at H
      simpa only [hsNormSq,Pi.neg_apply,norm_neg] using H
    have H := integral_mono_ae hHI (((hFI.add hDI).add hPI).const_mul K) hPoint
    have hSplit : (∫x in ball a R.val,K*((Real.sqrt (hsNormSq (F x)))^p+
        (Real.sqrt (hsNormSq (D x)))^p+(Real.sqrt (hsNormSq (P x)))^p))=K*(IF+ID+IP) := by
      have H1 := integral_add (hFI.add hDI) hPI
      have H2 := integral_add hFI hDI
      simp only [Pi.add_apply] at H1 H2
      rw [integral_const_mul,H1,H2]
    exact H.trans_eq hSplit
  have hSmall : (∫x in ball a (θ*R.val),(Real.sqrt (hsNormSq (F x)))^p)≤
      K*(ID+IP+(2 : ℝ)^n*θ^n*IH) := by
    have hPoint : ∀ᵐx∂volume.restrict (ball a (θ*R.val)),(Real.sqrt (hsNormSq (F x)))^p≤
        K*((Real.sqrt (hsNormSq (D x)))^p+(Real.sqrt (hsNormSq (P x)))^p+(Real.sqrt (hsNormSq (h x)))^p) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hSub hDecomp] with x hx
      have hEq : D x+P x+h x=F x := funext fun i=>(hx i).symm
      have H := hs_three_term_real_power_le (D x) (P x) (h x) p hp
      rw [hEq] at H
      exact H
    have H := integral_mono_ae (hFI.mono_set hSub)
      ((((hDI.mono_set hSub).add (hPI.mono_set hSub)).add (hHI.mono_set hSub)).const_mul K) hPoint
    have hDMono : (∫x in ball a (θ*R.val),(Real.sqrt (hsNormSq (D x)))^p)≤ID :=
      setIntegral_mono_set hDI (Eventually.of_forall fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _)
        (Eventually.of_forall fun _ hx=>hSub hx)
    have hPMono : (∫x in ball a (θ*R.val),(Real.sqrt (hsNormSq (P x)))^p)≤IP :=
      setIntegral_mono_set hPI (Eventually.of_forall fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _)
        (Eventually.of_forall fun _ hx=>hSub hx)
    have H1 := integral_add ((hDI.mono_set hSub).add (hPI.mono_set hSub)) (hHI.mono_set hSub)
    have H2 := integral_add (hDI.mono_set hSub) (hPI.mono_set hSub)
    simp only [Pi.add_apply] at H H1 H2
    rw [integral_const_mul,H1,H2] at H
    exact H.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hDMono hPMono) (Hdecay θ hθ hθHalf).2) hK.le)
  have hθOne : θ^n≤1 := pow_le_one₀ hθ.le (by linarith only [hθHalf])
  have hθN : 0≤θ^n := pow_nonneg hθ.le n
  refine ⟨hFI.mono_set hSub,hSmall.trans ?_⟩
  calc
    K*(ID+IP+(2 : ℝ)^n*θ^n*IH)≤K*(ID+IP+(2 : ℝ)^n*θ^n*(K*(IF+ID+IP))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hHBound
        (mul_nonneg (pow_nonneg (by norm_num) n) hθN))) hK.le
    _=K*(ID+IP)+B*(θ^n*IF)+B*θ^n*(ID+IP) := by dsimp only [B];ring
    _≤K*(ID+IP)+B*(θ^n*IF)+B*(ID+IP) := add_le_add le_rfl
      (by simpa only [mul_assoc,one_mul] using (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hθOne (add_nonneg hID hIP)) hB))
    _=C*(ID+IP)+B*(θ^n*IF) := by dsimp only [C];ring
    _≤C*(ID+IP)+C*(θ^n*IF) := add_le_add le_rfl (mul_le_mul_of_nonneg_right hBC (mul_nonneg hθN hIF))
    _=C*(ID+IP+θ^n*IF) := by ring

end StationaryHarmonicMaps.Analysis

end

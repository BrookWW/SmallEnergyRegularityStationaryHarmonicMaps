module

public import HarmonicMaps.Analysis.AffineEnergyScaling
public import HarmonicMaps.Minimizer

/-!
# Transport of all local Sobolev competitors

Original local data produce finite data on compactly contained balls. Each
unit-ball competitor is pushed to the original domain with its displayed
gradient, actual target membership and compact smooth zero-boundary difference.
Both energies acquire the same positive normalization factor.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicMaps

theorem affineBall_minimizer_transport {n q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (Ω : OpenDomain n) (a : Domain n) (R : PositiveRadius)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hclosed : Metric.closedBall a R.val ⊆ Ω.val)
    (hu : MemW12Loc Ω u Du) (hN : TakesValuesIn N Ω u)
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) :
    let v : Domain n → Ambient q := fun z => u (a + R.val • z)
    let Dv : Domain n → Gradient n q := fun z i => R.val • Du (a + R.val • z) i
    MemW12Loc (ballDomain (0 : Domain n) 1) v Dv ∧
    TakesValuesIn N (ballDomain (0 : Domain n) 1) v ∧
    IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) v Dv ∧
    dirichletEnergy Dv (Metric.ball (0 : Domain n) 1) = normalizedEnergy Du a R := by
  intro v Dv
  have hfinite : MemW12 (ballDomain a R.val) u Du := hu.memW12_ball hclosed
  have hfiniteV : MemW12 (ballDomain (0 : Domain n) 1) v Dv :=
    (affineBall_unit_memW12_iff a R u Du).mp hfinite
  have hNv : TakesValuesIn N (ballDomain (0 : Domain n) 1) v := by
    have hNb : ∀ᵐ x ∂volume.restrict (Metric.ball a R.val), u x ∈ N.carrierSet :=
      ae_restrict_of_ae_restrict_of_subset
        (Metric.ball_subset_closedBall.trans hclosed) hN
    simpa only [div_self R.property.ne', sub_zero, ballDomain, TakesValuesIn, v] using
      ae_affineBall a (0 : Domain n) R.property R.val hNb
  refine ⟨hfiniteV.to_memW12Loc, hNv, ?_, affineBall_unit_energy a R Du⟩
  intro b r hr hs w Dw hw hNw hzero
  let c : Domain n := a + R.val • b
  let ρ : ℝ := R.val * r
  let Q : Domain n → Domain n := fun x => b + R.val⁻¹ • (x - c)
  let W : Domain n → Ambient q := fun x => w (Q x)
  let DW : Domain n → Gradient n q := fun x i => R.val⁻¹ • Dw (Q x) i
  have hradius : r / R.val⁻¹ = ρ := by simp [ρ, div_eq_mul_inv, mul_comm]
  have hratio : ρ / R.val = r := by simp [ρ, R.property.ne']
  have hP (z : Domain n) : c + R.val • (z - b) = a + R.val • z := by
    dsimp [c]
    simp only [smul_sub]
    abel
  have hQP (z : Domain n) : Q (a + R.val • z) = z := by
    rw [← hP]
    exact affineBall_inverse c b R.property.ne' z
  have hPQ (x : Domain n) : a + R.val • Q x = x := by
    rw [← hP]
    dsimp [Q]
    simp [smul_smul, R.property.ne']
  have hclosedC : Metric.closedBall c ρ ⊆ Ω.val := by
    intro x hx
    have hQx : Q x ∈ Metric.closedBall b r := by
      have h := (affineBall_mem_closedBall_iff c b R.property ρ (Q x)).mp
        (by rw [hP, hPQ]; exact hx)
      simpa only [hratio] using h
    have hball : a + R.val • Q x ∈ Metric.ball a R.val := by
      have hh := (affineBall_mem_ball_iff a (0 : Domain n) R.property R.val (Q x)).mpr
        (by simpa only [div_self R.property.ne', ballDomain] using hs hQx)
      simpa only [sub_zero] using hh
    rw [hPQ] at hball
    exact hclosed (Metric.ball_subset_closedBall hball)
  have huC := hu.memW12_ball hclosedC
  have hW : MemW12 (ballDomain c ρ) W DW := by
    simpa only [hradius] using hw.affineBall_pullback c (inv_pos.mpr R.property)
  have hNW : TakesValuesIn N (ballDomain c ρ) W := by
    have hh := ae_affineBall b c (inv_pos.mpr R.property) r hNw
    simpa only [hradius, ballDomain, TakesValuesIn, W, Q] using hh
  have hZW : HasZeroBoundaryDifference (ballDomain c ρ) u Du W DW := by
    change HasZeroBoundaryValues (ballDomain b r) (w - v)
      (fun z i => Dw z i - Dv z i) at hzero
    have hh := hzero.affineBall_pullback c (inv_pos.mpr R.property)
    have heq : (fun x => (w - v) (b + R.val⁻¹ • (x - c))) = W - u := by
      funext x
      dsimp only [Pi.sub_apply, W, v]
      rw [show a + R.val • (b + R.val⁻¹ • (x - c)) = x from hPQ x]
    have hdeq : (fun x i => R.val⁻¹ •
        (Dw (b + R.val⁻¹ • (x - c)) i - Dv (b + R.val⁻¹ • (x - c)) i)) =
        (fun x i => DW x i - Du x i) := by
      funext x i
      dsimp only [DW, Dv]
      rw [show a + R.val • (b + R.val⁻¹ • (x - c)) = x from hPQ x]
      dsimp only [Q]
      simp only [smul_sub, smul_smul, inv_mul_cancel₀ R.property.ne', one_smul]
    simpa only [hradius, heq, hdeq, HasZeroBoundaryDifference] using hh
  have hcompare := hmin c ρ (mul_pos R.property hr) hclosedC W DW hW hNW hZW
  have hEu : dirichletEnergy Dv (Metric.ball b r) =
      ENNReal.ofReal (R.val ^ (2 - (n : ℤ))) * dirichletEnergy Du (Metric.ball c ρ) := by
    have h := dirichletEnergy_affineBall c b R.property ρ Du
    simpa only [hratio, hP] using h
  have hEw : dirichletEnergy Dw (Metric.ball b r) =
      ENNReal.ofReal (R.val ^ (2 - (n : ℤ))) * dirichletEnergy DW (Metric.ball c ρ) := by
    have h := dirichletEnergy_affineBall c b R.property ρ DW
    have hD : (fun z i => R.val • DW (c + R.val • (z - b)) i) = Dw := by
      funext z i
      dsimp only [DW]
      rw [hP, hQP]
      simp [smul_smul, R.property.ne']
    simpa only [hratio, hD] using h
  rw [hEu, hEw]
  exact mul_le_mul_right hcompare _

end HarmonicMaps

# Stationary small-energy regularity: objects, proof and interfaces

The public theorem proves interior small-energy Hölder regularity for
stationary weakly harmonic maps into compact embedded C² targets. The smooth
corollary upgrades the same representative for smooth targets. Their complete
Lean proofs use the same original map and displayed weak gradient throughout.
The independent mathematical proof is in [the paper](../paper/main.tex)
([PDF](../paper/main.pdf)).

## The mathematical objects

`HarmonicMaps.Domain n` and `Ambient q` are finite-dimensional Euclidean
spaces. `Gradient n q` is a family of coordinate columns, and the energy uses
their actual Hilbert–Schmidt sum:

```math
|Du|_{\mathrm{HS}}^2=\sum_{i=1}^n|D_i u|^2,
\qquad
E(u;B)=\int_B|Du|_{\mathrm{HS}}^2,
\qquad
\Theta_u(a,R)=R^{2-n}E(u;B_R(a)).
```

There is no factor of one half in the energy. The native norm of the family
of columns is not silently substituted for the Hilbert–Schmidt norm.
`MemW12Loc Ω u Du` means local L² data and distributional derivative identities
for this same `Du`.

`CompactC2EmbeddedTarget` supplies an actual nonempty compact Euclidean
subset, a C² manifold structure and a C² embedded inclusion. The manifold has
no boundary. Tangent spaces are the ranges of the actual differential of the
inclusion. Orthogonal normal projections, their C¹ dependence and ambient
extensions are proved consequences of those geometric data. Orientation and
a global normal trivialization are not fields of the target.

`IsWeaklyHarmonicByTangentVariations` quantifies over all compactly supported
C¹ ambient fields tangent along the target. It requires both integrability
and the vanishing first-variation integral. `IsDomainStationary` is the stress
identity against every smooth compactly supported domain vector field:

```math
\int_\Omega\left(
|Du|_{\mathrm{HS}}^2\operatorname{div}X
-2\sum_{i,j=1}^n
\langle D_i u,D_j u\rangle\,\partial_iX^j
\right)=0.
```

The two variational conditions and Sobolev membership are separate hypotheses.
Energy minimality is not required.

## The complete conclusion

For each $n\ge2$ and target $N$, the main theorem chooses
$\varepsilon\gt0$, $0\lt\alpha\lt1$ and $C\ge0$ before the open domain,
map, weak gradient, center and positive radius. If
$\overline{B_R(a)}\subset\Omega$ and $\Theta_u(a,R)\le\varepsilon$, it
produces a continuous $w:B_{R/2}(a)\to\mathbb R^q$, agreeing almost everywhere
with $u$, such that

```math
w(x)\in N,
\qquad
|w(x)-w(y)|\le
C R^{-\alpha}\sqrt{\Theta_u(a,R)}\,|x-y|^\alpha
\quad(x,y\in B_{R/2}(a)).
```

Every continuous almost-everywhere representative on this half ball equals
$w$. The theorem uses the entire open half ball and all its point pairs.
The implemented choice is $\alpha=1/2$; the public interface states the
existence of an exponent in $(0,1)$. Both dimension two and zero energy are
included.

The public C² theorem is
[`stationary_small_energy_regularity`](../StationaryHarmonicMaps/Frozen/SmallEnergyRegularity.lean).
Its implementation is
[`Providers.smallEnergyRegularity`](../StationaryHarmonicMaps/Providers/SmallEnergyRegularity.lean).
There are no gauge, decay, map-bound or regularity certificates in the caller's
hypotheses.

## Monotonicity and the actual antisymmetric system

Radial domain tests and radius calculus turn the stress identity into the
exact normalized-energy identity

```math
\Theta_u(a,r)-\Theta_u(a,s)
=2\int_{B_r(a)\setminus B_s(a)}
|x-a|^{2-n}|\partial_r u|^2\,dx\ge0
\qquad(0\lt s\lt r\le R).
```

Change of center then bounds the critical Morrey square of `Du` on
$B_{3R/4}(a)$ by $4^{n-2}\Theta_u(a,R)$. The critical quantity uses all
centers in that ball and all positive radii, with the actual truncated ball
integrals. It is not restricted to balls wholly contained in the domain.

Write $G$ for a compactly supported C¹ ambient extension of the target's
normal projection. Sobolev tangency and the map-variation identity give the
signed distributional equation

```math
\Delta u=-\sum_i DG(u)[D_i u]D_i u
=-\sum_i A_iD_i u,
\qquad
A_i=G(u)DG(u)[D_i u]-DG(u)[D_i u]G(u).
```

The coefficient $A_i$ is skew-adjoint and locally L². Its actual coefficient
Hilbert–Schmidt Morrey square is bounded by a target constant times that of
`Du`. Operator coefficients are encoded into a finite Euclidean space by a
proved linear equivalence preserving the Hilbert–Schmidt square. Thus the
original normalized-energy hypothesis makes both `Du` and this same
connection small in the required critical norms.

The definitions and proofs appear in
[VariationalWeakPoissonEquivalence](../StationaryHarmonicMaps/Frozen/VariationalWeakPoissonEquivalence.lean),
[StationaryMorreyBound](../StationaryHarmonicMaps/Frozen/StationaryMorreyBound.lean)
and the original-system construction in
[Providers.smallEnergyRegularity](../StationaryHarmonicMaps/Providers/SmallEnergyRegularity.lean).

## Construction of the critical Coulomb frame

For the original small skew L² connection, the development constructs a
Sobolev frame $P$ with values in $\mathrm{SO}(q)$ almost everywhere. The
literal transformed connection is

```math
Z_i=P^\mathsf{T}D_iP+P^\mathsf{T}A_iP.
```

It is divergence free with its complete native natural boundary identity,
and the critical Morrey squares of $DP$ and $Z$ are bounded by the original
connection's square. The construction first establishes the boundary linear
and compensated estimates, proves existence in a stronger Morrey class by
actual perturbations and continuation, and passes to the critical class
through skew approximation and compactness. The limit retains the same
weak derivative graph, special orthogonality and every native natural test.
Positive affine transport gives the theorem on arbitrary positive-radius
balls.

The main theorem applies
[CriticalNativeCoulombBallExistence](../StationaryHarmonicMaps/Analysis/CriticalNativeCoulombBallExistence.lean)
internally to its constructed connection. The frame and its estimates are
outputs of proved results, not data added to the stationary harmonic map.

## Compensation, envelope contraction and representative

On the normalized ball, a genuine smooth cutoff $\chi$ equals one on
$B_{2/3}$ and is supported in $\overline{B_{3/4}}$. For the original mean
$c=\fint_{B_1}u$, set

```math
v=\chi(u-c),
\qquad
D_i v=\chi D_i u+(\partial_i\chi)(u-c),
\qquad
F_i=P^\mathsf{T}D_i v.
```

One relative Hodge decomposition of this actual field supplies its exact
part, coexact part and harmonic remainder. The compensated pairings use
the actual weak equations and divergence/curl structure. Compactness of the
target provides the value bounds needed for the cutoff pairings. Cutoff
errors, component estimates, integrability and the harmonic decay estimate
are proved for these same fields.

Fix $1\lt p\lt2$ with $p/(p-1)\gt n$, and define the finite all-center
envelope from

```math
\Phi(x,r)=r^{p-n}\int_{B_r(x)}|Dv|_{\mathrm{HS}}^p,
\qquad
\Psi(t)=\sup_{x,\,0\lt r\le t}\Phi(x,r).
```

The one-ball estimate and absorption choices give a scale contraction for
$\Psi$. Iteration yields the improved all-radius gradient growth

```math
\int_{B_r(x)}|Dv|_{\mathrm{HS}}^p
\le C\eta^p r^{n-p\delta},
\qquad 0\lt\delta\lt1.
```

Sobolev Poincaré estimates and limits of ball averages produce a continuous
representative with Hölder exponent $1-\delta$. The cutoff plateau recovers
the original map. Closedness of $N$ upgrades almost-everywhere target values
to pointwise target values, and full support of Euclidean measure gives
uniqueness among continuous representatives.

The implementation fixes $p=1+1/(2n)$ and $\delta=1/2$. It constructs the
representative on two thirds of the original system ball. Choosing that
ball to be $B_{3R/4}(a)$ gives exactly $B_{R/2}(a)$. Affine transport gives
the factor $R^{-1/2}$, and the system smallness amplitude is a target constant
times $\sqrt{\Theta_u(a,R)}$. All threshold and absorption constants are
chosen before the map and ball.

See
[SystemCompensatedHodgeFields](../StationaryHarmonicMaps/Analysis/SystemCompensatedHodgeFields.lean),
[OneBallCompensatedDecay](../StationaryHarmonicMaps/Analysis/OneBallCompensatedDecay.lean),
[CompensatedCutoffPowerGrowth](../StationaryHarmonicMaps/Analysis/CompensatedCutoffPowerGrowth.lean)
and [CompensatedSystemRepresentative](../StationaryHarmonicMaps/Analysis/CompensatedSystemRepresentative.lean).

## Effective rational bounds

The effective theorem fixes $p=1+1/(2n)$, conjugate exponent $2n+1$ and
Hölder exponent $1/2$. Given certified embedding data, both the energy threshold and Hölder
coefficient can be completely evaluated. All analytic coefficients used by
this effective theorem are explicit natural numbers or rationals. The exact-arithmetic functions in
[EffectiveStationaryConstants](../StationaryHarmonicMaps/Analysis/EffectiveStationaryConstants.lean)
return an admissible normalized-energy threshold and Hölder coefficient.
Their complete formulas, analytical roles and self-contained evaluator appear
in the constant ledger and algorithm appendix of [the paper](../paper/main.tex).

For certified geometric data, let $G$ be a compactly supported C¹ ambient
extension of the orthogonal normal projection and let $\ell\in\mathbb Q$
be nonnegative with $\|DG(y)\|\le\ell$ for every $y\in\mathbb R^q$.
This derivative has the induced operator norm from Euclidean space to
operator-norm matrices. The original stationary gradient and encoded connection then have joint
critical square at most $M\Theta_u(a,R)$, where

```math
M=(1+4q\ell^2)4^{n-2},\qquad K=(1+C_g)(1+M).
```

The constructed frame has joint gradient/connection square at most $C_g$
times the original connection's critical square. The given-frame
representative theorem supplies the exact rational smallness $\theta$ and
coefficient $C_r$ on the two-thirds ball. With its rational frame threshold
$\kappa$, the actual final witnesses are

```math
\varepsilon_*(n,q,\ell)=\left(\frac{\min(\kappa,\theta)}K\right)^2,
\qquad C(n,q,\ell)=2C_rK.
```

The factor two bounds $(3/4)^{-1/2}$ when transporting the two-thirds
estimate on $B_{3R/4}(a)$ to the original half ball. The majorant
$\sqrt M\le1+M$ removes real square roots from the coefficient algorithm.
The resulting rational values are conservative and are not claimed optimal.

The public exports
[`stationary_small_energy_regularity_effective`](../StationaryHarmonicMaps/Frozen/EffectiveSmallEnergyRegularity.lean)
and [`stationary_small_energy_smooth_regularity_effective`](../StationaryHarmonicMaps/Frozen/EffectiveSmallEnergySmoothRegularity.lean)
consume the certified $G,\ell$ and prove the original all-point estimate for
the same map and weak gradient. The smooth export retains exactly this
Hölder bound and asserts C∞ regularity of the same representative; it does
not give numerical all-order derivative bounds.

[EffectiveNormalProjectionData](../StationaryHarmonicMaps/Geometry/EffectiveNormalProjectionData.lean)
proves that each abstract compact C² target admits a suitable certificate.
Numerical evaluation for a specified embedding uses a certified choice,
including derivative control on the whole ambient extension region.
Existence of that choice for an abstract manifold is not a numerical
certificate-extraction algorithm. No such geometric choice is an additional
hypothesis of the original existential theorem.

The integer and rational defining values require neither the target's value
bound nor an actual map or frame as computational inputs. Compactness still
supplies the ordinary pairing admissibility used in the analytic proof.
The exact input example $n=2,q=3,\ell=1$ is stored in
[effective-constants.json](../verification/effective-constants.json); its
presence does not certify that geometric bound for a particular embedding.

## Smoothness of the same representative

For a smooth target, the normal projection has a smooth ambient extension.
The original variational equation becomes

```math
\Delta w=\sum_i B(w)[D_iw,D_iw],
\qquad B(y)=-DG(y),
```

on the same half ball. Almost-everywhere replacement preserves the displayed
weak gradient `Du`. The established Hölder representative therefore supplies
the genuine local Sobolev and quadratic-Poisson inputs.

The included `HolderToCK` analysis proves C¹ regularity by harmonic comparison
and Campanato reconstruction of the actual weak gradient. A fundamental-
solution construction with Hessian cancellation proves the weak Poisson
Schauder estimate. Differentiating the actual equation then gives smoothness
of this same map. This bootstrap uses no energy-minimizing hypothesis.

[`stationary_small_energy_smooth_regularity`](../StationaryHarmonicMaps/Frozen/SmallEnergySmoothRegularity.lean)
retains the original half-ball, quantitative Hölder estimate and continuous
uniqueness. It asserts C∞ regularity there. Uniform all-order derivative
estimates are not part of this stationary export.

## Formal closure and reproduction

The public entry point imports the regularity interfaces and their full
proved dependencies. The required `HarmonicMaps` and `HolderToCK`
modules are included as libraries in the same package; Mathlib is the only
direct external Lake dependency. No external paper theorem is introduced as a
project axiom, and no unformalized analytic lemma occurs in the main
theorems' hypotheses.

The source checker, complete theorem-type checker, axiom checker, public
consumer checks and exact rational computation checker are shipped with the
package. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted by the axiom audit.
Compiled-declaration replay uses Lean's `leanchecker`. The exact commands and
pins are in the [README](../README.md).

The scope of the release is the stated stationary small-energy theorem and
its smooth-target corollary, with their complete proof dependencies. It does
not assert a general regularity theorem for arbitrary Euclidean-valued
antisymmetric systems, nor the full domain of every related BMO or Campanato
theorem.

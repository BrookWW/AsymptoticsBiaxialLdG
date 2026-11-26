# Asymptotics of biaxial Landau–de Gennes minimizers in Lean 4

[![Build and verify](https://github.com/BrookWW/AsymptoticsBiaxialLdG/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/BrookWW/AsymptoticsBiaxialLdG/actions/workflows/build.yml)
[![Kernel replay](https://github.com/BrookWW/AsymptoticsBiaxialLdG/actions/workflows/kernel.yml/badge.svg?branch=main)](https://github.com/BrookWW/AsymptoticsBiaxialLdG/actions/workflows/kernel.yml)

This repository formalizes **Theorems 1.4–1.6 of my doctoral thesis**,
*Landau–de Gennes Model with Sextic Potentials: Asymptotic Behavior of
Minimizers*. The [thesis excerpt](paper/thesis-excerpt.pdf) contains the
abstracts, introduction and original theorem statements.

The three results cover the bounded-energy limit, the fixed-trace limit with
its first correction, and the logarithmic-energy limit with line defects.
Theorem 1.4 has a complete Lean proof. Theorems 1.5 and 1.6 have complete
proofs relative to the explicit literature inputs listed below. The proof
terms use only Lean’s standard `propext`, `Classical.choice`, and
`Quot.sound` as axioms. [External inputs and dependency provenance](docs/external-inputs.md)

## What is proved

The field $Q$ takes values in the symmetric traceless real $3\times3$ matrices
with the Frobenius norm. For the nonnegative sextic bulk potential $f_b$,
the energy is

```math
E_\varepsilon(Q;U)
= \int_U \left(\tfrac12|\nabla Q|^2 + \varepsilon^{-2} f_b(Q)\right)\,dx.
```

The Lean definitions carry the displayed weak gradient through the energy,
minimization hypotheses, and convergence statements.

**Theorem 1.4 · Bounded energy.** Uniform energy and field bounds for local
minimizers give a subsequence converging strongly in $H^1_{\mathrm{loc}}$
to a vacuum-valued local Dirichlet minimizer. The limit solves the weak
harmonic-map equation, with locally finite point singularities and classical
convergence on the regular set. The harmonic-map equation remainder of the
regular representatives has an interior $O(\varepsilon^2)$ bound together
with bounds for all differentiated remainders.

**Theorem 1.5 · Fixed trace and first correction.** Global minimizers with
the prescribed trace converge strongly in $H^1$ to a limiting Dirichlet
minimizer with the same trace and a finite singular set. The theorem gives
$C^{1,\alpha}$ convergence locally up to the boundary away from the singular
set for every $0\lt\alpha\lt1$, as well as local classical convergence in
the interior. If the limit is smooth and its linearized Dirichlet operator
is bijective, the rescaled difference $\varepsilon_n^{-2}(Q_{\varepsilon_n}-Q_0)$
converges in $H^s$ for every $0\lt s\lt1/2$ and locally in $C^j$ in the
interior for every $j\ge2$. The theorem identifies the normal component
and the equation for the tangential component of the correction.

**Theorem 1.6 · Logarithmic energy and line defects.** Dividing the energy
measures by $\log(1/\varepsilon)$ gives a weak-* limit with support $S$.
Inside the domain, the support is countably 1-rectifiable with finite
length, and the associated one-dimensional varifold is stationary.
The theorem proves quantized edge weights, a finite straight-segment
network on each compactly contained region, a meridian obstruction
at transverse disks, and the junction conditions.

Both estimates in Theorem 1.6(3) use the same subsequence. For each domain
$U\Subset\Omega\setminus S$, a bound $B\gt0$ controls the energy on $U$
for every index of that subsequence. The positive function $C(U,r)$
is chosen from the bulk coefficients $a$ and shared energy and field
bound $M$ before the ambient domain and minimizer family are chosen.
For every such $U$ and $r\gt0$ with
$\overline B_r(x)\subset\Omega\setminus S$ for each $x\in\overline U$,
$C(U,r)$ controls the energy on $U$ eventually along the subsequence.

## Lean interface

The [`Thesis`](Thesis.lean) module exposes all three results.

```lean
import Thesis

open Thesis

#check @boundedEnergyLimit

example (hSU : External.SU83BoundaryRegularity) :
    GlobalEnergyLimitAndCorrectionConclusion :=
  globalEnergyLimitAndCorrection_relative hSU

example (hA19 : External.A19Prop31) (hAA : External.AllardAlmgrenLocalStructure) :
    LogarithmicEnergyLimitConclusion :=
  logarithmicEnergyLimit_relative hA19 hAA
```

Theorem 1.5 takes Schoen–Uhlenbeck’s boundary regularity theorem for the
limiting minimizing harmonic map. Theorem 1.6 takes Proposition 3.1 of
Arroyo-Rabasa, De Philippis, Hirsch, and Rindler for the stress measure
and Allard–Almgren’s local structure theorem for stationary
one-dimensional varifolds. [Statements and uses of the external inputs](docs/external-inputs.md#mathematical-inputs)

## Proof structure

1. **Bounded-energy compactness and the interior limit.** The proof
   constructs competitors on annuli using the vacuum projection and compares
   their penalized energies with the minimizers. This gives strong local
   Sobolev convergence, vanishing scaled potential, and Dirichlet minimality
   of the limit. The minimizing harmonic-map results give interior
   regularity, and the penalized equation gives the differentiated
   harmonic-map remainder. [Projection layer](Thesis/Interpolation/ProjectionLayer.lean) · [Strong limit](Thesis/Variational/BoundedEnergyStrongLimit.lean) · [Bounded-energy theorem](Thesis/Providers/BoundedEnergyLimit.lean)
2. **Fixed boundary data and the first correction.** The global comparison
   keeps the prescribed trace. Dirichlet Poisson estimates control the
   regular representatives up to the boundary, and the smooth-limit
   branch uses the inverse of the linearized Dirichlet operator and
   fractional compactness to identify the correction. [Global limit](Thesis/Variational/GlobalLimit.lean) · [Wall regularity](Thesis/Variational/DirichletWallRegularity.lean) · [First correction](Thesis/Variational/SmoothLimitFirstCorrection.lean)
3. **Stress measures and the line network.** The stress-energy identity
   leads to the divergence constraint used in rectifiability and
   stationarity. Cylindrical comparisons quantify the density, local
   structure gives the segment network, and transverse meridians connect
   the edge weights to the topology of the vacuum. [Logarithmic support](Thesis/MeasureGeometry/LogarithmicSupport.lean) · [Cylindrical comparison](Thesis/Interpolation/CylinderUpperRecovery.lean) · [Finite network](Thesis/MeasureGeometry/LogarithmicSegmentNetwork.lean) · [Meridian costs](Thesis/MeasureGeometry/MeridianCostAssembly.lean)

## Main exports and modules

| Result or object | Module |
| --- | --- |
| Public entry point | [`Thesis`](Thesis.lean) |
| 1.4 · `Thesis.boundedEnergyLimit` | [Frozen bounded-energy theorem](Thesis/Frozen/BoundedEnergyLimit.lean) |
| 1.5 · `Thesis.globalEnergyLimitAndCorrection_relative` | [Global energy limit and correction](Thesis/Providers/GlobalEnergyLimitAndCorrection.lean) |
| 1.6 · `Thesis.logarithmicEnergyLimit_relative` | [Logarithmic energy limit](Thesis/Providers/LogarithmicEnergyLimit.lean) |
| Tensor space, potential, and energy | [Model](Thesis/Model.lean) and [definitions](Thesis/Definitions.lean) |
| Stress-energy identity | [Stress energy](Thesis/StressEnergy.lean) |
| Explicit literature interfaces | [Boundary harmonic maps](Thesis/External/BoundaryHarmonicMaps.lean) and [geometric measure theory](Thesis/External/GeometricMeasureTheory.lean) |

## Build and verify

With [Elan](https://github.com/leanprover/elan) installed, run the following
from the repository root.

```sh
lake exe cache get
lake build
```

The default Lake target is `Thesis`. The project pins Lean `v4.32.2` in
[`lean-toolchain`](lean-toolchain) and all direct and transitive packages
in [`lake-manifest.json`](lake-manifest.json).

Use Lean’s axiom report to inspect the three public proof terms.

```sh
lake env lean --stdin <<'LEAN'
import Thesis

#print axioms Thesis.boundedEnergyLimit
#print axioms Thesis.globalEnergyLimitAndCorrection_relative
#print axioms Thesis.logarithmicEnergyLimit_relative
LEAN
```

Replay the compiled theorem library with Lean’s checker.

```sh
LEAN_NUM_THREADS=2 lake --no-build env leanchecker Thesis -v
```

The [build workflow](https://github.com/BrookWW/AsymptoticsBiaxialLdG/actions/workflows/build.yml)
compiles the project and audits the three public theorem proofs. The
[kernel workflow](https://github.com/BrookWW/AsymptoticsBiaxialLdG/actions/workflows/kernel.yml)
replays the compiled `Thesis` declarations.

## Reuse and acknowledgments

The development reuses
[minimizing harmonic-map stratification](https://github.com/BrookWW/StratificationTheoryMinimizingHarmonicMapsFormalization)
for interior singular-set isolation and Luckhaus interpolation, and the
[Schoen–Uhlenbeck small-energy regularity formalization](https://github.com/BrookWW/SchoenUhlenbeckSmallEnergyRegularityFormalization)
for interior regularity and Poisson estimates. The
[`SupportingAnalysis`](SupportingAnalysis) library includes covering
estimates, tangent measures for weighted rectifiable sets, scalar mean-value
bounds, and whole-space Poisson estimates. Third-party material retains its
attribution and applicable license. [Dependency revisions and roles](docs/external-inputs.md#lean-packages-and-reused-proofs)

The proof and verification workflow follows Scott Armstrong’s
[LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills)
at revision `05a07311f16bc581729e52f3e73647b95fa9bef1`. Cite the doctoral thesis for the mathematics and this repository for the
Lean formalization. [Rights and attribution](LICENSE.md)

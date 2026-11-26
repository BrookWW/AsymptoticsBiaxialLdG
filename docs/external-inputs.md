# External inputs and dependency provenance

## Mathematical inputs

The three main theorem signatures and their axiom closures were checked
against the frozen statements. The external mathematical results below are Lean propositions and
enter the appropriate theorem as explicit arguments.

| Thesis theorem | Export | Explicit input |
| --- | --- | --- |
| 1.4 | `Thesis.boundedEnergyLimit` | None |
| 1.5 | `Thesis.globalEnergyLimitAndCorrection_relative` | `Thesis.External.SU83BoundaryRegularity` |
| 1.6 | `Thesis.logarithmicEnergyLimit_relative` | `Thesis.External.A19Prop31`, `Thesis.External.AllardAlmgrenLocalStructure` |

- **SU83.** Richard Schoen and Karen Uhlenbeck, *Boundary regularity and the
  Dirichlet problem for harmonic maps*, J. Differential Geom. 18 (1983),
  253–268, Theorem 2.7. The Lean input supplies a C² representative in a
  neighborhood of the boundary for a Dirichlet-energy-minimizing harmonic
  map on a smooth domain with smooth prescribed trace. The proof applies it
  to the harmonic limit of the fixed-trace minimizers. [Paper](https://www.math.purdue.edu/~phillips/MA694/SU.pdf#page=13) · [Lean input](../Thesis/External/BoundaryHarmonicMaps.lean)
- **A19.** Adolfo Arroyo-Rabasa, Guido De Philippis, Jonas Hirsch and Filip
  Rindler, *Dimensional estimates and rectifiability for measures satisfying
  linear PDE constraints*, Geom. Funct. Anal. 29 (2019), 639–658,
  Proposition 3.1. The Lean input specializes to row-wise divergence-free
  matrix-valued measures in three dimensions. For the stated rank condition
  it supplies absolute continuity of the variation with respect to
  one-dimensional Hausdorff measure and the rank-one rectifiable
  representation on the positive upper one-density part. The formalization
  establishes the divergence condition for the stress-measure limit and
  uses the representation to identify its tangent densities. [Paper](https://link.springer.com/article/10.1007/s00039-019-00497-1#Sec6) · [Lean input](../Thesis/External/GeometricMeasureTheory.lean)
- **Allard–Almgren.** William K. Allard and Frederick J. Almgren Jr.,
  *The structure of stationary one dimensional varifolds with positive
  density*, Invent. Math. 34 (1976), 83–97, local structure on p. 89.
  The Lean input takes a stationary one-dimensional varifold with positive
  density bounded below and the two discrete weights required by the
  thesis. It supplies finitely many local straight rays and their weights.
  Density quantization, finite-network assembly, the meridian obstruction
  and the junction conditions are proved in the project. [Paper](https://doi.org/10.1007/BF01425476) · [Lean input](../Thesis/External/GeometricMeasureTheory.lean)

A downstream Lean file can supply the literature inputs directly.

```lean
import Thesis.Providers.GlobalEnergyLimitAndCorrection
import Thesis.Providers.LogarithmicEnergyLimit

open Thesis

example (hSU : External.SU83BoundaryRegularity) :
    GlobalEnergyLimitAndCorrectionConclusion :=
  globalEnergyLimitAndCorrection_relative hSU

example (hA19 : External.A19Prop31) (hAA : External.AllardAlmgrenLocalStructure) :
    LogarithmicEnergyLimitConclusion :=
  logarithmicEnergyLimit_relative hA19 hAA
```

## Lean packages and reused proofs

| Package | Pinned revision | Role |
| --- | --- | --- |
| [Mathlib](https://github.com/leanprover-community/mathlib4/tree/905b95818eb32af7874a58b427f50c1711a5e96c) | `905b95818eb32af7874a58b427f50c1711a5e96c` | Formalized analysis, measure theory, topology and algebra |
| [Minimizing harmonic-map stratification](https://github.com/BrookWW/StratificationTheoryMinimizingHarmonicMapsFormalization/tree/ec9a869bad0457e931523ef5ef6d096d30602b75) | `ec9a869bad0457e931523ef5ef6d096d30602b75` | Interior singular-set isolation in dimension three and Luckhaus interpolation |
| [Schoen–Uhlenbeck small-energy regularity](https://github.com/BrookWW/SchoenUhlenbeckSmallEnergyRegularityFormalization/tree/f3a3097025ab9ddd956859600211d1d4edf0654e) | `f3a3097025ab9ddd956859600211d1d4edf0654e` | Interior small-energy regularity and Poisson estimates, via the stratification package |

The local [`SupportingAnalysis`](../SupportingAnalysis) library supplies
the covering and tangent-measure results used in the line-defect proof,
the mean-value bound for nonnegative scalar subsolutions, and the
whole-space Poisson estimates used in the Dirichlet analysis. The proof
audit includes these modules and the pinned upstream libraries.

The [Lake manifest](../lake-manifest.json) records direct and transitive package
pins. The [Lean toolchain](../lean-toolchain) selects `v4.32.2`.

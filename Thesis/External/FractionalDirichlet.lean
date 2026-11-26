module

public import Thesis.Variational.WeakCorrectionPairing

/-! Fractional Dirichlet test spaces and independent adjoint regularity. -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ContDiff ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance fractionalDirichletHMinusOneNormed (U : Set Point) : NormedAddCommGroup (HMinusOne U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance fractionalDirichletHMinusOneNormedSpace (U : Set Point) : NormedSpace ℝ (HMinusOne U) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance fractionalDirichletCoefficientNorm : NormedAddCommGroup ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance fractionalDirichletColumnNorm : NormedAddCommGroup (S0 →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance fractionalDirichletColumnNormedSpace : NormedSpace ℝ (S0 →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance fractionalDirichletColumnDerivativeNorm : Norm (Point →L[ℝ] S0 →L[ℝ] S0) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ)

/-- The squared \(H^{2-s}\) norm of a zero-trace test, using the
literal weak columns of its Sobolev graph. -/
def dirichletFractionalTestEnergy (s : ℝ) (U : Set Point) (v : H10 U) : ℝ≥0∞ :=
  (∫⁻ x in U, ENNReal.ofReal (‖h10Value v x‖ ^ 2)) +
    ∑ j : Fin 3, fractionalEnergy (1 - s) U (fun x => h10Gradient v x j)

def dirichletFractionalTestNorm (s : ℝ) (U : Set Point) (v : H10 U) : ℝ :=
  Real.sqrt ((dirichletFractionalTestEnergy s U v).toReal)

/-- The upper bound for the actual \(H^s\) dual norm of an \(L^2\) test. -/
def FractionalL2DualBound (s : ℝ) (U : Set Point) (f : Lp S0 2 (volume.restrict U)) (N : ℝ) : Prop :=
  0 ≤ N ∧ ∀ v : Point → S0, MemHs s U v →
    |∫ x in U, frobeniusS0 (v x) (f x)| ≤ N * Real.sqrt ((fractionalEnergy s U v).toReal)

/-- The coefficient of one actual gradient column. -/
def correctionFirstOrderColumn (A : Point → (S0 × Gradient) →L[ℝ] S0) (j : Fin 3)
    (x : Point) : S0 →L[ℝ] S0 :=
  (A x).comp ((ContinuousLinearMap.inr ℝ S0 Gradient).comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => S0) j))

/-- Uniform \(L^\infty\) coefficients and the \(L^p\) derivative bounds for
the first-order columns used when expanding the weak adjoint. -/
def HasBoundedDirichletCorrectionCoefficients (U : Set Point) (p M : ℝ)
    (A : Point → (S0 × Gradient) →L[ℝ] S0) : Prop :=
  AEStronglyMeasurable A (volume.restrict U) ∧
  (∀ᵐ x ∂volume.restrict U, ‖A x‖ ≤ M) ∧
  ∀ j : Fin 3, ContDiffOn ℝ 1 (correctionFirstOrderColumn A j) U ∧
    MemLp (fun x => ‖fderiv ℝ (correctionFirstOrderColumn A j) x‖)
      (ENNReal.ofReal p) (volume.restrict U) ∧
    eLpNorm (fun x => ‖fderiv ℝ (correctionFirstOrderColumn A j) x‖)
      (ENNReal.ofReal p) (volume.restrict U) ≤ ENNReal.ofReal M

namespace External

/-- The pure Dirichlet Laplacian gains two derivatives on the negative
fractional scale. The source norm is the actual dual of the intrinsic
space and the result is expressed in the original gradient columns.
The fractional source exponent stays below the Dirichlet trace threshold.
See Lions–Magenes <https://www.numdam.org/item/AIF_1961__11__137_0/>. -/
def DirichletLaplacianFractionalRegularity : Prop :=
  ∀ (U : Set Point), IsSmoothDomain U → ∀ s : ℝ, 0 < s → s < 1 / 2 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : H10 U) (f : Lp S0 2 (volume.restrict U)) (N : ℝ),
      FractionalL2DualBound s U f N →
      (∀ v : H10 U, (∫ x in U, -(∑ j : Fin 3, frobeniusS0 (h10Gradient v x j) (h10Gradient w x j))) =
        ∫ x in U, frobeniusS0 (h10Value v x) (f x)) →
      dirichletFractionalTestEnergy s U w < ⊤ ∧ dirichletFractionalTestNorm s U w ≤ C * N

/-- The \(H^s\) norm is recovered by duality against the dense \(L^2\)
subspace of the full dual. This uses the intrinsic fractional Sobolev
norm on a smooth bounded domain, as in Adams–Fournier, Chapter 7
<https://shop.elsevier.com/books/sobolev-spaces/adams/978-0-12-044143-3>. -/
def FractionalL2NormDuality : Prop :=
  ∀ (U : Set Point), IsSmoothDomain U → ∀ s : ℝ, 0 < s → s < 1 / 2 →
    ∀ (u : Lp S0 2 (volume.restrict U)) (C : ℝ), 0 ≤ C →
      (∀ (f : Lp S0 2 (volume.restrict U)) (N : ℝ), FractionalL2DualBound s U f N →
        |∫ x in U, frobeniusS0 (u x) (f x)| ≤ C * N) →
      MemHs s U u ∧ Real.sqrt ((fractionalEnergy s U u).toReal) ≤ C

/-- Adjoint \(H^2\) Dirichlet regularity followed by interpolation below
the trace threshold \(s=1/2\). The constant uses a uniform weak inverse
bound, the coefficient norms and the domain. The test is the solution of
the actual adjoint pairing. See the trace and interpolation theory of
Lions–Magenes <https://www.numdam.org/item/AIF_1961__11__137_0/> and
the global Dirichlet estimates of Gilbarg–Trudinger
<https://doi.org/10.1007/978-3-642-61798-0>. -/
def DirichletAdjointFractionalEstimate : Prop :=
  ∀ (U : Set Point), IsSmoothDomain U → ∀ (s p M : ℝ), 0 < s → s < 1 / 2 → 3 < p → 0 ≤ M →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : Point → (S0 × Gradient) →L[ℝ] S0)
      (P : H10 U ≃L[ℝ] HMinusOne U),
      HasBoundedDirichletCorrectionCoefficients U p M A →
      ‖P.symm.toContinuousLinearMap‖ ≤ M →
      (∀ v w : H10 U, P v w = weakCorrectionPairing U A v w) →
      ∀ (f : Lp S0 2 (volume.restrict U)) (N : ℝ), FractionalL2DualBound s U f N →
        ∃ w : H10 U, dirichletFractionalTestEnergy s U w < ⊤ ∧
          dirichletFractionalTestNorm s U w ≤ C * N ∧
          ∀ v : H10 U, P v w = ∫ x in U, frobeniusS0 (h10Value v x) (f x)

/-- Hardy's inequality and the integrated zero-trace collar estimate.
The latter is obtained by applying the normal-variable trace estimate
to the first derivative and integrating from its zero Dirichlet value.
The distance and volume are those of the actual smooth domain.
See Lions–Magenes, trace estimates in sections 2–5
<https://www.numdam.org/item/AIF_1961__11__137_0/> and the Sobolev–Hardy
inequalities in Adams–Fournier
<https://shop.elsevier.com/books/sobolev-spaces/adams/978-0-12-044143-3>. -/
def DirichletFractionalHardyAndCollar : Prop :=
  ∀ (U : Set Point), IsSmoothDomain U → ∀ s : ℝ, 0 < s → s < 1 / 2 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : H10 U, dirichletFractionalTestEnergy s U v < ⊤ →
      let d (x : Point) := Metric.infDist x (frontier U)
      (IntegrableOn (fun x => ‖h10Value v x‖ / d x) U volume ∧
        ∫ x in U, ‖h10Value v x‖ / d x ≤ C * dirichletFractionalTestNorm s U v) ∧
      ∀ t : ℝ, 0 < t →
        ∫ x in U ∩ {x | d x < t}, ‖h10Value v x‖ ≤ C * t^2 * dirichletFractionalTestNorm s U v

/-- The fractional compact embedding on a smooth bounded domain, with
the intrinsic fractional energies. See Adams–Fournier, Chapters 6 and 7
<https://shop.elsevier.com/books/sobolev-spaces/adams/978-0-12-044143-3>. -/
def FractionalSobolevCompactEmbedding : Prop :=
  ∀ (U : Set Point), IsSmoothDomain U → ∀ s t : ℝ, 0 < s → s < t → t < 1/2 →
    ∀ u : ℕ → Point → S0, (∀ n, MemHs t U (u n)) →
      (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ᶠ n in Filter.atTop, fractionalEnergy t U (u n) ≤ C) →
      ∃ (κ : ℕ → ℕ) (v : Point → S0), StrictMono κ ∧ ConvergesHs s U (u ∘ κ) v

/-- The inclusion of the zero-trace first-order graph into the intrinsic
fractional Sobolev spaces below order one. See Adams–Fournier, Chapter 7
<https://shop.elsevier.com/books/sobolev-spaces/adams/978-0-12-044143-3>. -/
def H10FractionalEmbedding : Prop :=
  ∀ (U : Set Point), IsSmoothDomain U → ∀ s : ℝ, 0 < s → s < 1 →
    ∀ v : H10 U, MemHs s U (h10Value v)

end External

end Thesis

end

module

public import Mathlib
public import Thesis.Model

/-! The Sobolev, boundary, convergence and geometric objects in the three limit theorems. -/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Topology
open scoped BigOperators ContDiff ENNReal NNReal Matrix Matrix.Norms.Frobenius

namespace Thesis

abbrev Gradient := Fin 3 → S0
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def IsDomain (U : Set Point) : Prop := IsOpen U ∧ IsConnected U

def CompactlyContained (U W : Set Point) : Prop :=
  IsCompact (closure U) ∧ closure U ⊆ W

def SmoothTest (U : Set Point) (φ : Point → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

def IsWeakGradient (U : Set Point) (u : Point → S0) (D : Point → Gradient) : Prop :=
  ∀ (j : Fin 3) (φ : Point → ℝ), SmoothTest U φ →
    (∫ x in U, coordDeriv j φ x • u x) = -(∫ x in U, φ x • D x j)

def MemH1 (U : Set Point) (u : Point → S0) (D : Point → Gradient) : Prop :=
  MemLp u 2 (volume.restrict U) ∧
    (∀ j, MemLp (fun x => D x j) 2 (volume.restrict U)) ∧ IsWeakGradient U u D

def MemH1Loc (U : Set Point) (u : Point → S0) (D : Point → Gradient) : Prop :=
  ∀ W : Set Point, IsOpen W → CompactlyContained W U → MemH1 W u D

def h1Deviation (U : Set Point) (u v : Point → S0) (D G : Point → Gradient) : ℝ≥0∞ :=
  ∫⁻ x in U, ENNReal.ofReal (‖u x - v x‖ ^ 2 + ∑ j, ‖D x j - G x j‖ ^ 2)

def StrongH1 (U : Set Point) (u : ℕ → Point → S0) (D : ℕ → Point → Gradient)
    (v : Point → S0) (G : Point → Gradient) : Prop :=
  (∀ n, MemH1 U (u n) (D n)) ∧ MemH1 U v G ∧
    Tendsto (fun n => h1Deviation U (u n) v (D n) G) atTop (𝓝 0)

def StrongH1Loc (U : Set Point) (u : ℕ → Point → S0) (D : ℕ → Point → Gradient)
    (v : Point → S0) (G : Point → Gradient) : Prop :=
  ∀ W : Set Point, IsOpen W → CompactlyContained W U → StrongH1 W u D v G

def HasZeroTrace (U : Set Point) (u : Point → S0) (D : Point → Gradient) : Prop :=
  MemH1 U u D ∧ ∀ δ : ℝ≥0∞, 0 < δ → ∃ φ : Point → S0,
    ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
      h1Deviation U u φ D (fun x j => coordDeriv j φ x) < δ

def SameTrace (U : Set Point) (u v : Point → S0) (D G : Point → Gradient) : Prop :=
  HasZeroTrace U (u - v) (D - G)

def HasSmoothTrace (U : Set Point) (u : Point → S0) (D : Point → Gradient)
    (b : frontier U → S0) : Prop :=
  ∃ B : Point → S0, ContDiff ℝ ∞ B ∧ (∀ x : frontier U, B x = b x) ∧
    SameTrace U u B D (fun x j => coordDeriv j B x)

def biaxialTensor (a : BulkCoefficients) (n m : Point) : Tensor :=
  vacuumRadius a • (Matrix.vecMulVec (fun i => n i) (fun i => n i) -
    Matrix.vecMulVec (fun i => m i) (fun i => m i))

def vacuum (a : BulkCoefficients) : Set S0 :=
  {A | ∃ n m : Point, ‖n‖ = 1 ∧ ‖m‖ = 1 ∧ inner ℝ n m = 0 ∧
    (A : Tensor) = biaxialTensor a n m}

def TakesVacuumValues (a : BulkCoefficients) (U : Set Point) (u : Point → S0) : Prop :=
  ∀ᵐ x ∂volume.restrict U, u x ∈ vacuum a

def energy (a : BulkCoefficients) (ε : ElasticScale) (U : Set Point)
    (u : Point → S0) (D : Point → Gradient) : ℝ≥0∞ :=
  ∫⁻ x in U, ENNReal.ofReal (energyDensity a ε (u x) (D x))

def dirichletEnergy (U : Set Point) (D : Point → Gradient) : ℝ≥0∞ :=
  ∫⁻ x in U, ENNReal.ofReal ((1/2 : ℝ) * gradientNormSq (D x))

def IsLocalEnergyMinimizer (a : BulkCoefficients) (ε : ElasticScale)
    (U : Set Point) (u : Point → S0) (D : Point → Gradient) : Prop :=
  MemH1Loc U u D ∧ ∀ (x : Point) (r : ℝ), 0 < r → Metric.closedBall x r ⊆ U →
    ∀ (v : Point → S0) (G : Point → Gradient), MemH1 (Metric.ball x r) v G →
      SameTrace (Metric.ball x r) v u G D →
      energy a ε (Metric.ball x r) u D ≤ energy a ε (Metric.ball x r) v G

def IsLocalDirichletMinimizer (a : BulkCoefficients) (U : Set Point)
    (u : Point → S0) (D : Point → Gradient) : Prop :=
  MemH1Loc U u D ∧ TakesVacuumValues a U u ∧
    ∀ (x : Point) (r : ℝ), 0 < r → Metric.closedBall x r ⊆ U →
      ∀ (v : Point → S0) (G : Point → Gradient), MemH1 (Metric.ball x r) v G →
        TakesVacuumValues a (Metric.ball x r) v → SameTrace (Metric.ball x r) v u G D →
        dirichletEnergy (Metric.ball x r) D ≤ dirichletEnergy (Metric.ball x r) G

def IsGlobalEnergyMinimizer (a : BulkCoefficients) (ε : ElasticScale) (U : Set Point)
    (b : frontier U → S0) (u : Point → S0) (D : Point → Gradient) : Prop :=
  MemH1 U u D ∧ HasSmoothTrace U u D b ∧
    ∀ (v : Point → S0) (G : Point → Gradient), MemH1 U v G → HasSmoothTrace U v G b →
      energy a ε U u D ≤ energy a ε U v G

def IsGlobalDirichletMinimizer (a : BulkCoefficients) (U : Set Point)
    (b : frontier U → S0) (u : Point → S0) (D : Point → Gradient) : Prop :=
  MemH1 U u D ∧ HasSmoothTrace U u D b ∧ TakesVacuumValues a U u ∧
    ∀ (v : Point → S0) (G : Point → Gradient), MemH1 U v G → HasSmoothTrace U v G b →
      TakesVacuumValues a U v → dirichletEnergy U D ≤ dirichletEnergy U G

def gradientTraceMul (D G : Point → Gradient) (A : Tensor) (x : Point) : ℝ :=
  ∑ j, (((D x j : S0) : Tensor) * (G x j : Tensor) * A).trace

def biaxialQuadratic (a : BulkCoefficients) (A : Tensor) : Tensor :=
  A ^ 2 - (2 * vacuumRadius a ^ 2 / 3) • (1 : Tensor)

def harmonicRhs (a : BulkCoefficients) (u : Point → S0) (D : Point → Gradient)
    (x : Point) : Tensor :=
  (-(gradientNormSq (D x) / (2 * vacuumRadius a ^ 2))) • (u x : Tensor) -
  (3 / vacuumRadius a ^ 4 * gradientTraceMul D D (u x : Tensor) x) •
    biaxialQuadratic a (u x)

def WeakLaplacianEq (U : Set Point) (D : Point → Gradient) (rhs : Point → Tensor) : Prop :=
  ∀ φ : Point → ℝ, SmoothTest U φ →
    (∑ j, ∫ x in U, coordDeriv j φ x • (D x j : Tensor)) =
      -(∫ x in U, φ x • rhs x)

def ClassicalGradient (u : Point → S0) : Point → Gradient :=
  fun x j => coordDeriv j u x

def singularSet (U : Set Point) (u : Point → S0) : Set Point :=
  {x ∈ U | ¬∃ (W : Set Point) (v : Point → S0),
    IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ContDiffOn ℝ ∞ v W ∧
      u =ᵐ[volume.restrict W] v}

def LocallyFiniteIn (U S : Set Point) : Prop :=
  ∀ K : Set Point, IsCompact K → K ⊆ U → (S ∩ K).Finite

def ConvergesCjLoc (j : ℕ) (U : Set Point) (u : ℕ → Point → S0) (v : Point → S0) : Prop :=
  (∀ n, ContDiffOn ℝ j (u n) U) ∧ ContDiffOn ℝ j v U ∧
    ∀ (k : ℕ), k ≤ j → ∀ K : Set Point, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun n => iteratedFDeriv ℝ k (u n)) (iteratedFDeriv ℝ k v) atTop K

def ConvergesScaledPotentialLoc (a : BulkCoefficients) (U : Set Point)
    (ε : ℕ → ElasticScale) (u : ℕ → Point → S0) : Prop :=
  ∀ W : Set Point, IsOpen W → CompactlyContained W U →
    (∀ n, MemLp (fun x => (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (u n x))
      1 (volume.restrict W)) ∧
    Tendsto (fun n => eLpNorm (fun x => (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (u n x))
      1 (volume.restrict W)) atTop (𝓝 0)

def multiIndexDerivative (m : Fin 3 → ℕ) (R : Point → Tensor) : Point → Tensor :=
  (coordDeriv 0)^[m 0] ((coordDeriv 1)^[m 1] ((coordDeriv 2)^[m 2] R))

def multiIndexNorm (j : ℕ) (R : Point → Tensor) (x : Point) : ℝ :=
  Real.sqrt (∑ m : Fin 3 → Fin (j + 1) with (∑ i, (m i).val) = j,
    ‖multiIndexDerivative (fun i => (m i).val) R x‖ ^ 2)

def IsSmoothDomain (U : Set Point) : Prop :=
  IsBoundedDomain U ∧ ∀ x ∈ frontier U,
    ∃ (r : ℝ) (A : Point ≃ₗᵢ[ℝ] Point) (g : Plane → ℝ),
      0 < r ∧ ContDiff ℝ ∞ g ∧ g 0 = 0 ∧
      U ∩ Metric.ball x r =
        {y | let z := A (y - x); g (WithLp.toLp 2 ![z 0, z 1]) < z 2} ∩ Metric.ball x r

abbrev QuaternionCoordinates := EuclideanSpace ℝ (Fin 4)
abbrev Sphere3 := Metric.sphere (0 : QuaternionCoordinates) 1

def IsSmoothBoundaryLift (U : Set Point) (u : frontier U → Sphere3) : Prop :=
  ∃ v : Point → QuaternionCoordinates, ContDiff ℝ ∞ v ∧
    ∀ x : frontier U, v x = (u x : QuaternionCoordinates)

def firstFrameVector (v : QuaternionCoordinates) : Point :=
  WithLp.toLp 2 ![v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2,
    2 * (v 1 * v 2 + v 0 * v 3), 2 * (v 1 * v 3 - v 0 * v 2)]

def secondFrameVector (v : QuaternionCoordinates) : Point :=
  WithLp.toLp 2 ![2 * (v 1 * v 2 - v 0 * v 3),
    v 0 ^ 2 - v 1 ^ 2 + v 2 ^ 2 - v 3 ^ 2, 2 * (v 0 * v 1 + v 2 * v 3)]

def traceFreeSymmetricPart (A : Tensor) : S0 :=
  ⟨(1/2 : ℝ) • (A + Aᵀ) - (A.trace / 3) • (1 : Tensor), by
    change ((1/2 : ℝ) • (A + Aᵀ) - (A.trace / 3) • (1 : Tensor))ᵀ = _ ∧
      ((1/2 : ℝ) • (A + Aᵀ) - (A.trace / 3) • (1 : Tensor)).trace = 0
    constructor
    · simp [add_comm]
    · have h : (1 : Tensor).trace = 3 := by simp
      simp [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, h, smul_eq_mul]
      ring⟩

def cover (a : BulkCoefficients) (v : Sphere3) : S0 :=
  traceFreeSymmetricPart (biaxialTensor a (firstFrameVector v) (secondFrameVector v))

def holderSeminorm {E : Type*} [NormedAddCommGroup E] (α : ℝ) (K : Set Point)
    (w : Point → E) : ℝ≥0∞ :=
  ⨆ (x : K) (y : K), ENNReal.ofReal (‖w x - w y‖ / (dist (x : Point) y) ^ α)

def ConvergesC1HolderLoc (α : ℝ) (U S : Set Point)
    (u : ℕ → Point → S0) (v : Point → S0) : Prop :=
  let W := closure U \ S
  let D := fun (w : Point → S0) (x : Point) (j : Fin 3) => fderivWithin ℝ w W x (axis j)
  (∀ n, ContDiffOn ℝ 1 (u n) W) ∧ ContDiffOn ℝ 1 v W ∧
    ∀ K : Set Point, IsCompact K → K ⊆ W →
      (∀ n, holderSeminorm α K (D (u n)) < ⊤) ∧ holderSeminorm α K (D v) < ⊤ ∧
      TendstoUniformlyOn u v atTop K ∧
      TendstoUniformlyOn (fun n => D (u n)) (D v) atTop K ∧
      Tendsto (fun n => holderSeminorm α K (D (u n) - D v)) atTop (𝓝 0)

def fractionalEnergy (s : ℝ) (U : Set Point) (u : Point → S0) : ℝ≥0∞ :=
  (∫⁻ x in U, ENNReal.ofReal (‖u x‖ ^ 2)) +
    ∫⁻ x in U, ∫⁻ y in U, ENNReal.ofReal (‖u x - u y‖ ^ 2 / (dist x y) ^ (3 + 2*s))

def MemHs (s : ℝ) (U : Set Point) (u : Point → S0) : Prop :=
  AEStronglyMeasurable u (volume.restrict U) ∧ fractionalEnergy s U u < ⊤

def ConvergesHs (s : ℝ) (U : Set Point) (u : ℕ → Point → S0) (v : Point → S0) : Prop :=
  (∀ n, MemHs s U (u n)) ∧ MemHs s U v ∧
  Tendsto (fun n => fractionalEnergy s U (u n - v)) atTop (𝓝 0)

abbrev H1Graph (U : Set Point) :=
  Lp S0 2 (volume.restrict U) × (Fin 3 → Lp S0 2 (volume.restrict U))

def h10Submodule (U : Set Point) : Submodule ℝ (H1Graph U) :=
  (Submodule.span ℝ {p : H1Graph U | ∃ φ : Point → S0,
    ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
      (p.1 : Point → S0) =ᵐ[volume.restrict U] φ ∧
      ∀ j, (p.2 j : Point → S0) =ᵐ[volume.restrict U] coordDeriv j φ}).topologicalClosure

abbrev H10 (U : Set Point) := ↥(h10Submodule U)
abbrev HMinusOne (U : Set Point) := H10 U →L[ℝ] ℝ

def h10Value {U : Set Point} (v : H10 U) : Point → S0 := v.val.1

def h10Gradient {U : Set Point} (v : H10 U) : Point → Gradient := fun x j => v.val.2 j x

def linearizedPairing (a : BulkCoefficients) (U : Set Point)
    (Q : Point → S0) (D : Point → Gradient) (v w : H10 U) : ℝ :=
  let r := vacuumRadius a
  let P := h10Value v
  let G := h10Gradient v
  let H := h10Gradient w
  ∫ x in U, -(∑ j, frobeniusS0 (G x j) (H x j)) +
    frobenius (
      (gradientNormSq (D x) / (2*r^2)) • (P x : Tensor) +
      ((∑ j, frobeniusS0 (D x j) (G x j)) / r^2) • (Q x : Tensor) +
      (6/r^4 * gradientTraceMul G D (Q x) x
        + 3/r^4 * gradientTraceMul D D (P x) x) • biaxialQuadratic a (Q x) +
      (3/r^4 * gradientTraceMul D D (Q x) x) •
        (↑(Q x) * ↑(P x) + ↑(P x) * ↑(Q x) -
          (2/3 * ((Q x : Tensor) * (P x : Tensor)).trace) • (1 : Tensor))
    ) (h10Value w x)

def normalPart (a : BulkCoefficients) (A B : Tensor) : Tensor :=
  let r := vacuumRadius a
  ((A * B).trace / (2*r^2)) • A +
    ((A^2 * B).trace / (2*r^4)) • (3 : ℝ) • biaxialQuadratic a A

def tangentPart (a : BulkCoefficients) (A B : Tensor) : Tensor := B - normalPart a A B

def tangentCorrectionRhs (a : BulkCoefficients) (Q P : Point → S0) (x : Point) : Tensor :=
  let r := vacuumRadius a
  let A : Tensor := Q x
  let B : Tensor := P x
  let N : Point → Tensor := fun y => normalPart a (Q y) (P y)
  let T : Point → Tensor := fun y => tangentPart a (Q y) (P y)
  let Qsq : Point → Tensor := fun y => (Q y : Tensor)^2
  let t₁ := (A * B).trace
  let t₂ := (A^2 * B).trace
  let g₁ := ∑ j, (coordDeriv j T x * (coordDeriv j Q x : S0)).trace
  let g₂ := ∑ j, (coordDeriv j T x * coordDeriv j Qsq x).trace
  (-(g₁ / r^2)) • A -
    ((2*g₂ + (T x * laplacian Qsq x).trace) / (2*r^4)) •
      (3 : ℝ) • biaxialQuadratic a A +
    ((2*a.a4 + 8*a.a6*r^2)*t₁) • T x - tangentPart a A (laplacian N x) +
    (3*a.a6'*t₂) • (A*B + B*A - (2/3*t₁) • (1 : Tensor)) -
    (3*a.a6'/r^2*t₂) • (t₂ • A + t₁ • biaxialQuadratic a A)

abbrev HausdorffOne : Measure Point := Measure.hausdorffMeasure 1

def CountablyRectifiableOne (S : Set Point) : Prop :=
  ∃ f : ℕ → ℝ → Point,
    (∀ i, ∃ L : ℝ≥0, LipschitzWith L (f i)) ∧
    HausdorffOne (S \ ⋃ i, range (f i)) = 0

def normalizedEnergyMeasure (a : BulkCoefficients) (ε : ElasticScale) (U : Set Point)
    (u : Point → S0) (D : Point → Gradient) : Measure Point :=
  (volume.restrict U).withDensity (fun x =>
    ENNReal.ofReal (energyDensity a ε (u x) (D x) / Real.log (1 / (ε : ℝ))))

def WeakStarOnClosure (U : Set Point) (μ : ℕ → Measure Point) (ν : Measure Point) : Prop :=
  ∀ φ : C(↥(closure U), ℝ),
    Tendsto (fun n => ∫ x, φ x ∂(μ n).comap ((↑) : ↥(closure U) → Point))
      atTop (𝓝 (∫ x, φ x ∂ν.comap ((↑) : ↥(closure U) → Point)))

def oneDensity (μ : Measure Point) (x : Point) (r : ℝ) : ℝ :=
  (μ (Metric.closedBall x r)).toReal / (2*r)

def kappaStar (a : BulkCoefficients) : ℝ := Real.pi * vacuumRadius a ^ 2 / 2

def DensityQuantized (a : BulkCoefficients) (μ : Measure Point) (S : Set Point) : Prop :=
  ∀ᵐ x ∂HausdorffOne.restrict S, ∃ θ : ℝ, (θ = kappaStar a ∨ θ = 2*kappaStar a) ∧
    Tendsto (oneDensity μ x) (𝓝[>] (0 : ℝ)) (𝓝 θ)

abbrev LineProjection := {P : Tensor // Pᵀ = P ∧ P * P = P ∧ P.rank = 1}
instance : MeasurableSpace LineProjection := borel LineProjection

def matrixAction (P : Tensor) (v : Point) : Point :=
  WithLp.toLp 2 (P.mulVec fun j => v j)

def IsApproxTangentLine (S : Set Point) (x : Point) (P : LineProjection) : Prop :=
  (∃ (θ : ℝ), 0 < θ ∧ Tendsto (oneDensity (HausdorffOne.restrict S) x) (𝓝[>] (0 : ℝ)) (𝓝 θ)) ∧
  ∀ δ > 0,
    Tendsto (fun r : ℝ =>
      HausdorffOne ((S ∩ Metric.ball x r) \ {y | ‖matrixAction (1 - P.val) (y - x)‖ ≤
        δ * ‖y - x‖}) / ENNReal.ofReal (2*r)) (𝓝[>] (0 : ℝ)) (𝓝 0)

def IsAssociatedVarifold (U S : Set Point) (μ : Measure Point)
    (V : Measure (Point × LineProjection)) : Prop :=
  ∃ (θ : Point → ℝ≥0∞) (P : Point → LineProjection),
    Measurable θ ∧ (∫⁻ x, θ x ∂HausdorffOne.restrict S) < ⊤ ∧
    μ.restrict U = (HausdorffOne.restrict S).withDensity θ ∧
    AEMeasurable P (μ.restrict U) ∧
    (∀ᵐ x ∂μ.restrict U, IsApproxTangentLine S x (P x)) ∧
    V = Measure.map (fun x => (x, P x)) (μ.restrict U)

def IsStationaryVarifold (U : Set Point) (V : Measure (Point × LineProjection)) : Prop :=
  ∀ X : Point → Point, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
    (∫ y, ∑ i : Fin 3, ∑ j : Fin 3, y.2.val i j * coordDeriv i X y.1 j ∂V) = 0

abbrev Disk := Metric.closedBall (0 : Plane) 1

def IsSmoothDiskEmbedding (d : Plane → Point) : Prop :=
  ContDiffOn ℝ ∞ d Disk ∧ InjOn d Disk ∧
  ∀ y ∈ Disk, Function.Injective (fderivWithin ℝ d Disk y)

def HasMeridianFilling (a : BulkCoefficients) (d : Plane → Point) (Q : Point → S0) : Prop :=
  ∃ v : C(↥Disk, S0), (∀ y, v y ∈ vacuum a) ∧
    ∀ y : ↥Disk, ‖(y : Plane)‖ = 1 → v y = Q (d y)

def incidentSegments {m : ℕ} (p q : Fin m → Point) (x : Point) : Finset (Fin m) :=
  Finset.univ.filter fun i => x = p i ∨ x = q i

def outwardDirection {m : ℕ} (p q : Fin m → Point) (x : Point)
    (i : ↥(incidentSegments p q x)) : Point :=
  let y := if x = p i then q i else p i
  ‖y - x‖⁻¹ • (y - x)

end Thesis

end
end

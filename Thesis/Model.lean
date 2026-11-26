module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace

/-! The tensor space, the sextic potential, and the energy density. -/

@[expose] public section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace Thesis

abbrev Point := EuclideanSpace ℝ (Fin 3)
abbrev Tensor := Matrix (Fin 3) (Fin 3) ℝ

def IsBoundedDomain (Ω : Set Point) : Prop :=
  IsOpen Ω ∧ IsConnected Ω ∧ Bornology.IsBounded Ω

/-- The subspace of symmetric traceless tensors, with the induced Frobenius norm. -/
def symmetricTraceless : Submodule ℝ Tensor where
  carrier := {A | Aᵀ = A ∧ A.trace = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change Aᵀ = A ∧ A.trace = 0 at hA
    change Bᵀ = B ∧ B.trace = 0 at hB
    change (A + B)ᵀ = A + B ∧ (A + B).trace = 0
    simp [Matrix.transpose_add, Matrix.trace_add, hA.1, hB.1, hA.2, hB.2]
  smul_mem' := by
    intro c A hA
    change Aᵀ = A ∧ A.trace = 0 at hA
    change (c • A)ᵀ = c • A ∧ (c • A).trace = 0
    simp [Matrix.transpose_smul, Matrix.trace_smul, hA.1, hA.2]

abbrev S0 := ↥symmetricTraceless

theorem S0.transpose_eq (A : S0) : (A : Tensor)ᵀ = (A : Tensor) := A.property.1

theorem S0.trace_eq_zero (A : S0) : (A : Tensor).trace = 0 := A.property.2

/-- Frobenius contraction of two real tensors. -/
def frobenius (A B : Tensor) : ℝ := (Aᵀ * B).trace

def frobeniusS0 (A B : S0) : ℝ := frobenius A B

abbrev ElasticScale := Set.Ioo (0 : ℝ) 1

/-- The four positive coefficients of the sextic potential. -/
structure BulkCoefficients where
  a2 : ℝ
  a4 : ℝ
  a6 : ℝ
  a6' : ℝ
  a2_pos : 0 < a2
  a4_pos : 0 < a4
  a6_pos : 0 < a6
  a6'_pos : 0 < a6'

/-- The minimizing value of `tr (Q²)`, equal to `2 r_*²`. -/
noncomputable def preferredTraceSq (a : BulkCoefficients) : ℝ :=
  (-a.a4 + Real.sqrt (a.a4 ^ 2 + 4 * a.a2 * a.a6)) / (2 * a.a6)

noncomputable def vacuumRadius (a : BulkCoefficients) : ℝ :=
  Real.sqrt (preferredTraceSq a / 2)

noncomputable def bulkPotential (a : BulkCoefficients) (A : S0) : ℝ :=
  let t := ((A : Tensor) ^ 2).trace
  let s := ((A : Tensor) ^ 3).trace
  let t₀ := preferredTraceSq a
  a.a2 / 2 * t₀ - a.a4 / 4 * t₀ ^ 2 - a.a6 / 6 * t₀ ^ 3
    - a.a2 / 2 * t + a.a4 / 4 * t ^ 2 + a.a6 / 6 * t ^ 3 + a.a6' / 6 * s ^ 2

/-- The expression for `Ψ` in the Euler–Lagrange equation, viewed in the ambient matrix space. -/
noncomputable def bulkGradient (a : BulkCoefficients) (A : S0) : Tensor :=
  let t := ((A : Tensor) ^ 2).trace
  (-a.a2 + a.a4 * t + a.a6 * t ^ 2) • (A : Tensor)
    + (a.a6' * ((A : Tensor) ^ 3).trace) • ((A : Tensor) ^ 2 - (t / 3) • (1 : Tensor))

/-- `Ψ` as a symmetric traceless tensor. -/
noncomputable def bulkForce (a : BulkCoefficients) (A : S0) : S0 :=
  ⟨bulkGradient a A, by
    change (bulkGradient a A)ᵀ = bulkGradient a A ∧ (bulkGradient a A).trace = 0
    constructor
    · simp [bulkGradient, pow_two, Matrix.transpose_mul, A.transpose_eq]
    · have h : (1 : Tensor).trace = 3 := by simp
      simp [bulkGradient, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, h,
        A.trace_eq_zero, smul_eq_mul]⟩

noncomputable def axis (i : Fin 3) : Point := EuclideanSpace.single i 1

noncomputable def coordDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (u : Point → E) (x : Point) : E := fderiv ℝ u x (axis i)

noncomputable def laplacian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Point → E) (x : Point) : E := ∑ i : Fin 3, coordDeriv i (coordDeriv i u) x

noncomputable def gradientNormSq (D : Fin 3 → S0) : ℝ :=
  ∑ i, frobeniusS0 (D i) (D i)

noncomputable def energyDensity (a : BulkCoefficients) (ε : ElasticScale)
    (A : S0) (D : Fin 3 → S0) : ℝ :=
  (1 / 2 : ℝ) * gradientNormSq D + (ε : ℝ)⁻¹ ^ 2 * bulkPotential a A

end Thesis

end

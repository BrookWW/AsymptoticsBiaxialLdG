module

public import Thesis.Variational.EulerLagrange

/-! Linear Poisson regularity on the closure of a smooth Dirichlet domain. -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace Thesis.External

/-- Global Dirichlet regularity for the linear Poisson equation, with
the actual Sobolev trace and distributional spatial columns. The first
step is the global (W^{2,p}) estimate and Sobolev embedding for (p>3).
The second is the boundary Schauder bootstrap with smooth prescribed data.
See [Gilbarg and Trudinger](https://doi.org/10.1007/978-3-642-61798-0),
Chapters 6 and 9. -/
structure GlobalDirichletPoissonRegularity : Prop where
  c1Representative :
    ∀ {U : Set Point} {u b : Point → S0} {D : Point → Gradient} {F : Point → Tensor},
      IsSmoothDomain U → ContDiff ℝ ∞ b → MemH1 U u D →
      SameTrace U u b D (ClassicalGradient b) → IsWeakPoisson U D F →
      (∃ M : ℝ, ∀ᵐ x ∂volume.restrict U, ‖F x‖ ≤ M) →
      ∃ v : Point → S0, u =ᵐ[volume.restrict U] v ∧
        ContDiffOn ℝ 1 v (closure U) ∧ EqOn v b (frontier U)
  contDiffOn_succ :
    ∀ (n : ℕ), 0 < n →
      ∀ {U : Set Point} {u b : Point → S0} {D : Point → Gradient} {F : Point → Tensor},
        IsSmoothDomain U → ContDiff ℝ ∞ b → MemH1 U u D →
        SameTrace U u b D (ClassicalGradient b) → IsWeakPoisson U D F →
        ContDiffOn ℝ n u (closure U) → ContDiffOn ℝ n F (closure U) →
        ContDiffOn ℝ (↑(n + 1) : ℕ∞ω) u (closure U)

/-- The closure regularity needed for the variational limits. Ordinary
interior elliptic regularity supplies the higher derivatives in the open
domain. -/
structure GlobalDirichletPoissonClosureC2 : Prop where
  c1Representative :
    ∀ {U : Set Point} {u b : Point → S0} {D : Point → Gradient} {F : Point → Tensor},
      IsSmoothDomain U → ContDiff ℝ ∞ b → MemH1 U u D →
      SameTrace U u b D (ClassicalGradient b) → IsWeakPoisson U D F →
      (∃ M : ℝ, ∀ᵐ x ∂volume.restrict U, ‖F x‖ ≤ M) →
      ∃ v : Point → S0, u =ᵐ[volume.restrict U] v ∧
        ContDiffOn ℝ 1 v (closure U) ∧ EqOn v b (frontier U)
  contDiffOn_two :
    ∀ {U : Set Point} {u b : Point → S0} {D : Point → Gradient} {F : Point → Tensor},
      IsSmoothDomain U → ContDiff ℝ ∞ b → MemH1 U u D →
      SameTrace U u b D (ClassicalGradient b) → IsWeakPoisson U D F →
      ContDiffOn ℝ 1 u (closure U) → ContDiffOn ℝ 1 F (closure U) →
      ContDiffOn ℝ 2 u (closure U)

theorem GlobalDirichletPoissonRegularity.closureC2 (h : GlobalDirichletPoissonRegularity) :
    GlobalDirichletPoissonClosureC2 :=
  ⟨h.c1Representative,h.contDiffOn_succ 1 (by decide)⟩

/-- The classical Dirichlet inputs used to construct weak bounded-force
representatives. Smooth source data admit a classical zero-boundary solution.
The bootstrap applies to the original fixed-trace equation on the closure.
See [Gilbarg and Trudinger](https://doi.org/10.1007/978-3-642-61798-0),
Chapter 6. -/
structure ClassicalDirichletPoissonRegularity : Prop where
  smoothZeroTraceSolution :
    ∀ {U : Set Point}, IsSmoothDomain U → ∀ {f : Point → S0}, ContDiff ℝ ∞ f →
      ∃ v : Point → S0, ContDiffOn ℝ 2 v (closure U) ∧
        EqOn v (fun _ => 0) (frontier U) ∧ ∀ x ∈ U, laplacian v x = f x
  contDiffOn_succ :
    ∀ (n : ℕ), 0 < n →
      ∀ {U : Set Point} {u b : Point → S0} {D : Point → Gradient} {F : Point → Tensor},
        IsSmoothDomain U → ContDiff ℝ ∞ b → MemH1 U u D →
        SameTrace U u b D (ClassicalGradient b) → IsWeakPoisson U D F →
        ContDiffOn ℝ n u (closure U) → ContDiffOn ℝ n F (closure U) →
        ContDiffOn ℝ (↑(n + 1) : ℕ∞ω) u (closure U)

/-- Boundary Schauder regularity for an existing weak fixed-trace solution.
One additional derivative of the source supplies the Hölder control for
the next integer order at the wall. See
[Gilbarg and Trudinger](https://doi.org/10.1007/978-3-642-61798-0), Chapter 6. -/
def GlobalDirichletPoissonSchauderStep : Prop :=
  ∀ (n : ℕ), ∀ {U : Set Point} {u b : Point → S0} {D : Point → Gradient} {F : Point → Tensor},
    IsSmoothDomain U → ContDiff ℝ ∞ b → MemH1 U u D →
    SameTrace U u b D (ClassicalGradient b) → IsWeakPoisson U D F →
    ContDiffOn ℝ n u (closure U) → ContDiffOn ℝ (↑(n + 1) : ℕ∞ω) F (closure U) →
    ContDiffOn ℝ (↑(n + 2) : ℕ∞ω) u (closure U)

/-- The classical boundary Schauder estimate, expressed at integer order.
The solution satisfies its pointwise equation in the interior and its
continuous Dirichlet values on the actual wall. A source of class Cⁿ⁺¹
has the Hölder regularity needed for Cⁿ⁺² at the wall.
See [Gilbarg and Trudinger](https://doi.org/10.1007/978-3-642-61798-0_6),
Theorem 6.19. -/
def ClassicalDirichletPoissonBoundarySchauder : Prop :=
  ∀ (n : ℕ), ∀ {U : Set Point} {u b f : Point → S0},
    IsSmoothDomain U → ContDiff ℝ ∞ b → ContDiffOn ℝ 2 u U →
    ContinuousOn u (closure U) → EqOn u b (frontier U) →
    ContDiffOn ℝ (↑(n + 1) : ℕ∞ω) f (closure U) →
    (∀ x ∈ U, laplacian u x = f x) → ContDiffOn ℝ (↑(n + 2) : ℕ∞ω) u (closure U)

end Thesis.External

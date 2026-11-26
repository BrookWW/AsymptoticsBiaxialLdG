module

public import Thesis.Variational.DirichletAdjoint
public import Thesis.Variational.DirichletAdjointCoefficients
import Thesis.Variational.H10FractionalEmbedding
import Thesis.Variational.H10WeakGreen
import Thesis.Variational.DirichletLaplacianFractional

/-! The lower-order adjoint is reduced to a pure fractional Dirichlet
Laplacian estimate. -/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Frobenius

namespace Thesis

local instance adjointRegularityFrobenius : InnerProductSpace ℝ S0 := frobeniusInnerProductSpace

local instance adjointRegularityTensorENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

local instance adjointRegularityDualNormed (U : Set Point) : NormedAddCommGroup (HMinusOne U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance adjointRegularityDualSpace (U : Set Point) : NormedSpace ℝ (HMinusOne U) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

private theorem memLp_two_of_memHs {U : Set Point} {s : ℝ} {u : Point → S0} (hu : MemHs s U u) :
    MemLp u 2 (volume.restrict U) :=
  memLp_two_of_finite_tensor_square hu.1 ((le_add_of_nonneg_right zero_le).trans_lt hu.2)

private theorem norm_toLp_le_fractionalNorm {U : Set Point} {s : ℝ} {u : Point → S0}
    (hu : MemHs s U u) :
    ‖(memLp_two_of_memHs hu).toLp u‖ ≤ Real.sqrt ((fractionalEnergy s U u).toReal) := by
  let P := (memLp_two_of_memHs hu).toLp u
  have hE : ENNReal.ofReal (‖P‖ ^ 2) = ∫⁻ x in U, ENNReal.ofReal (‖u x‖ ^ 2) := by
    rw [← lintegral_sq_norm_lp]
    apply lintegral_congr_ae
    filter_upwards [(memLp_two_of_memHs hu).coeFn_toLp] with x hx
    exact congrArg (fun y : S0 => ENNReal.ofReal (‖y‖ ^ 2)) hx
  apply Real.le_sqrt_of_sq_le
  have hLe : ENNReal.ofReal (‖P‖ ^ 2) ≤ fractionalEnergy s U u := by
    rw [hE]
    exact le_add_of_nonneg_right zero_le
  have h := ENNReal.toReal_mono hu.2.ne hLe
  rwa [ENNReal.toReal_ofReal (sq_nonneg _)] at h

private theorem fractionalL2DualBound_of_lp {U : Set Point} {s : ℝ} (g : Lp S0 2 (volume.restrict U)) :
    FractionalL2DualBound s U g ‖g‖ := by
  refine ⟨norm_nonneg _,?_⟩
  intro u hu
  let P := (memLp_two_of_memHs hu).toLp u
  have hEq : (∫ x in U, frobeniusS0 (u x) (g x)) = inner ℝ P g := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_two_of_memHs hu).coeFn_toLp] with x hx
    rw [hx,frobenius_inner_eq]
  rw [hEq]
  exact (abs_real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_right (norm_toLp_le_fractionalNorm hu) (norm_nonneg g)).trans_eq (mul_comm _ _))

private theorem integral_frobenius_sub_Lp_right {U : Set Point}
    {u : Point → S0} (hu : MemLp u 2 (volume.restrict U))
    (f g : Lp S0 2 (volume.restrict U)) :
    (∫ x in U, frobeniusS0 (u x) ((f-g : Lp S0 2 (volume.restrict U)) x)) =
      (∫ x in U, frobeniusS0 (u x) (f x)) - ∫ x in U, frobeniusS0 (u x) (g x) := by
  have hinF := integrable_frobenius_of_memLp hu (Lp.memLp f)
  have hinG := integrable_frobenius_of_memLp hu (Lp.memLp g)
  rw [← integral_sub hinF hinG]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with x hx
  change ((f-g : Lp S0 2 (volume.restrict U)) x) = f x - g x at hx
  rw [hx,← frobenius_inner_eq,inner_sub_right,frobenius_inner_eq,frobenius_inner_eq]

private theorem fractionalL2DualBound_sub {U : Set Point} {s : ℝ}
    {f g : Lp S0 2 (volume.restrict U)} {N M : ℝ}
    (hf : FractionalL2DualBound s U f N) (hg : FractionalL2DualBound s U g M) :
    FractionalL2DualBound s U (f-g) (N+M) := by
  refine ⟨add_nonneg hf.1 hg.1,?_⟩
  intro u hu
  rw [integral_frobenius_sub_Lp_right (memLp_two_of_memHs hu) f g]
  exact (abs_sub _ _).trans ((add_le_add (hf.2 u hu) (hg.2 u hu)).trans_eq (add_mul _ _ _).symm)

private theorem exists_fractional_forcingFunctional {U : Set Point} (hU : IsBoundedDomain U)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp S0 2 (volume.restrict U)) (N : ℝ),
      FractionalL2DualBound s U f N →
      ∃ F : HMinusOne U, ‖F‖ ≤ C*N ∧ ∀ v : H10 U,
        F v = ∫ x in U, frobeniusS0 (h10Value v x) (f x) := by
  obtain ⟨C,hC,hEmb⟩ := exists_h10FractionalEmbedding_bound hU s hs hs'
  refine ⟨C,hC,?_⟩
  intro f N hN
  obtain ⟨F,hF⟩ := exists_H10_forcingFunctional_of_memLp (Lp.memLp f)
  have hE (v : H10 U) : F v = ∫ x in U, frobeniusS0 (h10Value v x) (f x) :=
    (hF v).2.trans (integral_congr_ae (Eventually.of_forall fun x => frobenius_comm _ _))
  refine ⟨F,ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC hN.1) (fun v => ?_),hE⟩
  rw [hE,Real.norm_eq_abs]
  exact (hN.2 _ (hEmb v).1).trans ((mul_le_mul_of_nonneg_left (hEmb v).2 hN.1).trans_eq (by ring))

private theorem principal_pairing_of_adjoint_equation
    {U : Set Point} {A : Point → (S0 × Gradient) →L[ℝ] S0}
    (P : H10 U ≃L[ℝ] HMinusOne U) (hP : ∀ v w : H10 U, P v w = weakCorrectionPairing U A v w)
    (w : H10 U) (f g : Lp S0 2 (volume.restrict U))
    (hW : ∀ v : H10 U, P v w = ∫ x in U, frobeniusS0 (h10Value v x) (f x))
    (hLower : ∀ v : H10 U,
      IntegrableOn (fun x => frobeniusS0 (A x (h10Value v x,h10Gradient v x)) (h10Value w x)) U ∧
      (∫ x in U, frobeniusS0 (A x (h10Value v x,h10Gradient v x)) (h10Value w x)) =
        ∫ x in U, frobeniusS0 (h10Value v x) (g x)) :
    ∀ v : H10 U,
      (∫ x in U, -(∑ j : Fin 3, frobeniusS0 (h10Gradient v x j) (h10Gradient w x j))) =
        ∫ x in U, frobeniusS0 (h10Value v x) ((f-g : Lp S0 2 (volume.restrict U)) x) := by
  intro v
  have hPrincipal : IntegrableOn
      (fun x => -(∑ j : Fin 3, frobeniusS0 (h10Gradient v x j) (h10Gradient w x j))) U :=
    (integrable_finsetSum Finset.univ (fun j _ =>
      integrable_frobenius_of_memLp (Lp.memLp (v.val.2 j)) (Lp.memLp (w.val.2 j)))).neg
  have h := (hP v w).symm.trans (hW v)
  rw [weakCorrectionPairing,integral_add hPrincipal (hLower v).1,(hLower v).2] at h
  have hSub := eq_sub_of_add_eq h
  exact hSub.trans (integral_frobenius_sub_Lp_right (Lp.memLp v.val.1) f g).symm

private theorem exists_adjoint_of_fractional_bounded_forcing
    (U : Set Point) (hU : IsBoundedDomain U) {s : ℝ} (hs : 0 < s) (hs₁ : s < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : H10 U ≃L[ℝ] HMinusOne U) (M : ℝ),
      0 ≤ M → ‖P.symm.toContinuousLinearMap‖ ≤ M →
      ∀ (f : Lp S0 2 (volume.restrict U)) (N : ℝ), FractionalL2DualBound s U f N →
        ∃ w : H10 U, ‖w‖ ≤ M*(C*N) ∧
          ∀ v : H10 U, P v w = ∫ x in U, frobeniusS0 (h10Value v x) (f x) := by
  obtain ⟨C,hC,hForcing⟩ := exists_fractional_forcingFunctional (U := U) (s := s) hU hs hs₁
  refine ⟨C,hC,?_⟩
  intro P M hM hInv f N hN
  obtain ⟨F,hF,hFApply⟩ := hForcing f N hN
  obtain ⟨w,hW,hApply,_⟩ := exists_unique_dirichletAdjoint_of_forcing P F
  exact ⟨w,hW.trans (mul_le_mul hInv hF (norm_nonneg F) hM),fun v => (hApply v).trans (hFApply v)⟩

private theorem exists_pure_fractional_forcing_of_adjoint
    {U : Set Point} (hU : IsBoundedDomain U) {s p M : ℝ} (hp : 3 < p)
    (A : Point → (S0 × Gradient) →L[ℝ] S0)
    (P : H10 U ≃L[ℝ] HMinusOne U)
    (hA : HasBoundedDirichletCorrectionCoefficients U p M A)
    (hP : ∀ v w : H10 U, P v w = weakCorrectionPairing U A v w)
    (f : Lp S0 2 (volume.restrict U)) (N : ℝ) (hN : FractionalL2DualBound s U f N)
    (w : H10 U) (hPair : ∀ v : H10 U, P v w = ∫ x in U, frobeniusS0 (h10Value v x) (f x))
    {L : ℝ} (hW : ‖w‖ ≤ L) :
    ∃ g : Lp S0 2 (volume.restrict U),
      FractionalL2DualBound s U g (N+lowerAdjointL2Constant U p M*L) ∧
      ∀ v : H10 U, (∫ x in U, -(∑ j : Fin 3, frobeniusS0 (h10Gradient v x j) (h10Gradient w x j))) =
        ∫ x in U, frobeniusS0 (h10Value v x) (g x) := by
  have h := @lowerAdjointL2_forcing U hU p M hp A hA w
  obtain ⟨g,hG,hGApply⟩ := h
  have hGb : ‖g‖ ≤ lowerAdjointL2Constant U p M * L :=
    hG.trans (mul_le_mul_of_nonneg_left hW (lowerAdjointL2Constant_nonneg U p M))
  have hOrder : N+‖g‖ ≤ N+lowerAdjointL2Constant U p M*L := by gcongr
  have hDual := fractionalL2DualBound_sub hN (fractionalL2DualBound_of_lp g)
  refine ⟨f-g,⟨hDual.1.trans hOrder,?_⟩,principal_pairing_of_adjoint_equation P hP w f g hPair hGApply⟩
  intro u hu
  exact (hDual.2 _ hu).trans (mul_le_mul_of_nonneg_right hOrder (Real.sqrt_nonneg _))

/-- The only fractional regularity input for the full correction adjoint is
the pure Dirichlet Laplacian estimate. The weak adjoint, lower-order terms
and all dependencies of its bound are proved on the original Sobolev graph. -/
theorem dirichletAdjointFractionalEstimate_of_laplacian
    (hLap : External.DirichletLaplacianFractionalRegularity) : External.DirichletAdjointFractionalEstimate := by
  intro U hU s p M hs hs₁ hp hM
  obtain ⟨C₀,hC₀,hPure⟩ := hLap U hU s hs hs₁
  have hsLessOne : s < 1 := hs₁.trans (by norm_num : (1 : ℝ)/2 < 1)
  have hDomain : IsBoundedDomain U := hU.1
  have hExists := @exists_adjoint_of_fractional_bounded_forcing U hDomain s hs hsLessOne
  rcases hExists with ⟨C₁,hC₁,hSolver⟩
  let C₂ := lowerAdjointL2Constant U p M
  have hC₂ : 0 ≤ C₂ := lowerAdjointL2Constant_nonneg U p M
  let C := C₀ * (1+C₂*M*C₁)
  have hC : 0 ≤ C := mul_nonneg hC₀ (add_nonneg zero_le_one (mul_nonneg (mul_nonneg hC₂ hM) hC₁))
  refine ⟨C,hC,?_⟩
  intro A P hA hInv hP f N hN
  obtain ⟨w,hNorm,hPair⟩ := hSolver P M hM hInv f N hN
  obtain ⟨g,hDual,hWeak⟩ := exists_pure_fractional_forcing_of_adjoint hU.1 hp A P hA hP f N hN w hPair hNorm
  obtain ⟨hFin,hEst⟩ := hPure w g (N+C₂*(M*(C₁*N))) hDual hWeak
  have hMul : C₀ * (N+C₂*(M*(C₁*N))) = C * N := by unfold C; ring
  exact ⟨w,hFin,hEst.trans_eq hMul,hPair⟩

/-- Fractional adjoint regularity with the intrinsic trace and the actual
first-order coefficient columns. -/
theorem dirichletAdjointFractionalEstimate : External.DirichletAdjointFractionalEstimate :=
  dirichletAdjointFractionalEstimate_of_laplacian dirichletLaplacianFractionalRegularity

end Thesis

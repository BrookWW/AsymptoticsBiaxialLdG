module

public import Thesis.External.FractionalDirichlet
public import Thesis.Foundation.FrobeniusInnerProduct
import Thesis.Variational.SobolevCoefficientProduct
import Thesis.Variational.H10WeakGreen
import Thesis.Variational.ScaledDefects
import Thesis.Foundation.WeakGradient
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Integration by parts for the original lower-order coordinates of the
Dirichlet correction operator. -/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal NNReal Matrix.Norms.Frobenius

namespace Thesis

local instance adjointCoefficientFrobenius : InnerProductSpace ℝ S0 := frobeniusInnerProductSpace
local instance adjointCoefficientComplete : CompleteSpace S0 := complete_of_proper

local instance adjointCoefficientTensorENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

local instance adjointCoefficientTensorENormed : ENormedAddMonoid S0 :=
  NormedAddGroup.toENormedAddMonoid

local instance adjointCoefficientColumnNormed : NormedAddCommGroup (S0 →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance adjointCoefficientColumnSpace : NormedSpace ℝ (S0 →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance adjointCoefficientColumnMetric : MetricSpace (S0 →L[ℝ] S0) :=
  adjointCoefficientColumnNormed.toMetricSpace

local instance adjointCoefficientColumnPseudoMetrizable : TopologicalSpace.PseudoMetrizableSpace (S0 →L[ℝ] S0) :=
  @UniformSpace.pseudoMetrizableSpace (S0 →L[ℝ] S0)
    adjointCoefficientColumnMetric.toPseudoMetricSpace.toUniformSpace inferInstance

local instance adjointCoefficientStateNormed : NormedAddCommGroup ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance adjointCoefficientStateSpace : NormedSpace ℝ ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance adjointCoefficientDerivativeNorm : Norm (Point →L[ℝ] S0 →L[ℝ] S0) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ)

local instance adjointCoefficientHolder : ENNReal.HolderTriple 3 6 2 := ennreal_holderTriple_three_six_two

private abbrev Coefficient := S0 →L[ℝ] S0
private abbrev StateCoefficient := (S0 × Gradient) →L[ℝ] S0

private def frobeniusAdjointCLM : Coefficient →L[ℝ] Coefficient := by
  let R := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := S0) (F := S0)
  exact
    { toFun := R
      map_add' := R.map_add
      map_smul' := fun c x => by
        have h := R.map_smulₛₗ c x
        rw [starRingEnd_apply,star_trivial] at h
        with_unfolding_all exact h
      cont := R.continuous }

private theorem frobeniusAdjointCLM_norm (L : Coefficient) : ‖frobeniusAdjointCLM L‖ = ‖L‖ :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := S0) (F := S0)).norm_map L

private theorem frobeniusAdjointCLM_pair (L : Coefficient) (x y : S0) :
    frobeniusS0 x (frobeniusAdjointCLM L y) = frobeniusS0 (L x) y := by
  rw [← frobenius_inner_eq, ← frobenius_inner_eq]
  exact ContinuousLinearMap.adjoint_inner_right L x y

private def adjointValueColumn (A : Point → StateCoefficient) (x : Point) : Coefficient :=
  frobeniusAdjointCLM ((A x).comp (ContinuousLinearMap.inl ℝ S0 Gradient))

private def adjointGradientColumn (A : Point → StateCoefficient) (i : Fin 3) (x : Point) : Coefficient :=
  frobeniusAdjointCLM (correctionFirstOrderColumn A i x)

private def adjointDivergenceColumn {U : Set Point} (A : Point → StateCoefficient)
    (w : H10 U) (i : Fin 3) (x : Point) : S0 :=
  (coordDeriv i (adjointGradientColumn A i) x) (h10Value w x) +
    (adjointGradientColumn A i x) (h10Gradient w x i)

private def lowerAdjointField {U : Set Point} (A : Point → StateCoefficient) (w : H10 U) (x : Point) : S0 :=
  adjointValueColumn A x (h10Value w x) - ∑ i : Fin 3, adjointDivergenceColumn A w i x

private theorem adjointValueColumn_norm_le (A : Point → StateCoefficient) (x : Point) :
    ‖adjointValueColumn A x‖ ≤ ‖A x‖ := by
  unfold adjointValueColumn
  rw [frobeniusAdjointCLM_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (A x))
  intro v
  change ‖A x (v,0)‖ ≤ ‖A x‖ * ‖v‖
  have h := (A x).le_opNorm ((v,0) : S0 × Gradient)
  rw [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg v)] at h
  with_unfolding_all exact h

private theorem firstOrderColumn_norm_le (A : Point → StateCoefficient) (i : Fin 3) (x : Point) :
    ‖adjointGradientColumn A i x‖ ≤ ‖A x‖ := by
  unfold adjointGradientColumn correctionFirstOrderColumn
  rw [frobeniusAdjointCLM_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (A x))
  intro v
  change ‖A x (0,Pi.single i v)‖ ≤ ‖A x‖ * ‖v‖
  have h := (A x).le_opNorm ((0,Pi.single i v) : S0 × Gradient)
  rw [Prod.norm_def,norm_zero,Pi.norm_single,max_eq_right (norm_nonneg v)] at h
  with_unfolding_all exact h

private theorem adjointGradientColumn_contDiffOn {U : Set Point} {A : Point → StateCoefficient}
    {p M : ℝ} (hA : HasBoundedDirichletCorrectionCoefficients U p M A) (i : Fin 3) :
    ContDiffOn ℝ 1 (adjointGradientColumn A i) U :=
  frobeniusAdjointCLM.contDiff.comp_contDiffOn ((hA.2.2 i).1)

private theorem norm_adjointGradientColumn_deriv_le {U : Set Point} (hU : IsOpen U)
    {A : Point → StateCoefficient} {p M : ℝ} (hA : HasBoundedDirichletCorrectionCoefficients U p M A)
    (i j : Fin 3) {x : Point} (hx : x ∈ U) :
    ‖coordDeriv j (adjointGradientColumn A i) x‖ ≤
      ‖fderiv ℝ (correctionFirstOrderColumn A i) x‖ := by
  have h := (((hA.2.2 i).1 x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  rw [show coordDeriv j (adjointGradientColumn A i) x =
    frobeniusAdjointCLM (coordDeriv j (correctionFirstOrderColumn A i) x)
    from coordDeriv_compCLM frobeniusAdjointCLM h j, frobeniusAdjointCLM_norm]
  have hOp := (fderiv ℝ (correctionFirstOrderColumn A i) x).le_opNorm (axis j)
  rw [show ‖axis j‖ = 1 by simp [axis],mul_one] at hOp
  with_unfolding_all exact hOp

private theorem adjointValueColumn_memLp_top {U : Set Point} {A : Point → StateCoefficient}
    {p M : ℝ} (hA : HasBoundedDirichletCorrectionCoefficients U p M A) :
    MemLp (adjointValueColumn A) ⊤ (volume.restrict U) ∧
      eLpNorm (adjointValueColumn A) ⊤ (volume.restrict U) ≤ ENNReal.ofReal M := by
  let C : StateCoefficient →L[ℝ] Coefficient :=
    (ContinuousLinearMap.compL ℝ S0 (S0 × Gradient) S0).flip (ContinuousLinearMap.inl ℝ S0 Gradient)
  have hMeas : AEStronglyMeasurable (adjointValueColumn A) (volume.restrict U) :=
    (frobeniusAdjointCLM.continuous.comp C.continuous).comp_aestronglyMeasurable hA.1
  have hB : ∀ᵐ x ∂volume.restrict U, ‖adjointValueColumn A x‖ ≤ M :=
    hA.2.1.mono fun x hx => (adjointValueColumn_norm_le A x).trans hx
  exact ⟨memLp_top_of_bound hMeas M hB, eLpNormEssSup_le_of_ae_bound hB⟩

private theorem adjointGradientColumn_memLp_top {U : Set Point} (hU : IsOpen U)
    {A : Point → StateCoefficient} {p M : ℝ} (hA : HasBoundedDirichletCorrectionCoefficients U p M A) (i : Fin 3) :
    MemLp (adjointGradientColumn A i) ⊤ (volume.restrict U) ∧
      eLpNorm (adjointGradientColumn A i) ⊤ (volume.restrict U) ≤ ENNReal.ofReal M := by
  have hMeas : AEStronglyMeasurable (adjointGradientColumn A i) (volume.restrict U) :=
    (adjointGradientColumn_contDiffOn hA i).continuousOn.aestronglyMeasurable hU.measurableSet
  have hB : ∀ᵐ x ∂volume.restrict U, ‖adjointGradientColumn A i x‖ ≤ M :=
    hA.2.1.mono fun x hx => (firstOrderColumn_norm_le A i x).trans hx
  exact ⟨memLp_top_of_bound hMeas M hB, eLpNormEssSup_le_of_ae_bound hB⟩

private theorem adjointGradientColumn_deriv_memLp_three {U : Set Point} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)] {A : Point → StateCoefficient}
    {p M : ℝ} (hp : (3 : ℝ) < p) (hA : HasBoundedDirichletCorrectionCoefficients U p M A)
    (i j : Fin 3) :
    MemLp (coordDeriv j (adjointGradientColumn A i)) 3 (volume.restrict U) ∧
      eLpNorm (coordDeriv j (adjointGradientColumn A i)) 3 (volume.restrict U) ≤
        ENNReal.ofReal M * (volume.restrict U) univ ^ (1/3-1/p : ℝ) := by
  let F (x : Point) := ‖fderiv ℝ (correctionFirstOrderColumn A i) x‖
  have hF : MemLp F (ENNReal.ofReal p) (volume.restrict U) := (hA.2.2 i).2.1
  have hFNorm : eLpNorm F (ENNReal.ofReal p) (volume.restrict U) ≤ ENNReal.ofReal M := (hA.2.2 i).2.2
  have hp₀ : 0 ≤ p := (by norm_num : (0 : ℝ) ≤ 3).trans hp.le
  have hp₃ : (3 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hUp : ∀ᵐ x ∂volume.restrict U, ‖coordDeriv j (adjointGradientColumn A i) x‖ ≤ F x :=
    (ae_restrict_mem hU.measurableSet).mono (fun _ hx => norm_adjointGradientColumn_deriv_le hU hA i j hx)
  have hCont :
      ContinuousOn (coordDeriv j (adjointGradientColumn A i)) U :=
    continuousOn_coordDeriv hU (adjointGradientColumn_contDiffOn hA i) j
  refine ⟨(hF.mono_exponent hp₃).mono' (hCont.aestronglyMeasurable hU.measurableSet) hUp, ?_⟩
  refine (eLpNorm_mono_ae_real hUp).trans ?_
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp₃ hF.1
  rw [ENNReal.toReal_ofReal hp₀,show (3 : ℝ≥0∞).toReal = 3 by norm_num] at h
  exact h.trans (mul_le_mul' hFNorm le_rfl)

private theorem stateCoefficient_expand (A : Point → StateCoefficient) (x : Point) (u : S0) (D : Gradient) :
    A x (u,D) = (A x).comp (ContinuousLinearMap.inl ℝ S0 Gradient) u +
      ∑ i : Fin 3, correctionFirstOrderColumn A i x (D i) := by
  classical
  have hD : ∑ i : Fin 3, Pi.single i (D i) = D := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      simp [Pi.single_eq_of_ne (Ne.symm hij)]
    · intro hj
      exact (hj (Finset.mem_univ _)).elim
  have hPair : ((u,D) : S0 × Gradient) =
      ((u,0) : S0 × Gradient) + ∑ i : Fin 3, ((0,Pi.single i (D i)) : S0 × Gradient) := by
    have hFst := map_sum (AddMonoidHom.fst S0 Gradient) (fun i : Fin 3 => ((0,Pi.single i (D i)) : S0 × Gradient)) Finset.univ
    have hSnd := map_sum (AddMonoidHom.snd S0 Gradient) (fun i : Fin 3 => ((0,Pi.single i (D i)) : S0 × Gradient)) Finset.univ
    change (∑ i : Fin 3, ((0,Pi.single i (D i)) : S0 × Gradient)).1 = ∑ _ : Fin 3, (0 : S0) at hFst
    change (∑ i : Fin 3, ((0,Pi.single i (D i)) : S0 × Gradient)).2 = ∑ i : Fin 3, Pi.single i (D i) at hSnd
    apply Prod.ext
    · change u = u + (∑ i : Fin 3, ((0,Pi.single i (D i)) : S0 × Gradient)).1
      rw [hFst,Finset.sum_const_zero,add_zero]
    · change D = 0 + (∑ i : Fin 3, ((0,Pi.single i (D i)) : S0 × Gradient)).2
      rw [zero_add,hSnd,hD]
  conv_lhs => rw [hPair]
  simp only [map_add,map_sum,correctionFirstOrderColumn,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply,ContinuousLinearMap.inr_apply,ContinuousLinearMap.single_apply]

private theorem integral_lowerAdjointField {U : Set Point} (hU : IsOpen U) (A : Point → StateCoefficient)
    (v w : H10 U)
    (hV : MemLp (fun x => adjointValueColumn A x (h10Value w x)) 2 (volume.restrict U))
    (hD : ∀ i, MemH1 U (fun x => adjointGradientColumn A i x (h10Value w x))
      (fun x j => coordDeriv j (adjointGradientColumn A i) x (h10Value w x) +
        adjointGradientColumn A i x (h10Gradient w x j))) :
    IntegrableOn (fun x => frobeniusS0 (A x (h10Value v x, h10Gradient v x)) (h10Value w x)) U ∧
    (∫ x in U, frobeniusS0 (A x (h10Value v x, h10Gradient v x)) (h10Value w x)) =
      ∫ x in U, frobeniusS0 (h10Value v x) (lowerAdjointField A w x) := by
  let μ := volume.restrict U
  let F₀ (x : Point) := frobeniusS0 (h10Value v x) (adjointValueColumn A x (h10Value w x))
  let F (i : Fin 3) (x : Point) := frobeniusS0 (h10Gradient v x i) (adjointGradientColumn A i x (h10Value w x))
  let G (i : Fin 3) (x : Point) := frobeniusS0 (h10Value v x) (adjointDivergenceColumn A w i x)
  have hF₀ : Integrable F₀ μ := integrable_frobenius_of_memLp (Lp.memLp v.val.1) hV
  have hF (i : Fin 3) : Integrable (F i) μ := integrable_frobenius_of_memLp (Lp.memLp (v.val.2 i)) (hD i).1
  have hG (i : Fin 3) : Integrable (G i) μ := integrable_frobenius_of_memLp (Lp.memLp v.val.1) ((hD i).2.1 i)
  have hFtrace (x : Point) :
      frobeniusS0 (A x (h10Value v x, h10Gradient v x)) (h10Value w x) = F₀ x + ∑ i : Fin 3, F i x := by
    rw [stateCoefficient_expand]
    simp only [← frobenius_inner_eq,inner_add_left,sum_inner,F₀,F,
      adjointValueColumn,adjointGradientColumn]
    congr 1
    · exact ContinuousLinearMap.adjoint_inner_right _ _ _ |>.symm
    · exact Finset.sum_congr rfl (fun _ _ => (ContinuousLinearMap.adjoint_inner_right _ _ _).symm)
  have hGtrace (x : Point) :
      frobeniusS0 (h10Value v x) (lowerAdjointField A w x) = F₀ x - ∑ i : Fin 3, G i x := by
    simp only [← frobenius_inner_eq,lowerAdjointField,F₀,G, inner_sub_right,inner_sum]
  have hFI := integrable_finsetSum Finset.univ (fun i _ => hF i)
  have hGI := integrable_finsetSum Finset.univ (fun i _ => hG i)
  refine ⟨(hF₀.add hFI).congr (Eventually.of_forall fun x => (hFtrace x).symm), ?_⟩
  simp_rw [hFtrace,hGtrace]
  rw [integral_add hF₀ hFI, integral_sub hF₀ hGI, integral_finsetSum, integral_finsetSum,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  · congr 1
    exact Finset.sum_congr rfl (fun i _ => integral_frobenius_h10_weak_col hU v (hD i) i)
  · exact fun i _ => hG i
  · exact fun i _ => hF i

private theorem eLpNorm_h10Column_le {U : Set Point} (v : H10 U) (j : Fin 3) :
    eLpNorm (fun x => h10Gradient v x j) 2 (volume.restrict U) ≤ ENNReal.ofReal ‖v‖ := by
  change eLpNorm (v.val.2 j : Point → S0) 2 _ ≤ _
  rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (v.val.2 j)), ← Lp.norm_def]
  exact ENNReal.ofReal_le_ofReal ((norm_le_pi_norm v.val.2 j).trans (le_max_right ‖v.val.1‖ ‖v.val.2‖))

private theorem eLpNorm_h10Value_le {U : Set Point} (v : H10 U) :
    eLpNorm (h10Value v) 2 (volume.restrict U) ≤ ENNReal.ofReal ‖v‖ := by
  change eLpNorm (v.val.1 : Point → S0) 2 _ ≤ _
  rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top v.val.1), ← Lp.norm_def]
  exact ENNReal.ofReal_le_ofReal (le_max_left ‖v.val.1‖ ‖v.val.2‖)

private theorem eLpNorm_adjointDivergenceColumn_le {U : Set Point}
    (A : Point → StateCoefficient) (w : H10 U) (i : Fin 3) {B L K : ℝ≥0∞}
    (hGcol : MemLp (adjointGradientColumn A i) ⊤ (volume.restrict U))
    (hGN : eLpNorm (adjointGradientColumn A i) ⊤ (volume.restrict U) ≤ B)
    (hDcol : MemLp (coordDeriv i (adjointGradientColumn A i)) 3 (volume.restrict U))
    (hDN : eLpNorm (coordDeriv i (adjointGradientColumn A i)) 3 (volume.restrict U) ≤ L)
    (hVal6 : MemLp (h10Value w) 6 (volume.restrict U))
    (hVal6Norm : eLpNorm (h10Value w) 6 (volume.restrict U) ≤ K * ENNReal.ofReal ‖w‖) :
    eLpNorm (adjointDivergenceColumn A w i) 2 (volume.restrict U) ≤ (L*K+B) * ENNReal.ofReal ‖w‖ := by
  let μ := volume.restrict U
  let a (x : Point) := coordDeriv i (adjointGradientColumn A i) x (h10Value w x)
  let b (x : Point) := adjointGradientColumn A i x (h10Gradient w x i)
  have hGrad2 : MemLp (fun x => h10Gradient w x i) 2 μ := Lp.memLp (w.val.2 i)
  have ha : MemLp a 2 μ := memLp_pointwise_operator_apply (r := 2) hDcol hVal6
  have hb : MemLp b 2 μ := memLp_pointwise_operator_apply (r := 2) hGcol hGrad2
  have hA0 : eLpNorm a 2 μ ≤ (L*K) * ENNReal.ofReal ‖w‖ :=
    (eLpNorm_pointwise_operator_apply_le (p := 3) (q := 6) hDcol.1 hVal6.1).trans
      ((mul_le_mul' hDN hVal6Norm).trans_eq (mul_assoc _ _ _).symm)
  have hB0 : eLpNorm b 2 μ ≤ B * ENNReal.ofReal ‖w‖ :=
    (eLpNorm_pointwise_operator_apply_le (p := ⊤) (q := 2) hGcol.1 hGrad2.1).trans
      (mul_le_mul' hGN (eLpNorm_h10Column_le w i))
  have hA : eLpNorm (adjointDivergenceColumn A w i) 2 μ ≤ eLpNorm a 2 μ + eLpNorm b 2 μ :=
    eLpNorm_add_le ha.1 hb.1 (by norm_num)
  exact hA.trans ((add_le_add hA0 hB0).trans_eq (add_mul _ _ _).symm)

private theorem memLp_and_eLpNorm_sub_three_sum {μ : Measure Point} {R : Point → S0}
    {S : Fin 3 → Point → S0} {B C E : ℝ≥0∞}
    (hR : MemLp R 2 μ) (hS : ∀ i, MemLp (S i) 2 μ)
    (hRN : eLpNorm R 2 μ ≤ B * E) (hSN : ∀ i, eLpNorm (S i) 2 μ ≤ C * E) :
    MemLp (R - ∑ i, S i) 2 μ ∧ eLpNorm (R - ∑ i, S i) 2 μ ≤ (B+C+C+C) * E := by
  rw [Fin.sum_univ_three]
  let Q := S 0 + S 1
  let T := Q + S 2
  have hQ : MemLp Q 2 μ := (hS 0).add (hS 1)
  have hT : MemLp T 2 μ := hQ.add (hS 2)
  have h₂ : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  refine ⟨hR.sub hT,?_⟩
  have hQle : eLpNorm Q 2 μ ≤ C*E+C*E :=
    (eLpNorm_add_le (hS 0).1 (hS 1).1 h₂).trans (add_le_add (hSN 0) (hSN 1))
  have hTle : eLpNorm T 2 μ ≤ C*E+C*E+C*E :=
    (eLpNorm_add_le hQ.1 (hS 2).1 h₂).trans (add_le_add hQle (hSN 2))
  have hAdd : eLpNorm (R-T) 2 μ ≤ eLpNorm R 2 μ + eLpNorm T 2 μ := by
    have h := eLpNorm_add_le (f := R) (g := -T) hR.1 hT.neg.1 h₂
    simpa only [sub_eq_add_neg,eLpNorm_neg] using h
  change eLpNorm (R-T) 2 μ ≤ _
  exact hAdd.trans ((add_le_add hRN hTle).trans_eq (by rw [add_mul,add_mul,add_mul]; ac_rfl))

/-- The L² bound for the lower-order adjoint in terms of the coefficient bound. -/
def lowerAdjointL2Constant (U : Set Point) (p M : ℝ) : ℝ :=
  let V := (volume.restrict U) univ ^ (1/3-1/p : ℝ)
  let B := ENNReal.ofReal M
  let C₁ := B * V * (exists_h10_sobolevL6_bound.choose : ℝ≥0∞) + B
  (B + C₁ + C₁ + C₁).toReal

theorem lowerAdjointL2Constant_nonneg (U : Set Point) (p M : ℝ) :
    0 ≤ lowerAdjointL2Constant U p M := ENNReal.toReal_nonneg

/-- The original lower-order adjoint has an L² density with a uniform graph-norm bound. -/
theorem lowerAdjointL2_forcing {U : Set Point} (hU : IsBoundedDomain U)
    {p M : ℝ} (hp : (3 : ℝ) < p)
    (A : Point → (S0 × Gradient) →L[ℝ] S0)
    (hA : HasBoundedDirichletCorrectionCoefficients U p M A) (w : H10 U) :
    ∃ g : Lp S0 2 (volume.restrict U), ‖g‖ ≤ lowerAdjointL2Constant U p M * ‖w‖ ∧
      ∀ v : H10 U,
        IntegrableOn (fun x => frobeniusS0 (A x (h10Value v x, h10Gradient v x)) (h10Value w x)) U ∧
        (∫ x in U, frobeniusS0 (A x (h10Value v x, h10Gradient v x)) (h10Value w x)) =
          ∫ x in U, frobeniusS0 (h10Value v x) (g x) := by
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.2.2.measure_lt_top.ne
  let C₆ := exists_h10_sobolevL6_bound.choose
  let V := μ univ ^ (1/3-1/p : ℝ)
  let B := ENNReal.ofReal M
  let C₁ : ℝ≥0∞ := B * V * (C₆ : ℝ≥0∞) + B
  let C : ℝ≥0∞ := B + C₁ + C₁ + C₁
  have hV : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr
    (one_div_le_one_div_of_le (by norm_num) hp.le)) (measure_ne_top _ _)
  have hB : B ≠ ⊤ := ENNReal.ofReal_ne_top
  have hC₁ : C₁ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top hB hV) ENNReal.coe_ne_top,hB⟩
  have hC : C ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hB,hC₁⟩,hC₁⟩,hC₁⟩
  obtain ⟨hVcol,hVnorm⟩ := adjointValueColumn_memLp_top hA
  have hGcol (i : Fin 3) := adjointGradientColumn_memLp_top hU.1 hA i
  have hDcol (i j : Fin 3) := adjointGradientColumn_deriv_memLp_three hU.1 hp hA i j
  have hVal2 : MemLp (h10Value w) 2 μ := Lp.memLp w.val.1
  obtain ⟨hVal6,hVal6Norm⟩ := exists_h10_sobolevL6_bound.choose_spec (U := U) hU.1.measurableSet w
  let R (x : Point) := adjointValueColumn A x (h10Value w x)
  let S (i : Fin 3) := adjointDivergenceColumn A w i
  have hR : MemLp R 2 μ := memLp_pointwise_operator_apply (r := 2) hVcol hVal2
  have hW (i : Fin 3) : MemH1 U (fun x => adjointGradientColumn A i x (h10Value w x))
      (fun x j => coordDeriv j (adjointGradientColumn A i) x (h10Value w x) +
        adjointGradientColumn A i x (h10Gradient w x j)) :=
    memH1_of_smoothCoefficient_apply_h10 hU w (B := adjointGradientColumn A i)
      (adjointGradientColumn_contDiffOn hA i) (hGcol i).1 (fun j => (hDcol i j).1)
  have hS (i : Fin 3) : MemLp (S i) 2 μ := (hW i).2.1 i
  have hSN (i : Fin 3) : eLpNorm (S i) 2 μ ≤ C₁ * ENNReal.ofReal ‖w‖ :=
    eLpNorm_adjointDivergenceColumn_le A w i (hGcol i).1 (hGcol i).2 (hDcol i i).1 (hDcol i i).2
      hVal6 hVal6Norm
  have hRN : eLpNorm R 2 μ ≤ B * ENNReal.ofReal ‖w‖ :=
    (eLpNorm_pointwise_operator_apply_le (p := ⊤) (q := 2) hVcol.1 hVal2.1).trans
      (mul_le_mul' hVnorm (eLpNorm_h10Value_le w))
  have hEq : lowerAdjointField A w = R - ∑ i : Fin 3, S i := by
    funext x
    simp only [lowerAdjointField, R, S, Pi.sub_apply, Finset.sum_apply]
  have hL : MemLp (lowerAdjointField A w) 2 μ ∧
      eLpNorm (lowerAdjointField A w) 2 μ ≤ C * ENNReal.ofReal ‖w‖ := by
    rw [hEq]
    exact memLp_and_eLpNorm_sub_three_sum hR hS hRN hSN
  obtain ⟨hLower,hBound⟩ := hL
  let g := hLower.toLp (lowerAdjointField A w)
  refine ⟨g, ?_, fun v => ?_⟩
  · change ‖hLower.toLp (lowerAdjointField A w)‖ ≤ C.toReal * ‖w‖
    rw [Lp.norm_toLp]
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hBound
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)] using h
  · obtain ⟨hi,hEq⟩ := integral_lowerAdjointField hU.1 A v w hR hW
    exact ⟨hi,hEq.trans (integral_congr_ae (hLower.coeFn_toLp.symm.mono fun x hx =>
      congrArg (frobeniusS0 (h10Value v x)) hx))⟩

end Thesis

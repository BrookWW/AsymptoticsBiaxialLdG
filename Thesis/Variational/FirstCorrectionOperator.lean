module

public import Thesis.Variational.ProjectedHarmonicRemainder
import Thesis.Variational.BoundaryDefect
import Thesis.Variational.AffineSegmentAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! The linearization of the projected harmonic expression. -/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius RealInnerProductSpace Interval

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance firstCorrectionOperatorCLMNormed : NormedAddCommGroup ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance firstCorrectionOperatorCLMNormedSpace : NormedSpace ℝ ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance firstCorrectionOperatorENormedS0 : ENormedAddMonoid S0 :=
  NormedAddGroup.toENormedAddMonoid

/-- The mixed cubic contraction with the two given gradient columns. -/
def mixedCubicGradientContraction (A : S0) (D G : Gradient) : ℝ :=
  ∑ j, ((D j : Tensor) * (G j : Tensor) * (A : Tensor)).trace

/-- The zeroth- and first-order part of the harmonic Jacobi expression in
the ambient trace-free tensor space. -/
def harmonicFirstOrderLinearization (a : BulkCoefficients) (A : S0) (D : Gradient)
    (P : S0) (G : Gradient) : S0 :=
  let r := vacuumRadius a
  (gradientNormSq D / (2*r^2)) • P +
    ((∑ j, frobeniusS0 (D j) (G j)) / r^2) • A +
    (6/r^4 * mixedCubicGradientContraction A G D +
      3/r^4 * mixedCubicGradientContraction P D D) • traceFreeSquare A +
    (3/r^4 * cubicGradientContraction A D) • traceFreeJordan A P

theorem contDiff_projectedHarmonicNonlinearity (a : BulkCoefficients) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fun p : S0 × Gradient => projectedHarmonicNonlinearity a p.1 p.2) := by
  have hA : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fun p : S0 × Gradient => p.1) := contDiff_fst
  have hD (j : Fin 3) : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fun p : S0 × Gradient => p.2 j) :=
    (ContinuousLinearMap.proj j : Gradient →L[ℝ] S0).contDiff.comp contDiff_snd
  have hAT := symmetricTraceless.subtypeL.contDiff.comp hA
  have hDT (j : Fin 3) := symmetricTraceless.subtypeL.contDiff.comp (hD j)
  have hG : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fun p : S0 × Gradient => gradientNormSq p.2) := by
    simp only [gradientNormSq, frobeniusS0, frobenius, S0.transpose_eq]
    exact ContDiff.sum fun j _ => tensorTraceCLM.contDiff.comp ((hDT j).mul (hDT j))
  have hS : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω)
      (fun p : S0 × Gradient => cubicGradientContraction p.1 p.2) := by
    unfold cubicGradientContraction
    exact ContDiff.sum fun j _ => tensorTraceCLM.contDiff.comp (((hDT j).mul (hDT j)).mul hAT)
  unfold projectedHarmonicNonlinearity
  exact ((hG.div_const _).smul hA).add
    ((contDiff_const.mul hS).smul (contDiff_traceFreeSquare.comp hA))

private theorem hasDerivAt_affine_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E) (t : ℝ) : HasDerivAt (fun s : ℝ => A + s • B) B t := by
  simpa only [id_eq, one_smul] using! ((hasDerivAt_id t).smul_const B).const_add A

private theorem hasDerivAt_gradientNormSq_line (D G : Gradient) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gradientNormSq (D + s • G))
      (2 * ∑ j, frobeniusS0 (D j + t • G j) (G j)) t := by
  let e := frobeniusCoordinateEquiv
  have h (j : Fin 3) :
      HasDerivAt (fun s : ℝ => frobeniusS0 ((D + s • G) j) ((D + s • G) j))
        (2 * frobeniusS0 (D j + t • G j) (G j)) t := by
    have h' := (hasDerivAt_affine_line (e (D j)) (e (G j)) t).norm_sq
    have hFun (s : ℝ) : ‖e (D j) + s • e (G j)‖ ^ 2 =
        frobeniusS0 ((D + s • G) j) ((D + s • G) j) := by
      rw [← map_smul e, ← map_add e, LinearIsometryEquiv.norm_map, norm_sq_eq_frobeniusS0]
      rfl
    have hVal : 2 * inner ℝ (e (D j) + t • e (G j)) (e (G j)) =
        2 * frobeniusS0 (D j + t • G j) (G j) := by
      rw [← map_smul e, ← map_add e, frobeniusCoordinateEquiv_inner]
    exact hVal ▸ (funext hFun) ▸ h'
  have hSum := HasDerivAt.sum (u := Finset.univ) (fun j _ => h j)
  simpa only [gradientNormSq, Finset.mul_sum, Finset.sum_apply] using! hSum

private theorem trace_mul_cycle_of_symmetric (A B C : S0) :
    ((A : Tensor) * (B : Tensor) * (C : Tensor)).trace =
      ((B : Tensor) * (A : Tensor) * (C : Tensor)).trace := by
  rw [← Matrix.trace_transpose ((A : Tensor) * (B : Tensor) * (C : Tensor)),
    Matrix.transpose_mul, Matrix.transpose_mul, A.transpose_eq, B.transpose_eq, C.transpose_eq,
    Matrix.trace_mul_comm, mul_assoc]

private theorem hasDerivAt_cubicGradientContraction_line (A P : S0) (D G : Gradient) (t : ℝ) :
    HasDerivAt (fun s : ℝ => cubicGradientContraction (A + s • P) (D + s • G))
      (2 * mixedCubicGradientContraction (A + t • P) G (D + t • G) +
        mixedCubicGradientContraction P (D + t • G) (D + t • G)) t := by
  let X (s : ℝ) : Tensor := (A : Tensor) + s • (P : Tensor)
  let Y (j : Fin 3) (s : ℝ) : Tensor := (D j : Tensor) + s • (G j : Tensor)
  have hX : HasDerivAt X (P : Tensor) t := hasDerivAt_affine_line _ _ _
  have hY (j : Fin 3) : HasDerivAt (Y j) (G j : Tensor) t := hasDerivAt_affine_line _ _ _
  have hTrace (j : Fin 3) := tensorTraceCLM.hasFDerivAt.comp_hasDerivAt t (((hY j).mul (hY j)).mul hX)
  have hEq (j : Fin 3) : ((G j : Tensor) * Y j t * X t).trace = (Y j t * (G j : Tensor) * X t).trace :=
    trace_mul_cycle_of_symmetric (G j) (D j + t • G j) (A + t • P)
  have hVal (j : Fin 3) :
      tensorTraceCLM (((G j : Tensor) * Y j t + Y j t * (G j : Tensor)) * X t +
        Y j t * Y j t * (P : Tensor)) =
        2 * ((G j : Tensor) * Y j t * X t).trace + (Y j t * Y j t * (P : Tensor)).trace := by
    change (((G j : Tensor) * Y j t + Y j t * (G j : Tensor)) * X t +
      Y j t * Y j t * (P : Tensor)).trace = _
    rw [Matrix.add_mul, Matrix.trace_add, Matrix.trace_add, ← hEq j, two_mul]
  have hEach (j : Fin 3) : HasDerivAt (fun s => (Y j s * Y j s * X s).trace)
      (2 * ((G j : Tensor) * Y j t * X t).trace + (Y j t * Y j t * (P : Tensor)).trace) t :=
    hVal j ▸ hTrace j
  have hSum := HasDerivAt.sum (u := Finset.univ) (fun j _ => hEach j)
  simpa only [cubicGradientContraction, mixedCubicGradientContraction, Finset.mul_sum,
    ← Finset.sum_add_distrib] using! hSum

private theorem hasDerivAt_traceFreeSquare_line (A P : S0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => traceFreeSquare (A + s • P)) (traceFreeJordan (A + t • P) P) t := by
  let X (s : ℝ) : Tensor := (A : Tensor) + s • (P : Tensor)
  have hX : HasDerivAt X (P : Tensor) t := hasDerivAt_affine_line _ _ _
  have h := traceFreeSymmetricPartCLM.hasFDerivAt.comp_hasDerivAt t (hX.mul hX)
  change HasDerivAt (fun s => traceFreeSymmetricPart (X s * X s))
    (traceFreeSymmetricPart ((P : Tensor) * X t + X t * (P : Tensor))) t at h
  have hEq : (fun s => traceFreeSquare (A + s • P)) =
      (fun s => traceFreeSymmetricPart (X s * X s)) := by
    funext s
    change traceFreeSymmetricPart (X s ^ 2) = _
    rw [pow_two]
  rw [hEq, traceFreeJordan, add_comm]
  exact h

/-- The derivative of the nonlinear part along every affine segment has
exactly the coefficients of the manuscript's weak linearized operator. -/
theorem hasDerivAt_projectedHarmonicNonlinearity_line
    (a : BulkCoefficients) (A P : S0) (D G : Gradient) (t : ℝ) :
    HasDerivAt (fun s : ℝ => projectedHarmonicNonlinearity a (A + s • P) (D + s • G))
      (harmonicFirstOrderLinearization a (A + t • P) (D + t • G) P G) t := by
  let r := vacuumRadius a
  let X (s : ℝ) := A + s • P
  let Y (s : ℝ) := D + s • G
  let B := ∑ j, frobeniusS0 (D j + t • G j) (G j)
  let S₁ := mixedCubicGradientContraction (X t) G (Y t)
  let S₂ := mixedCubicGradientContraction P (Y t) (Y t)
  have hA : HasDerivAt X P t := hasDerivAt_affine_line A P t
  have hOne := ((hasDerivAt_gradientNormSq_line D G t).div_const (2*r^2)).smul hA
  have hTwo := ((hasDerivAt_cubicGradientContraction_line A P D G t).const_mul (3/r^4)).smul
    (hasDerivAt_traceFreeSquare_line A P t)
  have h := hOne.add hTwo
  have h₁ : 2 * B / (2*r^2) = B / r^2 := by ring
  have h₂ : (3/r^4) * (2*S₁ + S₂) = 6/r^4 * S₁ + 3/r^4 * S₂ := by ring
  change HasDerivAt _ ((gradientNormSq (Y t) / (2*r^2)) • P +
    (2 * B / (2*r^2)) • X t +
    ((3/r^4 * cubicGradientContraction (X t) (Y t)) • traceFreeJordan (X t) P +
      (((3/r^4) * (2*S₁ + S₂)) • traceFreeSquare (X t)))) t at h
  rw [h₁, h₂] at h
  convert h using 1
  · rfl
  · unfold harmonicFirstOrderLinearization
    let p₁ := (gradientNormSq (Y t) / (2*r^2)) • P
    let p₂ := (B / r^2) • X t
    let p₃ := (6/r^4*S₁ + 3/r^4*S₂) • traceFreeSquare (X t)
    let p₄ := (3/r^4*cubicGradientContraction (X t) (Y t)) • traceFreeJordan (X t) P
    change p₁ + p₂ + p₃ + p₄ = p₁ + p₂ + (p₄ + p₃)
    abel

/-- The Fréchet derivative of the polynomial is the explicit first-order
linearization, evaluated on the actual tensor and gradient increments. -/
theorem fderiv_projectedHarmonicNonlinearity_apply
    (a : BulkCoefficients) (A P : S0) (D G : Gradient) :
    fderiv ℝ (fun p : S0 × Gradient => projectedHarmonicNonlinearity a p.1 p.2) (A,D) (P,G) =
      harmonicFirstOrderLinearization a A D P G := by
  let F (p : S0 × Gradient) := projectedHarmonicNonlinearity a p.1 p.2
  let γ (t : ℝ) := (A,D) + t • (P,G)
  have hγ0 : γ 0 = (A,D) := by simp [γ]
  have hF : HasFDerivAt F (fderiv ℝ F (A,D)) (γ 0) := by
    rw [hγ0]
    exact ((contDiff_projectedHarmonicNonlinearity a).differentiable (by simp) (A,D)).hasFDerivAt
  have h := hF.comp_hasDerivAt (0 : ℝ) (hasDerivAt_affine_line (A,D) (P,G) 0)
  have h' := hasDerivAt_projectedHarmonicNonlinearity_line a A P D G 0
  simp only [zero_smul, add_zero] at h'
  exact h.unique h'

private theorem continuous_harmonicDerivative_line (a : BulkCoefficients) (X V : S0 × Gradient) :
    Continuous (fun t : ℝ =>
      fderiv ℝ (fun p : S0 × Gradient => projectedHarmonicNonlinearity a p.1 p.2) (X + t • V)) :=
  ((contDiff_projectedHarmonicNonlinearity a).continuous_fderiv (by simp)).comp
    (continuous_const.add (continuous_id.smul continuous_const))

/-- The first-order coefficients obtained by integrating the exact
Jacobi derivative along the straight segment between two states. -/
@[no_expose] def averagedHarmonicLinearization (a : BulkCoefficients) (X Y : S0 × Gradient) :
    (S0 × Gradient) →L[ℝ] S0 := by
  let A (t : ℝ) :=
    fderiv ℝ (fun p : S0 × Gradient => projectedHarmonicNonlinearity a p.1 p.2) (X + t • (Y - X))
  have hA : Continuous A := continuous_harmonicDerivative_line a X (Y - X)
  have hAI (z : S0 × Gradient) : IntervalIntegrable (fun t => A t z) volume 0 1 :=
    ((ContinuousLinearMap.apply ℝ S0 z).continuous.comp hA).intervalIntegrable 0 1
  let T : (S0 × Gradient) →ₗ[ℝ] S0 :=
    { toFun := fun z => ∫ t in (0 : ℝ)..1, A t z
      map_add' := by
        intro z w
        simp only [map_add]
        exact intervalIntegral.integral_add (hAI z) (hAI w)
      map_smul' := by
        intro c z
        simp only [map_smul, intervalIntegral.integral_smul, RingHom.id_apply] }
  let hCompact := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hA.continuousOn
  let M := Classical.choose hCompact
  have hM := Classical.choose_spec hCompact
  apply T.mkContinuous (max M 0)
  intro z
  change ‖∫ t in (0 : ℝ)..1, A t z‖ ≤ max M 0 * ‖z‖
  have hBound (t : ℝ) (ht : t ∈ Ι (0 : ℝ) 1) : ‖A t z‖ ≤ (max M 0) * ‖z‖ := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simp only [Set.uIoc_of_le zero_le_one] at ht
      exact Ioc_subset_Icc_self ht
    exact (ContinuousLinearMap.le_opNorm (A t) z).trans
      (mul_le_mul_of_nonneg_right ((hM t ht').trans (le_max_left _ _)) (norm_nonneg _))
  simpa only [sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hBound

theorem averagedHarmonicLinearization_apply
    (a : BulkCoefficients) (X Y Z : S0 × Gradient) :
    averagedHarmonicLinearization a X Y Z =
      ∫ t in (0 : ℝ)..1,
        fderiv ℝ (fun p : S0 × Gradient => projectedHarmonicNonlinearity a p.1 p.2) (X + t • (Y - X)) Z := by
  unfold averagedHarmonicLinearization
  rfl

theorem averagedHarmonicLinearization_apply_difference
    (a : BulkCoefficients) (X Y : S0 × Gradient) :
    averagedHarmonicLinearization a X Y (Y - X) =
      projectedHarmonicNonlinearity a Y.1 Y.2 - projectedHarmonicNonlinearity a X.1 X.2 := by
  let F (p : S0 × Gradient) := projectedHarmonicNonlinearity a p.1 p.2
  let γ (t : ℝ) := X + t • (Y - X)
  let E := ContinuousLinearMap.apply ℝ S0 (Y - X)
  have hD : Continuous (fun t => fderiv ℝ F (γ t)) := continuous_harmonicDerivative_line a X (Y - X)
  have hI := (E.continuous.comp hD).intervalIntegrable (μ := volume) 0 1
  have hγ0 : γ 0 = X := by simp [γ]
  have hγ1 : γ 1 = Y := by simp only [γ, one_smul]; abel
  have hDer (t : ℝ) : HasDerivAt (F ∘ γ) (E (fderiv ℝ F (γ t))) t := by
    have h := ((contDiff_projectedHarmonicNonlinearity a).differentiable (by simp) (γ t)).hasFDerivAt
    exact h.comp_hasDerivAt t (hasDerivAt_affine_line X (Y - X) t)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hDer t) hI
  change (∫ t in (0 : ℝ)..1, E (fderiv ℝ F (γ t))) = F (γ 1) - F (γ 0) at hFTC
  rw [hγ0, hγ1] at hFTC
  exact hFTC

private theorem coordDeriv_sub_of_contDiffOn_one {U : Set Point} (hU : IsOpen U)
    {Q q : Point → S0} (hQ : ContDiffOn ℝ 1 Q U) (hq : ContDiffOn ℝ 1 q U)
    {x : Point} (hx : x ∈ U) (j : Fin 3) :
    coordDeriv j (fun y => Q y - q y) x = coordDeriv j Q x - coordDeriv j q x := by
  have h₁ := ((hQ x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have h₂ := ((hq x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  exact DFunLike.congr_fun (h₁.hasFDerivAt.sub h₂.hasFDerivAt).fderiv (axis j)

/-- The difference of the two harmonic expressions is precisely an
equation with componentwise Laplacian and the averaged first-order coefficients. -/
theorem projectedHarmonicExpression_difference
    (a : BulkCoefficients) {U : Set Point} (hU : IsOpen U)
    {Q q : Point → S0} (hQ : ContDiffOn ℝ 2 Q U) (hq : ContDiffOn ℝ 2 q U)
    {x : Point} (hx : x ∈ U) :
    let X := (q x, ClassicalGradient q x)
    let Y := (Q x, ClassicalGradient Q x)
    let d := fun y => Q y - q y
    laplacian d x + averagedHarmonicLinearization a X Y (d x, ClassicalGradient d x) =
      projectedHarmonicExpression a Q x - projectedHarmonicExpression a q x := by
  let X := (q x, ClassicalGradient q x)
  let Y := (Q x, ClassicalGradient Q x)
  let d := fun y => Q y - q y
  have hG : (d x, ClassicalGradient d x) = Y - X :=
    Prod.ext rfl (funext fun j =>
      coordDeriv_sub_of_contDiffOn_one hU (hQ.of_le (by norm_num)) (hq.of_le (by norm_num)) hx j)
  change laplacian d x + averagedHarmonicLinearization a X Y (d x, ClassicalGradient d x) = _
  have hD : laplacian d x = laplacian Q x - laplacian q x :=
    laplacian_sub_of_contDiffOn hU hQ hq hx
  rw [hD, hG, averagedHarmonicLinearization_apply_difference, projectedHarmonicExpression,
    projectedHarmonicExpression]
  change laplacian Q x - laplacian q x +
      (projectedHarmonicNonlinearity a (Q x) (ClassicalGradient Q x) -
        projectedHarmonicNonlinearity a (q x) (ClassicalGradient q x)) = _
  abel

theorem linearizedPairing_eq_harmonicFirstOrderLinearization
    (a : BulkCoefficients) (U : Set Point) (q : Point → S0) (D : Point → Gradient)
    (hq : TakesVacuumValues a U q) (v w : H10 U) :
    linearizedPairing a U q D v w =
      ∫ x in U, -(∑ j, frobeniusS0 (h10Gradient v x j) (h10Gradient w x j)) +
        frobeniusS0 (harmonicFirstOrderLinearization a (q x) (D x) (h10Value v x) (h10Gradient v x))
          (h10Value w x) := by
  unfold linearizedPairing
  apply integral_congr_ae
  filter_upwards [hq] with x hx
  congr 1
  unfold harmonicFirstOrderLinearization frobeniusS0
  change frobenius _ (h10Value w x : Tensor) = frobenius
    (((gradientNormSq (D x) / (2 * vacuumRadius a ^ 2)) • h10Value v x : S0) +
      ((∑ j, frobeniusS0 (D x j) (h10Gradient v x j)) / vacuumRadius a ^ 2) • q x +
      (6/vacuumRadius a ^ 4 * mixedCubicGradientContraction (q x) (h10Gradient v x) (D x) +
        3/vacuumRadius a ^ 4 * mixedCubicGradientContraction (h10Value v x) (D x) (D x)) • traceFreeSquare (q x) +
      (3/vacuumRadius a ^ 4 * cubicGradientContraction (q x) (D x)) • traceFreeJordan (q x) (h10Value v x) : S0)
      (h10Value w x : Tensor)
  push_cast
  rw [traceFreeSquare_coe_eq_biaxialQuadratic hx, traceFreeJordan_coe]
  rfl

/-- The averaged coefficients differ from the Jacobi coefficients by at
most a fixed multiple of the actual tensor and gradient increment. -/
theorem exists_norm_averagedHarmonicLinearization_sub_le
    (a : BulkCoefficients) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X Y : S0 × Gradient, ‖X‖ ≤ R → ‖Y‖ ≤ R →
      ‖averagedHarmonicLinearization a X Y -
        fderiv ℝ (fun p : S0 × Gradient => projectedHarmonicNonlinearity a p.1 p.2) X‖ ≤ C * ‖Y - X‖ := by
  let A := fderiv ℝ (fun p : S0 × Gradient => projectedHarmonicNonlinearity a p.1 p.2)
  have hA : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) A :=
    (contDiff_projectedHarmonicNonlinearity a).fderiv_right (by simp)
  obtain ⟨C, hC⟩ := hA.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : S0 × Gradient) R) (isCompact_closedBall _ _)
  refine ⟨C, C.coe_nonneg, ?_⟩
  intro X Y hX hY
  let M := (C : ℝ) * ‖Y-X‖
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg C.coe_nonneg (norm_nonneg _))
  intro z
  let γ (t : ℝ) := X + t • (Y-X)
  have hγ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖γ t‖ ≤ R := by
    have hEq : γ t = (1-t) • X + t • Y := by
      dsimp only [γ]
      calc
        _ = (1 : ℝ) • X - t • X + t • Y := by rw [one_smul, smul_sub]; abel
        _ = _ := congrArg (fun V : S0 × Gradient => V + t • Y) (sub_smul (1 : ℝ) t X).symm
    have hFirst := mul_le_mul_of_nonneg_left hX (sub_nonneg.mpr ht.2)
    have hSecond := mul_le_mul_of_nonneg_left hY ht.1
    rw [hEq]
    apply (norm_add_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht.2), Real.norm_of_nonneg ht.1]
    linarith only [hFirst, hSecond]
  have hBound (t : ℝ) (ht : t ∈ Ι (0 : ℝ) 1) : ‖(A (γ t) - A X) z‖ ≤ M * ‖z‖ := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simp only [Set.uIoc_of_le zero_le_one] at ht
      exact Ioc_subset_Icc_self ht
    have hL := hC.dist_le_mul (γ t) (mem_closedBall_zero_iff.mpr (hγ t ht'))
      X (mem_closedBall_zero_iff.mpr hX)
    rw [dist_eq_norm, dist_eq_norm, show γ t - X = t • (Y-X) by dsimp only [γ]; abel,
      norm_smul, Real.norm_of_nonneg ht'.1] at hL
    have hT : t * ‖Y - X‖ ≤ ‖Y - X‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht'.2 (norm_nonneg (Y-X))
    have hM : ‖A (γ t) - A X‖ ≤ M :=
      hL.trans (mul_le_mul_of_nonneg_left hT C.coe_nonneg)
    exact (ContinuousLinearMap.le_opNorm _ z).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  have hI : IntervalIntegrable (fun t => A (γ t) z) volume (0 : ℝ) 1 :=
    ((ContinuousLinearMap.apply ℝ S0 z).continuous.comp
      (continuous_harmonicDerivative_line a X (Y-X))).intervalIntegrable 0 1
  have hInt := intervalIntegral.integral_sub hI (intervalIntegrable_const (c := A X z))
  rw [intervalIntegral.integral_const, sub_zero, one_smul] at hInt
  change ‖averagedHarmonicLinearization a X Y z - A X z‖ ≤ M * ‖z‖
  rw [averagedHarmonicLinearization_apply, ← hInt]
  simpa only [sub_zero, abs_one, mul_one, sub_apply] using!
    intervalIntegral.norm_integral_le_of_norm_le_const hBound

/-- The actual \(\varepsilon^{-2}\) scaled difference satisfies the same
averaged linear equation with the correspondingly scaled projected source. -/
theorem scaled_firstCorrection_equation
    (a : BulkCoefficients) (ε : ElasticScale) {U : Set Point} (hU : IsOpen U)
    {Q q : Point → S0} (hQ : ContDiffOn ℝ 2 Q U) (hq : ContDiffOn ℝ 2 q U)
    {x : Point} (hx : x ∈ U)
    (hVac : q x ∈ vacuum a)
    (hHarm : (↑(laplacian q x) : Tensor) = harmonicRhs a q (ClassicalGradient q) x)
    (hEuler : ε.val^2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) :
    let X := (q x, ClassicalGradient q x)
    let Y := (Q x, ClassicalGradient Q x)
    let w := fun y => ε.val⁻¹^2 • (Q y - q y)
    laplacian w x + averagedHarmonicLinearization a X Y (w x, ClassicalGradient w x) =
      ε.val⁻¹^2 • projectedHarmonicRemainder a ε Q x := by
  let X := (q x, ClassicalGradient q x)
  let Y := (Q x, ClassicalGradient Q x)
  let d := fun y => Q y - q y
  let s := ε.val⁻¹ ^ 2
  let w := fun y => s • d y
  let A := averagedHarmonicLinearization a X Y
  have hd : ContDiffOn ℝ 2 d U := hQ.sub hq
  have hΔ : laplacian w x = s • laplacian d x := laplacian_const_smul hU hd hx s
  have hG : (w x, ClassicalGradient w x) = s • (d x, ClassicalGradient d x) := by
    apply Prod.ext
    · rfl
    · funext j
      exact coordDeriv_compCLM (s • ContinuousLinearMap.id ℝ S0)
        (((hd x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt two_ne_zero) j
  have hD := projectedHarmonicExpression_difference a hU hQ hq hx
  change laplacian d x + A (d x, ClassicalGradient d x) =
    projectedHarmonicExpression a Q x - projectedHarmonicExpression a q x at hD
  change laplacian w x + A (w x, ClassicalGradient w x) = _
  rw [hΔ, hG, map_smul, ← smul_add, hD, projectedHarmonicExpression_eq_remainder a ε Q x hEuler,
    projectedHarmonicExpression_eq_zero_of_harmonic a q x hVac hHarm, sub_zero]

local instance firstCorrectionAverageCompleteS0 : CompleteSpace S0 := complete_of_proper

local instance firstCorrectionAverageUniformGroupS0 : IsUniformAddGroup S0 :=
  SeminormedAddCommGroup.to_isUniformAddGroup

local instance firstCorrectionAverageCountableS0 : FirstCountableTopology S0 :=
  frobeniusCoordinateEquiv.toHomeomorph.isInducing.firstCountableTopology

local instance firstCorrectionAverageCompleteOperator : CompleteSpace ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.instCompleteSpace (σ := RingHom.id ℝ)

local instance firstCorrectionAverageENormedOperator : ENormedAddMonoid ((S0 × Gradient) →L[ℝ] S0) :=
  NormedAddGroup.toENormedAddMonoid

private theorem averagedHarmonicLinearization_eq_operator_integral
    (a : BulkCoefficients) (X Y : S0 × Gradient) :
    averagedHarmonicLinearization a X Y =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (fun p : S0 × Gradient => projectedHarmonicNonlinearity a p.1 p.2)
        (X + t • (Y - X)) := by
  apply ContinuousLinearMap.ext
  intro Z
  let A (t : ℝ) :=
    fderiv ℝ (fun p : S0 × Gradient => projectedHarmonicNonlinearity a p.1 p.2) (X + t • (Y - X))
  let L := ContinuousLinearMap.apply ℝ S0 Z
  have hA : IntervalIntegrable A volume (0 : ℝ) 1 :=
    (continuous_harmonicDerivative_line a X (Y-X)).intervalIntegrable 0 1
  rw [averagedHarmonicLinearization_apply]
  change (∫ t in (0 : ℝ)..1, L (A t)) = L (∫ t in (0 : ℝ)..1, A t)
  exact @ContinuousLinearMap.intervalIntegral_comp_comm ℝ ((S0 × Gradient) →L[ℝ] S0) S0
    firstCorrectionOperatorCLMNormed firstCorrectionOperatorCLMNormedSpace
    0 1 volume A inferInstance firstCorrectionOperatorCLMNormedSpace
    inferInstance inferInstance inferInstance firstCorrectionAverageCompleteS0 firstCorrectionAverageCompleteOperator L hA

/-- The actual linearization averaged along the two states is smooth
in the endpoints and hence has the required coefficient derivatives. -/
theorem contDiff_averagedHarmonicLinearization (a : BulkCoefficients) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω)
      (fun p : (S0 × Gradient) × (S0 × Gradient) => averagedHarmonicLinearization a p.1 p.2) := by
  let A := fderiv ℝ (fun p : S0 × Gradient => projectedHarmonicNonlinearity a p.1 p.2)
  have hA : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) A := (contDiff_projectedHarmonicNonlinearity a).fderiv_right (by simp)
  have hSmooth := @contDiff_affineSegmentAverage (S0 × Gradient) ((S0 × Gradient) →L[ℝ] S0)
    inferInstance inferInstance inferInstance firstCorrectionOperatorCLMNormed firstCorrectionOperatorCLMNormedSpace
    firstCorrectionAverageCompleteOperator A hA
  convert hSmooth using 1
  funext p
  rw [averagedHarmonicLinearization_eq_operator_integral]
  apply intervalIntegral.integral_congr
  intro t _
  have h : p.1 + t • (p.2-p.1) = (1-t) • p.1 + t • p.2 := by
    calc
      _ = (1:ℝ) • p.1 - t • p.1 + t • p.2 := by rw [one_smul, smul_sub]; abel
      _ = _ := congrArg (fun V : S0 × Gradient => V + t • p.2) (sub_smul (1:ℝ) t p.1).symm
  exact congrArg A h

end Thesis

end

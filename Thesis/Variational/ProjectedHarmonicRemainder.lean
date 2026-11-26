module

public import Thesis.Variational.ScaledDefects
public import Thesis.Foundation.LinearizedBulk

/-! The exact projected harmonic equation and its scalar defect sources. -/

@[expose] public section

open Set
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

/-- The cubic contraction of one tensor with two actual gradient columns. -/
def cubicGradientContraction (A : S0) (D : Gradient) : ℝ :=
  ∑ j, ((D j : Tensor) * (D j : Tensor) * (A : Tensor)).trace

theorem cubicGradientContraction_eq (Q : Point → S0) (D : Point → Gradient) (x : Point) :
    cubicGradientContraction (Q x) (D x) = gradientTraceMul D D (Q x : Tensor) x := rfl

/-- The norm defect shifted by its limiting gradient contribution. -/
def adjustedNormDefect (a : BulkCoefficients) (ε : ElasticScale) (Q : Point → S0) (x : Point) : ℝ :=
  scaledNormDefect a ε (Q x) +
    (1 / (2 * bulkRadialCoefficient a * vacuumRadius a ^ 2)) * gradientNormSq (ClassicalGradient Q x)

/-- The cubic scalar defect shifted by its limiting gradient contribution. -/
def adjustedCubicDefect (a : BulkCoefficients) (ε : ElasticScale) (Q : Point → S0) (x : Point) : ℝ :=
  scaledCubicTrace a ε (Q x) +
    (3 / (a.a6' * vacuumRadius a ^ 4)) * cubicGradientContraction (Q x) (ClassicalGradient Q x)

/-- The polynomial part of the projected harmonic-map expression. -/
def projectedHarmonicNonlinearity (a : BulkCoefficients) (A : S0) (D : Gradient) : S0 :=
  (gradientNormSq D / (2 * vacuumRadius a ^ 2)) • A +
    (3 / vacuumRadius a ^ 4 * cubicGradientContraction A D) • traceFreeSquare A

/-- The residual of the ambient harmonic-map equation in the traceless
symmetric tensor space, including the actual componentwise Laplacian. -/
def projectedHarmonicExpression (a : BulkCoefficients) (Q : Point → S0) (x : Point) : S0 :=
  laplacian Q x + projectedHarmonicNonlinearity a (Q x) (ClassicalGradient Q x)

/-- The traceless part of the exact remainder in the penalized map equation. -/
def projectedHarmonicRemainder (a : BulkCoefficients) (ε : ElasticScale) (Q : Point → S0) (x : Point) : S0 :=
  (bulkRadialCoefficient a * adjustedNormDefect a ε Q x) • Q x +
    (a.a6 * ε.val ^ 2 * scaledNormDefect a ε (Q x) ^ 2) • Q x +
    (a.a6' * adjustedCubicDefect a ε Q x) • traceFreeSquare (Q x)

/-- The unprojected remainder also carries the scalar multiple of the identity. -/
def harmonicRemainder (a : BulkCoefficients) (ε : ElasticScale) (Q : Point → S0) (x : Point) : Tensor :=
  (projectedHarmonicRemainder a ε Q x : Tensor) +
    (ε.val ^ 2 / vacuumRadius a ^ 4 * scaledNormDefect a ε (Q x) *
      cubicGradientContraction (Q x) (ClassicalGradient Q x)) • (1 : Tensor)

theorem harmonicRemainder_trace (a : BulkCoefficients) (ε : ElasticScale) (Q : Point → S0) (x : Point) :
    (harmonicRemainder a ε Q x).trace =
      3 * ε.val ^ 2 * scaledNormDefect a ε (Q x) *
        cubicGradientContraction (Q x) (ClassicalGradient Q x) / vacuumRadius a ^ 4 := by
  rw [harmonicRemainder, Matrix.trace_add, S0.trace_eq_zero, zero_add, Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin, smul_eq_mul, Nat.cast_ofNat]
  ring

theorem traceFreeSymmetricPart_harmonicRemainder
    (a : BulkCoefficients) (ε : ElasticScale) (Q : Point → S0) (x : Point) :
    traceFreeSymmetricPart (harmonicRemainder a ε Q x) = projectedHarmonicRemainder a ε Q x := by
  change traceFreeSymmetricPartCLM (harmonicRemainder a ε Q x) = _
  rw [harmonicRemainder, map_add, map_smul, traceFreeSymmetricPartCLM_apply, traceFreeSymmetricPart_of_S0,
    traceFreeSymmetricPartCLM_apply]
  have hOne : traceFreeSymmetricPart (1 : Tensor) = 0 := by
    apply (traceFreeSymmetricPart_eq_zero_iff _).2
    intro B
    rw [frobenius, Matrix.transpose_one, one_mul, B.trace_eq_zero]
  rw [hOne, smul_zero, add_zero]

theorem projectedHarmonicExpression_eq_remainder
    (a : BulkCoefficients) (ε : ElasticScale) (Q : Point → S0) (x : Point)
    (hEq : ε.val ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) :
    projectedHarmonicExpression a Q x = projectedHarmonicRemainder a ε Q x := by
  let r := vacuumRadius a
  let k := bulkRadialCoefficient a
  let G := gradientNormSq (ClassicalGradient Q x)
  let S := cubicGradientContraction (Q x) (ClassicalGradient Q x)
  have hΔ : laplacian Q x = scaledRadialCoefficient a ε (Q x) • Q x +
      (a.a6' * scaledCubicTrace a ε (Q x)) • traceFreeSquare (Q x) :=
    Subtype.ext (laplacian_eq_scaledDefects a ε Q x hEq)
  have hk : k ≠ 0 := (bulkRadialCoefficient_pos a).ne'
  have hr : r ≠ 0 := (vacuumRadius_pos a).ne'
  have h₁ : k * ((1 / (2 * k * r ^ 2)) * G) = G / (2 * r ^ 2) := by
    field_simp [hk, hr]
  have h₂ : a.a6' * ((3 / (a.a6' * r ^ 4)) * S) = 3 / r ^ 4 * S := by
    field_simp [a.a6'_pos.ne', hr]
  unfold projectedHarmonicExpression projectedHarmonicNonlinearity projectedHarmonicRemainder
    adjustedNormDefect adjustedCubicDefect
  rw [hΔ, scaledRadialCoefficient, add_smul, mul_add, mul_add, h₁, h₂]
  simp only [add_smul]
  abel

theorem laplacian_eq_harmonicRhs_add_remainder
    (a : BulkCoefficients) (ε : ElasticScale) (Q : Point → S0) (x : Point)
    (hEq : ε.val ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) :
    (↑(laplacian Q x) : Tensor) = harmonicRhs a Q (ClassicalGradient Q) x + harmonicRemainder a ε Q x := by
  have h := congrArg Subtype.val (projectedHarmonicExpression_eq_remainder a ε Q x hEq)
  let A : Tensor := Q x
  let S := cubicGradientContraction (Q x) (ClassicalGradient Q x)
  let hN := scaledNormDefect a ε (Q x)
  let r := vacuumRadius a
  have hSquare : (traceFreeSquare (Q x) : Tensor) =
      biaxialQuadratic a A - (ε.val ^ 2 * hN / 3) • (1 : Tensor) := by
    rw [traceFreeSquare_coe, trace_sq_eq_scaledNormDefect a ε (Q x)]
    unfold biaxialQuadratic
    change A ^ 2 - ((2*r^2 + ε.val^2*hN)/3) • (1 : Tensor) =
      A ^ 2 - (2*r^2/3) • (1 : Tensor) - (ε.val^2*hN/3) • (1 : Tensor)
    rw [add_div, add_smul]
    abel
  have hW : (3 / r^4 * S) * (ε.val^2 * hN / 3) = ε.val^2 / r^4 * hN * S := by ring
  change (↑(laplacian Q x) : Tensor) +
    ((gradientNormSq (ClassicalGradient Q x) / (2*r^2)) • A +
      (3 / r^4 * S) • (traceFreeSquare (Q x) : Tensor)) =
    (projectedHarmonicRemainder a ε Q x : Tensor) at h
  rw [hSquare, smul_sub, smul_smul, hW] at h
  unfold harmonicRhs harmonicRemainder
  change (↑(laplacian Q x) : Tensor) =
    -(gradientNormSq (ClassicalGradient Q x) / (2*r^2)) • A - (3 / r^4 * S) • biaxialQuadratic a A +
      ((projectedHarmonicRemainder a ε Q x : Tensor) + (ε.val^2 / r^4 * hN * S) • (1 : Tensor))
  rw [neg_smul, ← h]
  abel

theorem projectedHarmonicExpression_eq_zero_of_harmonic
    (a : BulkCoefficients) (Q : Point → S0) (x : Point) (hVac : Q x ∈ vacuum a)
    (hHarm : (↑(laplacian Q x) : Tensor) = harmonicRhs a Q (ClassicalGradient Q) x) :
    projectedHarmonicExpression a Q x = 0 := by
  apply Subtype.ext
  change (↑(laplacian Q x) : Tensor) +
    ((gradientNormSq (ClassicalGradient Q x) / (2 * vacuumRadius a ^ 2)) • (Q x : Tensor) +
      (3 / vacuumRadius a ^ 4 * cubicGradientContraction (Q x) (ClassicalGradient Q x)) •
        (traceFreeSquare (Q x) : Tensor)) = 0
  rw [hHarm, traceFreeSquare_coe_eq_biaxialQuadratic hVac, harmonicRhs, cubicGradientContraction_eq, neg_smul]
  abel

/-- The scalar source in the screened equation for the adjusted norm defect. -/
def adjustedNormDefectSource (a : BulkCoefficients) (ε : ElasticScale) (Q : Point → S0) (x : Point) : ℝ :=
  let h := scaledNormDefect a ε (Q x)
  let t := scaledCubicTrace a ε (Q x)
  0 - (1 / (2 * bulkRadialCoefficient a * vacuumRadius a ^ 2)) *
      laplacian (fun y => gradientNormSq (ClassicalGradient Q y)) x -
    (2 * bulkRadialCoefficient a + 4 * a.a6 * vacuumRadius a ^ 2) * h ^ 2 -
    2 * a.a6 * ε.val ^ 2 * h ^ 3 - 2 * a.a6' * t ^ 2

/-- The scalar source in the screened equation for the adjusted cubic defect. -/
def adjustedCubicDefectSource (a : BulkCoefficients) (ε : ElasticScale) (Q : Point → S0) (x : Point) : ℝ :=
  let h := scaledNormDefect a ε (Q x)
  let t := scaledCubicTrace a ε (Q x)
  0 - (3 / (a.a6' * vacuumRadius a ^ 4)) *
      laplacian (fun y => cubicGradientContraction (Q y) (ClassicalGradient Q y)) x -
    (3 * bulkRadialCoefficient a + 2 * a.a6' * vacuumRadius a ^ 2) * h * t -
    ε.val ^ 2 * (3 * a.a6 + a.a6' / 2) * h ^ 2 * t

private theorem laplacian_add_mul_const {U : Set Point} (hU : IsOpen U)
    {f g : Point → ℝ} (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U)
    {x : Point} (hx : x ∈ U) (k : ℝ) :
    laplacian (fun y => f y + k * g y) x = laplacian f x + k * laplacian g x := by
  let u (y : Point) := (f y, g y)
  let F := ContinuousLinearMap.fst ℝ ℝ ℝ
  let G := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hu : ContDiffOn ℝ 2 u U := hf.prodMk hg
  have hf' : (laplacian u x).1 = laplacian f x := (laplacian_compCLM hU hu hx F).symm
  have hg' : (laplacian u x).2 = laplacian g x := (laplacian_compCLM hU hu hx G).symm
  have h := laplacian_compCLM hU hu hx (F + k • G)
  change laplacian (fun y => f y + k * g y) x = (laplacian u x).1 + k * (laplacian u x).2 at h
  rwa [hf', hg'] at h

private theorem contDiffOn_classicalGradient_tensor_columns
    {U : Set Point} (hU : IsOpen U) {Q : Point → S0} (hQ : ContDiffOn ℝ 3 Q U) (j : Fin 3) :
    ContDiffOn ℝ 2 (fun y => (↑(coordDeriv j Q y) : Tensor)) U :=
  (symmetricTraceless.subtypeL.comp (ContinuousLinearMap.apply ℝ S0 (axis j))).contDiff.comp_contDiffOn
    (hQ.fderiv_of_isOpen hU (by norm_num))

private theorem contDiffOn_classicalGradient_normSq
    {U : Set Point} (hU : IsOpen U) {Q : Point → S0} (hQ : ContDiffOn ℝ 3 Q U) :
    ContDiffOn ℝ 2 (fun y => gradientNormSq (ClassicalGradient Q y)) U := by
  simp only [gradientNormSq, ClassicalGradient, frobeniusS0, frobenius, S0.transpose_eq]
  exact ContDiffOn.sum fun j _ => tensorTraceCLM.contDiff.comp_contDiffOn
    ((contDiffOn_classicalGradient_tensor_columns hU hQ j).mul
      (contDiffOn_classicalGradient_tensor_columns hU hQ j))

private theorem contDiffOn_cubicGradientContraction
    {U : Set Point} (hU : IsOpen U) {Q : Point → S0} (hQ : ContDiffOn ℝ 3 Q U) :
    ContDiffOn ℝ 2 (fun y => cubicGradientContraction (Q y) (ClassicalGradient Q y)) U := by
  have hA : ContDiffOn ℝ 2 (fun y => (Q y : Tensor)) U :=
    symmetricTraceless.subtypeL.contDiff.comp_contDiffOn (hQ.of_le (by norm_num))
  unfold cubicGradientContraction ClassicalGradient
  exact ContDiffOn.sum fun j _ => tensorTraceCLM.contDiff.comp_contDiffOn
    (((contDiffOn_classicalGradient_tensor_columns hU hQ j).mul
      (contDiffOn_classicalGradient_tensor_columns hU hQ j)).mul hA)

theorem adjustedNormDefect_screened_equation
    (a : BulkCoefficients) (ε : ElasticScale) {U : Set Point} (hU : IsOpen U)
    {Q : Point → S0} (hQ : ContDiffOn ℝ 3 Q U) {x : Point} (hx : x ∈ U)
    (hEq : ε.val ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) :
    -ε.val ^ 2 * laplacian (adjustedNormDefect a ε Q) x +
      bulkRadialMass a * adjustedNormDefect a ε Q x =
        ε.val ^ 2 * adjustedNormDefectSource a ε Q x := by
  let h (y : Point) := scaledNormDefect a ε (Q y)
  let g (y : Point) := gradientNormSq (ClassicalGradient Q y)
  let k := 1 / (2 * bulkRadialCoefficient a * vacuumRadius a ^ 2)
  have hA : ContDiffOn ℝ 2 (fun y => (Q y : Tensor)) U :=
    symmetricTraceless.subtypeL.contDiff.comp_contDiffOn (hQ.of_le (by norm_num))
  have hh : ContDiffOn ℝ 2 h U :=
    contDiffOn_const.mul ((tensorTraceCLM.contDiff.comp_contDiffOn (hA.pow 2)).sub contDiffOn_const)
  have hg : ContDiffOn ℝ 2 g U := contDiffOn_classicalGradient_normSq hU hQ
  have hΔ := laplacian_add_mul_const hU hh hg hx k
  have hk : bulkRadialMass a * k = 2 := by
    dsimp [bulkRadialMass, k]
    field_simp [(bulkRadialCoefficient_pos a).ne', (vacuumRadius_pos a).ne']
    norm_num
  have hP := scaledNormDefect_equation a ε hU (hQ.of_le (by norm_num)) hx hEq
  unfold adjustedNormDefectSource adjustedNormDefect
  change -ε.val ^ 2 * laplacian (fun y => h y + k * g y) x +
    bulkRadialMass a * (h x + k * g x) = _
  rw [hΔ, mul_add (bulkRadialMass a) (h x) (k * g x), ← mul_assoc (bulkRadialMass a) k (g x), hk]
  dsimp only [h, g, k] at *
  nlinarith only [hP]

theorem adjustedCubicDefect_screened_equation
    (a : BulkCoefficients) (ε : ElasticScale) {U : Set Point} (hU : IsOpen U)
    {Q : Point → S0} (hQ : ContDiffOn ℝ 3 Q U) {x : Point} (hx : x ∈ U)
    (hEq : ε.val ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) :
    -ε.val ^ 2 * laplacian (adjustedCubicDefect a ε Q) x +
      bulkBiaxialMass a * adjustedCubicDefect a ε Q x =
        ε.val ^ 2 * adjustedCubicDefectSource a ε Q x := by
  let t (y : Point) := scaledCubicTrace a ε (Q y)
  let g (y : Point) := cubicGradientContraction (Q y) (ClassicalGradient Q y)
  let k := 3 / (a.a6' * vacuumRadius a ^ 4)
  have hA : ContDiffOn ℝ 2 (fun y => (Q y : Tensor)) U :=
    symmetricTraceless.subtypeL.contDiff.comp_contDiffOn (hQ.of_le (by norm_num))
  have ht : ContDiffOn ℝ 2 t U := by
    simp only [t, scaledCubicTrace_eq]
    exact contDiffOn_const.mul (tensorTraceCLM.contDiff.comp_contDiffOn (hA.pow 3))
  have hg : ContDiffOn ℝ 2 g U := contDiffOn_cubicGradientContraction hU hQ
  have hΔ := laplacian_add_mul_const hU ht hg hx k
  have hk : bulkBiaxialMass a * k = 6 := by
    dsimp [bulkBiaxialMass, k]
    field_simp [a.a6'_pos.ne', (vacuumRadius_pos a).ne']
    norm_num
  have hP := scaledCubicTrace_equation a ε hU (hQ.of_le (by norm_num)) hx hEq
  unfold adjustedCubicDefectSource adjustedCubicDefect
  change -ε.val ^ 2 * laplacian (fun y => t y + k * g y) x +
    bulkBiaxialMass a * (t x + k * g x) = _
  rw [hΔ, mul_add (bulkBiaxialMass a) (t x) (k * g x), ← mul_assoc (bulkBiaxialMass a) k (g x), hk]
  dsimp only [t, g, k] at *
  rw [cubicGradientContraction_eq]
  nlinarith only [hP]

end Thesis

end

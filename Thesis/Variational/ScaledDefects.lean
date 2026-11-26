module

public import Thesis.Foundation.LinearizedBulk
public import Thesis.Foundation.SpectralProjection

/-! Differential identities for the scaled defects of a classical sextic solution. -/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Filter Set
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius Topology

namespace Thesis

/-- The squared-trace defect divided by the square of the elastic scale. -/
def scaledNormDefect (a : BulkCoefficients) (ε : ElasticScale) (A : S0) : ℝ :=
  (ε.val ^ 2)⁻¹ * (((A : Tensor) ^ 2).trace - 2 * vacuumRadius a ^ 2)

/-- The cubic tensor defect divided by the square of the elastic scale. -/
def scaledCubicDefect (a : BulkCoefficients) (ε : ElasticScale) (A : S0) : Tensor :=
  (ε.val ^ 2)⁻¹ • ((A : Tensor) ^ 3 - vacuumRadius a ^ 2 • (A : Tensor))

/-- The scalar trace of the scaled cubic tensor defect. -/
def scaledCubicTrace (a : BulkCoefficients) (ε : ElasticScale) (A : S0) : ℝ :=
  (scaledCubicDefect a ε A).trace

/-- The scalar coefficient of the tensor in the scaled force equation. -/
def scaledRadialCoefficient (a : BulkCoefficients) (ε : ElasticScale) (A : S0) : ℝ :=
  bulkRadialCoefficient a * scaledNormDefect a ε A + a.a6 * ε.val ^ 2 * scaledNormDefect a ε A ^ 2

theorem scaledCubicTrace_eq (a : BulkCoefficients) (ε : ElasticScale) (A : S0) :
    scaledCubicTrace a ε A = (ε.val ^ 2)⁻¹ * ((A : Tensor) ^ 3).trace := by
  rw [scaledCubicTrace, scaledCubicDefect, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul,
    A.trace_eq_zero, smul_zero, sub_zero, smul_eq_mul]

theorem trace_sq_eq_scaledNormDefect (a : BulkCoefficients) (ε : ElasticScale) (A : S0) :
    ((A : Tensor) ^ 2).trace = 2 * vacuumRadius a ^ 2 + ε.val ^ 2 * scaledNormDefect a ε A := by
  unfold scaledNormDefect
  have hε : (ε.val ^ 2 : ℝ) ≠ 0 := pow_ne_zero _ ε.property.1.ne'
  rw [← mul_assoc, mul_inv_cancel₀ hε, one_mul]
  ring

theorem trace_cube_eq_scaledCubicTrace (a : BulkCoefficients) (ε : ElasticScale) (A : S0) :
    ((A : Tensor) ^ 3).trace = ε.val ^ 2 * scaledCubicTrace a ε A := by
  have hε : (ε.val ^ 2 : ℝ) ≠ 0 := pow_ne_zero _ ε.property.1.ne'
  rw [scaledCubicTrace_eq, ← mul_assoc, mul_inv_cancel₀ hε, one_mul]

private theorem orderedEigenbasis_pow_mulVec (A : S0) (i : Fin 3) (k : ℕ) :
    (A : Tensor) ^ k *ᵥ (orderedEigenbasis A i).ofLp =
      orderedEigenvalue A i ^ k • (orderedEigenbasis A i).ofLp := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, orderedEigenbasis_mulVec, Matrix.mulVec_smul, hk, smul_smul,
      pow_succ, mul_comm (orderedEigenvalue A i)]

/-- Cayley–Hamilton in the trace form for the symmetric traceless tensor. -/
theorem cube_eq_trace_smul (A : S0) :
    (A : Tensor) ^ 3 =
      (((A : Tensor) ^ 2).trace / 2) • (A : Tensor) + (((A : Tensor) ^ 3).trace / 3) • (1 : Tensor) := by
  apply Matrix.toEuclideanLin.injective
  apply (orderedEigenbasis A).toBasis.ext
  intro i
  apply PiLp.ext
  intro j
  change (((A : Tensor) ^ 3) *ᵥ (orderedEigenbasis A i).ofLp) j =
    (((((A : Tensor) ^ 2).trace / 2) • (A : Tensor) +
      (((A : Tensor) ^ 3).trace / 3) • (1 : Tensor)) *ᵥ (orderedEigenbasis A i).ofLp) j
  simp only [orderedEigenbasis_pow_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    orderedEigenbasis_mulVec, Matrix.one_mulVec, smul_smul, ← add_smul]
  have h := orderedEigenvalue_cubic_equation A i
  have he : orderedEigenvalue A i ^ 3 = ((A : Tensor) ^ 2).trace / 2 * orderedEigenvalue A i +
      ((A : Tensor) ^ 3).trace / 3 := by linarith only [h]
  rw [he]

theorem trace_four_eq_trace_sq_sq (A : S0) :
    ((A : Tensor) ^ 4).trace = (((A : Tensor) ^ 2).trace) ^ 2 / 2 := by
  rw [pow_succ _ 3, cube_eq_trace_smul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, one_mul,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, ← pow_two, A.trace_eq_zero,
    smul_zero, add_zero, smul_eq_mul]
  ring

theorem trace_mul_scaledCubicDefect (a : BulkCoefficients) (ε : ElasticScale) (A : S0) :
    ((A : Tensor) * scaledCubicDefect a ε A).trace =
      ((A : Tensor) ^ 2).trace * scaledNormDefect a ε A / 2 := by
  rw [scaledCubicDefect, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_sub, Matrix.trace_smul, ← pow_succ', ← pow_two, trace_four_eq_trace_sq_sq, scaledNormDefect]
  simp only [smul_eq_mul]
  ring

theorem scaledCubicDefect_eq_scalar_parts (a : BulkCoefficients) (ε : ElasticScale) (A : S0) :
    scaledCubicDefect a ε A =
      (scaledNormDefect a ε A / 2) • (A : Tensor) + (scaledCubicTrace a ε A / 3) • (1 : Tensor) := by
  rw [scaledCubicDefect, cube_eq_trace_smul, scaledCubicTrace_eq]
  simp only [scaledNormDefect, add_sub_right_comm, ← sub_smul, smul_add, smul_smul]
  have h₁ : (ε.val ^ 2)⁻¹ * (((A : Tensor) ^ 2).trace / 2 - vacuumRadius a ^ 2) =
    (ε.val ^ 2)⁻¹ * (((A : Tensor) ^ 2).trace - 2 * vacuumRadius a ^ 2) / 2 := by ring
  have h₂ : (ε.val ^ 2)⁻¹ * (((A : Tensor) ^ 3).trace / 3) =
    (ε.val ^ 2)⁻¹ * ((A : Tensor) ^ 3).trace / 3 := by ring
  rw [h₁, h₂]

theorem fderiv_trace_sq_field {u : Point → S0} {x : Point} (hu : DifferentiableAt ℝ u x)
    (v : Point) :
    fderiv ℝ (fun y => ((u y : Tensor) ^ 2).trace) x v =
      2 * ((u x : Tensor) * (fderiv ℝ u x v : S0).val).trace := by
  have hd := (((hasStrictFDerivAt_vacuumInvariants (u x)).hasFDerivAt.comp x hu.hasFDerivAt).fst).fderiv
  have hv := DFunLike.congr_fun hd v
  exact hv.trans (congrArg Prod.fst (vacuumInvariantDerivative_apply (u x) (fderiv ℝ u x v)))

theorem fderiv_trace_cube_field {u : Point → S0} {x : Point} (hu : DifferentiableAt ℝ u x)
    (v : Point) :
    fderiv ℝ (fun y => ((u y : Tensor) ^ 3).trace) x v =
      3 * (((u x : Tensor) ^ 2) * (fderiv ℝ u x v : S0).val).trace := by
  have hd := (((hasStrictFDerivAt_vacuumInvariants (u x)).hasFDerivAt.comp x hu.hasFDerivAt).snd).fderiv
  have hv := DFunLike.congr_fun hd v
  exact hv.trans (congrArg Prod.snd (vacuumInvariantDerivative_apply (u x) (fderiv ℝ u x v)))

theorem scaled_bulkGradient_eq_scaledDefects (a : BulkCoefficients) (ε : ElasticScale) (A : S0) :
    (ε.val ^ 2)⁻¹ • bulkGradient a A = scaledRadialCoefficient a ε A • (A : Tensor) +
      (a.a6' * scaledCubicTrace a ε A) • (traceFreeSquare A : Tensor) := by
  let s := ε.val ^ 2
  let r := vacuumRadius a
  let h := scaledNormDefect a ε A
  let m := scaledRadialCoefficient a ε A
  let t := scaledCubicTrace a ε A
  have hs : s ≠ 0 := pow_ne_zero _ ε.property.1.ne'
  have hRad : -a.a2 + a.a4 * ((A : Tensor) ^ 2).trace + a.a6 * (((A : Tensor) ^ 2).trace) ^ 2 =
      s * m := by
    change -a.a2 + a.a4 * ((A : Tensor) ^ 2).trace + a.a6 * (((A : Tensor) ^ 2).trace) ^ 2 =
      s * (bulkRadialCoefficient a * h + a.a6 * s * h ^ 2)
    rw [trace_sq_eq_scaledNormDefect a ε A, bulkRadialCoefficient]
    change -a.a2 + a.a4 * (2 * r ^ 2 + s * h) + a.a6 * (2 * r ^ 2 + s * h) ^ 2 =
      s * ((a.a4 + 4 * a.a6 * r ^ 2) * h + a.a6 * s * h ^ 2)
    have hr : 4 * a.a6 * r ^ 4 + 2 * a.a4 * r ^ 2 - a.a2 = 0 := vacuumRadius_equation a
    linear_combination hr
  have hCubic : ((A : Tensor) ^ 3).trace = s * t := trace_cube_eq_scaledCubicTrace a ε A
  have h₁ : s⁻¹ * (s * m) = m := inv_mul_cancel_left₀ hs _
  have h₂ : s⁻¹ * (a.a6' * (s * t)) = a.a6' * t := by
    rw [mul_left_comm a.a6' s, inv_mul_cancel_left₀ hs]
  unfold bulkGradient
  dsimp only
  rw [← traceFreeSquare_coe, hRad, hCubic]
  change s⁻¹ • ((s * m) • (A : Tensor) + (a.a6' * (s * t)) • (traceFreeSquare A : Tensor)) = _
  rw [smul_add, smul_smul, smul_smul, h₁, h₂]

/-- The classical matrix equation expressed using the scaled scalar defects. -/
theorem laplacian_eq_scaledDefects (a : BulkCoefficients) (ε : ElasticScale) (u : Point → S0)
    (x : Point) (hEq : ε.val ^ 2 • (laplacian u x : S0).val = bulkGradient a (u x)) :
    (laplacian u x : S0).val = scaledRadialCoefficient a ε (u x) • (u x : Tensor) +
      (a.a6' * scaledCubicTrace a ε (u x)) • (traceFreeSquare (u x) : Tensor) := by
  have hε : (ε.val ^ 2 : ℝ) ≠ 0 := pow_ne_zero _ ε.property.1.ne'
  calc
    _ = (ε.val ^ 2)⁻¹ • (ε.val ^ 2 • (laplacian u x : S0).val) := by
      rw [smul_smul, inv_mul_cancel₀ hε, one_smul]
    _ = _ := by rw [hEq, scaled_bulkGradient_eq_scaledDefects]

theorem scaledRadialCoefficient_eq_cubic_pairing (a : BulkCoefficients) (ε : ElasticScale) (A : S0) :
    scaledRadialCoefficient a ε A =
      2 * a.a6 * ((A : Tensor) * scaledCubicDefect a ε A).trace +
        (a.a2 / (2 * vacuumRadius a ^ 2)) * scaledNormDefect a ε A := by
  let r := vacuumRadius a
  let h := scaledNormDefect a ε A
  have hr : 0 < r := vacuumRadius_pos a
  have hc : a.a2 / (2 * r ^ 2) = a.a4 + 2 * a.a6 * r ^ 2 := by
    apply (div_eq_iff (by positivity : (2 * r ^ 2 : ℝ) ≠ 0)).2
    have hR : 4 * a.a6 * r ^ 4 + 2 * a.a4 * r ^ 2 - a.a2 = 0 := vacuumRadius_equation a
    linear_combination -hR
  rw [trace_mul_scaledCubicDefect, trace_sq_eq_scaledNormDefect a ε A]
  change (a.a4 + 4 * a.a6 * r ^ 2) * h + a.a6 * ε.val ^ 2 * h ^ 2 =
    2 * a.a6 * ((2 * r ^ 2 + ε.val ^ 2 * h) * h / 2) + (a.a2 / (2 * r ^ 2)) * h
  rw [hc]
  ring

theorem coordDeriv_compCLM {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Point → E} {x : Point}
    (L : E →L[ℝ] F) (hf : DifferentiableAt ℝ f x) (j : Fin 3) :
    coordDeriv j (fun y => L (f y)) x = L (coordDeriv j f x) := by
  have hd := (L.hasFDerivAt (x := f x)).comp x hf.hasFDerivAt
  exact DFunLike.congr_fun hd.fderiv (axis j)

theorem differentiableAt_coordDeriv_of_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} {x : Point} (hf : ContDiffAt ℝ 2 f x) (j : Fin 3) :
    DifferentiableAt ℝ (coordDeriv j f) x := by
  let ev := ContinuousLinearMap.apply ℝ E (axis j)
  exact (ev.differentiableAt (x := fderiv ℝ f x)).comp x
    ((hf.fderiv_right_succ (n := 1)).differentiableAt one_ne_zero)

private theorem coordDeriv_congr_nhds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Point → E} {x : Point} (h : f =ᶠ[𝓝 x] g) (j : Fin 3) :
    coordDeriv j f x = coordDeriv j g x :=
  DFunLike.congr_fun h.fderiv_eq (axis j)

theorem laplacian_compCLM {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Set Point} (hΩ : IsOpen Ω)
    {f : Point → E} (hf : ContDiffOn ℝ 2 f Ω) {x : Point} (hx : x ∈ Ω) (L : E →L[ℝ] F) :
    laplacian (fun y => L (f y)) x = L (laplacian f x) := by
  unfold laplacian
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : coordDeriv j (fun y => L (f y)) =ᶠ[𝓝 x] fun y => L (coordDeriv j f y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact coordDeriv_compCLM L (((hf y hy).contDiffAt (hΩ.mem_nhds hy)).differentiableAt two_ne_zero) j
  rw [coordDeriv_congr_nhds h j]
  exact coordDeriv_compCLM L (differentiableAt_coordDeriv_of_contDiffAt
    ((hf x hx).contDiffAt (hΩ.mem_nhds hx)) j) j

theorem coordDeriv_matrix_product {f g : Point → Tensor} {x : Point}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (j : Fin 3) :
    coordDeriv j (fun y => f y * g y) x = f x * coordDeriv j g x + coordDeriv j f x * g x :=
  DFunLike.congr_fun (hf.hasFDerivAt.mul' hg.hasFDerivAt).fderiv (axis j)

theorem laplacian_matrix_product {f g : Point → Tensor} {Ω : Set Point} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ 2 f Ω) (hg : ContDiffOn ℝ 2 g Ω) {x : Point} (hx : x ∈ Ω) :
    laplacian (fun y => f y * g y) x = f x * laplacian g x + laplacian f x * g x +
      (2 : ℝ) • ∑ j, coordDeriv j f x * coordDeriv j g x := by
  have hf₂ := (hf x hx).contDiffAt (hΩ.mem_nhds hx)
  have hg₂ := (hg x hx).contDiffAt (hΩ.mem_nhds hx)
  have hpoint (j : Fin 3) : coordDeriv j (coordDeriv j (fun y => f y * g y)) x =
      f x * coordDeriv j (coordDeriv j g) x + coordDeriv j (coordDeriv j f) x * g x +
        (2 : ℝ) • (coordDeriv j f x * coordDeriv j g x) := by
    have hGerm : coordDeriv j (fun y => f y * g y) =ᶠ[𝓝 x]
        fun y => f y * coordDeriv j g y + coordDeriv j f y * g y := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      exact coordDeriv_matrix_product (((hf y hy).contDiffAt (hΩ.mem_nhds hy)).differentiableAt two_ne_zero)
        (((hg y hy).contDiffAt (hΩ.mem_nhds hy)).differentiableAt two_ne_zero) j
    rw [coordDeriv_congr_nhds hGerm j]
    have hD₁ := differentiableAt_coordDeriv_of_contDiffAt hf₂ j
    have hD₂ := differentiableAt_coordDeriv_of_contDiffAt hg₂ j
    have hp := (((hf₂.differentiableAt two_ne_zero).hasFDerivAt.mul' hD₂.hasFDerivAt).add
      (hD₁.hasFDerivAt.mul' (hg₂.differentiableAt two_ne_zero).hasFDerivAt)).fderiv
    calc
      _ = f x * coordDeriv j (coordDeriv j g) x + coordDeriv j f x * coordDeriv j g x +
          (coordDeriv j f x * coordDeriv j g x + coordDeriv j (coordDeriv j f) x * g x) :=
        DFunLike.congr_fun hp (axis j)
      _ = _ := by rw [two_smul ℝ]; abel
  simp only [laplacian, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => hpoint j

theorem laplacian_matrix_square {f : Point → Tensor} {Ω : Set Point} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ 2 f Ω) {x : Point} (hx : x ∈ Ω) :
    laplacian (fun y => (f y) ^ 2) x = f x * laplacian f x + laplacian f x * f x +
      (2 : ℝ) • ∑ j, (coordDeriv j f x) ^ 2 := by
  simpa only [pow_two] using laplacian_matrix_product hΩ hf hf hx

theorem laplacian_matrix_cube {f : Point → Tensor} {Ω : Set Point} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ 2 f Ω) {x : Point} (hx : x ∈ Ω) :
    laplacian (fun y => (f y) ^ 3) x = laplacian f x * (f x) ^ 2 + f x * laplacian f x * f x +
      ((f x) ^ 2) * laplacian f x + (2 : ℝ) • ∑ j,
        (coordDeriv j f x * coordDeriv j f x * f x +
          f x * coordDeriv j f x * coordDeriv j f x + coordDeriv j f x * f x * coordDeriv j f x) := by
  have hf₁ := ((hf x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt two_ne_zero
  have hD (j : Fin 3) : coordDeriv j (fun y => (f y) ^ 2) x =
      f x * coordDeriv j f x + coordDeriv j f x * f x := by
    simpa only [pow_two] using coordDeriv_matrix_product hf₁ hf₁ j
  have hFun : (fun y => (f y) ^ 3) = (fun y => (f y) ^ 2 * f y) := by
    funext y
    rw [pow_succ _ 2]
  rw [hFun, laplacian_matrix_product hΩ (hf.pow 2) hf hx, laplacian_matrix_square hΩ hf hx]
  simp only [hD, Matrix.add_mul, Matrix.smul_mul, Matrix.sum_mul]
  have hsum : (2 : ℝ) • (∑ j, (coordDeriv j f x) ^ 2 * f x) +
      (2 : ℝ) • (∑ j, (f x * coordDeriv j f x * coordDeriv j f x +
        coordDeriv j f x * f x * coordDeriv j f x)) = (2 : ℝ) • ∑ j,
        (coordDeriv j f x * coordDeriv j f x * f x +
          f x * coordDeriv j f x * coordDeriv j f x + coordDeriv j f x * f x * coordDeriv j f x) := by
    rw [← smul_add, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_two]
    abel
  rw [pow_two, mul_assoc (laplacian f x) (f x) (f x)]
  calc
    _ = f x * f x * laplacian f x + f x * laplacian f x * f x + laplacian f x * (f x * f x) +
        ((2 : ℝ) • (∑ j, (coordDeriv j f x) ^ 2 * f x) +
          (2 : ℝ) • ∑ j, (f x * coordDeriv j f x * coordDeriv j f x +
            coordDeriv j f x * f x * coordDeriv j f x)) := by abel
    _ = _ := by rw [hsum]; abel

theorem laplacian_trace_sq_field {u : Point → S0} {Ω : Set Point} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) {x : Point} (hx : x ∈ Ω) :
    laplacian (fun y => ((u y : Tensor) ^ 2).trace) x =
      2 * ((u x : Tensor) * (laplacian u x : S0).val).trace + 2 * gradientNormSq (ClassicalGradient u x) := by
  let U : Point → Tensor := fun y => u y
  let L : Tensor := (laplacian u x : S0).val
  have hU : ContDiffOn ℝ 2 U Ω := symmetricTraceless.subtypeL.contDiff.comp_contDiffOn hu
  have hL : laplacian U x = L := laplacian_compCLM hΩ hu hx symmetricTraceless.subtypeL
  have hD (j : Fin 3) : coordDeriv j U x = (coordDeriv j u x : S0).val :=
    coordDeriv_compCLM symmetricTraceless.subtypeL
      (((hu x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt two_ne_zero) j
  calc
    _ = tensorTraceCLM (laplacian (fun y => (U y) ^ 2) x) :=
      laplacian_compCLM hΩ (hU.pow 2) hx tensorTraceCLM
    _ = _ := by
      rw [laplacian_matrix_square hΩ hU hx, hL]
      change (U x * L + L * U x + (2 : ℝ) • ∑ j, (coordDeriv j U x) ^ 2).trace =
        2 * (U x * L).trace + 2 * gradientNormSq (ClassicalGradient u x)
      simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum, Matrix.trace_mul_comm L (U x),
        smul_eq_mul, hD, pow_two, gradientNormSq, ClassicalGradient, frobeniusS0, frobenius, S0.transpose_eq]
      ring

theorem laplacian_trace_cube_field {u : Point → S0} {Ω : Set Point} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) {x : Point} (hx : x ∈ Ω) :
    laplacian (fun y => ((u y : Tensor) ^ 3).trace) x =
      3 * (((u x : Tensor) ^ 2) * (laplacian u x : S0).val).trace +
        6 * gradientTraceMul (ClassicalGradient u) (ClassicalGradient u) (u x : Tensor) x := by
  let U : Point → Tensor := fun y => u y
  let L : Tensor := (laplacian u x : S0).val
  let d (j : Fin 3) := coordDeriv j U x
  let G := gradientTraceMul (ClassicalGradient u) (ClassicalGradient u) (u x : Tensor) x
  have hU : ContDiffOn ℝ 2 U Ω := symmetricTraceless.subtypeL.contDiff.comp_contDiffOn hu
  have hL : laplacian U x = L := laplacian_compCLM hΩ hu hx symmetricTraceless.subtypeL
  have hD (j : Fin 3) : d j = (coordDeriv j u x : S0).val :=
    coordDeriv_compCLM symmetricTraceless.subtypeL
      (((hu x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt two_ne_zero) j
  have hSum : (∑ j, (d j * d j * U x + U x * d j * d j + d j * U x * d j).trace) = 3 * G := by
    change (∑ j, (d j * d j * U x + U x * d j * d j + d j * U x * d j).trace) =
      3 * ∑ j, (((coordDeriv j u x : S0) : Tensor) * ((coordDeriv j u x : S0) : Tensor) * U x).trace
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_mul_cycle (U x) (d j) (d j),
      Matrix.trace_mul_cycle (d j) (U x) (d j), hD]
    ring
  have hcyc : (U x * L * U x).trace = ((U x) ^ 2 * L).trace := by
    rw [Matrix.trace_mul_cycle, ← pow_two]
  calc
    _ = tensorTraceCLM (laplacian (fun y => (U y) ^ 3) x) :=
      laplacian_compCLM hΩ (hU.pow 3) hx tensorTraceCLM
    _ = _ := by
      rw [laplacian_matrix_cube hΩ hU hx, hL]
      change (L * (U x) ^ 2 + U x * L * U x + (U x) ^ 2 * L + (2 : ℝ) • ∑ j,
        (d j * d j * U x + U x * d j * d j + d j * U x * d j)).trace =
          3 * ((U x) ^ 2 * L).trace + 6 * G
      rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum,
        hSum, hcyc, Matrix.trace_mul_comm L ((U x) ^ 2), smul_eq_mul]
      ring

theorem laplacian_sub_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Point → E) (c : E) (x : Point) : laplacian (fun y => f y - c) x = laplacian f x := by
  have h (j : Fin 3) : coordDeriv j (fun y => f y - c) = coordDeriv j f := by
    funext y
    exact DFunLike.congr_fun (fderiv_sub_const (𝕜 := ℝ) (f := f) (x := y) c) (axis j)
  simp only [laplacian, h]

theorem laplacian_const_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set Point} (hΩ : IsOpen Ω) {f : Point → E} (hf : ContDiffOn ℝ 2 f Ω) {x : Point}
    (hx : x ∈ Ω) (c : ℝ) : laplacian (fun y => c • f y) x = c • laplacian f x :=
  laplacian_compCLM hΩ hf hx (c • ContinuousLinearMap.id ℝ E)

theorem scale_sq_mul_laplacian_scaledNormDefect (a : BulkCoefficients) (ε : ElasticScale)
    {u : Point → S0} {Ω : Set Point} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) {x : Point}
    (hx : x ∈ Ω) : ε.val ^ 2 * laplacian (fun y => scaledNormDefect a ε (u y)) x =
      laplacian (fun y => ((u y : Tensor) ^ 2).trace) x := by
  let f (y : Point) := (vacuumInvariants (u y)).1
  have hC : ContDiff ℝ 2 (fun A : S0 => (vacuumInvariants A).1) :=
    (contDiff_infty.mp contDiff_vacuumInvariants.fst) 2
  have hf : ContDiffOn ℝ 2 f Ω := hC.comp_contDiffOn hu
  have hg : ContDiffOn ℝ 2 (fun y => f y - 2 * vacuumRadius a ^ 2) Ω := hf.sub contDiffOn_const
  have hε : (ε.val ^ 2 : ℝ) ≠ 0 := pow_ne_zero _ ε.property.1.ne'
  change ε.val ^ 2 * laplacian (fun y => (ε.val ^ 2)⁻¹ • (f y - 2 * vacuumRadius a ^ 2)) x =
    laplacian f x
  rw [laplacian_const_smul hΩ hg hx, laplacian_sub_const, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hε, one_mul]

theorem scale_sq_mul_laplacian_scaledCubicTrace (a : BulkCoefficients) (ε : ElasticScale)
    {u : Point → S0} {Ω : Set Point} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) {x : Point}
    (hx : x ∈ Ω) : ε.val ^ 2 * laplacian (fun y => scaledCubicTrace a ε (u y)) x =
      laplacian (fun y => ((u y : Tensor) ^ 3).trace) x := by
  let f (y : Point) := (vacuumInvariants (u y)).2
  have hC : ContDiff ℝ 2 (fun A : S0 => (vacuumInvariants A).2) :=
    (contDiff_infty.mp contDiff_vacuumInvariants.snd) 2
  have hf : ContDiffOn ℝ 2 f Ω := hC.comp_contDiffOn hu
  have hFun : (fun y => scaledCubicTrace a ε (u y)) = fun y => (ε.val ^ 2)⁻¹ • f y := by
    funext y
    exact scaledCubicTrace_eq a ε (u y)
  have hε : (ε.val ^ 2 : ℝ) ≠ 0 := pow_ne_zero _ ε.property.1.ne'
  rw [hFun, laplacian_const_smul hΩ hf hx, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hε, one_mul]
  rfl

theorem trace_mul_traceFreeSquare (A : S0) :
    ((A : Tensor) * (traceFreeSquare A : Tensor)).trace = ((A : Tensor) ^ 3).trace := by
  rw [traceFreeSquare_coe, Matrix.mul_sub, Matrix.mul_smul, mul_one, Matrix.trace_sub,
    Matrix.trace_smul, A.trace_eq_zero, smul_zero, sub_zero, ← pow_succ']

theorem trace_sq_mul_traceFreeSquare (A : S0) :
    (((A : Tensor) ^ 2) * (traceFreeSquare A : Tensor)).trace = (((A : Tensor) ^ 2).trace) ^ 2 / 6 := by
  have hpow : (A : Tensor) ^ 2 * (A : Tensor) ^ 2 = (A : Tensor) ^ 4 := (pow_add _ 2 2).symm
  rw [traceFreeSquare_coe, Matrix.mul_sub, Matrix.mul_smul, mul_one, Matrix.trace_sub,
    Matrix.trace_smul, hpow, trace_four_eq_trace_sq_sq, smul_eq_mul]
  ring

theorem trace_mul_laplacian_eq_scaledDefects (a : BulkCoefficients) (ε : ElasticScale) (u : Point → S0)
    (x : Point) (hEq : ε.val ^ 2 • (laplacian u x : S0).val = bulkGradient a (u x)) :
    ((u x : Tensor) * (laplacian u x : S0).val).trace =
      scaledRadialCoefficient a ε (u x) * ((u x : Tensor) ^ 2).trace +
        a.a6' * ε.val ^ 2 * scaledCubicTrace a ε (u x) ^ 2 := by
  rw [laplacian_eq_scaledDefects a ε u x hEq]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
    ← pow_two, trace_mul_traceFreeSquare, trace_cube_eq_scaledCubicTrace a ε (u x)]
  ring

theorem trace_sq_mul_laplacian_eq_scaledDefects (a : BulkCoefficients) (ε : ElasticScale) (u : Point → S0)
    (x : Point) (hEq : ε.val ^ 2 • (laplacian u x : S0).val = bulkGradient a (u x)) :
    (((u x : Tensor) ^ 2) * (laplacian u x : S0).val).trace =
      ε.val ^ 2 * scaledRadialCoefficient a ε (u x) * scaledCubicTrace a ε (u x) +
        (a.a6' / 6) * (((u x : Tensor) ^ 2).trace) ^ 2 * scaledCubicTrace a ε (u x) := by
  rw [laplacian_eq_scaledDefects a ε u x hEq]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
    ← pow_succ _ 2, trace_sq_mul_traceFreeSquare, trace_cube_eq_scaledCubicTrace a ε (u x)]
  ring

theorem scaledNormDefect_equation_unexpanded (a : BulkCoefficients) (ε : ElasticScale)
    {u : Point → S0} {Ω : Set Point} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) {x : Point}
    (hx : x ∈ Ω) (hEq : ε.val ^ 2 • (laplacian u x : S0).val = bulkGradient a (u x)) :
    ε.val ^ 2 * laplacian (fun y => scaledNormDefect a ε (u y)) x =
      2 * scaledRadialCoefficient a ε (u x) * ((u x : Tensor) ^ 2).trace +
        2 * a.a6' * ε.val ^ 2 * scaledCubicTrace a ε (u x) ^ 2 + 2 * gradientNormSq (ClassicalGradient u x) := by
  rw [scale_sq_mul_laplacian_scaledNormDefect a ε hΩ hu hx, laplacian_trace_sq_field hΩ hu hx,
    trace_mul_laplacian_eq_scaledDefects a ε u x hEq]
  ring

theorem scaledCubicTrace_equation_unexpanded (a : BulkCoefficients) (ε : ElasticScale)
    {u : Point → S0} {Ω : Set Point} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) {x : Point}
    (hx : x ∈ Ω) (hEq : ε.val ^ 2 • (laplacian u x : S0).val = bulkGradient a (u x)) :
    ε.val ^ 2 * laplacian (fun y => scaledCubicTrace a ε (u y)) x =
      3 * ε.val ^ 2 * scaledRadialCoefficient a ε (u x) * scaledCubicTrace a ε (u x) +
        (a.a6' / 2) * (((u x : Tensor) ^ 2).trace) ^ 2 * scaledCubicTrace a ε (u x) +
        6 * gradientTraceMul (ClassicalGradient u) (ClassicalGradient u) (u x : Tensor) x := by
  rw [scale_sq_mul_laplacian_scaledCubicTrace a ε hΩ hu hx, laplacian_trace_cube_field hΩ hu hx,
    trace_sq_mul_laplacian_eq_scaledDefects a ε u x hEq]
  ring

/-- The exact equation for the squared-norm defect with its positive mass term. -/
theorem scaledNormDefect_equation (a : BulkCoefficients) (ε : ElasticScale)
    {u : Point → S0} {Ω : Set Point} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) {x : Point}
    (hx : x ∈ Ω) (hEq : ε.val ^ 2 • (laplacian u x : S0).val = bulkGradient a (u x)) :
    let h := scaledNormDefect a ε (u x)
    let t := scaledCubicTrace a ε (u x)
    ε.val ^ 2 * laplacian (fun y => scaledNormDefect a ε (u y)) x =
      bulkRadialMass a * h + 2 * gradientNormSq (ClassicalGradient u x) +
        ε.val ^ 2 * (2 * bulkRadialCoefficient a + 4 * a.a6 * vacuumRadius a ^ 2) * h ^ 2 +
        2 * a.a6 * ε.val ^ 4 * h ^ 3 + 2 * a.a6' * ε.val ^ 2 * t ^ 2 := by
  dsimp only
  rw [scaledNormDefect_equation_unexpanded a ε hΩ hu hx hEq, trace_sq_eq_scaledNormDefect a ε (u x),
    scaledRadialCoefficient, bulkRadialMass]
  ring

/-- The exact equation for the cubic trace defect with its positive mass term. -/
theorem scaledCubicTrace_equation (a : BulkCoefficients) (ε : ElasticScale)
    {u : Point → S0} {Ω : Set Point} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) {x : Point}
    (hx : x ∈ Ω) (hEq : ε.val ^ 2 • (laplacian u x : S0).val = bulkGradient a (u x)) :
    let h := scaledNormDefect a ε (u x)
    let t := scaledCubicTrace a ε (u x)
    ε.val ^ 2 * laplacian (fun y => scaledCubicTrace a ε (u y)) x =
      bulkBiaxialMass a * t + 6 * gradientTraceMul (ClassicalGradient u) (ClassicalGradient u) (u x : Tensor) x +
        ε.val ^ 2 * (3 * bulkRadialCoefficient a + 2 * a.a6' * vacuumRadius a ^ 2) * h * t +
        ε.val ^ 4 * (3 * a.a6 + a.a6' / 2) * h ^ 2 * t := by
  dsimp only
  rw [scaledCubicTrace_equation_unexpanded a ε hΩ hu hx hEq, trace_sq_eq_scaledNormDefect a ε (u x),
    scaledRadialCoefficient, bulkBiaxialMass]
  ring

end Thesis

end

end

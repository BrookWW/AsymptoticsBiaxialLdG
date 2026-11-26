module

public import Thesis.Variational.ProjectedLaplacian
import Thesis.Foundation.LinearizedBulk
import Thesis.MeasureGeometry.StressAlgebra
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The normal defect from the nearest vacuum projection. -/

public section

open Set Filter Topology
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius RealInnerProductSpace

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem frobeniusS0_eq_trace_mul (A B : S0) :
    frobeniusS0 A B = ((A : Tensor) * (B : Tensor)).trace := by
  rw [frobeniusS0, frobenius, A.transpose_eq]

private theorem frobeniusS0_traceFreeSquare_eq_trace (A B : S0) :
    frobeniusS0 (traceFreeSquare A) B = (((A : Tensor) ^ 2) * (B : Tensor)).trace := by
  rw [frobeniusS0_eq_trace_mul, traceFreeSquare_coe]
  simp only [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    B.trace_eq_zero, smul_eq_mul, mul_zero, sub_zero]

private theorem abs_trace_mul_sq_le (A B : S0) :
    |((A : Tensor) * ((B : Tensor) ^ 2)).trace| ≤ ‖A‖ * ‖B‖ ^ 2 := by
  rw [← show frobenius (A : Tensor) ((B : Tensor) ^ 2) =
    ((A : Tensor) * ((B : Tensor) ^ 2)).trace by rw [frobenius, A.transpose_eq]]
  exact (abs_frobenius_le_norm_mul_norm _ _).trans (mul_le_mul_of_nonneg_left
    (by rw [pow_two, pow_two]; exact Matrix.frobenius_norm_mul _ _) (norm_nonneg _))

/-- The force pairing with the defect from the spectral nearest vacuum
tensor controls its squared Frobenius norm on a material tube. -/
theorem exists_bulkForce_nearest_defect_pairing_lower_bound (a : BulkCoefficients) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ A ∈ vacuumTube a δ, c * ‖A - (spectralVacuumPoint a A).val‖ ^ 2 ≤
        frobeniusS0 (bulkForce a A) (A - (spectralVacuumPoint a A).val) := by
  obtain ⟨K, δ₀, hK, hδ₀, hError⟩ := exists_vacuumInvariantErrorBound a
  let R := Real.sqrt 2 * vacuumRadius a + 1
  let μ := preferredTraceSq a
  let Γ := a.a4 + a.a6 * (R ^ 2 + μ)
  let C := Γ / 2 + a.a6' * (R + 1 / 3)
  let k := min (a.a4 / 2) (a.a6' / 3)
  have hR : 0 < R := by dsimp only [R]; have := vacuumRadius_pos a; positivity
  have hΓ : 0 < Γ := add_pos_of_pos_of_nonneg a.a4_pos
    (mul_nonneg a.a6_pos.le (add_nonneg (sq_nonneg _) (preferredTraceSq_pos a).le))
  have hC : 0 < C := add_pos_of_pos_of_nonneg (half_pos hΓ)
    (mul_nonneg a.a6'_pos.le (by positivity))
  have hk : 0 < k := lt_min (half_pos a.a4_pos) (div_pos a.a6'_pos (by norm_num))
  let δ := min δ₀ (min 1 (k / (2 * C * K)))
  let c := (k / 2) / K ^ 2
  have hδ : 0 < δ := lt_min hδ₀ (lt_min zero_lt_one (div_pos hk (by positivity)))
  have hc : 0 < c := div_pos (half_pos hk) (sq_pos_of_pos hK)
  refine ⟨δ, c, hδ, hc, ?_⟩
  intro A hA
  let P := (spectralVacuumPoint a A).val
  let B := A - P
  let d := ‖B‖
  let x := (vacuumInvariants A).1 - μ
  let y := (vacuumInvariants A).2
  let E := vacuumInvariantError a A
  let γ := a.a4 + a.a6 * ((vacuumInvariants A).1 + μ)
  have hP : P ∈ vacuum a := (spectralVacuumPoint a A).property
  have hBP : A + (-1 : ℝ) • B = P := by
    have hNeg : (-1 : ℝ) • B = -B := neg_one_smul ℝ B
    rw [hNeg]
    change A + -(A - P) = P
    abel
  have hDist : d = Metric.infDist A (vacuum a) :=
    (dist_eq_norm A P).symm.trans (spectralVacuumPoint_dist_eq_infDist a A)
  have hd : d < δ := hDist.trans_lt hA
  have hd₀ : 0 ≤ d := norm_nonneg _
  have hd₁ : d ≤ 1 := hd.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRange : ‖A‖ ≤ R := by
    have hTri := norm_add_le B P
    rw [show B + P = A from sub_add_cancel _ _, vacuum_norm hP] at hTri
    refine hTri.trans ?_
    dsimp only [R]
    linarith only [hd₁]
  have hE : E = max |x| |y| := by
    change ‖((vacuumInvariants A).1, (vacuumInvariants A).2) - (2 * vacuumRadius a ^ 2, 0)‖ = _
    rw [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
      two_mul_vacuumRadius_sq]
  have hxE : |x| ≤ E := hE.symm ▸ le_max_left _ _
  have hyE : |y| ≤ E := hE.symm ▸ le_max_right _ _
  have hE₀ : 0 ≤ E := (abs_nonneg _).trans hxE
  have hEf : E ^ 2 ≤ x ^ 2 + y ^ 2 := by
    rw [hE]
    rcases le_total |x| |y| with h | h
    · rw [max_eq_right h, sq_abs]
      exact le_add_of_nonneg_left (sq_nonneg _)
    · rw [max_eq_left h, sq_abs]
      exact le_add_of_nonneg_right (sq_nonneg _)
  have hTube : A ∈ vacuumTube a δ₀ := by
    change Metric.infDist A (vacuum a) < δ₀
    rw [← hDist]
    exact hd.trans_le (min_le_left _ _)
  have hdE : d ≤ K * E := hDist.trans_le (hError A hTube)
  have hγ₁ : a.a4 ≤ γ := le_add_of_nonneg_right
    (mul_nonneg a.a6_pos.le (add_nonneg A.trace_sq_nonneg (preferredTraceSq_pos a).le))
  have hγ₂ : γ ≤ Γ := by
    change a.a4 + a.a6 * (((A : Tensor) ^ 2).trace + μ) ≤ a.a4 + a.a6 * (R ^ 2 + μ)
    rw [← norm_sq_eq_trace_sq]
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hRange 2) le_rfl) a.a6_pos.le)
  have hF : bulkForce a A = (γ * x) • A + (a.a6' * y) • traceFreeSquare A := by
    rw [bulkForce_eq_smul_components]
    congr 2
    change -a.a2 + a.a4 * (vacuumInvariants A).1 + a.a6 * (vacuumInvariants A).1 ^ 2 =
      (a.a4 + a.a6 * ((vacuumInvariants A).1 + μ)) * ((vacuumInvariants A).1 - μ)
    rw [show a.a2 = a.a6 * μ ^ 2 + a.a4 * μ from (preferredTraceSq_equation a).symm]
    ring
  have h1 : frobeniusS0 A B = (x + d ^ 2) / 2 := by
    have h := trace_sq_add_smul A B (-1)
    rw [hBP, (vacuum_traces hP).1, two_mul_vacuumRadius_sq, ← norm_sq_eq_trace_sq B,
      ← frobeniusS0_eq_trace_mul] at h
    change μ = (vacuumInvariants A).1 + 2 * (-1) * frobeniusS0 A B + (-1) ^ 2 * d ^ 2 at h
    dsimp only [x]
    linarith only [h]
  let T := ((A : Tensor) * ((B : Tensor) ^ 2)).trace - ((B : Tensor) ^ 3).trace / 3
  have h2 : frobeniusS0 (traceFreeSquare A) B = y / 3 + T := by
    have h := trace_cube_add_smul A B (-1)
    rw [hBP, (vacuum_traces hP).2, ← frobeniusS0_traceFreeSquare_eq_trace] at h
    change 0 = y + 3 * (-1) * frobeniusS0 (traceFreeSquare A) B +
      3 * (-1) ^ 2 * ((A : Tensor) * ((B : Tensor) ^ 2)).trace + (-1) ^ 3 * ((B : Tensor) ^ 3).trace at h
    dsimp only [T]
    linarith only [h]
  have hT : |T| ≤ (R + 1 / 3) * d ^ 2 := by
    have hA2 := (abs_trace_mul_sq_le A B).trans (mul_le_mul_of_nonneg_right hRange (sq_nonneg d))
    have hB2 : |((B : Tensor) ^ 3).trace| ≤ d ^ 2 := by
      rw [pow_succ', show d ^ 2 = (1 : ℝ) * d ^ 2 from (one_mul _).symm]
      exact (abs_trace_mul_sq_le B B).trans (mul_le_mul_of_nonneg_right hd₁ (sq_nonneg d))
    have h := (abs_sub _ _).trans (add_le_add hA2
      (show |((B : Tensor) ^ 3).trace / 3| ≤ d ^ 2 / 3 by
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
        exact div_le_div_of_nonneg_right hB2 (by norm_num)))
    exact h.trans_eq (by ring)
  have hX : -((Γ / 2) * E * d ^ 2) ≤ (γ / 2) * x * d ^ 2 := by
    have hL := (neg_le_neg hxE).trans (neg_abs_le x)
    have hp : 0 ≤ γ / 2 := (half_pos (a.a4_pos.trans_le hγ₁)).le
    have ha := mul_le_mul_of_nonneg_left hL hp
    have hb := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hγ₂ (by norm_num : (0 : ℝ) ≤ 2)) hE₀
    have hAB : -(Γ / 2 * E) ≤ (γ / 2) * x := by linarith only [ha, hb]
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right hAB (sq_nonneg d)
  have hY : -(a.a6' * (R + 1 / 3) * E * d ^ 2) ≤ a.a6' * y * T := by
    have h := mul_le_mul hyE hT (abs_nonneg T) hE₀
    rw [← abs_mul] at h
    have h' := (neg_le_neg h).trans (neg_abs_le (y * T))
    have h'' := mul_le_mul_of_nonneg_left h' a.a6'_pos.le
    linarith only [h'']
  have hCore : k * E ^ 2 ≤ (γ / 2) * x ^ 2 + (a.a6' / 3) * y ^ 2 := by
    calc
      _ ≤ k * (x ^ 2 + y ^ 2) := mul_le_mul_of_nonneg_left hEf hk.le
      _ = k * x ^ 2 + k * y ^ 2 := mul_add _ _ _
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (div_le_div_of_nonneg_right hγ₁ (by norm_num)))
          (sq_nonneg x))
        (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg y))
  have hSmall : C * E * d ^ 2 ≤ k / 2 * E ^ 2 := by
    have hCoeff : C * δ * K ≤ k / 2 := by
      have hδ' : δ ≤ k / (2 * C * K) := (min_le_right _ _).trans (min_le_right _ _)
      have h := (le_div_iff₀ (by positivity : 0 < 2 * C * K)).mp hδ'
      linarith only [h]
    have hD : d ^ 2 ≤ δ * (K * E) := by
      rw [pow_two]
      exact mul_le_mul hd.le hdE hd₀ hδ.le
    calc
      _ ≤ C * E * (δ * (K * E)) := mul_le_mul_of_nonneg_left hD (mul_nonneg hC.le hE₀)
      _ = (C * δ * K) * E ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCoeff (sq_nonneg _)
  have hcD : c * d ^ 2 ≤ k / 2 * E ^ 2 := by
    calc
      _ ≤ c * (K * E)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd₀ hdE 2) hc.le
      _ = _ := by dsimp only [c]; field_simp [hK.ne']
  change c * d ^ 2 ≤ frobeniusS0 (bulkForce a A) B
  rw [hF, ← frobeniusCoordinateEquiv_inner, map_add, map_smul, map_smul, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, frobeniusCoordinateEquiv_inner, frobeniusCoordinateEquiv_inner,
    h1, h2]
  dsimp only [C] at hSmall
  nlinarith only [hCore, hSmall, hX, hY, hcD]

theorem exists_bulkForce_nearest_defect_pairing_nonneg (a : BulkCoefficients) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ A ∈ vacuumTube a δ, 0 ≤ frobeniusS0 (bulkForce a A) (A - (spectralVacuumPoint a A).val) := by
  obtain ⟨δ, c, hδ, hc, hPair⟩ := exists_bulkForce_nearest_defect_pairing_lower_bound a
  exact ⟨δ, hδ, fun A hA => (mul_nonneg hc.le (sq_nonneg _)).trans (hPair A hA)⟩

/-- A smooth, convex approximation of the Frobenius norm that vanishes
exactly at zero for positive smoothing parameter. -/
@[expose] def regularizedFrobeniusNorm (η : ℝ) (A : S0) : ℝ :=
  Real.sqrt (‖A‖ ^ 2 + η ^ 2) - η

theorem regularizedFrobeniusNorm_zero {η : ℝ} (hη : 0 ≤ η) :
    regularizedFrobeniusNorm η 0 = 0 := by
  simp only [regularizedFrobeniusNorm, norm_zero, zero_pow two_ne_zero, zero_add, Real.sqrt_sq hη, sub_self]

theorem regularizedFrobeniusNorm_nonneg_le {η : ℝ} (hη : 0 ≤ η) (A : S0) :
    0 ≤ regularizedFrobeniusNorm η A ∧
      regularizedFrobeniusNorm η A ≤ ‖A‖ ∧ ‖A‖ ≤ regularizedFrobeniusNorm η A + η := by
  have hS : 0 ≤ ‖A‖ ^ 2 + η ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hLow : η ≤ Real.sqrt (‖A‖ ^ 2 + η ^ 2) := by
    apply (sq_le_sq₀ hη (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hS]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hHigh : Real.sqrt (‖A‖ ^ 2 + η ^ 2) ≤ ‖A‖ + η := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (norm_nonneg _) hη)).mp
    rw [Real.sq_sqrt hS]
    nlinarith only [mul_nonneg (norm_nonneg A) hη]
  have hA : ‖A‖ ≤ Real.sqrt (‖A‖ ^ 2 + η ^ 2) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hS]
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact ⟨sub_nonneg.mpr hLow, sub_le_iff_le_add.mpr hHigh, by
    simpa only [regularizedFrobeniusNorm, sub_add_cancel] using hA⟩

theorem contDiff_regularizedFrobeniusNorm {η : ℝ} (hη : 0 < η) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (regularizedFrobeniusNorm η) := by
  have h : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fun A : S0 => ‖A‖ ^ 2) := by
    simpa only [Function.comp_def, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.norm_map] using
      (contDiff_norm_sq ℝ (E := EuclideanSpace ℝ (Fin 5))).comp
        frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
  exact ((h.add contDiff_const).sqrt fun A => (add_pos_of_nonneg_of_pos (sq_nonneg ‖A‖)
    (sq_pos_of_pos hη)).ne').sub contDiff_const

theorem fderiv_regularizedFrobeniusNorm_apply {η : ℝ} (hη : 0 < η) (A B : S0) :
    (fderiv ℝ (regularizedFrobeniusNorm η) A) B =
      frobeniusS0 A B / Real.sqrt (‖A‖ ^ 2 + η ^ 2) := by
  let L := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hD : HasFDerivAt (fun A : S0 => frobeniusCoordinateEquiv A) L A := L.hasFDerivAt
  have hPos : 0 < ‖A‖ ^ 2 + η ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hη)
  have hP : ‖frobeniusCoordinateEquiv A‖ ^ 2 + η ^ 2 ≠ 0 := by
    simpa only [LinearIsometryEquiv.norm_map] using hPos.ne'
  have h := ((hD.norm_sq.add_const (η ^ 2)).sqrt hP).sub_const η
  have hF : HasFDerivAt (regularizedFrobeniusNorm η)
      ((1 / (2 * Real.sqrt (‖A‖ ^ 2 + η ^ 2))) •
        ((2 : ℕ) • (innerSL ℝ (frobeniusCoordinateEquiv A)).comp L)) A := by
    simpa only [regularizedFrobeniusNorm, LinearIsometryEquiv.norm_map] using! h
  refine (DFunLike.congr_fun hF.fderiv B).trans ?_
  simp only [smul_apply, two_nsmul, add_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  change (1 / (2 * Real.sqrt (‖A‖ ^ 2 + η ^ 2))) *
    (inner ℝ (frobeniusCoordinateEquiv A) (frobeniusCoordinateEquiv B) +
      inner ℝ (frobeniusCoordinateEquiv A) (frobeniusCoordinateEquiv B)) = _
  rw [frobeniusCoordinateEquiv_inner]
  field_simp [(Real.sqrt_pos.mpr hPos).ne']
  ring

local instance regularizedFrobeniusDerivativeNormedGroup : NormedAddCommGroup (S0 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ) (E := S0) (F := ℝ)

local instance regularizedFrobeniusDerivativeNormedSpace : NormedSpace ℝ (S0 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ) (E := S0) (F := ℝ)

private theorem fderiv_fderiv_regularizedFrobeniusNorm_apply {η : ℝ} (hη : 0 < η) (A B : S0) :
    ((fderiv ℝ (fderiv ℝ (regularizedFrobeniusNorm η)) A) B) B =
      (‖B‖ ^ 2 * (‖A‖ ^ 2 + η ^ 2) - (frobeniusS0 A B) ^ 2) /
        (Real.sqrt (‖A‖ ^ 2 + η ^ 2)) ^ 3 := by
  let f := regularizedFrobeniusNorm η
  let J := fderiv ℝ f
  let γ (t : ℝ) := A + t • B
  let R := Real.sqrt (‖A‖ ^ 2 + η ^ 2)
  let p := frobeniusS0 A B
  have hR : 0 < R := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hη))
  have hSq : R ^ 2 = ‖A‖ ^ 2 + η ^ 2 := Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hγ0 : γ 0 = A := by simp only [γ, zero_smul, add_zero]
  have hγ : HasDerivAt γ B 0 := by
    simpa only [γ, id_eq, one_smul] using! ((hasDerivAt_id (0 : ℝ)).smul_const B).const_add A
  have hJ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) J := (contDiff_regularizedFrobeniusNorm hη).fderiv_right (by simp)
  have hJ' : HasFDerivAt J (fderiv ℝ J A) (γ 0) := hγ0.symm ▸ (hJ.differentiable (by simp) A).hasFDerivAt
  let E := ContinuousLinearMap.apply ℝ ℝ B
  have hDJ : HasDerivAt (fun t => (J (γ t)) B) (((fderiv ℝ J A) B) B) 0 := by
    have hEval : HasFDerivAt (fun M : S0 →L[ℝ] ℝ => M B) E (J (γ 0)) := E.hasFDerivAt
    simpa only [E, Function.comp_def, ContinuousLinearMap.apply_apply] using!
      hEval.comp_hasDerivAt 0 (hJ'.comp_hasDerivAt 0 hγ)
  let L := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hNum : HasDerivAt (fun t => frobeniusS0 (γ t) B) (‖B‖ ^ 2) 0 := by
    have hL : HasDerivAt (fun t => frobeniusCoordinateEquiv (γ t)) (frobeniusCoordinateEquiv B) 0 :=
      L.hasFDerivAt.comp_hasDerivAt 0 hγ
    simpa only [frobeniusCoordinateEquiv_inner, inner_zero_right, zero_add, ← norm_sq_eq_frobeniusS0] using
      HasDerivAt.inner ℝ hL (hasDerivAt_const 0 (frobeniusCoordinateEquiv B))
  have hF : HasFDerivAt f (J A) (γ 0) := by
    rw [hγ0]
    exact ((contDiff_regularizedFrobeniusNorm hη).differentiable (by simp) A).hasFDerivAt
  have hDen : HasDerivAt (fun t => Real.sqrt (‖γ t‖ ^ 2 + η ^ 2)) (p / R) 0 := by
    have h := (hF.comp_hasDerivAt 0 hγ).add_const η
    have hEq : (fun t => Real.sqrt (‖γ t‖ ^ 2 + η ^ 2)) =ᶠ[𝓝 (0 : ℝ)] fun t => (f ∘ γ) t + η :=
      Eventually.of_forall fun t => (sub_add_cancel _ _).symm
    have h' := h.congr_of_eventuallyEq hEq
    have hVal : J A B = p / R := fderiv_regularizedFrobeniusNorm_apply hη A B
    exact hVal ▸ h'
  have hQuot := hNum.div hDen (by simpa only [hγ0] using hR.ne')
  have hEq : (fun t => J (γ t) B) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => frobeniusS0 (γ t) B / Real.sqrt (‖γ t‖ ^ 2 + η ^ 2)) :=
    Eventually.of_forall fun t => fderiv_regularizedFrobeniusNorm_apply hη (γ t) B
  have hV := hDJ.unique (hQuot.congr_of_eventuallyEq hEq)
  rw [hV, hγ0]
  change (‖B‖ ^ 2 * R - p * (p / R)) / R ^ 2 = (‖B‖ ^ 2 * (‖A‖ ^ 2 + η ^ 2) - p ^ 2) / R ^ 3
  rw [← hSq]
  field_simp [hR.ne']

theorem fderiv_fderiv_regularizedFrobeniusNorm_nonneg {η : ℝ} (hη : 0 < η) (A B : S0) :
    0 ≤ ((fderiv ℝ (fderiv ℝ (regularizedFrobeniusNorm η)) A) B) B := by
  rw [fderiv_fderiv_regularizedFrobeniusNorm_apply hη]
  apply div_nonneg _ (pow_nonneg (Real.sqrt_nonneg _) _)
  have hAbs := abs_real_inner_le_norm (frobeniusCoordinateEquiv A) (frobeniusCoordinateEquiv B)
  rw [frobeniusCoordinateEquiv_inner, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at hAbs
  have hSq := pow_le_pow_left₀ (abs_nonneg _) hAbs 2
  rw [sq_abs, mul_pow] at hSq
  nlinarith only [hSq, mul_nonneg (sq_nonneg η) (sq_nonneg ‖B‖)]

theorem laplacian_sub_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set Point} (hU : IsOpen U)
    {u v : Point → E} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    {x : Point} (hx : x ∈ U) :
    laplacian (fun y => u y - v y) x = laplacian u x - laplacian v x := by
  let f (y : Point) := (u y, v y)
  have hF : ContDiffOn ℝ 2 f U := hu.prodMk hv
  have h₁ : (laplacian f x).1 = laplacian u x :=
    (laplacian_compCLM hU hF hx (ContinuousLinearMap.fst ℝ E E)).symm
  have h₂ : (laplacian f x).2 = laplacian v x :=
    (laplacian_compCLM hU hF hx (ContinuousLinearMap.snd ℝ E E)).symm
  have h := laplacian_compCLM hU hF hx (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E)
  change laplacian (fun y => u y - v y) x = (laplacian f x).1 - (laplacian f x).2 at h
  rwa [h₁, h₂] at h

/-- The smooth regularized normal defect satisfies a scaled positive-mass
inequality uniformly in the regularization and elastic scale. -/
theorem exists_regularized_vacuum_defect_screened_laplacian_bound (a : BulkCoefficients) :
    ∃ (p : VacuumTubularProjection a) (δ c C : ℝ), 0 < δ ∧ 0 < c ∧ 0 < C ∧ δ ≤ p.radius ∧
      ∀ (ε η : ℝ), 0 < ε → 0 < η → ∀ (U : Set Point), IsOpen U →
        ∀ Q : Point → S0, ContDiffOn ℝ 2 Q U →
          ∀ x ∈ U, Q x ∈ vacuumTube a δ →
            ε ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x) →
            let Z (y : Point) := Q y - p.extend (Q y);
            -laplacian (regularizedFrobeniusNorm η ∘ Z) x +
              (c * ε⁻¹ ^ 2) * regularizedFrobeniusNorm η (Z x) ≤
                C * gradientNormSq (ClassicalGradient Q x) := by
  obtain ⟨p, δP, C, hδP, hC, hPR, hProj⟩ := exists_projected_laplacian_quadratic_bound a
  obtain ⟨δB, c, hδB, hc, hBulk⟩ := exists_bulkForce_nearest_defect_pairing_lower_bound a
  let δ := min δP δB
  refine ⟨p, δ, c, C, lt_min hδP hδB, hc, hC, (min_le_left _ _).trans hPR, ?_⟩
  intro ε η hε hη U hU Q hQ x hx hTube hEuler
  let Z (y : Point) := Q y - p.extend (Q y)
  let F := p.extend ∘ Q
  let w := regularizedFrobeniusNorm η
  let G := gradientNormSq (ClassicalGradient Q x)
  let R := Real.sqrt (‖Z x‖ ^ 2 + η ^ 2)
  have hR : 0 < R := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hη))
  have hRN : ‖Z x‖ ≤ R := by
    simpa only [R, regularizedFrobeniusNorm, sub_add_cancel] using
      (regularizedFrobeniusNorm_nonneg_le hη.le (Z x)).2.2
  have hG : 0 ≤ G := by
    change 0 ≤ gradientNormSq (ClassicalGradient Q x)
    rw [gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hδ : Metric.infDist (Q x) (vacuum a) < δ := hTube
  have hTP : Q x ∈ vacuumTube a δP := hδ.trans_le (min_le_left _ _)
  have hTB : Q x ∈ vacuumTube a δB := hδ.trans_le (min_le_right _ _)
  have hTE : Q x ∈ vacuumTube a p.radius := hδ.trans_le ((min_le_left _ _).trans hPR)
  have hPF : p.extend (Q x) = (spectralVacuumPoint a (Q x)).val := by
    rw [p.extend_eq ⟨Q x, hTE⟩, ← spectralVacuumPoint_eq_tubeProjection p ⟨Q x, hTE⟩]
  have hForce : c * ‖Z x‖ ^ 2 ≤ frobeniusS0 (bulkForce a (Q x)) (Z x) := by
    change c * ‖Q x - p.extend (Q x)‖ ^ 2 ≤ frobeniusS0 (bulkForce a (Q x)) (Q x - p.extend (Q x))
    rw [hPF]
    exact hBulk (Q x) hTB
  have hProj' : ‖laplacian F x‖ ≤ C * G := (hProj ε hε U hU Q hQ x hx hTP hEuler).2
  have hF : ContDiffOn ℝ 2 F U :=
    (p.contDiff_extend.of_le (WithTop.coe_le_coe.mpr le_top)).comp_contDiffOn hQ
  have hZ : ContDiffOn ℝ 2 Z U := hQ.sub hF
  have hΔZ : laplacian Z x = laplacian Q x - laplacian F x := laplacian_sub_of_contDiffOn hU hQ hF hx
  have hΔQ : laplacian Q x = ε⁻¹ ^ 2 • bulkForce a (Q x) := by
    apply Subtype.ext
    change (↑(laplacian Q x) : Tensor) = ε⁻¹ ^ 2 • bulkGradient a (Q x)
    have hScale : ε⁻¹ ^ 2 * ε ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hε.ne', one_pow]
    calc
      _ = (1 : ℝ) • (↑(laplacian Q x) : Tensor) := (one_smul ℝ _).symm
      _ = (ε⁻¹ ^ 2 * ε ^ 2) • (↑(laplacian Q x) : Tensor) := congrArg (· • (↑(laplacian Q x) : Tensor)) hScale.symm
      _ = ε⁻¹ ^ 2 • (ε ^ 2 • (↑(laplacian Q x) : Tensor)) := mul_smul _ _ _
      _ = _ := congrArg (ε⁻¹ ^ 2 • ·) hEuler
  have hL : (c * ε⁻¹ ^ 2) * ‖Z x‖ ^ 2 ≤ frobeniusS0 (laplacian Q x) (Z x) := by
    rw [hΔQ, ← frobeniusCoordinateEquiv_inner, map_smul, real_inner_smul_left, frobeniusCoordinateEquiv_inner]
    calc
      _ = ε⁻¹ ^ 2 * (c * ‖Z x‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hForce (sq_nonneg (ε⁻¹))
  have hΔF : frobeniusS0 (laplacian F x) (Z x) ≤ C * G * R := by
    have hAbs := abs_real_inner_le_norm (frobeniusCoordinateEquiv (laplacian F x)) (frobeniusCoordinateEquiv (Z x))
    rw [frobeniusCoordinateEquiv_inner, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at hAbs
    exact (le_abs_self _).trans (hAbs.trans (mul_le_mul hProj' hRN (norm_nonneg _) (mul_nonneg hC.le hG)))
  have hRη : η ≤ R := by
    change η ≤ Real.sqrt (‖Z x‖ ^ 2 + η ^ 2)
    exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg _))
  have hSq : R ^ 2 = ‖Z x‖ ^ 2 + η ^ 2 := Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hWR : w (Z x) * R ≤ ‖Z x‖ ^ 2 := by
    change (R - η) * R ≤ ‖Z x‖ ^ 2
    nlinarith only [hSq, mul_le_mul_of_nonneg_left hRη hη.le]
  have hMass : (c * ε⁻¹ ^ 2) * (w (Z x) * R) ≤ (c * ε⁻¹ ^ 2) * ‖Z x‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hWR (mul_nonneg hc.le (sq_nonneg _))
  have hBound : ((c * ε⁻¹ ^ 2) * w (Z x) - C * G) * R ≤ frobeniusS0 (laplacian Z x) (Z x) := by
    rw [hΔZ, ← frobeniusCoordinateEquiv_inner, map_sub, inner_sub_left,
      frobeniusCoordinateEquiv_inner, frobeniusCoordinateEquiv_inner]
    nlinarith only [hΔF, hL, hMass]
  have hDf := fderiv_regularizedFrobeniusNorm_apply hη (Z x) (laplacian Z x)
  have hChain := laplacian_comp_smooth_map (contDiff_regularizedFrobeniusNorm hη) hU hZ hx
  have hD' : (c * ε⁻¹ ^ 2) * w (Z x) - C * G ≤ fderiv ℝ w (Z x) (laplacian Z x) := by
    change (c * ε⁻¹ ^ 2) * w (Z x) - C * G ≤
      fderiv ℝ (regularizedFrobeniusNorm η) (Z x) (laplacian Z x)
    have hSymm : frobeniusS0 (Z x) (laplacian Z x) = frobeniusS0 (laplacian Z x) (Z x) := by
      rw [← frobeniusCoordinateEquiv_inner, ← frobeniusCoordinateEquiv_inner, real_inner_comm]
    rw [hDf, hSymm]
    exact (le_div_iff₀ hR).mpr hBound
  have hH : 0 ≤ ∑ j : Fin 3,
      ((fderiv ℝ (fderiv ℝ w) (Z x)) (coordDeriv j Z x)) (coordDeriv j Z x) :=
    Finset.sum_nonneg fun j _ => fderiv_fderiv_regularizedFrobeniusNorm_nonneg hη (Z x) (coordDeriv j Z x)
  change laplacian (w ∘ Z) x = (fderiv ℝ w (Z x)) (laplacian Z x) +
    ∑ j, ((fderiv ℝ (fderiv ℝ w) (Z x)) (coordDeriv j Z x)) (coordDeriv j Z x) at hChain
  change -laplacian (w ∘ Z) x + (c * ε⁻¹ ^ 2) * w (Z x) ≤ C * G
  linarith only [hChain, hD', hH]

theorem exists_regularized_vacuum_defect_laplacian_bound (a : BulkCoefficients) :
    ∃ (p : VacuumTubularProjection a) (δ C : ℝ), 0 < δ ∧ 0 < C ∧ δ ≤ p.radius ∧
      ∀ (ε η : ℝ), 0 < ε → 0 < η → ∀ (U : Set Point), IsOpen U →
        ∀ Q : Point → S0, ContDiffOn ℝ 2 Q U →
          ∀ x ∈ U, Q x ∈ vacuumTube a δ →
            ε ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x) →
            let Z (y : Point) := Q y - p.extend (Q y);
            -laplacian (regularizedFrobeniusNorm η ∘ Z) x ≤ C * gradientNormSq (ClassicalGradient Q x) := by
  obtain ⟨p, δ, c, C, hδ, hc, hC, hp, hScreened⟩ :=
    exists_regularized_vacuum_defect_screened_laplacian_bound a
  refine ⟨p, δ, C, hδ, hC, hp, ?_⟩
  intro ε η hε hη U hU Q hQ x hx hTube hEq
  have h := hScreened ε η hε hη U hU Q hQ x hx hTube hEq
  have hMass := mul_nonneg (mul_nonneg hc.le (sq_nonneg (ε⁻¹)))
    (regularizedFrobeniusNorm_nonneg_le hη.le (Q x - p.extend (Q x))).1
  linarith only [h, hMass]

end Thesis

end

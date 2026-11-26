module

public import Thesis.Foundation.VacuumTarget

/-! The orthonormal director pairs over the biaxial vacuum. -/

@[expose] public section

noncomputable section

open Metric Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace Thesis

/-- The ordered orthonormal pair defining a biaxial vacuum tensor. -/
abbrev VacuumFrame := {f : Point × Point // ‖f.1‖ = 1 ∧ ‖f.2‖ = 1 ∧ inner ℝ f.1 f.2 = 0}

/-- The dyadic tensor of a director, which is its rank-one projector when the director is unit. -/
def directorProjector (n : Point) : Tensor :=
  Matrix.vecMulVec (fun i => n i) (fun i => n i)

theorem directorProjector_trace (n : Point) : (directorProjector n).trace = ‖n‖ ^ 2 := by
  rw [directorProjector, Matrix.trace_vecMulVec, EuclideanSpace.real_norm_sq_eq, dotProduct]
  exact Finset.sum_congr rfl fun i _ => (pow_two (n i)).symm

/-- The original map from ordered frames onto the vacuum. -/
def vacuumFrameProjection (a : BulkCoefficients) (f : VacuumFrame) : vacuum a := by
  let n := f.val.1
  let m := f.val.2
  have hn : ‖n‖ = 1 := f.property.1
  have hm : ‖m‖ = 1 := f.property.2.1
  have hs : (biaxialTensor a n m)ᵀ = biaxialTensor a n m := by
    simp only [biaxialTensor, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_vecMulVec]
  have ht : (biaxialTensor a n m).trace = 0 := by
    change (vacuumRadius a • (directorProjector n - directorProjector m)).trace = 0
    rw [Matrix.trace_smul, Matrix.trace_sub, directorProjector_trace, directorProjector_trace,
      hn, hm, sub_self, smul_zero]
  exact ⟨⟨biaxialTensor a n m, hs, ht⟩, n, m, hn, hm, f.property.2.2, rfl⟩

theorem vacuumFrameProjection_tensor (a : BulkCoefficients) (f : VacuumFrame) :
    ((vacuumFrameProjection a f).val : Tensor) = biaxialTensor a f.val.1 f.val.2 := rfl

theorem vacuumFrameProjection_surjective (a : BulkCoefficients) :
    Function.Surjective (vacuumFrameProjection a) := by
  intro A
  obtain ⟨n, m, hn, hm, hnm, h⟩ := A.property
  refine ⟨⟨(n, m), hn, hm, hnm⟩, Subtype.ext (Subtype.ext ?_)⟩
  exact h.symm

theorem vacuumFrame_compact :
    IsCompact {f : Point × Point | ‖f.1‖ = 1 ∧ ‖f.2‖ = 1 ∧ inner ℝ f.1 f.2 = 0} := by
  have hSet : {f : Point × Point | ‖f.1‖ = 1 ∧ ‖f.2‖ = 1 ∧ inner ℝ f.1 f.2 = 0} =
      ((sphere (0 : Point) 1) ×ˢ (sphere (0 : Point) 1)) ∩ {f | inner ℝ f.1 f.2 = 0} := by
    ext f
    simp only [mem_setOf_eq, mem_inter_iff, mem_prod, mem_sphere, dist_zero_right, and_assoc]
  rw [hSet]
  exact ((isCompact_sphere _ _).prod (isCompact_sphere _ _)).inter_right
    (isClosed_eq (continuous_fst.inner continuous_snd) continuous_const)

instance vacuumFrameCompactSpace : CompactSpace VacuumFrame :=
  isCompact_iff_compactSpace.mp vacuumFrame_compact

theorem continuous_vacuumFrameProjection (a : BulkCoefficients) :
    Continuous (vacuumFrameProjection a) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun f : VacuumFrame => biaxialTensor a f.val.1 f.val.2)
  apply continuous_matrix
  intro i j
  let coord (i : Fin 3) : Point →L[ℝ] ℝ := EuclideanSpace.proj i
  have hn (i : Fin 3) : Continuous (fun f : VacuumFrame => f.val.1 i) :=
    (coord i).continuous.comp (continuous_fst.comp continuous_subtype_val)
  have hm (i : Fin 3) : Continuous (fun f : VacuumFrame => f.val.2 i) :=
    (coord i).continuous.comp (continuous_snd.comp continuous_subtype_val)
  simp only [biaxialTensor, Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  exact continuous_const.mul (((hn i).mul (hn j)).sub ((hm i).mul (hm j)))

theorem directorProj_pair (a : BulkCoefficients) (f : VacuumFrame) :
    let r := vacuumRadius a
    let A := ((vacuumFrameProjection a f).val : Tensor)
    A ^ 2 + r • A = (2 * r ^ 2) • directorProjector f.val.1 ∧
      A ^ 2 - r • A = (2 * r ^ 2) • directorProjector f.val.2 := by
  intro r A
  have hA : A = r • (directorProjector f.val.1 - directorProjector f.val.2) := rfl
  have hA₂ : A ^ 2 = r ^ 2 • (directorProjector f.val.1 + directorProjector f.val.2) :=
    biaxialTensor_sq a f.property.1 f.property.2.1 f.property.2.2
  rw [hA₂, hA, smul_smul, ← pow_two, ← smul_add, ← smul_sub]
  constructor
  · rw [show directorProjector f.val.1 + directorProjector f.val.2 +
      (directorProjector f.val.1 - directorProjector f.val.2) = directorProjector f.val.1 + directorProjector f.val.1 by abel,
      ← two_smul ℝ, smul_smul, mul_comm]
  · rw [show directorProjector f.val.1 + directorProjector f.val.2 -
      (directorProjector f.val.1 - directorProjector f.val.2) = directorProjector f.val.2 + directorProjector f.val.2 by abel,
      ← two_smul ℝ, smul_smul, mul_comm]

private theorem director_eq_or_neg_of_projector_eq {x y : Point} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (h : directorProjector x = directorProjector y) : x = y ∨ x = -y := by
  let c := (fun i => x i) ⬝ᵥ (fun i => y i)
  have hSelf : (fun i => y i) ⬝ᵥ (fun i => y i) = 1 := by
    rw [dotProduct]
    simpa only [pow_two, hy, one_mul] using (EuclideanSpace.real_norm_sq_eq y).symm
  have hVec := congrArg (fun M : Tensor => M *ᵥ (fun i => y i)) h
  simp only [directorProjector, Matrix.vecMulVec_mulVec, hSelf, op_smul_eq_smul, one_smul] at hVec
  have hY : c • x = y := PiLp.ext fun i => congrFun hVec i
  have hc : |c| = 1 := by
    have hNorm := congrArg norm hY
    rwa [norm_smul, Real.norm_eq_abs, hx, mul_one, hy] at hNorm
  rcases abs_choice c with hc' | hc'
  · left
    rw [← hY, ← hc', hc, one_smul]
  · right
    have hNeg : c = -1 := by linarith only [hc, hc']
    rw [← hY, hNeg, neg_smul, one_smul, neg_neg]

private theorem directorProjector_neg (x : Point) : directorProjector (-x) = directorProjector x := by
  change Matrix.vecMulVec (- (fun i => x i)) (- (fun i => x i)) = _
  rw [Matrix.neg_vecMulVec, Matrix.vecMulVec_neg, neg_neg]
  rfl

/-- Exactly the two independently reversible director signs survive in a
fiber of the frame-to-vacuum map. -/
theorem vacuumFrameProjection_eq_iff_signs (a : BulkCoefficients) (f g : VacuumFrame) :
    vacuumFrameProjection a f = vacuumFrameProjection a g ↔
      (f.val.1 = g.val.1 ∨ f.val.1 = -g.val.1) ∧ (f.val.2 = g.val.2 ∨ f.val.2 = -g.val.2) := by
  let A := ((vacuumFrameProjection a f).val : Tensor)
  let B := ((vacuumFrameProjection a g).val : Tensor)
  let s := 2 * vacuumRadius a ^ 2
  have hs : s ≠ 0 := (mul_pos (by norm_num) (sq_pos_of_pos (vacuumRadius_pos a))).ne'
  constructor
  · intro h
    have heq : A = B := congrArg (fun p : vacuum a => (p.val : Tensor)) h
    obtain ⟨hpF, hnF⟩ := directorProj_pair a f
    obtain ⟨hpG, hnG⟩ := directorProj_pair a g
    have hN : s • directorProjector f.val.1 = s • directorProjector g.val.1 := hpF.symm.trans
      ((congrArg (fun T : Tensor => T ^ 2 + vacuumRadius a • T) heq).trans hpG)
    have hM : s • directorProjector f.val.2 = s • directorProjector g.val.2 := hnF.symm.trans
      ((congrArg (fun T : Tensor => T ^ 2 - vacuumRadius a • T) heq).trans hnG)
    have hCancel {X Y : Tensor} (h : s • X = s • Y) : X = Y := by
      have he := congrArg (fun Z : Tensor => s⁻¹ • Z) h
      simpa only [smul_smul, inv_mul_cancel₀ hs, one_smul] using he
    exact ⟨director_eq_or_neg_of_projector_eq f.property.1 g.property.1 (hCancel hN),
      director_eq_or_neg_of_projector_eq f.property.2.1 g.property.2.1 (hCancel hM)⟩
  · rintro ⟨h₁, h₂⟩
    have hn : directorProjector f.val.1 = directorProjector g.val.1 :=
      h₁.elim (congrArg directorProjector) (fun h => (congrArg directorProjector h).trans (directorProjector_neg _))
    have hm : directorProjector f.val.2 = directorProjector g.val.2 :=
      h₂.elim (congrArg directorProjector) (fun h => (congrArg directorProjector h).trans (directorProjector_neg _))
    apply Subtype.ext
    apply Subtype.ext
    change vacuumRadius a • (directorProjector f.val.1 - directorProjector f.val.2) =
      vacuumRadius a • (directorProjector g.val.1 - directorProjector g.val.2)
    rw [hn, hm]

end Thesis

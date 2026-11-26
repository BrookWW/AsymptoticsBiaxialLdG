module

public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Analysis.Normed.Module.Normalize

/-! Short paths on a unit sphere can be replaced by normalized secants. -/

public section

noncomputable section

open Metric Set unitInterval

namespace Thesis

private theorem norm_affine_sub_le_of_norm_sub_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {x u v : E} {r t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : ‖u - x‖ ≤ r) (hv : ‖v - x‖ ≤ r) :
    ‖(1 - t) • u + t • v - x‖ ≤ r := by
  have h : (1 - t) • u + t • v - x = (1 - t) • (u - x) + t • (v - x) := by
    have hx : (1 - t) • x + t • x = x := by rw [← add_smul, sub_add_cancel, one_smul]
    calc
      _ = (1 - t) • u + t • v - ((1 - t) • x + t • x) := by rw [hx]
      _ = _ := by simp only [smul_sub]; abel
  rw [h]
  calc
    _ ≤ ‖(1 - t) • (u - x)‖ + ‖t • (v - x)‖ := norm_add_le _ _
    _ = (1 - t) * ‖u - x‖ + t * ‖v - x‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht.2), Real.norm_of_nonneg ht.1]
    _ ≤ (1 - t) * r + t * r := add_le_add
      (mul_le_mul_of_nonneg_left hu (sub_nonneg.mpr ht.2)) (mul_le_mul_of_nonneg_left hv ht.1)
    _ = r := by ring

/-- A unit-sphere path contained in the radius-one-half ball about its
starting point is homotopic relative to endpoints to a path in the span of
its two endpoint vectors. -/
theorem exists_path_homotopic_secant_in_span {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : sphere (0 : E) 1} (p : Path x y) (hClose : ∀ t : I, ‖(p t).val - x.val‖ ≤ 1 / 2) :
    ∃ q : Path x y, p.Homotopic q ∧ ∀ t : I, (q t).val ∈ Submodule.span ℝ {x.val, y.val} := by
  have hx : ‖x.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using x.property
  have hy : ‖y.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using y.property
  have hx' : ‖y.val - x.val‖ ≤ 1 / 2 := by simpa only [p.target] using hClose 1
  let line (t : I) := (1 - (t : ℝ)) • x.val + (t : ℝ) • y.val
  have hLine (t : I) : ‖line t - x.val‖ ≤ 1 / 2 :=
    norm_affine_sub_le_of_norm_sub_le t.property (by rw [sub_self, norm_zero]; norm_num) hx'
  let A (s : I × I) := (1 - (s.1 : ℝ)) • (p s.2).val + (s.1 : ℝ) • line s.2
  have hA (s : I × I) : A s ≠ 0 := by
    have h := norm_affine_sub_le_of_norm_sub_le s.1.property (hClose s.2) (hLine s.2)
    change ‖A s - x.val‖ ≤ 1 / 2 at h
    intro hz
    rw [hz, zero_sub, norm_neg, hx] at h
    norm_num at h
  let H (s : I × I) : sphere (0 : E) 1 := ⟨NormedSpace.normalize (A s), by
    rw [mem_sphere, dist_zero_right, NormedSpace.norm_normalize (hA s)]⟩
  have hLineC : Continuous line := by
    exact ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
      (continuous_subtype_val.smul continuous_const)
  have hAC : Continuous A := by
    have hS : Continuous (fun s : I × I => (s.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
    have hP : Continuous (fun s : I × I => (p s.2).val) :=
      continuous_subtype_val.comp (p.continuous.comp continuous_snd)
    exact ((continuous_const.sub hS).smul hP).add (hS.smul (hLineC.comp continuous_snd))
  have hHC : Continuous H :=
    (((hAC.norm.inv₀ (fun s => norm_ne_zero_iff.2 (hA s))).smul hAC).subtype_mk _)
  have hLine₀ : line 0 = x.val := by simp [line]
  have hLine₁ : line 1 = y.val := by simp [line]
  have hH₀ (s : I) : H (s, 0) = x := by
    apply Subtype.ext
    change NormedSpace.normalize ((1 - (s : ℝ)) • (p 0).val + (s : ℝ) • line 0) = _
    rw [p.source, hLine₀, ← add_smul, sub_add_cancel, one_smul,
      NormedSpace.normalize_eq_self_of_norm_eq_one hx]
  have hH₁ (s : I) : H (s, 1) = y := by
    apply Subtype.ext
    change NormedSpace.normalize ((1 - (s : ℝ)) • (p 1).val + (s : ℝ) • line 1) = _
    rw [p.target, hLine₁, ← add_smul, sub_add_cancel, one_smul,
      NormedSpace.normalize_eq_self_of_norm_eq_one hy]
  let q : Path x y :=
    { toFun := fun t => H (1, t)
      continuous_toFun := hHC.comp (continuous_const.prodMk continuous_id)
      source' := hH₀ 1
      target' := hH₁ 1 }
  have hHp (t : I) : H (0, t) = p t := by
    apply Subtype.ext
    have hp : ‖(p t).val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using (p t).property
    change NormedSpace.normalize (A (0, t)) = (p t).val
    simp [A, NormedSpace.normalize_eq_self_of_norm_eq_one hp]
  refine ⟨q, ?_, ?_⟩
  · refine ⟨{
      toFun := H
      continuous_toFun := hHC
      map_zero_left := hHp
      map_one_left := fun _ => rfl
      prop' := ?_ }⟩
    intro s t ht
    simp only [mem_insert_iff, mem_singleton_iff] at ht
    change H (s, t) = p t
    rcases ht with h | h
    · rw [h, hH₀, p.source]
    · rw [h, hH₁, p.target]
  · intro t
    have hAt : A (1, t) = line t := by simp [A]
    change NormedSpace.normalize (A (1, t)) ∈ Submodule.span ℝ {x.val, y.val}
    rw [hAt, NormedSpace.normalize]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl rfl)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl))))

end Thesis

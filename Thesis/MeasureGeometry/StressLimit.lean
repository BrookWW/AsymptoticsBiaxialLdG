module

public import Thesis.MeasureGeometry.StressAlgebra
public import Thesis.MeasureGeometry.BoundedDensities
public import Thesis.External.GeometricMeasureTheory

/-! Compactness of the stress relative to the actual scalar energy limit. -/

public section

open Filter MeasureTheory Matrix Set TopologicalSpace
open scoped BigOperators BoundedContinuousFunction ContDiff ENNReal NNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

noncomputable local instance stressLimitContinuousENorm : ContinuousENorm Tensor :=
  @SeminormedAddGroup.toContinuousENorm Tensor inferInstance

private theorem ae_forall_of_dense {Y : Type*} [TopologicalSpace Y] [SeparableSpace Y] [Nonempty Y]
    {μ : Measure Point} {P : Point → Y → Prop}
    (hc : ∀ x, IsClosed {y | P x y}) (h : ∀ y, ∀ᵐ x ∂μ, P x y) : ∀ᵐ x ∂μ, ∀ y, P x y := by
  obtain ⟨d, hd⟩ := exists_dense_seq Y
  filter_upwards [ae_all_iff.2 (fun n : ℕ => h (d n))] with x hx
  intro y
  exact hd.induction_on y (hc x) hx

private theorem frobenius_single_left (i j : Fin 3) (T : Tensor) :
    frobenius (Matrix.single i j 1) T = T i j := by
  simp only [frobenius_eq_sum, Matrix.single_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

private theorem frobenius_neg_left (B T : Tensor) : frobenius (-B) T = -frobenius B T := by
  simp [frobenius, Matrix.transpose_neg, Matrix.trace_neg]

private theorem frobenius_sub_left (B C T : Tensor) :
    frobenius (B - C) T = frobenius B T - frobenius C T := by
  simp [sub_eq_add_neg, frobenius_add_left, frobenius_neg_left]

private theorem frobenius_vecMulVec (T : Tensor) (v : Point) :
    frobenius (Matrix.vecMulVec v.ofLp v.ofLp) T = tensorQuadratic T v := by
  simp only [frobenius_eq_sum, Matrix.vecMulVec_apply, tensorQuadratic]

/-- The limit of the matrix densities keeps the symmetry, Frobenius norm,
trace, and quadratic-form bounds along a single subsequence of all entries. -/
theorem exists_matrixStressDensity_subsequence {K : Set Point} (hK : IsCompact K) (hne : K.Nonempty)
    {μ : ℕ → FiniteMeasure Point} {ν : FiniteMeasure Point} (hμ : Tendsto μ atTop (𝓝 ν))
    (B : ℝ≥0) (hB : ∀ n, (μ n).mass ≤ B) (hμK : ∀ n, (μ n : Measure Point) Kᶜ = 0)
    (T : ℕ → Point → Tensor) (hm : ∀ n i j, Measurable (fun x => T n x i j))
    (hbound : ∀ n x, (T n x)ᵀ = T n x ∧ 1 ≤ (T n x).trace ∧ ‖T n x‖ ≤ 2 ∧
      ∀ v : Point, tensorQuadratic (T n x) v ≤ ‖v‖ ^ 2) :
    ∃ (s : ℕ → ℕ) (F : Point → Tensor), StrictMono s ∧ (∀ i j, Measurable (fun x => F x i j)) ∧
      Integrable F (ν : Measure Point) ∧
      (∀ᵐ x ∂(ν : Measure Point), (F x)ᵀ = F x ∧ 1 ≤ (F x).trace ∧ ‖F x‖ ≤ 2 ∧
        ∀ v : Point, tensorQuadratic (F x) v ≤ ‖v‖ ^ 2) ∧
      ∀ (i j : Fin 3) (φ : Point →ᵇ ℝ), Tendsto
        (fun n => ∫ x, T (s n) x i j * φ x ∂(μ (s n) : Measure Point)) atTop
        (𝓝 (∫ x, F x i j * φ x ∂(ν : Measure Point))) := by
  let g (k : Fin 3 × Fin 3) (n : ℕ) (x : Point) := T n x k.1 k.2
  have hg (k : Fin 3 × Fin 3) (n : ℕ) : Measurable (g k n) := hm n k.1 k.2
  have hcap (k : Fin 3 × Fin 3) (n : ℕ) (x : Point) : |g k n x| ≤ (2 : ℝ≥0) :=
    (abs_tensor_entry_le_frobenius_norm (T n x) k.1 k.2).trans (hbound n x).2.2.1
  obtain ⟨s, f, hs, hf⟩ := exists_weaklyConvergent_boundedDensities hK hne hμ B hB hμK
    2 g hg hcap
  let F (x : Point) : Tensor := fun i j => f (i, j) x
  have hFMeas (i j : Fin 3) : Measurable (fun x => F x i j) := (hf (i, j)).1
  have hFInt : Integrable F (ν : Measure Point) := by
    have hsum : F = fun x => ∑ i, ∑ j, f (i, j) x • Matrix.single i j (1 : ℝ) := by
      funext x
      simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single (F x)
    rw [hsum]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      ((hf (i, j)).2.1).smul_const (Matrix.single i j (1 : ℝ))
  have hgInt (k : Fin 3 × Fin 3) (n : ℕ) : Integrable (g k n) (μ n : Measure Point) :=
    (integrable_const (2 : ℝ)).mono' (hg k n).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, NNReal.coe_ofNat] using hcap k n x)
  have hpass (A : Tensor) (c : ℝ) (hp : ∀ n x, 0 ≤ c + frobenius A (T n x)) :
      ∀ᵐ x ∂(ν : Measure Point), 0 ≤ c + frobenius A (F x) := by
    simp only [frobenius_eq_sum] at hp ⊢
    have h := ae_affine_nonneg_of_weakDensities (hμ.comp hs.tendsto_atTop)
      (fun k n => hgInt k (s n)) (fun k => (hf k).1) (fun k => (hf k).2.1)
      (fun k => (hf k).2.2) (fun k : Fin 3 × Fin 3 => A k.1 k.2) c (by
        intro n
        apply Filter.Eventually.of_forall
        intro x
        rw [Fintype.sum_prod_type]
        exact hp (s n) x)
    simpa only [Fintype.sum_prod_type, F] using h
  have hentry (i j : Fin 3) : ∀ᵐ x ∂(ν : Measure Point), F x j i ≤ F x i j := by
    have h := hpass (Matrix.single i j 1 - Matrix.single j i 1) 0 (by
      intro n x
      rw [zero_add, frobenius_sub_left, frobenius_single_left, frobenius_single_left]
      exact sub_nonneg.mpr (le_of_eq (congrFun (congrFun (hbound n x).1 i) j)))
    exact h.mono fun x hx => by
      simpa only [zero_add, frobenius_sub_left, frobenius_single_left, sub_nonneg] using hx
  have hsym : ∀ᵐ x ∂(ν : Measure Point), (F x)ᵀ = F x := by
    filter_upwards [ae_all_iff.2 (fun i => ae_all_iff.2 (fun j => hentry i j))] with x hx
    ext i j
    exact le_antisymm (hx i j) (hx j i)
  have htrace : ∀ᵐ x ∂(ν : Measure Point), 1 ≤ (F x).trace := by
    have h := hpass 1 (-1) (fun n x => by
      rw [frobenius_one_left, neg_add_eq_sub]
      exact sub_nonneg.mpr (hbound n x).2.1)
    simpa only [frobenius_one_left, neg_add_eq_sub, sub_nonneg] using h
  have hquad : ∀ᵐ x ∂(ν : Measure Point), ∀ v : Point, tensorQuadratic (F x) v ≤ ‖v‖ ^ 2 := by
    apply ae_forall_of_dense
    · intro x
      apply isClosed_le _ (by fun_prop)
      unfold tensorQuadratic
      fun_prop
    · intro v
      have h := hpass (-(Matrix.vecMulVec v.ofLp v.ofLp)) (‖v‖ ^ 2) (fun n x => by
        rw [frobenius_neg_left, frobenius_vecMulVec, ← sub_eq_add_neg]
        exact sub_nonneg.mpr ((hbound n x).2.2.2 v))
      simpa only [frobenius_neg_left, frobenius_vecMulVec, ← sub_eq_add_neg, sub_nonneg] using h
  have hnorm : ∀ᵐ x ∂(ν : Measure Point), ‖F x‖ ≤ 2 := by
    letI : SeparableSpace Tensor := inferInstanceAs (SeparableSpace (Fin 3 → Fin 3 → ℝ))
    have htest : ∀ᵐ x ∂(ν : Measure Point), ∀ A : Tensor, frobenius A (F x) ≤ 2 * ‖A‖ := by
      apply ae_forall_of_dense
      · intro x
        apply isClosed_le _ (continuous_const.mul continuous_norm)
        simp only [frobenius_eq_sum]
        fun_prop
      · intro A
        have h := hpass (-A) (2 * ‖A‖) (fun n x => by
          rw [frobenius_neg_left, ← sub_eq_add_neg]
          apply sub_nonneg.mpr
          calc
            _ ≤ |frobenius A (T n x)| := le_abs_self _
            _ ≤ ‖A‖ * ‖T n x‖ := abs_frobenius_le_norm_mul_norm _ _
            _ ≤ 2 * ‖A‖ := by
              rw [mul_comm 2]
              exact mul_le_mul_of_nonneg_left (hbound n x).2.2.1 (norm_nonneg _))
        simpa only [frobenius_neg_left, ← sub_eq_add_neg, sub_nonneg] using h
    filter_upwards [htest] with x hx
    have hh := hx (F x)
    rw [← norm_sq_eq_frobenius, pow_two] at hh
    rcases (norm_nonneg (F x)).eq_or_lt with hzero | hpos
    · rw [← hzero]
      norm_num
    · exact le_of_mul_le_mul_right hh hpos
  refine ⟨s, F, hs, hFMeas, hFInt, ?_, fun i j => (hf (i, j)).2.2⟩
  filter_upwards [hsym, htrace, hnorm, hquad] with x h₁ h₂ h₃ h₄
  exact ⟨h₁, h₂, h₃, h₄⟩

end Thesis.MeasureGeometry

end

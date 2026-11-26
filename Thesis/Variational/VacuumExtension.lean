module

public import Thesis.Variational.GlobalLimit
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Smooth relative extension of a boundary quaternion lift and its induced
vacuum-valued Dirichlet competitor. -/

public section

open Set Filter MeasureTheory Topology
open scoped BigOperators ContDiff ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

variable {Ω : Set Point}

private theorem norm_eq_one_of_sphere3 (v : Sphere3) : ‖(v : QuaternionCoordinates)‖ = 1 := by
  have hv := v.property
  rw [Metric.mem_sphere, dist_zero_right] at hv
  exact hv

/-- A smooth ambient lift of a boundary map into `S³` admits a smooth
unit-quaternion extension that keeps the original boundary values. -/
theorem IsSmoothBoundaryLift.exists_unit_extension {b : frontier Ω → Sphere3}
    (hLift : IsSmoothBoundaryLift Ω b) :
    ∃ v : Point → QuaternionCoordinates, ContDiff ℝ ∞ v ∧
      (∀ x, ‖v x‖ = 1) ∧ ∀ x : frontier Ω, v x = (b x : QuaternionCoordinates) := by
  obtain ⟨B, hB, hb⟩ := hLift
  have hDim : Module.finrank ℝ Point < Module.finrank ℝ QuaternionCoordinates := by
    simp only [Point, QuaternionCoordinates, finrank_euclideanSpace, Fintype.card_fin]
    decide
  have hB₁ : ContDiff ℝ 1 B := hB.of_le (by simp)
  have hDense := hB₁.dense_compl_range_of_finrank_lt_finrank hDim
  obtain ⟨c, hcBall, hcRange⟩ := (Metric.dense_iff.mp hDense) (0 : QuaternionCoordinates)
    (1 / 2) (by norm_num)
  have hc : ‖c‖ < 1 / 2 := by
    rw [Metric.mem_ball, dist_zero_right] at hcBall
    exact hcBall
  let χ (x : Point) := Real.smoothTransition (2 * ‖B x‖ ^ 2 - 1)
  let F (x : Point) := B x - (1 - χ x) • c
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (hB.norm_sq ℝ)).sub contDiff_const)
  have hF : ContDiff ℝ ∞ F := hB.sub ((contDiff_const.sub hχ).smul contDiff_const)
  have hF_ne (x : Point) : F x ≠ 0 := by
    rcases le_or_gt (‖B x‖ ^ 2) (1 / 2) with hx | hx
    · have hχ₀ : χ x = 0 := Real.smoothTransition.zero_of_nonpos (by linarith only [hx])
      have hEq : F x = B x - c := by simp only [F, hχ₀, sub_zero, one_smul]
      rw [hEq]
      exact sub_ne_zero.mpr fun h => hcRange ⟨x, h⟩
    · have hx' : 1 / 2 < ‖B x‖ := by
        by_contra! hl
        have hSq := pow_le_pow_left₀ (norm_nonneg (B x)) hl 2
        linarith only [hx, hSq]
      intro hZero
      have hEq : B x = (1 - χ x) • c := sub_eq_zero.mp hZero
      have hChi : 0 ≤ χ x := Real.smoothTransition.nonneg _
      have hChi' : χ x ≤ 1 := Real.smoothTransition.le_one _
      have hLe : ‖B x‖ ≤ ‖c‖ := by
        rw [hEq, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hChi')]
        exact mul_le_of_le_one_left (norm_nonneg _) (by linarith only [hChi])
      exact (not_lt_of_ge hLe) (hc.trans hx')
  let v (x : Point) := ‖F x‖⁻¹ • F x
  have hv : ContDiff ℝ ∞ v :=
    ((hF.norm ℝ hF_ne).inv (fun x => norm_ne_zero_iff.mpr (hF_ne x))).smul hF
  refine ⟨v, hv, ?_, ?_⟩
  · intro x
    change ‖‖F x‖⁻¹ • F x‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hF_ne x))]
  · intro x
    have hNorm : ‖B x‖ = 1 := (congrArg norm (hb x)).trans (norm_eq_one_of_sphere3 (b x))
    have hχ₁ : χ x = 1 := by
      change Real.smoothTransition (2 * ‖B x‖ ^ 2 - 1) = 1
      rw [hNorm]
      norm_num
    have hEq : F x = B x := by simp only [F, hχ₁, sub_self, zero_smul, sub_zero]
    change ‖F x‖⁻¹ • F x = (b x : QuaternionCoordinates)
    rw [hEq, hNorm, inv_one, one_smul, hb]

private theorem norm_sq_firstFrameVector (v : QuaternionCoordinates) :
    ‖firstFrameVector v‖ ^ 2 = (‖v‖ ^ 2) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq v]
  simp [firstFrameVector, Fin.sum_univ_succ]
  ring

private theorem norm_sq_secondFrameVector (v : QuaternionCoordinates) :
    ‖secondFrameVector v‖ ^ 2 = (‖v‖ ^ 2) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq v]
  simp [secondFrameVector, Fin.sum_univ_succ]
  ring

private theorem inner_first_secondFrameVector (v : QuaternionCoordinates) :
    inner ℝ (firstFrameVector v) (secondFrameVector v) = 0 := by
  simp [PiLp.inner_apply, firstFrameVector, secondFrameVector, Fin.sum_univ_succ]
  ring

theorem cover_mem_vacuum (a : BulkCoefficients) (v : Sphere3) : cover a v ∈ vacuum a := by
  let n := firstFrameVector v
  let m := secondFrameVector v
  have hn : ‖n‖ = 1 := (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by
    rw [show ‖n‖ ^ 2 = (‖(v : QuaternionCoordinates)‖ ^ 2) ^ 2 from norm_sq_firstFrameVector v,
      norm_eq_one_of_sphere3 v, one_pow, one_pow])
  have hm : ‖m‖ = 1 := (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by
    rw [show ‖m‖ ^ 2 = (‖(v : QuaternionCoordinates)‖ ^ 2) ^ 2 from norm_sq_secondFrameVector v,
      norm_eq_one_of_sphere3 v, one_pow, one_pow])
  have htr (x : Point) : (Matrix.vecMulVec (fun i => x i) (fun i => x i)).trace = ‖x‖ ^ 2 := by
    rw [Matrix.trace_vecMulVec, EuclideanSpace.real_norm_sq_eq, dotProduct]
    exact Finset.sum_congr rfl fun i _ => (pow_two (x i)).symm
  have hsymm : (biaxialTensor a n m)ᵀ = biaxialTensor a n m := by
    simp only [biaxialTensor, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_vecMulVec]
  have htrace : (biaxialTensor a n m).trace = 0 := by
    rw [biaxialTensor, Matrix.trace_smul, Matrix.trace_sub, htr, htr, hn, hm, sub_self, smul_zero]
  let A : S0 := ⟨biaxialTensor a n m, hsymm, htrace⟩
  exact ⟨n, m, hn, hm, inner_first_secondFrameVector v,
    congrArg (fun X : S0 => (X : Tensor)) (traceFreeSymmetricPart_of_S0 A)⟩

private theorem contDiff_firstFrameVector : ContDiff ℝ ∞ firstFrameVector := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> simp [firstFrameVector] <;> fun_prop

private theorem contDiff_secondFrameVector : ContDiff ℝ ∞ secondFrameVector := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> simp [secondFrameVector] <;> fun_prop

private noncomputable def vecMulVecCLM :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] Tensor :=
  ((LinearMap.toContinuousLinearMap :
    ((Fin 3 → ℝ) →ₗ[ℝ] Tensor) ≃ₗ[ℝ] ((Fin 3 → ℝ) →L[ℝ] Tensor)).toLinearMap.comp
      (vecMulVecBilin ℝ ℝ)).toContinuousLinearMap

private theorem contDiff_rankOne {f : QuaternionCoordinates → Point}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => Matrix.vecMulVec (fun i => f x i) (fun i => f x i)) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap
  have he := e.contDiff.comp hf
  exact (vecMulVecCLM.contDiff.comp he).clm_apply he

/-- The polynomial defining the quaternion cover, evaluated on the ambient
quaternion coordinates. Its restriction to the unit sphere is `cover`. -/
@[expose] def ambientQuaternionCover (a : BulkCoefficients) (v : QuaternionCoordinates) : S0 :=
  traceFreeSymmetricPart (biaxialTensor a (firstFrameVector v) (secondFrameVector v))

theorem contDiff_ambientQuaternionCover (a : BulkCoefficients) :
    ContDiff ℝ ∞ (ambientQuaternionCover a) := by
  have hn := contDiff_rankOne contDiff_firstFrameVector
  have hm := contDiff_rankOne contDiff_secondFrameVector
  exact traceFreeSymmetricPartCLM.contDiff.comp ((hn.sub hm).const_smul (vacuumRadius a))

/-- A smooth boundary quaternion lift gives one finite-energy vacuum-valued
Dirichlet comparison with its actual classical gradient. -/
theorem exists_vacuum_competitor_of_smoothBoundaryLift
    (a : BulkCoefficients) (hΩ : IsOpen Ω) (hBound : Bornology.IsBounded Ω)
    {b : frontier Ω → Sphere3} (hLift : IsSmoothBoundaryLift Ω b) :
    ∃ w : Point → S0, ContDiff ℝ ∞ w ∧ MemH1 Ω w (ClassicalGradient w) ∧
      HasSmoothTrace Ω w (ClassicalGradient w) (fun x => cover a (b x)) ∧
      TakesVacuumValues a Ω w ∧ dirichletEnergy Ω (ClassicalGradient w) < ⊤ := by
  obtain ⟨v, hv, hvUnit, hEq⟩ := hLift.exists_unit_extension
  let w := ambientQuaternionCover a ∘ v
  have hw : ContDiff ℝ ∞ w := (contDiff_ambientQuaternionCover a).comp hv
  have hH : MemH1 Ω w (ClassicalGradient w) :=
    memH1Loc_of_contDiffOn isOpen_univ (hw.of_le (by simp)).contDiffOn
      Ω hΩ ⟨hBound.isCompact_closure, subset_univ _⟩
  refine ⟨w, hw, hH, ⟨w, hw, ?_, SameTrace.refl hΩ w _⟩, ?_, dirichletEnergy_lt_top_of_memLp hH.2.1⟩
  · intro x
    change ambientQuaternionCover a (v x) = cover a (b x)
    rw [hEq x]
    rfl
  · exact Eventually.of_forall fun x => cover_mem_vacuum a
      ⟨v x, Metric.mem_sphere.mpr (by rw [dist_zero_right, hvUnit x])⟩

/-- The global strong limit with the boundary datum and minimizing family in
the frozen smooth-lift formulation. -/
theorem exists_global_energy_limit_of_smoothBoundaryLift
    (a : BulkCoefficients) (hΩ : IsBoundedDomain Ω)
    (T : SobolevTraceOperator Ω) (hComp : NonexpansiveSobolevTraceComposition Ω)
    (b : frontier Ω → Sphere3) (hLift : IsSmoothBoundaryLift Ω b)
    (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient)
    (hMin : ∀ ε, IsGlobalEnergyMinimizer a ε Ω (fun x => cover a (b x)) (Q ε) (D ε)) :
    ∃ (ε : ℕ → ElasticScale) (v : Point → S0) (G : Point → Gradient),
      Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0) ∧
      StrongH1 Ω (Q ∘ ε) (D ∘ ε) v G ∧
      IsGlobalDirichletMinimizer a Ω (fun x => cover a (b x)) v G ∧
      (∀ k, MemLp (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (Q (ε k) x))
        1 (volume.restrict Ω)) ∧
      Tendsto (fun k => eLpNorm (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (Q (ε k) x))
        1 (volume.restrict Ω)) atTop (𝓝 0) ∧
      Tendsto (fun k => energy a (ε k) Ω (Q (ε k)) (D (ε k))) atTop
        (𝓝 (dirichletEnergy Ω G)) := by
  obtain ⟨w, _, hw, hTrace, hVac, _⟩ :=
    exists_vacuum_competitor_of_smoothBoundaryLift a hΩ.1 hΩ.2.2 hLift
  exact exists_global_energy_limit_of_vacuum_competitor a hΩ T hComp _ Q D hMin hw hTrace hVac

end Thesis

end

module

public import Thesis.Foundation.VacuumTarget

/-! The normal projection and the first linearization of the sextic bulk force. -/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Filter Set
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius Topology

namespace Thesis

/-- The symmetric traceless normal projection defined by the two invariant traces. -/
def vacuumNormalProjector (a : BulkCoefficients) (A : S0) : S0 →L[ℝ] S0 :=
  (vacuumInvariantRightInverse a A).comp (vacuumInvariantDerivative A)

theorem normalPart_eq_vacuumNormalProjector {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) (B : S0) :
    normalPart a (A : Tensor) (B : Tensor) = (vacuumNormalProjector a A B : Tensor) := by
  let t := ((A : Tensor) * (B : Tensor)).trace
  let s := (((A : Tensor) ^ 2) * (B : Tensor)).trace
  let r := vacuumRadius a
  have hr : r ≠ 0 := (vacuumRadius_pos a).ne'
  have ht : (2 * t) / (4 * r ^ 2) = t / (2 * r ^ 2) := by
    field_simp [hr]
    ring
  have hs : (3 * s) / (2 * r ^ 4) = (s / (2 * r ^ 4)) * 3 := by
    field_simp [hr]
  change normalPart a (A : Tensor) (B : Tensor) =
    (vacuumInvariantRightInverse a A (vacuumInvariantDerivative A B) : Tensor)
  rw [vacuumInvariantRightInverse_apply, vacuumInvariantDerivative_apply]
  change (t / (2 * r ^ 2)) • (A : Tensor) + (s / (2 * r ^ 4)) • (3 : ℝ) •
      biaxialQuadratic a (A : Tensor) =
    ((2 * t) / (4 * r ^ 2)) • (A : Tensor) + ((3 * s) / (2 * r ^ 4)) • (traceFreeSquare A : Tensor)
  rw [ht, hs, traceFreeSquare_coe_eq_biaxialQuadratic hA, smul_smul]

theorem tangentPart_eq_vacuumInvariantSplit {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) (B : S0) :
    tangentPart a (A : Tensor) (B : Tensor) = (((vacuumInvariantSplit hA B).2 : S0) : Tensor) := by
  rw [tangentPart, normalPart_eq_vacuumNormalProjector hA, vacuumInvariantSplit_snd_coe]
  rfl

theorem vacuumNormalProjector_idempotent {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    (vacuumNormalProjector a A).comp (vacuumNormalProjector a A) = vacuumNormalProjector a A := by
  apply ContinuousLinearMap.ext
  intro B
  change vacuumInvariantRightInverse a A
      (vacuumInvariantDerivative A (vacuumInvariantRightInverse a A (vacuumInvariantDerivative A B))) =
    vacuumInvariantRightInverse a A (vacuumInvariantDerivative A B)
  rw [vacuumInvariantRightInverse_isRightInverse hA]

theorem vacuumNormalProjector_apply_self {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    vacuumNormalProjector a A A = A := by
  change vacuumInvariantRightInverse a A (vacuumInvariantDerivative A A) = A
  rw [vacuumInvariantDerivative_self hA, vacuumInvariantRightInverse_apply]
  have hr : vacuumRadius a ≠ 0 := (vacuumRadius_pos a).ne'
  simp [hr]

theorem vacuumNormalProjector_apply_traceFreeSquare {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) : vacuumNormalProjector a A (traceFreeSquare A) = traceFreeSquare A := by
  change vacuumInvariantRightInverse a A (vacuumInvariantDerivative A (traceFreeSquare A)) =
    traceFreeSquare A
  rw [vacuumInvariantDerivative_traceFreeSquare hA, vacuumInvariantRightInverse_apply]
  have hr : vacuumRadius a ≠ 0 := (vacuumRadius_pos a).ne'
  simp [hr]

theorem vacuum_normal_basis_pairings {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    frobeniusS0 A A = 2 * vacuumRadius a ^ 2 ∧
      frobeniusS0 A (traceFreeSquare A) = 0 ∧
      frobeniusS0 (traceFreeSquare A) (traceFreeSquare A) = 2 * vacuumRadius a ^ 4 / 3 := by
  have hA' := vacuumInvariantDerivative_self hA
  have hSq := vacuumInvariantDerivative_traceFreeSquare hA
  rw [vacuumInvariantDerivative_apply_frobenius] at hA' hSq
  have h₁ := congrArg Prod.fst hA'
  have h₂ := congrArg Prod.fst hSq
  have h₃ := congrArg Prod.snd hSq
  change 2 * frobeniusS0 A A = 4 * vacuumRadius a ^ 2 at h₁
  change 2 * frobeniusS0 A (traceFreeSquare A) = 0 at h₂
  change 3 * frobeniusS0 (traceFreeSquare A) (traceFreeSquare A) = 2 * vacuumRadius a ^ 4 at h₃
  exact ⟨by linarith only [h₁], by linarith only [h₂], by linarith only [h₃]⟩

/-- The coefficient of the quadratic trace defect in the force linearization. -/
def bulkRadialCoefficient (a : BulkCoefficients) : ℝ :=
  a.a4 + 4 * a.a6 * vacuumRadius a ^ 2

theorem bulkRadialCoefficient_pos (a : BulkCoefficients) : 0 < bulkRadialCoefficient a := by
  have := a.a4_pos
  have := a.a6_pos
  unfold bulkRadialCoefficient
  positivity

/-- The derivative in a normal direction proportional to the vacuum tensor. -/
def bulkRadialMass (a : BulkCoefficients) : ℝ :=
  4 * vacuumRadius a ^ 2 * bulkRadialCoefficient a

/-- The derivative in a normal direction proportional to the trace-free square. -/
def bulkBiaxialMass (a : BulkCoefficients) : ℝ :=
  2 * a.a6' * vacuumRadius a ^ 4

theorem bulkRadialMass_pos (a : BulkCoefficients) : 0 < bulkRadialMass a := by
  have := vacuumRadius_pos a
  have := bulkRadialCoefficient_pos a
  unfold bulkRadialMass
  positivity

theorem bulkBiaxialMass_pos (a : BulkCoefficients) : 0 < bulkBiaxialMass a := by
  have := a.a6'_pos
  have := vacuumRadius_pos a
  unfold bulkBiaxialMass
  positivity

/-- The linearization of the actual force at a vacuum tensor. -/
def bulkForceLinearization (a : BulkCoefficients) (A : S0) : S0 →L[ℝ] S0 :=
  (((bulkRadialCoefficient a • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight A) +
    ((a.a6' • ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (traceFreeSquare A))).comp
      (vacuumInvariantDerivative A)

theorem bulkForceLinearization_apply (a : BulkCoefficients) (A B : S0) :
    bulkForceLinearization a A B =
      (2 * bulkRadialCoefficient a * ((A : Tensor) * (B : Tensor)).trace) • A +
      (3 * a.a6' * (((A : Tensor) ^ 2) * (B : Tensor)).trace) • traceFreeSquare A := by
  unfold bulkForceLinearization
  rw [ContinuousLinearMap.comp_apply, vacuumInvariantDerivative_apply]
  change (bulkRadialCoefficient a * (2 * ((A : Tensor) * (B : Tensor)).trace)) • A +
    (a.a6' * (3 * (((A : Tensor) ^ 2) * (B : Tensor)).trace)) • traceFreeSquare A = _
  congr 1 <;> congr 1 <;> ring

theorem bulkForce_eq_smul_components (a : BulkCoefficients) (A : S0) :
    bulkForce a A =
      (-a.a2 + a.a4 * (vacuumInvariants A).1 + a.a6 * (vacuumInvariants A).1 ^ 2) • A +
      (a.a6' * (vacuumInvariants A).2) • traceFreeSquare A := by
  apply Subtype.ext
  change bulkGradient a A =
    (-a.a2 + a.a4 * (vacuumInvariants A).1 + a.a6 * (vacuumInvariants A).1 ^ 2) • (A : Tensor) +
      (a.a6' * (vacuumInvariants A).2) • (traceFreeSquare A : Tensor)
  rw [traceFreeSquare_coe]
  rfl

private theorem bulkForce_radialCoefficient_at_vacuum {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) :
    -a.a2 + a.a4 * (vacuumInvariants A).1 + a.a6 * (vacuumInvariants A).1 ^ 2 = 0 := by
  change -a.a2 + a.a4 * ((A : Tensor) ^ 2).trace + a.a6 * (((A : Tensor) ^ 2).trace) ^ 2 = 0
  rw [(vacuum_traces hA).1]
  linear_combination vacuumRadius_equation a

theorem bulkForce_eq_zero_of_mem_vacuum {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) : bulkForce a A = 0 := by
  have h₃ : (vacuumInvariants A).2 = 0 := (vacuum_traces hA).2
  rw [bulkForce_eq_smul_components, bulkForce_radialCoefficient_at_vacuum hA, h₃]
  simp

theorem contDiff_traceFreeSquare : ContDiff ℝ ∞ traceFreeSquare := by
  change ContDiff ℝ ∞ (fun A : S0 =>
    traceFreeSymmetricPartCLM ((symmetricTraceless.subtypeL A) ^ 2))
  fun_prop

theorem contDiff_bulkForce (a : BulkCoefficients) : ContDiff ℝ ∞ (bulkForce a) := by
  have h : bulkForce a = fun A =>
      (-a.a2 + a.a4 * (vacuumInvariants A).1 + a.a6 * (vacuumInvariants A).1 ^ 2) • A +
      (a.a6' * (vacuumInvariants A).2) • traceFreeSquare A :=
    funext (bulkForce_eq_smul_components a)
  rw [h]
  have ht := contDiff_vacuumInvariants.fst
  have hs := contDiff_vacuumInvariants.snd
  have hc : ContDiff ℝ ∞ (fun _ : S0 => -a.a2) := contDiff_const
  have h₄ : ContDiff ℝ ∞ (fun _ : S0 => a.a4) := contDiff_const
  have h₆ : ContDiff ℝ ∞ (fun _ : S0 => a.a6) := contDiff_const
  have h₆' : ContDiff ℝ ∞ (fun _ : S0 => a.a6') := contDiff_const
  exact (((hc.add (h₄.mul ht)).add (h₆.mul (ht.pow 2))).smul contDiff_id).add
    ((h₆'.mul hs).smul contDiff_traceFreeSquare)

theorem hasStrictFDerivAt_bulkForce {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    HasStrictFDerivAt (bulkForce a) (bulkForceLinearization a A) A := by
  let t (B : S0) := (vacuumInvariants B).1
  let s (B : S0) := (vacuumInvariants B).2
  let dt := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (vacuumInvariantDerivative A)
  let ds := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (vacuumInvariantDerivative A)
  have ht : HasStrictFDerivAt t dt A := (hasStrictFDerivAt_vacuumInvariants A).fst
  have hs : HasStrictFDerivAt s ds A := (hasStrictFDerivAt_vacuumInvariants A).snd
  let k (B : S0) := -a.a2 + a.a4 * t B + a.a6 * (t B) ^ 2
  have hk : HasStrictFDerivAt k (bulkRadialCoefficient a • dt) A := by
    have h := ((hasStrictFDerivAt_const (-a.a2) A).add (ht.const_mul a.a4)).add
      ((ht.mul ht).const_mul a.a6)
    have hkFun : k = (fun _ : S0 => -a.a2) + (fun B => a.a4 * t B) +
        (fun B => a.a6 * (t * t) B) := by
      funext B
      simp [k, pow_two]
    rw [hkFun]
    refine h.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro B
    change (0 : ℝ) + a.a4 * dt B + a.a6 * (t A * dt B + t A * dt B) =
      bulkRadialCoefficient a * dt B
    have hT : t A = 2 * vacuumRadius a ^ 2 := (vacuum_traces hA).1
    rw [hT, bulkRadialCoefficient]
    ring
  have hq : HasStrictFDerivAt traceFreeSquare (fderiv ℝ traceFreeSquare A) A :=
    contDiff_traceFreeSquare.contDiffAt.hasStrictFDerivAt (by simp)
  have hg := hs.const_mul a.a6'
  have hWide := (hk.smul (hasStrictFDerivAt_id A)).add (hg.smul hq)
  have hFunc : bulkForce a = fun B => k B • B + (a.a6' * s B) • traceFreeSquare B :=
    funext (bulkForce_eq_smul_components a)
  rw [hFunc]
  refine hWide.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro B
  have hk₀ : k A = 0 := bulkForce_radialCoefficient_at_vacuum hA
  have hs₀ : s A = 0 := (vacuum_traces hA).2
  change k A • B + (bulkRadialCoefficient a * dt B) • A +
      ((a.a6' * s A) • fderiv ℝ traceFreeSquare A B + (a.a6' * ds B) • traceFreeSquare A) = _
  have hdt : dt B = 2 * ((A : Tensor) * (B : Tensor)).trace := congrArg Prod.fst (vacuumInvariantDerivative_apply A B)
  have hds : ds B = 3 * (((A : Tensor) ^ 2) * (B : Tensor)).trace := congrArg Prod.snd (vacuumInvariantDerivative_apply A B)
  rw [hk₀, hs₀, hdt, hds, zero_smul, zero_add, mul_zero, zero_smul, zero_add]
  calc
    _ = (2 * bulkRadialCoefficient a * ((A : Tensor) * (B : Tensor)).trace) • A +
        (3 * a.a6' * (((A : Tensor) ^ 2) * (B : Tensor)).trace) • traceFreeSquare A := by
      congr 1 <;> congr 1 <;> ring
    _ = _ := (bulkForceLinearization_apply a A B).symm

theorem fderiv_bulkForce_at_vacuum {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    fderiv ℝ (bulkForce a) A = bulkForceLinearization a A :=
  (hasStrictFDerivAt_bulkForce hA).hasFDerivAt.fderiv

theorem bulkForceLinearization_eq_normalCoordinates (a : BulkCoefficients) (A B : S0) :
    bulkForceLinearization a A B = vacuumInvariantRightInverse a A
      (bulkRadialMass a * (vacuumInvariantDerivative A B).1,
        bulkBiaxialMass a * (vacuumInvariantDerivative A B).2) := by
  let p := vacuumInvariantDerivative A B
  let r := vacuumRadius a
  have hr : 0 < r := vacuumRadius_pos a
  have h₁ : bulkRadialMass a * p.1 / (4 * r ^ 2) = bulkRadialCoefficient a * p.1 := by
    apply (div_eq_iff (by positivity : (4 * r ^ 2 : ℝ) ≠ 0)).2
    dsimp only [bulkRadialMass, r]
    ring
  have h₂ : bulkBiaxialMass a * p.2 / (2 * r ^ 4) = a.a6' * p.2 := by
    apply (div_eq_iff (by positivity : (2 * r ^ 4 : ℝ) ≠ 0)).2
    dsimp only [bulkBiaxialMass, r]
    ring
  rw [vacuumInvariantRightInverse_apply]
  change (bulkRadialCoefficient a * p.1) • A + (a.a6' * p.2) • traceFreeSquare A =
    (bulkRadialMass a * p.1 / (4 * r ^ 2)) • A + (bulkBiaxialMass a * p.2 / (2 * r ^ 4)) • traceFreeSquare A
  rw [h₁, h₂]

theorem vacuumInvariantDerivative_bulkForceLinearization {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) (B : S0) :
    vacuumInvariantDerivative A (bulkForceLinearization a A B) =
      (bulkRadialMass a * (vacuumInvariantDerivative A B).1,
        bulkBiaxialMass a * (vacuumInvariantDerivative A B).2) := by
  rw [bulkForceLinearization_eq_normalCoordinates a A, vacuumInvariantRightInverse_isRightInverse hA]

theorem bulkForceLinearization_self {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    bulkForceLinearization a A A = bulkRadialMass a • A := by
  change (bulkRadialCoefficient a * (vacuumInvariantDerivative A A).1) • A +
      (a.a6' * (vacuumInvariantDerivative A A).2) • traceFreeSquare A = _
  rw [vacuumInvariantDerivative_self hA]
  simp only [mul_zero, zero_smul, add_zero]
  rw [bulkRadialMass, mul_comm (bulkRadialCoefficient a)]

theorem bulkForceLinearization_traceFreeSquare {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) :
    bulkForceLinearization a A (traceFreeSquare A) = bulkBiaxialMass a • traceFreeSquare A := by
  change (bulkRadialCoefficient a * (vacuumInvariantDerivative A (traceFreeSquare A)).1) • A +
      (a.a6' * (vacuumInvariantDerivative A (traceFreeSquare A)).2) • traceFreeSquare A = _
  rw [vacuumInvariantDerivative_traceFreeSquare hA]
  simp only [mul_zero, zero_smul, zero_add]
  congr 1
  unfold bulkBiaxialMass
  ring

theorem bulkForceLinearization_ker {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    (bulkForceLinearization a A).ker = (vacuumInvariantDerivative A).ker := by
  ext B
  change bulkForceLinearization a A B = 0 ↔ vacuumInvariantDerivative A B = 0
  constructor
  · intro h
    have heq := vacuumInvariantDerivative_bulkForceLinearization hA B
    rw [h, map_zero] at heq
    have h₁ := congrArg Prod.fst heq.symm
    have h₂ := congrArg Prod.snd heq.symm
    change bulkRadialMass a * (vacuumInvariantDerivative A B).1 = 0 at h₁
    change bulkBiaxialMass a * (vacuumInvariantDerivative A B).2 = 0 at h₂
    exact Prod.ext ((mul_eq_zero.mp h₁).resolve_left (bulkRadialMass_pos a).ne')
      ((mul_eq_zero.mp h₂).resolve_left (bulkBiaxialMass_pos a).ne')
  · intro h
    rw [bulkForceLinearization_eq_normalCoordinates a A, h]
    simp only [Prod.fst_zero, Prod.snd_zero, mul_zero]
    exact map_zero (vacuumInvariantRightInverse a A)

theorem bulkForceLinearization_rank {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    Module.finrank ℝ (bulkForceLinearization a A).range = 2 := by
  letI : FiniteDimensional ℝ S0 := Module.Finite.of_basis frobeniusBasis
  have hS0 : Module.finrank ℝ S0 = 5 :=
    frobeniusCoordinateEquiv.toLinearEquiv.finrank_eq.trans finrank_euclideanSpace_fin
  have hRank := LinearMap.finrank_range_add_finrank_ker (bulkForceLinearization a A).toLinearMap
  rw [bulkForceLinearization_ker hA, vacuumInvariantKernel_finrank hA, hS0] at hRank
  omega

/-- The inverse normal masses acting on the invariant trace coordinates. -/
def bulkForceNormalInverse (a : BulkCoefficients) (A : S0) : S0 →L[ℝ] S0 :=
  (vacuumInvariantRightInverse a A).comp
    ((((bulkRadialMass a)⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      ((bulkBiaxialMass a)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)).comp (vacuumInvariantDerivative A))

theorem bulkForceNormalInverse_apply (a : BulkCoefficients) (A B : S0) :
    bulkForceNormalInverse a A B = vacuumInvariantRightInverse a A
      ((bulkRadialMass a)⁻¹ * (vacuumInvariantDerivative A B).1,
        (bulkBiaxialMass a)⁻¹ * (vacuumInvariantDerivative A B).2) := rfl

theorem bulkForceNormalInverse_comp_linearization {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    (bulkForceNormalInverse a A).comp (bulkForceLinearization a A) = vacuumNormalProjector a A := by
  apply ContinuousLinearMap.ext
  intro B
  change bulkForceNormalInverse a A (bulkForceLinearization a A B) = _
  rw [bulkForceNormalInverse_apply, vacuumInvariantDerivative_bulkForceLinearization hA]
  have h₁ := (bulkRadialMass_pos a).ne'
  have h₂ := (bulkBiaxialMass_pos a).ne'
  simp [h₁, h₂, vacuumNormalProjector]

theorem bulkForceLinearization_comp_normalInverse {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    (bulkForceLinearization a A).comp (bulkForceNormalInverse a A) = vacuumNormalProjector a A := by
  apply ContinuousLinearMap.ext
  intro B
  change bulkForceLinearization a A (bulkForceNormalInverse a A B) = _
  rw [bulkForceLinearization_eq_normalCoordinates a A, bulkForceNormalInverse_apply,
    vacuumInvariantRightInverse_isRightInverse hA]
  have h₁ := (bulkRadialMass_pos a).ne'
  have h₂ := (bulkBiaxialMass_pos a).ne'
  simp [h₁, h₂, vacuumNormalProjector]

/-- The span of the vacuum tensor and the trace-free square. -/
def vacuumNormalSpace (A : S0) : Submodule ℝ S0 :=
  Submodule.span ℝ {A, traceFreeSquare A}

theorem vacuumNormalProjector_range {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    (vacuumNormalProjector a A).range = vacuumNormalSpace A := by
  have hA₀ : A ∈ vacuumNormalSpace A := Submodule.subset_span (by simp)
  have hA₂ : traceFreeSquare A ∈ vacuumNormalSpace A := Submodule.subset_span (by simp)
  apply le_antisymm
  · rintro B ⟨C, rfl⟩
    change vacuumInvariantRightInverse a A (vacuumInvariantDerivative A C) ∈ vacuumNormalSpace A
    rw [vacuumInvariantRightInverse_apply]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hA₀) (Submodule.smul_mem _ _ hA₂)
  · rw [vacuumNormalSpace, Submodule.span_le]
    intro C hC
    simp only [mem_insert_iff, mem_singleton_iff] at hC
    rcases hC with h | h
    · subst C
      exact LinearMap.mem_range.mpr ⟨A, vacuumNormalProjector_apply_self hA⟩
    · subst C
      exact LinearMap.mem_range.mpr ⟨traceFreeSquare A, vacuumNormalProjector_apply_traceFreeSquare hA⟩

theorem vacuumNormalProjector_eq_self_of_mem {a : BulkCoefficients} {A B : S0}
    (hA : A ∈ vacuum a) (hB : B ∈ vacuumNormalSpace A) : vacuumNormalProjector a A B = B := by
  rw [← vacuumNormalProjector_range hA] at hB
  obtain ⟨C, rfl⟩ := hB
  exact DFunLike.congr_fun (vacuumNormalProjector_idempotent hA) C

theorem bulkForceLinearization_normalInverse_of_mem {a : BulkCoefficients} {A B : S0}
    (hA : A ∈ vacuum a) (hB : B ∈ vacuumNormalSpace A) :
    bulkForceLinearization a A (bulkForceNormalInverse a A B) = B :=
  (DFunLike.congr_fun (bulkForceLinearization_comp_normalInverse hA) B).trans
    (vacuumNormalProjector_eq_self_of_mem hA hB)

theorem bulkForceNormalInverse_linearization_of_mem {a : BulkCoefficients} {A B : S0}
    (hA : A ∈ vacuum a) (hB : B ∈ vacuumNormalSpace A) :
    bulkForceNormalInverse a A (bulkForceLinearization a A B) = B :=
  (DFunLike.congr_fun (bulkForceNormalInverse_comp_linearization hA) B).trans
    (vacuumNormalProjector_eq_self_of_mem hA hB)

theorem bulkForceLinearization_range {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    (bulkForceLinearization a A).range = vacuumNormalSpace A := by
  apply le_antisymm
  · rintro _ ⟨B, rfl⟩
    rw [← vacuumNormalProjector_range hA]
    refine LinearMap.mem_range.mpr ⟨bulkForceLinearization a A B, ?_⟩
    change vacuumInvariantRightInverse a A (vacuumInvariantDerivative A (bulkForceLinearization a A B)) =
      bulkForceLinearization a A B
    rw [vacuumInvariantDerivative_bulkForceLinearization hA, bulkForceLinearization_eq_normalCoordinates a A]
  · intro B hB
    exact LinearMap.mem_range.mpr ⟨bulkForceNormalInverse a A B,
      bulkForceLinearization_normalInverse_of_mem hA hB⟩

theorem harmonicRhs_eq_invariantRightInverse {a : BulkCoefficients} {Q : Point → S0}
    (D : Point → Gradient) {x : Point} (hQ : Q x ∈ vacuum a) :
    harmonicRhs a Q D x = (vacuumInvariantRightInverse a (Q x)
      (-2 * gradientNormSq (D x), -6 * gradientTraceMul D D (Q x) x) : Tensor) := by
  let r := vacuumRadius a
  let g := gradientNormSq (D x)
  let t := gradientTraceMul D D (Q x) x
  have hr : 0 < r := vacuumRadius_pos a
  have h₁ : (-2 * g) / (4 * r ^ 2) = -(g / (2 * r ^ 2)) := by
    apply (div_eq_iff (by positivity : (4 * r ^ 2 : ℝ) ≠ 0)).2
    field_simp
    ring
  have h₂ : (-6 * t) / (2 * r ^ 4) = -(3 / r ^ 4 * t) := by
    apply (div_eq_iff (by positivity : (2 * r ^ 4 : ℝ) ≠ 0)).2
    field_simp
    ring
  rw [vacuumInvariantRightInverse_apply]
  change (-(g / (2 * r ^ 2))) • (Q x : Tensor) - (3 / r ^ 4 * t) • biaxialQuadratic a (Q x : Tensor) =
    ((-2 * g) / (4 * r ^ 2)) • (Q x : Tensor) + ((-6 * t) / (2 * r ^ 4)) • (traceFreeSquare (Q x) : Tensor)
  rw [h₁, h₂, traceFreeSquare_coe_eq_biaxialQuadratic hQ, sub_eq_add_neg]
  simp only [neg_smul]

/-- The two scalar components of a correction satisfying the first linearized bulk equation. -/
theorem firstCorrection_trace_coefficients {a : BulkCoefficients} {Q P : Point → S0}
    (D : Point → Gradient) {x : Point} (hQ : Q x ∈ vacuum a)
    (hEq : ((fderiv ℝ (bulkForce a) (Q x) (P x)) : Tensor) = harmonicRhs a Q D x) :
    ((Q x : Tensor) * (P x : Tensor)).trace =
      -(gradientNormSq (D x) / (4 * vacuumRadius a ^ 2 * (a.a4 + 4 * a.a6 * vacuumRadius a ^ 2))) ∧
    (((Q x : Tensor) ^ 2) * (P x : Tensor)).trace =
      -(gradientTraceMul D D (Q x) x / (a.a6' * vacuumRadius a ^ 4)) := by
  let g := gradientNormSq (D x)
  let t := gradientTraceMul D D (Q x) x
  let b₁ := ((Q x : Tensor) * (P x : Tensor)).trace
  let b₂ := (((Q x : Tensor) ^ 2) * (P x : Tensor)).trace
  let v := (-2 * g, -6 * t)
  have hF := DFunLike.congr_fun (fderiv_bulkForce_at_vacuum hQ) (P x)
  have hLinear : bulkForceLinearization a (Q x) (P x) = vacuumInvariantRightInverse a (Q x) v :=
    Subtype.ext ((congrArg Subtype.val hF).symm.trans (hEq.trans (harmonicRhs_eq_invariantRightInverse D hQ)))
  have hCoord := congrArg (vacuumInvariantDerivative (Q x)) hLinear
  rw [vacuumInvariantDerivative_bulkForceLinearization hQ, vacuumInvariantRightInverse_isRightInverse hQ,
    vacuumInvariantDerivative_apply] at hCoord
  have h₁ := congrArg Prod.fst hCoord
  have h₂ := congrArg Prod.snd hCoord
  change bulkRadialMass a * (2 * b₁) = -2 * g at h₁
  change bulkBiaxialMass a * (3 * b₂) = -6 * t at h₂
  have hm₁ := (bulkRadialMass_pos a).ne'
  have hr := vacuumRadius_pos a
  have ha6' := a.a6'_pos
  have hm₂ : a.a6' * vacuumRadius a ^ 4 ≠ 0 := by positivity
  change b₁ = -(g / bulkRadialMass a) ∧ b₂ = -(t / (a.a6' * vacuumRadius a ^ 4))
  rw [← neg_div, ← neg_div, eq_div_iff hm₁, eq_div_iff hm₂]
  constructor
  · linarith only [h₁]
  · unfold bulkBiaxialMass at h₂
    linarith only [h₂]

theorem normalPart_eq_trace_formula (a : BulkCoefficients) (A B : Tensor) :
    normalPart a A B = (((A * B).trace) / (2 * vacuumRadius a ^ 2)) • A +
      (((A ^ 2 * B).trace) / (2 * vacuumRadius a ^ 4)) •
        ((3 : ℝ) • A ^ 2 - (2 * vacuumRadius a ^ 2) • (1 : Tensor)) := by
  unfold normalPart biaxialQuadratic
  have h : (3 : ℝ) * (2 * vacuumRadius a ^ 2 / 3) = 2 * vacuumRadius a ^ 2 := by ring
  rw [smul_sub, smul_smul, h]

private theorem tensor_sq_add_smul (A B : Tensor) (t : ℝ) :
    (A + t • B) ^ 2 = A ^ 2 + t • (A * B + B * A) + t ^ 2 • B ^ 2 := by
  simp only [pow_two, Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, smul_add]
  abel

theorem trace_sq_add_smul (A B : S0) (t : ℝ) :
    (((A + t • B : S0) : Tensor) ^ 2).trace =
      ((A : Tensor) ^ 2).trace + 2 * t * ((A : Tensor) * (B : Tensor)).trace +
        t ^ 2 * ((B : Tensor) ^ 2).trace := by
  change (((A : Tensor) + t • (B : Tensor)) ^ 2).trace = _
  rw [tensor_sq_add_smul]
  simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
    Matrix.trace_mul_comm (B : Tensor) (A : Tensor)]
  ring

theorem trace_cube_add_smul (A B : S0) (t : ℝ) :
    (((A + t • B : S0) : Tensor) ^ 3).trace =
      ((A : Tensor) ^ 3).trace + 3 * t * (((A : Tensor) ^ 2) * (B : Tensor)).trace +
        3 * t ^ 2 * ((A : Tensor) * ((B : Tensor) ^ 2)).trace + t ^ 3 * ((B : Tensor) ^ 3).trace := by
  let X : Tensor := A
  let Y : Tensor := B
  change ((X + t • Y) ^ 3).trace = (X ^ 3).trace + 3 * t * (X ^ 2 * Y).trace +
    3 * t ^ 2 * (X * Y ^ 2).trace + t ^ 3 * (Y ^ 3).trace
  have h₁ : (X * Y * X).trace = (X ^ 2 * Y).trace := by
    rw [pow_two, Matrix.trace_mul_cycle]
  have h₂ : (Y * X * X).trace = (X ^ 2 * Y).trace := (Matrix.trace_mul_cycle Y X X).trans h₁
  have h₃ : (Y * X * Y).trace = (X * Y ^ 2).trace := by
    rw [pow_two, Matrix.trace_mul_cycle, Matrix.trace_mul_comm (Y * Y) X]
  have h₄ : (X * Y * Y).trace = (X * Y ^ 2).trace := by rw [pow_two, mul_assoc]
  rw [pow_succ _ 2, tensor_sq_add_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, h₁, h₂, h₃, h₄,
    Matrix.trace_mul_comm (Y ^ 2) X, ← pow_succ X 2, ← pow_succ Y 2]
  ring

/-- The trace-free symmetrized product arising in the first variation of the square. -/
def traceFreeJordan (A B : S0) : S0 :=
  traceFreeSymmetricPart ((A : Tensor) * (B : Tensor) + (B : Tensor) * (A : Tensor))

theorem traceFreeJordan_coe (A B : S0) :
    (traceFreeJordan A B : Tensor) = (A : Tensor) * (B : Tensor) + (B : Tensor) * (A : Tensor) -
      (2 / 3 * ((A : Tensor) * (B : Tensor)).trace) • (1 : Tensor) := by
  let M := (A : Tensor) * (B : Tensor) + (B : Tensor) * (A : Tensor)
  have hM : Mᵀ = M := by
    simp only [M, Matrix.transpose_add, Matrix.transpose_mul, A.transpose_eq, B.transpose_eq]
    exact add_comm _ _
  change (1 / 2 : ℝ) • (M + Mᵀ) - (M.trace / 3) • (1 : Tensor) =
    M - (2 / 3 * ((A : Tensor) * (B : Tensor)).trace) • (1 : Tensor)
  have htrace : M.trace / 3 = 2 / 3 * ((A : Tensor) * (B : Tensor)).trace := by
    dsimp only [M]
    rw [Matrix.trace_add, Matrix.trace_mul_comm (B : Tensor) (A : Tensor)]
    ring
  rw [hM, ← two_smul ℝ, smul_smul, htrace]
  norm_num

theorem normalPart_traceFreeJordan {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) (B : S0) :
    normalPart a (A : Tensor) (traceFreeJordan A B : Tensor) =
      ((((A : Tensor) ^ 2 * (B : Tensor)).trace) / vacuumRadius a ^ 2) • (A : Tensor) +
      ((((A : Tensor) * (B : Tensor)).trace) / vacuumRadius a ^ 2) • biaxialQuadratic a (A : Tensor) := by
  let X : Tensor := A
  let Y : Tensor := B
  let J : Tensor := traceFreeJordan A B
  let r := vacuumRadius a
  let u := (X * Y).trace
  let w := (X ^ 2 * Y).trace
  have hJ : J = X * Y + Y * X - (2 / 3 * u) • (1 : Tensor) := traceFreeJordan_coe A B
  have hX : X.trace = 0 := A.trace_eq_zero
  have hX₂ : (X ^ 2).trace = 2 * r ^ 2 := (vacuum_traces hA).1
  have hX₃ : X ^ 3 = r ^ 2 • X := vacuum_cube hA
  have hTrace₁ : (X * J).trace = 2 * w := by
    rw [hJ, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, mul_one, Matrix.trace_sub,
      Matrix.trace_add, Matrix.trace_smul, hX, smul_zero, sub_zero, ← mul_assoc, ← mul_assoc,
      Matrix.trace_mul_cycle X Y X, ← pow_two]
    change w + w = 2 * w
    ring
  have hLeft : (X ^ 2 * (X * Y)).trace = r ^ 2 * u := by
    rw [← mul_assoc, ← pow_succ, hX₃, Matrix.smul_mul, Matrix.trace_smul]
    rfl
  have hRight : (X ^ 2 * (Y * X)).trace = r ^ 2 * u := by
    rw [Matrix.trace_mul_comm (X ^ 2), mul_assoc, ← pow_succ', hX₃, Matrix.mul_smul,
      Matrix.trace_smul, Matrix.trace_mul_comm Y X]
    rfl
  have hTrace₂ : (X ^ 2 * J).trace = (2 / 3 : ℝ) * r ^ 2 * u := by
    rw [hJ, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, mul_one, Matrix.trace_sub,
      Matrix.trace_add, Matrix.trace_smul, hLeft, hRight, hX₂, smul_eq_mul]
    ring
  have hr : r ≠ 0 := (vacuumRadius_pos a).ne'
  have h₁ : (2 * w) / (2 * r ^ 2) = w / r ^ 2 := by field_simp
  have h₂ : ((2 / 3 : ℝ) * r ^ 2 * u) / (2 * r ^ 4) * 3 = u / r ^ 2 := by
    field_simp
  change ((X * J).trace / (2 * r ^ 2)) • X +
      ((X ^ 2 * J).trace / (2 * r ^ 4)) • (3 : ℝ) • biaxialQuadratic a X =
    (w / r ^ 2) • X + (u / r ^ 2) • biaxialQuadratic a X
  rw [hTrace₁, hTrace₂, smul_smul, h₁, h₂]

theorem traceFreeSquare_add_smul (A B : S0) (t : ℝ) :
    traceFreeSquare (A + t • B) = traceFreeSquare A + t • traceFreeJordan A B + t ^ 2 • traceFreeSquare B := by
  change traceFreeSymmetricPartLinear (((A : Tensor) + t • (B : Tensor)) ^ 2) = _
  rw [tensor_sq_add_smul, map_add, map_add, map_smul, map_smul]
  rfl

/-- The coefficient of the second power of the perturbation parameter in the bulk force. -/
def bulkForceQuadraticTerm (a : BulkCoefficients) (A B : S0) : S0 :=
  let u := ((A : Tensor) * (B : Tensor)).trace
  let v := ((B : Tensor) ^ 2).trace
  let w := (((A : Tensor) ^ 2) * (B : Tensor)).trace
  let z := ((A : Tensor) * (B : Tensor) ^ 2).trace
  (2 * bulkRadialCoefficient a * u) • B + (bulkRadialCoefficient a * v + 4 * a.a6 * u ^ 2) • A +
    (3 * a.a6' * z) • traceFreeSquare A + (3 * a.a6' * w) • traceFreeJordan A B

/-- The tangent projection complementary to the two invariant normal directions. -/
def vacuumTangentProjector (a : BulkCoefficients) (A : S0) : S0 →L[ℝ] S0 :=
  ContinuousLinearMap.id ℝ S0 - vacuumNormalProjector a A

theorem tangentPart_eq_vacuumTangentProjector {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) (B : S0) :
    tangentPart a (A : Tensor) (B : Tensor) = (vacuumTangentProjector a A B : Tensor) := by
  rw [tangentPart, normalPart_eq_vacuumNormalProjector hA]
  rfl

theorem tangentPart_bulkForceLinearization {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) (B : S0) :
    tangentPart a (A : Tensor) (bulkForceLinearization a A B : Tensor) = 0 := by
  have hN : bulkForceLinearization a A B ∈ vacuumNormalSpace A := by
    rw [← bulkForceLinearization_range hA]
    exact LinearMap.mem_range_self _ _
  rw [tangentPart, normalPart_eq_vacuumNormalProjector hA, vacuumNormalProjector_eq_self_of_mem hA hN,
    sub_self]

theorem tangentPart_bulkForceQuadraticTerm {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) (B : S0) :
    tangentPart a (A : Tensor) (bulkForceQuadraticTerm a A B : Tensor) =
      (2 * bulkRadialCoefficient a * ((A : Tensor) * (B : Tensor)).trace) •
        tangentPart a (A : Tensor) (B : Tensor) +
      (3 * a.a6' * (((A : Tensor) ^ 2) * (B : Tensor)).trace) •
        tangentPart a (A : Tensor) (traceFreeJordan A B : Tensor) := by
  let T := vacuumTangentProjector a A
  have hX : T A = 0 := by
    change A - vacuumNormalProjector a A A = 0
    rw [vacuumNormalProjector_apply_self hA, sub_self]
  have hX₂ : T (traceFreeSquare A) = 0 := by
    change traceFreeSquare A - vacuumNormalProjector a A (traceFreeSquare A) = 0
    rw [vacuumNormalProjector_apply_traceFreeSquare hA, sub_self]
  have hQ : T (bulkForceQuadraticTerm a A B) =
      (2 * bulkRadialCoefficient a * ((A : Tensor) * (B : Tensor)).trace) • T B +
      (3 * a.a6' * (((A : Tensor) ^ 2) * (B : Tensor)).trace) • T (traceFreeJordan A B) := by
    simp [bulkForceQuadraticTerm, map_add, map_smul, hX, hX₂]
  simp only [tangentPart_eq_vacuumTangentProjector hA]
  exact congrArg Subtype.val hQ

/-- The polynomial remaining after factoring the third power of the perturbation parameter. -/
def bulkForcePolynomialRemainder (a : BulkCoefficients) (A B : S0) (t : ℝ) : S0 :=
  let u := ((A : Tensor) * (B : Tensor)).trace
  let v := ((B : Tensor) ^ 2).trace
  let w := (((A : Tensor) ^ 2) * (B : Tensor)).trace
  let z := ((A : Tensor) * (B : Tensor) ^ 2).trace
  let s := ((B : Tensor) ^ 3).trace
  let c₂ := bulkRadialCoefficient a * v + 4 * a.a6 * u ^ 2
  let c₃ := 4 * a.a6 * u * v
  let c₄ := a.a6 * v ^ 2
  (c₃ + t * c₄) • A + (c₂ + t * c₃ + t ^ 2 * c₄) • B +
    a.a6' • ((3 * w) • traceFreeSquare B + (3 * z) • (traceFreeJordan A B + t • traceFreeSquare B) +
      s • (traceFreeSquare A + t • traceFreeJordan A B + t ^ 2 • traceFreeSquare B))

/-- The exact finite expansion of the sextic bulk force about a vacuum tensor. -/
theorem bulkForce_polynomial_expansion {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a)
    (B : S0) (t : ℝ) :
    bulkForce a (A + t • B) = t • bulkForceLinearization a A B + t ^ 2 • bulkForceQuadraticTerm a A B +
      t ^ 3 • bulkForcePolynomialRemainder a A B t := by
  let u := ((A : Tensor) * (B : Tensor)).trace
  let v := ((B : Tensor) ^ 2).trace
  let T := 2 * vacuumRadius a ^ 2 + 2 * t * u + t ^ 2 * v
  have hRad : -a.a2 + a.a4 * T + a.a6 * T ^ 2 =
      t * (2 * bulkRadialCoefficient a * u) + t ^ 2 * (bulkRadialCoefficient a * v + 4 * a.a6 * u ^ 2) +
      t ^ 3 * (4 * a.a6 * u * v) + t ^ 4 * (a.a6 * v ^ 2) := by
    dsimp only [T, bulkRadialCoefficient]
    linear_combination vacuumRadius_equation a
  rw [bulkForce_eq_smul_components, traceFreeSquare_add_smul]
  simp only [vacuumInvariants]
  rw [trace_sq_add_smul, trace_cube_add_smul, (vacuum_traces hA).1, (vacuum_traces hA).2, zero_add,
    bulkForceLinearization_apply]
  have hRad' : -a.a2 + a.a4 * (2 * vacuumRadius a ^ 2 + 2 * t * u + t ^ 2 * v) +
        a.a6 * (2 * vacuumRadius a ^ 2 + 2 * t * u + t ^ 2 * v) ^ 2 = _ := hRad
  rw [hRad']
  unfold bulkForceQuadraticTerm bulkForcePolynomialRemainder
  apply Subtype.ext
  ext i j
  simp only [Submodule.coe_add, Submodule.coe_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  dsimp only [u, v]
  ring

/-- The expansion at the scale used for the first correction in the Euler–Lagrange equation. -/
theorem bulkForce_scaled_expansion {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a)
    (B : S0) (ε : ElasticScale) :
    ((ε.val ^ 2)⁻¹ : ℝ) • bulkForce a (A + ε.val ^ 2 • B) =
      bulkForceLinearization a A B + ε.val ^ 2 • bulkForceQuadraticTerm a A B +
        ε.val ^ 4 • bulkForcePolynomialRemainder a A B (ε.val ^ 2) := by
  let s := ε.val
  have hs : 0 < s := ε.property.1
  have h₁ : (s ^ 2)⁻¹ * s ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
  have h₂ : (s ^ 2)⁻¹ * (s ^ 2) ^ 2 = s ^ 2 := by field_simp
  have h₃ : (s ^ 2)⁻¹ * (s ^ 2) ^ 3 = s ^ 4 := by field_simp
  change ((s ^ 2)⁻¹ : ℝ) • bulkForce a (A + s ^ 2 • B) = _
  rw [bulkForce_polynomial_expansion hA]
  simp only [smul_add, smul_smul, h₁, h₂, h₃, one_smul]
  rfl

/-- The tangent projection removes the entire order-two term in the bulk force. -/
theorem tangentPart_bulkForce_fourth_scale {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) (B : S0) (ε : ElasticScale) :
    ((ε.val ^ 4)⁻¹ : ℝ) • tangentPart a (A : Tensor) (bulkForce a (A + ε.val ^ 2 • B) : Tensor) =
      tangentPart a (A : Tensor) (bulkForceQuadraticTerm a A B : Tensor) +
        ε.val ^ 2 • tangentPart a (A : Tensor)
          (bulkForcePolynomialRemainder a A B (ε.val ^ 2) : Tensor) := by
  let s := ε.val
  let T := vacuumTangentProjector a A
  have hs : 0 < s := ε.property.1
  have hL : T (bulkForceLinearization a A B) = 0 := by
    apply Subtype.ext
    exact (tangentPart_eq_vacuumTangentProjector hA _).symm.trans (tangentPart_bulkForceLinearization hA B)
  have hT : T (bulkForce a (A + s ^ 2 • B)) =
      (s ^ 2) ^ 2 • T (bulkForceQuadraticTerm a A B) +
        (s ^ 2) ^ 3 • T (bulkForcePolynomialRemainder a A B (s ^ 2)) := by
    rw [bulkForce_polynomial_expansion hA]
    simp [map_add, map_smul, hL]
  have h₁ : (s ^ 4)⁻¹ * (s ^ 2) ^ 2 = 1 := by field_simp
  have h₂ : (s ^ 4)⁻¹ * (s ^ 2) ^ 3 = s ^ 2 := by field_simp
  have hScaled : ((s ^ 4)⁻¹ : ℝ) • T (bulkForce a (A + s ^ 2 • B)) =
      T (bulkForceQuadraticTerm a A B) + s ^ 2 • T (bulkForcePolynomialRemainder a A B (s ^ 2)) := by
    rw [hT]
    simp only [smul_add, smul_smul, h₁, h₂, one_smul]
  simp only [tangentPart_eq_vacuumTangentProjector hA]
  exact congrArg Subtype.val hScaled

theorem contDiff_bulkForcePolynomialRemainder (a : BulkCoefficients) :
    ContDiff ℝ ∞ (fun p : S0 × S0 × ℝ => bulkForcePolynomialRemainder a p.1 p.2.1 p.2.2) := by
  have htrace (A : Tensor) : tensorTraceCLM A = A.trace := rfl
  have hval (A : S0) : symmetricTraceless.subtypeL A = (A : Tensor) := rfl
  simp only [bulkForcePolynomialRemainder, traceFreeJordan, traceFreeSquare,
    ← traceFreeSymmetricPartCLM_apply, ← htrace, ← hval]
  fun_prop

theorem contDiff_bulkForceQuadraticTerm (a : BulkCoefficients) :
    ContDiff ℝ ∞ (fun p : S0 × S0 => bulkForceQuadraticTerm a p.1 p.2) := by
  have htrace (A : Tensor) : tensorTraceCLM A = A.trace := rfl
  have hval (A : S0) : symmetricTraceless.subtypeL A = (A : Tensor) := rfl
  simp only [bulkForceQuadraticTerm, traceFreeJordan, traceFreeSquare,
    ← traceFreeSymmetricPartCLM_apply, ← htrace, ← hval]
  fun_prop

theorem exists_norm_bound_bulkForcePolynomialRemainder (a : BulkCoefficients)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ A ∈ vacuum a, ∀ B : S0, ‖B‖ ≤ M →
      ∀ t ∈ Icc (-1 : ℝ) 1, ‖bulkForcePolynomialRemainder a A B t‖ ≤ C := by
  let E := EuclideanSpace ℝ (Fin 5)
  let e := frobeniusCoordinateEquiv
  let K : Set (E × E × ℝ) := (e '' vacuum a) ×ˢ (Metric.closedBall 0 M ×ˢ Icc (-1 : ℝ) 1)
  have hK : IsCompact K := (isCompact_coordinateVacuum a).prod
    ((isCompact_closedBall (0 : E) M).prod isCompact_Icc)
  obtain ⟨A₀, hA₀⟩ := vacuum_nonempty a
  have hK₀ : K.Nonempty := ⟨(e A₀, 0, 0), mem_image_of_mem e hA₀,
    Metric.mem_closedBall_self hM, by norm_num, by norm_num⟩
  let f (p : E × E × ℝ) := ‖e (bulkForcePolynomialRemainder a (e.symm p.1) (e.symm p.2.1) p.2.2)‖
  have hInv : Continuous (fun p : E × E × ℝ => (e.symm p.1, e.symm p.2.1, p.2.2)) :=
    (e.symm.continuous.comp continuous_fst).prodMk
      ((e.symm.continuous.comp continuous_snd.fst).prodMk continuous_snd.snd)
  have hf : Continuous f :=
    (e.continuous.comp ((contDiff_bulkForcePolynomialRemainder a).continuous.comp hInv)).norm
  obtain ⟨p, _, hp⟩ := hK.exists_isMaxOn hK₀ hf.continuousOn
  have hFp : 0 ≤ f p := norm_nonneg _
  refine ⟨f p + 1, by linarith, ?_⟩
  intro A hA B hB t ht
  have hBall : e B ∈ Metric.closedBall 0 M := by
    rw [Metric.mem_closedBall, dist_zero_right, e.norm_map]
    exact hB
  have hX : (e A, e B, t) ∈ K := ⟨mem_image_of_mem e hA, hBall, ht⟩
  have hF := hp hX
  change ‖e (bulkForcePolynomialRemainder a (e.symm (e A)) (e.symm (e B)) t)‖ ≤ f p at hF
  rw [e.symm_apply_apply, e.symm_apply_apply, e.norm_map] at hF
  linarith only [hF]

theorem bulkForce_scaled_expansion_remainder_bound (a : BulkCoefficients) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ A ∈ vacuum a, ∀ B : S0, ‖B‖ ≤ M → ∀ ε : ElasticScale,
      ‖((ε.val ^ 2)⁻¹ : ℝ) • bulkForce a (A + ε.val ^ 2 • B) -
        (bulkForceLinearization a A B + ε.val ^ 2 • bulkForceQuadraticTerm a A B)‖ ≤ C * ε.val ^ 4 := by
  obtain ⟨C, hC, hR⟩ := exists_norm_bound_bulkForcePolynomialRemainder a hM
  refine ⟨C, hC, ?_⟩
  intro A hA B hB ε
  have hε₂ : ε.val ^ 2 ∈ Icc (-1 : ℝ) 1 := by
    refine ⟨(show (-1 : ℝ) ≤ 0 by norm_num).trans (sq_nonneg _), ?_⟩
    simpa only [one_pow] using pow_le_pow_left₀ ε.property.1.le ε.property.2.le 2
  have h := hR A hA B hB (ε.val ^ 2) hε₂
  rw [bulkForce_scaled_expansion hA, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ ε.val ^ 4)]
  rw [mul_comm C]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem tendsto_scaled_bulkForce {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a)
    {ι : Type*} {F : Filter ι} {B : ι → S0} {B₀ : S0} {ε : ι → ElasticScale}
    (hε : Tendsto (fun n => (ε n).val) F (𝓝 0)) (hB : Tendsto B F (𝓝 B₀)) :
    Tendsto (fun n => (((ε n).val ^ 2)⁻¹ : ℝ) • bulkForce a (A + (ε n).val ^ 2 • B n)) F
      (𝓝 (fderiv ℝ (bulkForce a) A B₀)) := by
  let G (p : ℝ × S0) :=
    bulkForceLinearization a A p.2 + p.1 ^ 2 • bulkForceQuadraticTerm a A p.2 +
      p.1 ^ 4 • bulkForcePolynomialRemainder a A p.2 (p.1 ^ 2)
  have ht : ContDiff ℝ ∞ (fun p : ℝ × S0 => p.1) := contDiff_fst
  have hP : ContDiff ℝ ∞ (fun p : ℝ × S0 => p.2) := contDiff_snd
  have hAconst : ContDiff ℝ ∞ (fun _ : ℝ × S0 => A) := contDiff_const
  have hL : ContDiff ℝ ∞ (fun p : ℝ × S0 => bulkForceLinearization a A p.2) :=
    (bulkForceLinearization a A).contDiff.comp hP
  have hAB : ContDiff ℝ ∞ (fun p : ℝ × S0 => (A, p.2)) := hAconst.prodMk hP
  have hABt : ContDiff ℝ ∞ (fun p : ℝ × S0 => (A, p.2, p.1 ^ 2)) :=
    hAconst.prodMk (hP.prodMk (ht.pow 2))
  have hQ := (contDiff_bulkForceQuadraticTerm a).comp hAB
  have hR := (contDiff_bulkForcePolynomialRemainder a).comp hABt
  have hG' := (hL.add ((ht.pow 2).smul hQ)).add ((ht.pow 4).smul hR)
  have hG : ContDiff ℝ ∞ G := hG'
  have hLimit : G (0, B₀) = fderiv ℝ (bulkForce a) A B₀ := by
    simp only [G, zero_pow two_ne_zero, zero_pow (by decide : 4 ≠ 0), zero_smul, add_zero]
    exact (DFunLike.congr_fun (fderiv_bulkForce_at_vacuum hA) B₀).symm
  have hT := (hG.continuous.tendsto ((0 : ℝ), B₀)).comp (hε.prodMk_nhds hB)
  rw [hLimit] at hT
  exact hT.congr' (Filter.Eventually.of_forall fun n => (bulkForce_scaled_expansion hA (B n) (ε n)).symm)

/-- The limit of the scaled Euler–Lagrange force is the actual linearized force. -/
theorem linearized_bulkForce_eq_of_scaled_limit {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a)
    {ι : Type*} {F : Filter ι} [F.NeBot] {B Δ : ι → S0} {B₀ Δ₀ : S0} {ε : ι → ElasticScale}
    (hε : Tendsto (fun n => (ε n).val) F (𝓝 0)) (hB : Tendsto B F (𝓝 B₀))
    (hΔ : Tendsto Δ F (𝓝 Δ₀))
    (hEq : ∀ᶠ n in F, (((ε n).val ^ 2)⁻¹ : ℝ) • bulkForce a (A + (ε n).val ^ 2 • B n) = Δ n) :
    fderiv ℝ (bulkForce a) A B₀ = Δ₀ := by
  have hEq' : (fun n => (((ε n).val ^ 2)⁻¹ : ℝ) • bulkForce a (A + (ε n).val ^ 2 • B n)) =ᶠ[F] Δ := hEq
  exact tendsto_nhds_unique (tendsto_scaled_bulkForce hA hε hB) (hΔ.congr' hEq'.symm)

end Thesis

end

end

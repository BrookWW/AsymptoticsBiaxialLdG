module

public import Thesis.Foundation.WeakGradient
public import Thesis.Foundation.BulkGeometry
public import Thesis.Foundation.Frobenius
public import Thesis.StressEnergy

/-! First variation of the sextic energy, the weak Euler–Lagrange equation, and
interior regularity of bounded minimizers from Poisson estimates. -/

public section

open Set Filter MeasureTheory Topology
open scoped BigOperators ContDiff Manifold Matrix Matrix.Norms.Frobenius

set_option autoImplicit false

noncomputable section

namespace Thesis

-- Use the Frobenius normed structures for the inherited product topologies.
local instance eulerLagrangeContinuousENormS0 : ContinuousENorm S0 := @SeminormedAddGroup.toContinuousENorm S0 inferInstance
local instance : ContinuousENorm Tensor := @SeminormedAddGroup.toContinuousENorm Tensor inferInstance

variable {Ω : Set Point}

private noncomputable def traceL : Tensor →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap

private def PolynomialGrowth {E : Type*} [SeminormedAddCommGroup E] (f : S0 → E) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ A, ‖f A‖ ≤ C * (1 + ‖A‖) ^ n

private theorem PolynomialGrowth.const {E : Type*} [SeminormedAddCommGroup E] (e : E) :
    PolynomialGrowth (fun _ : S0 => e) 0 := by
  exact ⟨‖e‖, norm_nonneg _, fun _ => by rw [pow_zero, mul_one]⟩

private theorem PolynomialGrowth.val : PolynomialGrowth (fun A : S0 => (A : Tensor)) 1 :=
  ⟨1, zero_le_one, fun A => by
    change ‖A‖ ≤ 1 * (1 + ‖A‖) ^ 1
    rw [pow_one, one_mul]
    linarith⟩

private theorem PolynomialGrowth.up {E : Type*} [SeminormedAddCommGroup E] {f : S0 → E} {m n : ℕ}
    (hf : PolynomialGrowth f m) (hmn : m ≤ n) : PolynomialGrowth f n := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨C, hC, fun A => (hf A).trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
  exact pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg A)) hmn

private theorem PolynomialGrowth.add {E : Type*} [SeminormedAddCommGroup E]
    {f g : S0 → E} {n : ℕ} (hf : PolynomialGrowth f n) (hg : PolynomialGrowth g n) :
    PolynomialGrowth (fun A => f A + g A) n := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf + Cg, add_nonneg hCf hCg, fun A => ?_⟩
  rw [add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hf A) (hg A))

private theorem PolynomialGrowth.neg {E : Type*} [SeminormedAddCommGroup E]
    {f : S0 → E} {n : ℕ} (hf : PolynomialGrowth f n) :
    PolynomialGrowth (fun A => -f A) n := by
  obtain ⟨C, hC, hf⟩ := hf
  exact ⟨C, hC, fun A => by simpa only [norm_neg] using hf A⟩

private theorem PolynomialGrowth.sub {E : Type*} [SeminormedAddCommGroup E]
    {f g : S0 → E} {n : ℕ} (hf : PolynomialGrowth f n) (hg : PolynomialGrowth g n) :
    PolynomialGrowth (fun A => f A - g A) n := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

private theorem PolynomialGrowth.mul {E : Type*} [NonUnitalSeminormedRing E]
    {f g : S0 → E} {m n : ℕ} (hf : PolynomialGrowth f m) (hg : PolynomialGrowth g n) :
    PolynomialGrowth (fun A => f A * g A) (m + n) := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf * Cg, mul_nonneg hCf hCg, fun A => ?_⟩
  calc
    ‖f A * g A‖ ≤ (Cf * (1 + ‖A‖) ^ m) * (Cg * (1 + ‖A‖) ^ n) :=
      (norm_mul_le _ _).trans
        (mul_le_mul (hf A) (hg A) (norm_nonneg _) (mul_nonneg hCf (by positivity)))
    _ = _ := by rw [pow_add]; ring

private theorem PolynomialGrowth.pow {E : Type*} [SeminormedRing E]
    {f : S0 → E} {m : ℕ} (hf : PolynomialGrowth f m) (n : ℕ) :
    PolynomialGrowth (fun A => f A ^ n) (m * n) := by
  induction n with
  | zero => simpa only [pow_zero, mul_zero] using PolynomialGrowth.const (1 : E)
  | succ n h =>
    simpa only [pow_succ, Nat.mul_succ] using h.mul hf

private theorem PolynomialGrowth.smul {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {f : S0 → ℝ} {g : S0 → E} {m n : ℕ} (hf : PolynomialGrowth f m)
    (hg : PolynomialGrowth g n) : PolynomialGrowth (fun A => f A • g A) (m + n) := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf * Cg, mul_nonneg hCf hCg, fun A => ?_⟩
  rw [norm_smul]
  calc
    ‖f A‖ * ‖g A‖ ≤ (Cf * (1 + ‖A‖) ^ m) * (Cg * (1 + ‖A‖) ^ n) :=
      mul_le_mul (hf A) (hg A) (norm_nonneg _) (mul_nonneg hCf (by positivity))
    _ = _ := by rw [pow_add]; ring

private theorem PolynomialGrowth.comp_clm
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] {f : S0 → E} {n : ℕ}
    (hf : PolynomialGrowth f n) (L : E →L[ℝ] F) :
    PolynomialGrowth (fun A => L (f A)) n := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, fun A => ?_⟩
  rw [mul_assoc]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hf A) (norm_nonneg _))

private theorem polynomialGrowth_trace_pow (n : ℕ) :
    PolynomialGrowth (fun A : S0 => ((A : Tensor) ^ n).trace) n := by
  have h := (PolynomialGrowth.val.pow n).comp_clm traceL
  rw [one_mul] at h
  exact h

private theorem polynomialGrowth_bulkPotential (a : BulkCoefficients) :
    PolynomialGrowth (bulkPotential a) 6 := by
  let t₀ := preferredTraceSq a
  have hc := PolynomialGrowth.const (a.a2 / 2 * t₀ - a.a4 / 4 * t₀ ^ 2 - a.a6 / 6 * t₀ ^ 3)
  have ht := polynomialGrowth_trace_pow 2
  have hs := polynomialGrowth_trace_pow 3
  have h2 := (PolynomialGrowth.const (a.a2 / 2)).mul ht
  have h4 := (PolynomialGrowth.const (a.a4 / 4)).mul (ht.pow 2)
  have h6 := (PolynomialGrowth.const (a.a6 / 6)).mul (ht.pow 3)
  have h6' := (PolynomialGrowth.const (a.a6' / 6)).mul (hs.pow 2)
  exact (((((hc.up (by decide)).sub (h2.up (by decide))).add (h4.up (by decide))).add h6).add h6')

private theorem polynomialGrowth_bulkGradient (a : BulkCoefficients) :
    PolynomialGrowth (bulkGradient a) 5 := by
  have hu := PolynomialGrowth.val
  have ht := polynomialGrowth_trace_pow 2
  have hs := polynomialGrowth_trace_pow 3
  have hcoeff₁ :=
    (((PolynomialGrowth.const (-a.a2)).up (show 0 ≤ 4 by decide)).add
      (((PolynomialGrowth.const a.a4).mul ht).up (by decide))).add
        ((PolynomialGrowth.const a.a6).mul (ht.pow 2))
  have hcoeff₂ := (PolynomialGrowth.const a.a6').mul hs
  have ht₃ := ht.mul (PolynomialGrowth.const (3 : ℝ)⁻¹)
  have htf := (hu.pow 2).sub (ht₃.smul (PolynomialGrowth.const (1 : Tensor)))
  exact (hcoeff₁.smul hu).add (hcoeff₂.smul htf)

/-- The bulk force is bounded on each Frobenius-norm ball. -/
theorem exists_bound_bulkGradient_on_norm_le (a : BulkCoefficients) {M : ℝ} (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A : S0, ‖A‖ ≤ M → ‖bulkGradient a A‖ ≤ K := by
  obtain ⟨C, hC, h⟩ := polynomialGrowth_bulkGradient a
  refine ⟨C * (1 + M) ^ 5, mul_nonneg hC (by positivity), fun A hA => ?_⟩
  exact (h A).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1) hA) 5) hC)

private theorem integrable_shifted_norm_pow {μ : Measure Point} [IsFiniteMeasure μ]
    {u : Point → S0} {n : ℕ} (hu : MemLp u n μ) :
    Integrable (fun x => (1 + ‖u x‖) ^ n) μ := by
  have hLp : MemLp (fun x => 1 + ‖u x‖) n μ :=
    (memLp_const (1 : ℝ)).add hu.norm
  refine hLp.integrable_norm_pow'.congr (Eventually.of_forall fun x => ?_)
  exact congrArg (fun r : ℝ => r ^ n) (Real.norm_of_nonneg (by positivity))

private theorem PolynomialGrowth.integrable_comp {E : Type*} [NormedAddCommGroup E]
    {μ : Measure Point} [IsFiniteMeasure μ] {f : S0 → E} {n : ℕ}
    (hf : PolynomialGrowth f n) (hfc : Continuous f) {u : Point → S0} (hu : MemLp u n μ) :
    Integrable (fun x => f (u x)) μ := by
  obtain ⟨C, _, hbound⟩ := hf
  have hInt := (integrable_shifted_norm_pow hu).const_mul C
  have hmf : AEStronglyMeasurable (fun x => f (u x)) μ :=
    Continuous.comp_aestronglyMeasurable (β := S0) (f := u) (g := f) hfc hu.1
  exact hInt.mono' hmf (Eventually.of_forall fun x => hbound (u x))

private theorem continuous_frobenius :
    Continuous (fun X : Tensor × Tensor => frobenius X.1 X.2) := by
  change Continuous (fun X : Tensor × Tensor => traceL (X.1ᵀ * X.2))
  fun_prop

private theorem continuous_frobeniusS0 :
    Continuous (fun X : S0 × S0 => frobeniusS0 X.1 X.2) :=
  continuous_frobenius.comp
    ((symmetricTraceless.subtypeL.continuous.comp continuous_fst).prodMk
      (symmetricTraceless.subtypeL.continuous.comp continuous_snd))

private theorem frobeniusS0_add_left (A B C : S0) :
    frobeniusS0 (A + B) C = frobeniusS0 A C + frobeniusS0 B C :=
  frobenius_add_left _ _ _

private theorem frobeniusS0_smul_left (c : ℝ) (A B : S0) :
    frobeniusS0 (c • A) B = c * frobeniusS0 A B := by
  change frobenius (c • (A : Tensor)) B = c * frobenius A B
  simp [frobenius, Matrix.transpose_smul, Matrix.trace_smul, smul_eq_mul]

private theorem frobeniusS0_comm (A B : S0) : frobeniusS0 A B = frobeniusS0 B A :=
  frobenius_comm _ _

private theorem frobeniusS0_add_right (A B C : S0) :
    frobeniusS0 A (B + C) = frobeniusS0 A B + frobeniusS0 A C :=
  frobenius_add_right _ _ _

private theorem frobeniusS0_smul_right (c : ℝ) (A B : S0) :
    frobeniusS0 A (c • B) = c * frobeniusS0 A B := by
  rw [frobeniusS0_comm A, frobeniusS0_smul_left, frobeniusS0_comm B A]

private theorem abs_frobeniusS0_le (A B : S0) :
    |frobeniusS0 A B| ≤ ‖A‖ * ‖B‖ := by
  rw [← frobeniusCoordinateEquiv_inner A B]
  simpa only [LinearIsometryEquiv.norm_map] using
    abs_real_inner_le_norm (frobeniusCoordinateEquiv A) (frobeniusCoordinateEquiv B)

private theorem differentiable_bulkPotential (a : BulkCoefficients) :
    Differentiable ℝ (bulkPotential a) := by
  change Differentiable ℝ (fun B : S0 =>
    let t := traceL ((symmetricTraceless.subtypeL B) ^ 2)
    let s := traceL ((symmetricTraceless.subtypeL B) ^ 3)
    let t₀ := preferredTraceSq a
    a.a2 / 2 * t₀ - a.a4 / 4 * t₀ ^ 2 - a.a6 / 6 * t₀ ^ 3
      - a.a2 / 2 * t + a.a4 / 4 * t ^ 2 + a.a6 / 6 * t ^ 3 + a.a6' / 6 * s ^ 2)
  fun_prop

theorem contDiff_bulkGradient (a : BulkCoefficients) : ContDiff ℝ ∞ (bulkGradient a) := by
  change ContDiff ℝ ∞ (fun B : S0 =>
    let A := symmetricTraceless.subtypeL B
    let t := traceL (A ^ 2)
    (-a.a2 + a.a4 * t + a.a6 * t ^ 2) • A +
      (a.a6' * traceL (A ^ 3)) • (A ^ 2 - (t / 3) • (1 : Tensor)))
  fun_prop

private theorem continuous_bulkGradient (a : BulkCoefficients) : Continuous (bulkGradient a) :=
  (contDiff_bulkGradient a).continuous

private theorem continuous_bulkVariation (a : BulkCoefficients) :
    Continuous (fun X : S0 × S0 => frobenius (bulkGradient a X.1) X.2) :=
  continuous_frobenius.comp (((continuous_bulkGradient a).comp continuous_fst).prodMk
    (symmetricTraceless.subtypeL.continuous.comp continuous_snd))

private theorem hasDerivAt_bulkPotential_add_smul (a : BulkCoefficients)
    (A B : S0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => bulkPotential a (A + s • B))
      (frobenius (bulkGradient a (A + t • B)) B) t := by
  have hline : HasDerivAt (fun s : ℝ => A + s • B) B t := by
    simpa only [one_smul, id_eq] using! ((hasDerivAt_id t).smul_const B).const_add A
  have h := ((differentiable_bulkPotential a) (A + t • B)).hasFDerivAt.comp_hasDerivAt t hline
  have hvalue := fderiv_bulkPotential a (A + t • B) B
  exact hvalue ▸ h

private theorem hasDerivAt_half_norm_add_smul (A B : S0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1/2 : ℝ) * frobeniusS0 (A + s • B) (A + s • B))
      (frobeniusS0 (A + t • B) B) t := by
  let c₀ := (1/2 : ℝ) * frobeniusS0 A A
  let c₁ := frobeniusS0 A B
  let c₂ := (1/2 : ℝ) * frobeniusS0 B B
  have h₁ := (hasDerivAt_id t).mul_const c₁
  have h₂ := ((hasDerivAt_id t).pow 2).mul_const c₂
  have hpoly : HasDerivAt (fun s : ℝ => c₀ + s * c₁ + s ^ 2 * c₂)
      (c₁ + 2 * t * c₂) t := by
    simpa only [id_eq, Pi.pow_apply, one_mul, mul_one, zero_add, Nat.reduceSub, pow_one,
      Nat.cast_ofNat] using! ((hasDerivAt_const t c₀).fun_add h₁).fun_add h₂
  have hvalue : c₁ + 2 * t * c₂ = frobeniusS0 (A + t • B) B := by
    rw [frobeniusS0_add_left, frobeniusS0_smul_left]
    dsimp [c₁, c₂]
    ring
  refine (hvalue ▸ hpoly).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  change (1/2 : ℝ) * frobeniusS0 (A + s • B) (A + s • B) = _
  rw [frobeniusS0_add_left, frobeniusS0_add_right A, frobeniusS0_add_right (s • B),
    frobeniusS0_smul_right, frobeniusS0_smul_left, frobeniusS0_smul_left,
    frobeniusS0_smul_right, frobeniusS0_comm B A]
  dsimp [c₀, c₁, c₂]
  ring

private noncomputable def energyVariationDensity (a : BulkCoefficients) (ε : ElasticScale)
    (A B : S0) (D V : Gradient) (t : ℝ) : ℝ :=
  (∑ k : Fin 3, frobeniusS0 (D k + t • V k) (V k)) +
    (ε : ℝ)⁻¹ ^ 2 * frobenius (bulkGradient a (A + t • B)) B

private theorem hasDerivAt_energyDensity_variation (a : BulkCoefficients) (ε : ElasticScale)
    (A B : S0) (D V : Gradient) (t : ℝ) :
    HasDerivAt (fun s : ℝ => energyDensity a ε (A + s • B) (D + s • V))
      (energyVariationDensity a ε A B D V t) t := by
  have hK := HasDerivAt.fun_sum (u := Finset.univ)
    (fun k _ => hasDerivAt_half_norm_add_smul (D k) (V k) t)
  have hF := ((hasDerivAt_bulkPotential_add_smul a A B t).const_mul ((ε : ℝ)⁻¹ ^ 2))
  refine (hK.fun_add hF).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  change energyDensity a ε (A + s • B) (D + s • V) = _
  simp only [Pi.add_apply, Pi.smul_apply, energyDensity, gradientNormSq, Finset.mul_sum]

private theorem classicalGradient_const_smul {v : Point → S0} (hv : ContDiff ℝ ∞ v) (c : ℝ) :
    ClassicalGradient (c • v) = c • ClassicalGradient v := by
  funext x j
  exact DFunLike.congr_fun (((hv.differentiable (by simp) x).hasFDerivAt.const_smul c).fderiv) (axis j)

/-- A smooth compact variation inside the comparison domain preserves the exact trace. -/
theorem compact_variation_sameTrace {u v : Point → S0} {D : Point → Gradient}
    (hΩ : IsOpen Ω) (hu : MemH1 Ω u D) (hv : IsSmoothTest Ω v) (t : ℝ) :
    MemH1 Ω (u + t • v) (D + t • ClassicalGradient v) ∧
      SameTrace Ω (u + t • v) u (D + t • ClassicalGradient v) D := by
  have hV := hasZeroTrace_of_contDiff_hasCompactSupport hΩ hv.1 hv.2.1 hv.2.2
  have hVMem : MemH1 Ω v (ClassicalGradient v) := hV.1
  refine ⟨MemH1.add hu (hVMem.const_smul t), ?_⟩
  have hSp := tsupport_smul_subset_right (fun _ : Point => t) v
  have hCp : HasCompactSupport (t • v) := hv.2.1.smul_left (f := fun _ : Point => t)
  have hVt : HasZeroTrace Ω (t • v) (ClassicalGradient (t • v)) :=
    hasZeroTrace_of_contDiff_hasCompactSupport hΩ (hv.1.const_smul t) hCp (hSp.trans hv.2.2)
  simpa only [SameTrace, add_sub_cancel_left, classicalGradient_const_smul hv.1] using hVt

private theorem exists_norm_bound {E : Type*} [NormedAddCommGroup E] {v : Point → E}
    (hv : Continuous v) (hvSupp : HasCompactSupport v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖v x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hv.norm.bddAbove_range_of_hasCompactSupport (hvSupp.comp_left norm_zero)
  exact ⟨max C 0, le_max_right _ _, fun x => (hC (mem_range_self x)).trans (le_max_left _ _)⟩

/-- Integrability of the sextic density on a finite-measure set for a field
in `L⁶` and a square-integrable gradient. -/
theorem integrable_energyDensity_of_memLp_six {μ : Measure Point} [IsFiniteMeasure μ]
    (a : BulkCoefficients) (ε : ElasticScale) {u : Point → S0} {D : Point → Gradient}
    (hu : MemLp u 6 μ) (hD : ∀ j, MemLp (fun x => D x j) 2 μ) :
    Integrable (fun x => energyDensity a ε (u x) (D x)) μ := by
  simp only [energyDensity, gradientNormSq_eq_sum_norm_sq]
  have hD₂ (j : Fin 3) : Integrable (fun x => ‖D x j‖ ^ 2) μ :=
    (hD j).integrable_norm_pow (p := 2) (by decide)
  have hB := (polynomialGrowth_bulkPotential a).integrable_comp
    (differentiable_bulkPotential a).continuous hu
  exact ((integrable_finsetSum Finset.univ (fun j _ => hD₂ j)).const_mul _).add (hB.const_mul _)

private theorem energyDensity_nonneg (a : BulkCoefficients) (ε : ElasticScale)
    (A : S0) (D : Gradient) : 0 ≤ energyDensity a ε A D := by
  rw [energyDensity, gradientNormSq_eq_sum_norm_sq]
  exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => sq_nonneg ‖D j‖))
    (mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a A))

/-- On finite-volume sets with the sextic moment, the extended comparison
energy is the integral of its real nonnegative density. -/
theorem energy_eq_ofReal_integral_of_memLp_six
    (a : BulkCoefficients) (ε : ElasticScale) {U : Set Point} (hU : volume U ≠ ⊤)
    {u : Point → S0} {D : Point → Gradient}
    (hu : MemLp u 6 (volume.restrict U))
    (hD : ∀ k, MemLp (fun x => D x k) 2 (volume.restrict U)) :
    energy a ε U u D = ENNReal.ofReal (∫ x in U, energyDensity a ε (u x) (D x)) := by
  letI := isFiniteMeasure_restrict.mpr hU
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_energyDensity_of_memLp_six a ε hu hD)
    (Eventually.of_forall fun x => energyDensity_nonneg a ε (u x) (D x))).symm

theorem energy_lt_top_of_memLp_six
    (a : BulkCoefficients) (ε : ElasticScale) {U : Set Point} (hU : volume U ≠ ⊤)
    {u : Point → S0} {D : Point → Gradient}
    (hu : MemLp u 6 (volume.restrict U))
    (hD : ∀ k, MemLp (fun x => D x k) 2 (volume.restrict U)) :
    energy a ε U u D < ⊤ := by
  rw [energy_eq_ofReal_integral_of_memLp_six a ε hU hu hD]
  exact ENNReal.ofReal_lt_top

private theorem norm_add_smul_le (A B : S0) (t : ℝ) :
    ‖A + t • B‖ ≤ ‖A‖ + |t| * ‖B‖ := by
  simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le A (t • B)

private theorem energyVariationDensity_zero (a : BulkCoefficients) (ε : ElasticScale)
    (A B : S0) (D V : Gradient) :
    energyVariationDensity a ε A B D V 0 =
      (∑ j : Fin 3, frobeniusS0 (D j) (V j)) +
        (ε : ℝ)⁻¹ ^ 2 * frobenius (bulkGradient a A) B := by
  simp only [energyVariationDensity, zero_smul, add_zero]

private theorem aestronglyMeasurable_energyVariationDensity {μ : Measure Point}
    (a : BulkCoefficients) (ε : ElasticScale) {u v : Point → S0} {D V : Point → Gradient}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (hD : ∀ j, AEStronglyMeasurable (fun x => D x j) μ)
    (hV : ∀ j, AEStronglyMeasurable (fun x => V x j) μ) :
    AEStronglyMeasurable (fun x => energyVariationDensity a ε (u x) (v x) (D x) (V x) 0) μ := by
  let K : Fin 3 → Point → ℝ := fun j x => frobeniusS0 (D x j) (V x j)
  let G : Point → ℝ := fun x => frobenius (bulkGradient a (u x)) (v x)
  have hpair (j : Fin 3) : AEStronglyMeasurable (fun x => (D x j, V x j)) μ :=
    (hD j).prodMk (hV j)
  have hitem (j : Fin 3) : AEStronglyMeasurable (K j) μ := by
    let k : Point → S0 × S0 := fun x => (D x j, V x j)
    change AEStronglyMeasurable (fun x => frobeniusS0 (k x).1 (k x).2) μ
    exact Continuous.comp_aestronglyMeasurable (β := S0 × S0) (f := k)
      (g := fun X : S0 × S0 => frobeniusS0 X.1 X.2) continuous_frobeniusS0 (hpair j)
  have hK : AEStronglyMeasurable (∑ j, K j) μ :=
    Finset.aestronglyMeasurable_sum (f := K) Finset.univ (fun j _ => hitem j)
  have hUV : AEStronglyMeasurable (fun x => (u x, v x)) μ := hu.prodMk hv
  have hF : AEStronglyMeasurable G μ := by
    let g : Point → S0 × S0 := fun x => (u x, v x)
    change AEStronglyMeasurable (fun x => frobenius (bulkGradient a (g x).1) (g x).2) μ
    exact Continuous.comp_aestronglyMeasurable (β := S0 × S0) (f := g)
      (g := fun X : S0 × S0 => frobenius (bulkGradient a X.1) X.2)
      (continuous_bulkVariation a) hUV
  have hc : Continuous (fun s : ℝ => (ε : ℝ)⁻¹ ^ 2 * s) := continuous_const.mul continuous_id
  have hSum := hK.add (hc.comp_aestronglyMeasurable hF)
  refine hSum.congr (Eventually.of_forall fun x => ?_)
  change (∑ j, K j) x + (ε : ℝ)⁻¹ ^ 2 * G x =
    energyVariationDensity a ε (u x) (v x) (D x) (V x) 0
  rw [energyVariationDensity_zero, Finset.sum_apply]


private theorem comparisonBall_compactlyContained {c : Point} {r : ℝ}
    (hcl : Metric.closedBall c r ⊆ Ω) : CompactlyContained (Metric.ball c r) Ω := by
  have hsub : closure (Metric.ball c r) ⊆ Metric.closedBall c r :=
    closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
  exact ⟨(isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hsub, hsub.trans hcl⟩

private theorem measure_ball_finite (c : Point) (r : ℝ) :
    IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
  isFiniteMeasure_restrict.mpr
    (ne_of_lt ((measure_mono Metric.ball_subset_closedBall).trans_lt
      (isCompact_closedBall c r).measure_lt_top))

/-- Vanishing first variation under the sextic moment on a comparison ball. -/
theorem firstVariation_eq_zero_on_ball_of_memLp_six
    (a : BulkCoefficients) (ε : ElasticScale) {u v : Point → S0} {D : Point → Gradient}
    (hu : IsLocalEnergyMinimizer a ε Ω u D)
    {c : Point} {r : ℝ} (hr : 0 < r) (hcl : Metric.closedBall c r ⊆ Ω)
    (huSix : MemLp u 6 (volume.restrict (Metric.ball c r)))
    (hv : IsSmoothTest (Metric.ball c r) v) :
    (∫ x in Metric.ball c r, (∑ j, frobeniusS0 (D x j) (ClassicalGradient v x j)) +
      (ε : ℝ)⁻¹ ^ 2 * frobenius (bulkGradient a (u x)) (v x)) = 0 := by
  let B := Metric.ball c r
  let μ := volume.restrict B
  let V := ClassicalGradient v
  letI : IsFiniteMeasure μ := measure_ball_finite c r
  have huH := hu.1 B Metric.isOpen_ball (comparisonBall_compactlyContained hcl)
  have hvH : MemH1 B v V :=
    (hasZeroTrace_of_contDiff_hasCompactSupport Metric.isOpen_ball hv.1 hv.2.1 hv.2.2).1
  obtain ⟨C₀, hC₀, hvBound⟩ := exists_norm_bound hv.1.continuous hv.2.1
  have hVBounds (j : Fin 3) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖V x j‖ ≤ C :=
    exists_norm_bound ((hv.1.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hv.2.1.fderiv_apply ℝ (axis j))
  choose C hC hVBound using hVBounds
  obtain ⟨K, hK, hForce⟩ := polynomialGrowth_bulkGradient a
  let forceScale := K * (1 + C₀) ^ 5 * C₀
  let q (x : Point) := (1 + ‖u x‖) ^ 6
  have hq : Integrable q μ := integrable_shifted_norm_pow (n := 6) huSix
  have hvSix : MemLp v 6 μ := MemLp.of_bound hvH.1.1 C₀ (Eventually.of_forall hvBound)
  let F (t : ℝ) (x : Point) :=
    energyDensity a ε (u x + t • v x) (D x + t • V x)
  let F' (t : ℝ) (x : Point) :=
    energyVariationDensity a ε (u x) (v x) (D x) (V x) t
  let bound (x : Point) :=
    (∑ j : Fin 3, (‖D x j‖ + C j) * C j) + ((ε : ℝ)⁻¹ ^ 2 * forceScale) * q x
  have hcomp (t : ℝ) := compact_variation_sameTrace Metric.isOpen_ball huH hv t
  have hshiftLp (t : ℝ) : MemLp (u + t • v) 6 μ := by
    have htv : MemLp (t • v) 6 μ := hvSix.const_smul t
    have hsub : MemLp (u - -(t • v)) 6 μ := huSix.sub htv.neg
    rwa [sub_neg_eq_add] at hsub
  have hFint (t : ℝ) : Integrable (F t) μ := by
    exact integrable_energyDensity_of_memLp_six (μ := μ) a ε
      (u := u + t • v) (D := D + t • V) (hshiftLp t) (hcomp t).1.2.1
  have hF'm := aestronglyMeasurable_energyVariationDensity a ε huH.1.1 hvH.1.1
    (fun j => (huH.2.1 j).1) (fun j => (hvH.2.1 j).1)
  have hboundInt : Integrable bound μ := by
    apply Integrable.add _ (hq.const_mul _)
    apply integrable_finsetSum Finset.univ
    intro j _
    exact (((huH.2.1 j).integrable (by norm_num)).norm.add (integrable_const _)).mul_const _
  have hbd : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (-1 : ℝ) 1, ‖F' t x‖ ≤ bound x := by
    refine Eventually.of_forall fun x t ht => ?_
    have habs : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
    have hle (A W : S0) (b : ℝ) (hb : ‖W‖ ≤ b) :
        ‖A + t • W‖ ≤ ‖A‖ + b :=
      (norm_add_smul_le A W t).trans (add_le_add le_rfl
        ((mul_le_of_le_one_left (norm_nonneg _) habs).trans hb))
    have hshift : 1 + ‖u x + t • v x‖ ≤ (1 + C₀) * (1 + ‖u x‖) := by
      have h := hle (u x) (v x) C₀ (hvBound x)
      nlinarith [mul_nonneg hC₀ (norm_nonneg (u x))]
    have hpower : (1 + ‖u x + t • v x‖) ^ 5 ≤ (1 + C₀) ^ 5 * q x := by
      calc
        _ ≤ ((1 + C₀) * (1 + ‖u x‖)) ^ 5 := pow_le_pow_left₀ (by positivity) hshift 5
        _ = (1 + C₀) ^ 5 * (1 + ‖u x‖) ^ 5 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg _)) (by decide)) (by positivity)
    have hFrob : |frobenius (bulkGradient a (u x + t • v x)) (v x)| ≤ forceScale * q x := by
      change |frobeniusS0 (bulkForce a (u x + t • v x)) (v x)| ≤ _
      calc
        _ ≤ ‖bulkForce a (u x + t • v x)‖ * ‖v x‖ := abs_frobeniusS0_le _ _
        _ ≤ (K * (1 + ‖u x + t • v x‖) ^ 5) * C₀ :=
          mul_le_mul (hForce _) (hvBound x) (norm_nonneg _) (by positivity)
        _ ≤ (K * ((1 + C₀) ^ 5 * q x)) * C₀ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hK) hC₀
        _ = _ := by unfold forceScale; ring
    unfold F' energyVariationDensity bound
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      refine (abs_frobeniusS0_le _ _).trans
        (mul_le_mul (hle _ _ _ (hVBound j x)) (hVBound j x)
          (norm_nonneg _) (add_nonneg (norm_nonneg _) (hC j)))
    · rw [abs_mul, abs_of_nonneg (sq_nonneg _), mul_assoc]
      exact mul_le_mul_of_nonneg_left hFrob (sq_nonneg _)
  have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall fun t => (hFint t).1) (hFint 0) hF'm hbd hboundInt
    (Eventually.of_forall fun x t _ => hasDerivAt_energyDensity_variation a ε
      (u x) (v x) (D x) (V x) t)).2
  have hmin : IsLocalMin (fun t : ℝ => ∫ x, F t x ∂μ) 0 := by
    apply Eventually.of_forall
    intro t
    have hNN (s : ℝ) : 0 ≤ᵐ[μ] F s :=
      Eventually.of_forall fun x => energyDensity_nonneg a ε _ _
    have hineq := hu.2 c r hr hcl (u + t • v) (D + t • V) (hcomp t).1 (hcomp t).2
    change (∫⁻ x, ENNReal.ofReal (energyDensity a ε (u x) (D x)) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (F t x) ∂μ at hineq
    have hFzero (x : Point) : energyDensity a ε (u x) (D x) = F 0 x := by
      simp only [F, zero_smul, add_zero]
    simp_rw [hFzero] at hineq
    rw [← ofReal_integral_eq_lintegral_ofReal (hFint 0) (hNN 0),
      ← ofReal_integral_eq_lintegral_ofReal (hFint t) (hNN t)] at hineq
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae (hNN t))).mp hineq
  simpa only [F', energyVariationDensity, V, zero_smul, add_zero] using hmin.hasDerivAt_eq_zero hderiv

/-- Vanishing first variation for an essentially bounded minimizer and a smooth
variation supported in its comparison ball. -/
theorem firstVariation_eq_zero_on_ball_of_bounded
    (a : BulkCoefficients) (ε : ElasticScale) {u v : Point → S0} {D : Point → Gradient}
    (hu : IsLocalEnergyMinimizer a ε Ω u D)
    {c : Point} {r : ℝ} (hr : 0 < r) (hcl : Metric.closedBall c r ⊆ Ω)
    {M : ℝ} (huBound : ∀ᵐ x ∂volume.restrict (Metric.ball c r), ‖u x‖ ≤ M)
    (hv : IsSmoothTest (Metric.ball c r) v) :
    (∫ x in Metric.ball c r, (∑ j, frobeniusS0 (D x j) (ClassicalGradient v x j)) +
      (ε : ℝ)⁻¹ ^ 2 * frobenius (bulkGradient a (u x)) (v x)) = 0 := by
  letI := measure_ball_finite c r
  have huH := hu.1 (Metric.ball c r) Metric.isOpen_ball (comparisonBall_compactlyContained hcl)
  exact firstVariation_eq_zero_on_ball_of_memLp_six a ε hu hr hcl (MemLp.of_bound huH.1.1 M huBound) hv

private noncomputable def matrixUnitTest (i j : Fin 3) : S0 :=
  traceFreeSymmetricPart (Matrix.single i j 1)

private theorem frobeniusS0_matrixUnitTest (i j : Fin 3) (A : S0) :
    frobeniusS0 A (matrixUnitTest i j) = (A : Tensor) i j := by
  change frobenius A (traceFreeSymmetricPart (Matrix.single i j 1)) = _
  rw [frobenius_comm, frobenius_traceFreeSymmetricPart, frobenius_eq_sum]
  simp [Matrix.single_apply, ite_and, ite_mul]

private theorem classicalGradient_smul_matrixUnitTest (i j k : Fin 3) {φ : Point → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : Point) :
    ClassicalGradient (fun y => φ y • matrixUnitTest i j) x k =
      coordDeriv k φ x • matrixUnitTest i j :=
  DFunLike.congr_fun (((hφ.differentiable (by simp) x).hasFDerivAt.smul_const
    (matrixUnitTest i j)).fderiv) (axis k)

private noncomputable def tensorEntryLinear (i j : Fin 3) : Tensor →L[ℝ] ℝ :=
  ({ toFun := fun A : Tensor => A i j
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Tensor →ₗ[ℝ] ℝ).toContinuousLinearMap

private noncomputable def entryLinear (i j : Fin 3) : S0 →L[ℝ] ℝ :=
  (tensorEntryLinear i j).comp symmetricTraceless.subtypeL

private theorem locallyIntegrableOn_entry {f : Point → S0} (hf : LocallyIntegrableOn f Ω volume)
    (i j : Fin 3) : LocallyIntegrableOn (fun x => (f x : Tensor) i j) Ω volume := by
  intro x hx
  obtain ⟨W, hW, hInt⟩ := hf x hx
  exact ⟨W, hW, (entryLinear i j).integrable_comp hInt⟩

private theorem integrable_bulkGradient_entry_of_memLp_six
    {μ : Measure Point} [IsFiniteMeasure μ] (a : BulkCoefficients)
    {u : Point → S0} (hu : MemLp u 6 μ) (i j : Fin 3) :
    Integrable (fun x => bulkGradient a (u x) i j) μ := by
  have h5 : MemLp u (5 : ℕ) μ := hu.mono_exponent (by norm_num)
  have h := (polynomialGrowth_bulkGradient a).integrable_comp (continuous_bulkGradient a) h5
  exact (tensorEntryLinear i j).integrable_comp h

private theorem integrable_gradient_test_entry {D : Point → Gradient} {k : Fin 3}
    (hD : LocallyIntegrableOn (fun x => D x k) Ω volume)
    {φ : Point → ℝ} (hφ : SmoothTest Ω φ) (i j : Fin 3) :
    Integrable (fun x => coordDeriv k φ x * (D x k : Tensor) i j) volume := by
  simpa only [smul_eq_mul] using
    (hφ.coordDeriv k).integrable_smul (locallyIntegrableOn_entry hD i j)

private theorem setIntegral_coordDeriv_mul_entry {D : Point → Gradient}
    {φ : Point → ℝ} (hφ : SmoothTest Ω φ) (i j k : Fin 3) :
    (∫ x in Ω, coordDeriv k φ x * (D x k : Tensor) i j) =
      ∫ x, coordDeriv k φ x * (D x k : Tensor) i j := by
  simpa only [smul_eq_mul] using (hφ.coordDeriv k).setIntegral_smul_eq_integral
    (fun x => (D x k : Tensor) i j)

private theorem setIntegral_mul_force_entry (a : BulkCoefficients) {u : Point → S0}
    {φ : Point → ℝ} (hφ : SmoothTest Ω φ) (i j : Fin 3) :
    (∫ x in Ω, φ x * bulkGradient a (u x) i j) = ∫ x, φ x * bulkGradient a (u x) i j := by
  simpa only [smul_eq_mul] using hφ.setIntegral_smul_eq_integral (fun x => bulkGradient a (u x) i j)

/-- The weak Euler–Lagrange equation on a comparison ball with the sextic moment. -/
theorem isWeakEulerLagrange_on_ball_of_memLp_six
    (a : BulkCoefficients) (ε : ElasticScale) {u : Point → S0} {D : Point → Gradient}
    (hu : IsLocalEnergyMinimizer a ε Ω u D)
    {c : Point} {r : ℝ} (hr : 0 < r) (hcl : Metric.closedBall c r ⊆ Ω)
    (huSix : MemLp u 6 (volume.restrict (Metric.ball c r))) :
    IsWeakEulerLagrange a ε (Metric.ball c r) u D := by
  let B := Metric.ball c r
  let μ := volume.restrict B
  letI : IsFiniteMeasure μ := measure_ball_finite c r
  have huH := hu.1 B Metric.isOpen_ball (comparisonBall_compactlyContained hcl)
  intro i j φ hφ
  have hφ' : SmoothTest B φ := hφ
  have hψ : IsSmoothTest B (fun x => φ x • matrixUnitTest i j) :=
    ⟨hφ.1.smul contDiff_const, hφ.2.1.smul_right (f' := fun _ : Point => matrixUnitTest i j),
      (tsupport_smul_subset_left φ (fun _ : Point => matrixUnitTest i j)).trans hφ.2.2⟩
  have hvar := firstVariation_eq_zero_on_ball_of_memLp_six a ε hu hr hcl huSix hψ
  have hVeq (k : Fin 3) (x : Point) :
      frobeniusS0 (D x k) (ClassicalGradient (fun x => φ x • matrixUnitTest i j) x k) =
        coordDeriv k φ x * (D x k : Tensor) i j := by
    rw [classicalGradient_smul_matrixUnitTest i j k hφ.1, frobeniusS0_smul_right,
      frobeniusS0_matrixUnitTest]
  have hFeq (x : Point) :
      frobenius (bulkGradient a (u x)) (φ x • matrixUnitTest i j : S0) =
        φ x * bulkGradient a (u x) i j := by
    change frobeniusS0 (bulkForce a (u x)) (φ x • matrixUnitTest i j) = _
    rw [frobeniusS0_smul_right, frobeniusS0_matrixUnitTest]
    rfl
  simp_rw [hVeq, hFeq] at hvar
  have hDint (k : Fin 3) : Integrable (fun x => coordDeriv k φ x * (D x k : Tensor) i j) μ :=
    (integrable_gradient_test_entry (huH.locallyIntegrableOn_gradient k) hφ' i j).integrableOn
  have hGInt : Integrable (fun x => bulkGradient a (u x) i j) μ :=
    integrable_bulkGradient_entry_of_memLp_six a huSix i j
  have hFint : Integrable (fun x => φ x * bulkGradient a (u x) i j) μ := by
    have hGOn : IntegrableOn (fun x => bulkGradient a (u x) i j) B volume := hGInt
    have hprod : Integrable (fun x => φ x • bulkGradient a (u x) i j) volume :=
      hφ'.integrable_smul hGOn.locallyIntegrableOn
    exact (hprod.integrableOn : IntegrableOn (fun x => φ x • bulkGradient a (u x) i j) B volume)
  rw [integral_add (integrable_finsetSum Finset.univ (fun k _ => hDint k))
    (hFint.const_mul _), integral_finsetSum Finset.univ (fun k _ => hDint k),
    integral_const_mul] at hvar
  have hDK (k : Fin 3) := setIntegral_coordDeriv_mul_entry (D := D) hφ' i j k
  have hKsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => hDK k)
  have hFP := setIntegral_mul_force_entry a (u := u) hφ' i j
  rw [hKsum, hFP] at hvar
  have hε : (ε : ℝ) ≠ 0 := ne_of_gt ε.2.1
  have hcancel : (ε : ℝ) ^ 2 * (ε : ℝ)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hε, one_pow]
  calc
    _ = (ε : ℝ) ^ 2 * ((∑ k : Fin 3, ∫ x, coordDeriv k φ x * (D x k : Tensor) i j) +
        (ε : ℝ)⁻¹ ^ 2 * ∫ x, φ x * bulkGradient a (u x) i j) := by
      rw [mul_add, ← mul_assoc, hcancel, one_mul]
    _ = 0 := by rw [hvar, mul_zero]

/-- The weak Euler–Lagrange equation on each comparison ball for a locally
minimizing field with an essential bound on that ball. -/
theorem isWeakEulerLagrange_on_ball_of_bounded
    (a : BulkCoefficients) (ε : ElasticScale) {u : Point → S0} {D : Point → Gradient}
    (hu : IsLocalEnergyMinimizer a ε Ω u D)
    {c : Point} {r : ℝ} (hr : 0 < r) (hcl : Metric.closedBall c r ⊆ Ω)
    {M : ℝ} (huBound : ∀ᵐ x ∂volume.restrict (Metric.ball c r), ‖u x‖ ≤ M) :
    IsWeakEulerLagrange a ε (Metric.ball c r) u D := by
  letI := measure_ball_finite c r
  have huH := hu.1 (Metric.ball c r) Metric.isOpen_ball (comparisonBall_compactlyContained hcl)
  exact isWeakEulerLagrange_on_ball_of_memLp_six a ε hu hr hcl (MemLp.of_bound huH.1.1 M huBound)

private abbrev ComparisonBall (Ω : Set Point) :=
  {b : Point × ℝ // 0 < b.2 ∧ Metric.closedBall b.1 b.2 ⊆ Ω}

private theorem exists_scalar_test_decomposition
    (hΩ : IsOpen Ω) {φ : Point → ℝ} (hφ : SmoothTest Ω φ) :
    ∃ (I : Finset (ComparisonBall Ω)) (ψ : I → Point → ℝ),
      (∀ i, SmoothTest (Metric.ball i.1.1.1 i.1.1.2) (ψ i)) ∧
        φ = fun x => ∑ i, ψ i x := by
  classical
  let U : ComparisonBall Ω → Set Point := fun b => Metric.ball b.1.1 b.1.2
  have hU (b : ComparisonBall Ω) : IsOpen (U b) := Metric.isOpen_ball
  have hcover : tsupport φ ⊆ ⋃ b, U b := by
    intro x hx
    obtain ⟨r, hr, hrΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds (hφ.2.2 hx))
    let b : ComparisonBall Ω :=
      ⟨(x, r/2), half_pos hr, (Metric.closedBall_subset_ball (half_lt_self hr)).trans hrΩ⟩
    exact mem_iUnion.mpr ⟨b, Metric.mem_ball_self (half_pos hr)⟩
  obtain ⟨I, hI⟩ := hφ.2.1.elim_finite_subcover U hU hcover
  have hIcover : tsupport φ ⊆ ⋃ i : I, U i := by
    rw [iUnion_subtype]
    exact hI
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Point)
    (isClosed_tsupport φ) (fun i : I => U i) (fun i => hU i) hIcover
  let ψ (i : I) (x : Point) := ρ i x * φ x
  refine ⟨I, ψ, ?_, ?_⟩
  · intro i
    have hρdiff : ContDiff ℝ ∞ (fun x => ρ i x) := (ρ i).contMDiff.contDiff
    exact ⟨hρdiff.mul hφ.1, hφ.2.1.mul_left,
      (tsupport_mul_subset_left (f := fun x => ρ i x) (g := φ)).trans (hρ i)⟩
  · funext x
    by_cases hx : x ∈ tsupport φ
    · have hρSum : ∑ i : I, ρ i x = 1 := ρ.sum_finsupport' x hx (Finset.subset_univ _)
      change φ x = ∑ i : I, ρ i x * φ x
      rw [← Finset.sum_mul, hρSum, one_mul]
    · simp [ψ, image_eq_zero_of_notMem_tsupport hx]

private theorem coordDeriv_sum {ι : Type*} [Fintype ι] {ψ : ι → Point → ℝ}
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (k : Fin 3) (x : Point) :
    coordDeriv k (fun y => ∑ i, ψ i y) x = ∑ i, coordDeriv k (ψ i) x := by
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => ((hψ i).differentiable (by simp) x).hasFDerivAt)
  have h := DFunLike.congr_fun hsum.fderiv (axis k)
  simpa only [coordDeriv, sum_apply] using h

/-- Weak Euler–Lagrange identities on comparison balls imply the identity on
their open ambient domain for fields with locally integrable bulk force. -/
theorem IsWeakEulerLagrange.of_on_comparison_balls
    (a : BulkCoefficients) (ε : ElasticScale) {u : Point → S0} {D : Point → Gradient}
    (hΩ : IsOpen Ω) (hu : MemH1Loc Ω u D)
    (hForce : ∀ i j, LocallyIntegrableOn (fun x => bulkGradient a (u x) i j) Ω volume)
    (hball : ∀ c r, 0 < r → Metric.closedBall c r ⊆ Ω →
      IsWeakEulerLagrange a ε (Metric.ball c r) u D) :
    IsWeakEulerLagrange a ε Ω u D := by
  classical
  intro i j φ hφ
  obtain ⟨I, ψ, hψ, hSum⟩ := exists_scalar_test_decomposition hΩ hφ
  have hψΩ (m : I) : SmoothTest Ω (ψ m) :=
    (hψ m).mono (Metric.ball_subset_closedBall.trans m.1.2.2)
  have hDInt (m : I) (k : Fin 3) :=
    integrable_gradient_test_entry (hu.locallyIntegrableOn_gradient hΩ k) (hψΩ m) i j
  have hFInt (m : I) : Integrable (fun x => ψ m x * bulkGradient a (u x) i j) := by
    simpa only [smul_eq_mul] using (hψΩ m).integrable_smul (hForce i j)
  have hF :
      (∫ x, φ x * bulkGradient a (u x) i j) =
        ∑ m : I, ∫ x, ψ m x * bulkGradient a (u x) i j := by
    rw [← integral_finsetSum Finset.univ (fun m _ => hFInt m)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change φ x * bulkGradient a (u x) i j = _
      rw [congrFun hSum x, Finset.sum_mul]
  have hD (k : Fin 3) :
      (∫ x, coordDeriv k φ x * (D x k : Tensor) i j) =
        ∑ m : I, ∫ x, coordDeriv k (ψ m) x * (D x k : Tensor) i j := by
    rw [← integral_finsetSum Finset.univ (fun m _ => hDInt m k)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change coordDeriv k φ x * (D x k : Tensor) i j = _
      rw [hSum, coordDeriv_sum (fun m => (hψ m).1) k x, Finset.sum_mul]
  rw [hF, Finset.sum_congr rfl (fun k _ => hD k), Finset.sum_comm, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun m _ => hball m.1.1.1 m.1.1.2 m.1.2.1 m.1.2.2 i j (ψ m) (hψ m)

private theorem locallyIntegrableOn_of_integrableOn_comparison_balls
    {E : Type*} [NormedAddCommGroup E] {f : Point → E}
    (hΩ : IsOpen Ω) (h : ∀ c r, 0 < r → Metric.closedBall c r ⊆ Ω →
      IntegrableOn f (Metric.ball c r) volume) : LocallyIntegrableOn f Ω volume := by
  intro x hx
  obtain ⟨r, hr, hrΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx)
  exact ⟨Metric.ball x (r / 2), mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (half_pos hr)),
    h x (r / 2) (half_pos hr) ((Metric.closedBall_subset_ball (half_lt_self hr)).trans hrΩ)⟩

/-- An open-domain local minimizer satisfying the sextic moment on every
comparison ball solves the weak Euler–Lagrange equation. -/
theorem isWeakEulerLagrange_of_localEnergyMinimizer_of_local_memLp_six
    (a : BulkCoefficients) (ε : ElasticScale) {u : Point → S0} {D : Point → Gradient}
    (hΩ : IsOpen Ω) (hu : IsLocalEnergyMinimizer a ε Ω u D)
    (hSix : ∀ c r, 0 < r → Metric.closedBall c r ⊆ Ω →
      MemLp u 6 (volume.restrict (Metric.ball c r))) :
    IsWeakEulerLagrange a ε Ω u D := by
  apply IsWeakEulerLagrange.of_on_comparison_balls a ε hΩ hu.1
  · intro i j
    apply locallyIntegrableOn_of_integrableOn_comparison_balls hΩ
    intro c r hr hcl
    letI := measure_ball_finite c r
    exact integrable_bulkGradient_entry_of_memLp_six a (hSix c r hr hcl) i j
  · intro c r hr hcl
    exact isWeakEulerLagrange_on_ball_of_memLp_six a ε hu hr hcl (hSix c r hr hcl)

/-- The comparison-ball instance of the three-dimensional Sobolev embedding
for the frozen weak-gradient representation. -/
def ComparisonBallSobolevSix : Prop :=
  ∀ (c : Point) (r : ℝ), 0 < r →
    ∀ (u : Point → S0) (D : Point → Gradient),
      MemH1 (Metric.ball c r) u D → MemLp u 6 (volume.restrict (Metric.ball c r))

/-- The weak Euler–Lagrange equation of a local minimizer, with the
three-dimensional Sobolev embedding on balls as an explicit input. -/
theorem isWeakEulerLagrange_of_localEnergyMinimizer
    (a : BulkCoefficients) (ε : ElasticScale) {u : Point → S0} {D : Point → Gradient}
    (hΩ : IsOpen Ω) (hu : IsLocalEnergyMinimizer a ε Ω u D) (hSob : ComparisonBallSobolevSix) :
    IsWeakEulerLagrange a ε Ω u D := by
  apply isWeakEulerLagrange_of_localEnergyMinimizer_of_local_memLp_six a ε hΩ hu
  intro c r hr hcl
  exact hSob c r hr u D (hu.1 _ Metric.isOpen_ball (comparisonBall_compactlyContained hcl))

/-- A local penalized minimizer that is essentially bounded on comparison balls
satisfies the weak Euler–Lagrange equation throughout its open domain. -/
theorem isWeakEulerLagrange_of_localEnergyMinimizer_of_bounded
    (a : BulkCoefficients) (ε : ElasticScale) {u : Point → S0} {D : Point → Gradient}
    (hΩ : IsOpen Ω) (hu : IsLocalEnergyMinimizer a ε Ω u D)
    (hBound : ∀ c r, 0 < r → Metric.closedBall c r ⊆ Ω →
      ∃ M : ℝ, ∀ᵐ x ∂volume.restrict (Metric.ball c r), ‖u x‖ ≤ M) :
    IsWeakEulerLagrange a ε Ω u D := by
  apply isWeakEulerLagrange_of_localEnergyMinimizer_of_local_memLp_six a ε hΩ hu
  intro c r hr hcl
  have huH := hu.1 (Metric.ball c r) Metric.isOpen_ball (comparisonBall_compactlyContained hcl)
  letI := measure_ball_finite c r
  obtain ⟨M, hM⟩ := hBound c r hr hcl
  exact MemLp.of_bound huH.1.1 M hM

theorem ae_norm_le_of_eLpNorm_top_le {μ : Measure Point} {u : Point → S0}
    {M : ℝ} (hBound : eLpNorm u ⊤ μ ≤ ENNReal.ofReal M) :
    ∀ᵐ x ∂μ, ‖u x‖ ≤ max 0 M := by
  rw [eLpNorm_exponent_top] at hBound
  filter_upwards [enorm_ae_le_eLpNormEssSup u μ] with x hx
  apply (ENNReal.ofReal_le_ofReal_iff (le_max_left 0 M)).mp
  calc
    ENNReal.ofReal ‖u x‖ = ‖u x‖ₑ := ofReal_norm (u x)
    _ ≤ eLpNormEssSup u μ := hx
    _ ≤ ENNReal.ofReal M := hBound
    _ ≤ ENNReal.ofReal (max 0 M) := ENNReal.ofReal_le_ofReal (le_max_right 0 M)

/-- The weak Euler–Lagrange equation for a minimizer with an essential
Frobenius-norm bound on the domain. -/
theorem isWeakEulerLagrange_of_localEnergyMinimizer_of_eLpNorm_top_le
    (a : BulkCoefficients) (ε : ElasticScale) {u : Point → S0} {D : Point → Gradient}
    (hΩ : IsOpen Ω) (hu : IsLocalEnergyMinimizer a ε Ω u D)
    {M : ℝ} (hBound : eLpNorm u ⊤ (volume.restrict Ω) ≤ ENNReal.ofReal M) :
    IsWeakEulerLagrange a ε Ω u D := by
  apply isWeakEulerLagrange_of_localEnergyMinimizer_of_bounded a ε hΩ hu
  have hAE := ae_norm_le_of_eLpNorm_top_le hBound
  intro c r _ hcl
  exact ⟨max 0 M, ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_closedBall.trans hcl) hAE⟩

/-- The matrix-valued test identity for the weak Euler–Lagrange equation. -/
theorem IsWeakEulerLagrange.integral_frobenius_eq_zero
    {a : BulkCoefficients} {ε : ElasticScale} {u : Point → S0} {D : Point → Gradient}
    (h : IsWeakEulerLagrange a ε Ω u D) (hΩ : IsOpen Ω) (hu : MemH1Loc Ω u D)
    (hForce : ∀ i j, LocallyIntegrableOn (fun x => bulkGradient a (u x) i j) Ω volume)
    {P : Point → Tensor} (hP : IsSmoothTest Ω P) :
    (∫ x in Ω, (ε : ℝ) ^ 2 * (∑ k, frobenius (D x k) (coordDeriv k P x)) +
      frobenius (bulkGradient a (u x)) (P x)) = 0 := by
  let φ (i j : Fin 3) (x : Point) := tensorEntryLinear i j (P x)
  have hφ (i j : Fin 3) : SmoothTest Ω (φ i j) := by
    refine ⟨(tensorEntryLinear i j).contDiff.comp hP.1,
      hP.2.1.comp_left (tensorEntryLinear i j).map_zero, ?_⟩
    apply (closure_mono ?_).trans hP.2.2
    intro x hx
    change φ i j x ≠ 0 at hx
    change P x ≠ 0
    intro hzero
    exact hx (show tensorEntryLinear i j (P x) = 0 by rw [hzero, map_zero])
  have hcoord (i j k : Fin 3) (x : Point) :
      coordDeriv k (φ i j) x = (coordDeriv k P x) i j :=
    DFunLike.congr_fun (((tensorEntryLinear i j).hasFDerivAt (x := P x)).comp x
      ((hP.1.differentiable (by simp) x).hasFDerivAt)).fderiv (axis k)
  let K (i j k : Fin 3) (x : Point) := coordDeriv k (φ i j) x * (D x k : Tensor) i j
  let B (i j : Fin 3) (x : Point) := φ i j x * bulkGradient a (u x) i j
  let E (i j : Fin 3) (x : Point) := (ε : ℝ) ^ 2 * (∑ k, K i j k x) + B i j x
  let μ := volume.restrict Ω
  have hK (i j k : Fin 3) : Integrable (K i j k) μ :=
    (integrable_gradient_test_entry (hu.locallyIntegrableOn_gradient hΩ k) (hφ i j) i j).integrableOn
  have hB (i j : Fin 3) : Integrable (B i j) μ := by
    have hInt : Integrable (fun x => φ i j x • bulkGradient a (u x) i j) volume :=
      (hφ i j).integrable_smul (hForce i j)
    exact hInt.integrableOn
  have hKS (i j : Fin 3) : Integrable (fun x => ∑ k, K i j k x) μ :=
    integrable_finsetSum _ (fun k _ => hK i j k)
  have hE (i j : Fin 3) : Integrable (E i j) μ := (hKS i j).const_mul _ |>.add (hB i j)
  have hEzero (i j : Fin 3) : (∫ x, E i j x ∂μ) = 0 := by
    have hvar := h i j (φ i j) (hφ i j)
    have hKeq (k : Fin 3) : (∫ x, K i j k x ∂μ) = ∫ x, K i j k x :=
      setIntegral_coordDeriv_mul_entry (hφ i j) i j k
    change (∫ x, (ε : ℝ) ^ 2 * (∑ k, K i j k x) + B i j x ∂μ) = 0
    rw [integral_add ((hKS i j).const_mul _) (hB i j),
      integral_const_mul, integral_finsetSum _ (fun k _ => hK i j k),
      Finset.sum_congr rfl (fun k _ => hKeq k)]
    have hBeq : (∫ x, B i j x ∂μ) = ∫ x, B i j x :=
      setIntegral_mul_force_entry a (u := u) (hφ i j) i j
    rw [hBeq]
    exact hvar
  have hPair (x : Point) :
      (∑ k, frobenius (D x k) (coordDeriv k P x)) = ∑ i, ∑ j, ∑ k, K i j k x := by
    simp only [frobenius_eq_sum]
    calc
      _ = ∑ i, ∑ k, ∑ j, (D x k : Tensor) i j * (coordDeriv k P x) i j := Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, (D x k : Tensor) i j * (coordDeriv k P x) i j :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        change (D x k : Tensor) i j * (coordDeriv k P x) i j =
          coordDeriv k (φ i j) x * (D x k : Tensor) i j
        rw [hcoord, mul_comm]
  have hForcePair (x : Point) :
      frobenius (bulkGradient a (u x)) (P x) = ∑ i, ∑ j, B i j x := by
    simp only [frobenius_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have hSplit (x : Point) :
      (ε : ℝ) ^ 2 * (∑ k, frobenius (D x k) (coordDeriv k P x)) +
        frobenius (bulkGradient a (u x)) (P x) = ∑ i, ∑ j, E i j x := by
    simp only [hPair, hForcePair, E, Finset.mul_sum, Finset.sum_add_distrib]
  rw [integral_congr_ae (Eventually.of_forall hSplit), integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => hE i j))]
  simp only [integral_finsetSum _ (fun j _ => hE _ j), hEzero, Finset.sum_const_zero]


/-- The matrix-valued weak equation of a local minimizer under the
three-dimensional Sobolev embedding on balls. -/
theorem integral_frobenius_eq_zero_of_localEnergyMinimizer
    (a : BulkCoefficients) (ε : ElasticScale) {u : Point → S0} {D : Point → Gradient}
    (hΩ : IsOpen Ω) (hu : IsLocalEnergyMinimizer a ε Ω u D) (hSob : ComparisonBallSobolevSix)
    {P : Point → Tensor} (hP : IsSmoothTest Ω P) :
    (∫ x in Ω, (ε : ℝ) ^ 2 * (∑ k, frobenius (D x k) (coordDeriv k P x)) +
      frobenius (bulkGradient a (u x)) (P x)) = 0 := by
  apply (isWeakEulerLagrange_of_localEnergyMinimizer a ε hΩ hu hSob
    ).integral_frobenius_eq_zero hΩ hu.1 _ hP
  intro i j
  apply locallyIntegrableOn_of_integrableOn_comparison_balls hΩ
  intro c r hr hcl
  letI := measure_ball_finite c r
  have hSix := hSob c r hr u D (hu.1 _ Metric.isOpen_ball (comparisonBall_compactlyContained hcl))
  exact integrable_bulkGradient_entry_of_memLp_six a hSix i j

theorem IsWeakEulerLagrange.congr_ae
    {a : BulkCoefficients} {ε : ElasticScale} {u v : Point → S0} {D G : Point → Gradient}
    (h : IsWeakEulerLagrange a ε Ω u D)
    (huv : u =ᵐ[volume.restrict Ω] v) (hDG : D =ᵐ[volume.restrict Ω] G) :
    IsWeakEulerLagrange a ε Ω v G := by
  intro i j φ hφ
  have hφ' : SmoothTest Ω φ := hφ
  have hgrad (k : Fin 3) :
      (∫ x, coordDeriv k φ x * (D x k : Tensor) i j) =
        (∫ x, coordDeriv k φ x * (G x k : Tensor) i j) := by
    rw [← setIntegral_coordDeriv_mul_entry (D := D) hφ' i j k,
      ← setIntegral_coordDeriv_mul_entry (D := G) hφ' i j k]
    exact integral_congr_ae
      (hDG.mono fun x hx => congrArg (fun A : Gradient => coordDeriv k φ x * (A k : Tensor) i j) hx)
  have hforce : (∫ x, φ x * bulkGradient a (u x) i j) = (∫ x, φ x * bulkGradient a (v x) i j) := by
    rw [← setIntegral_mul_force_entry a (u := u) hφ' i j,
      ← setIntegral_mul_force_entry a (u := v) hφ' i j]
    exact integral_congr_ae
      (huv.mono fun x hx => congrArg (fun A : S0 => φ x * bulkGradient a A i j) hx)
  have htest := h i j φ hφ
  rw [Finset.sum_congr rfl (fun k _ => hgrad k), hforce] at htest
  exact htest

/-- Identification of the actual weak gradient and pointwise equation
for a smooth representative of a weak solution. -/
theorem IsWeakEulerLagrange.classical_of_ae_representative
    {a : BulkCoefficients} {ε : ElasticScale} {u v : Point → S0} {D : Point → Gradient}
    (h : IsWeakEulerLagrange a ε Ω u D) (hΩ : IsOpen Ω) (hu : MemH1Loc Ω u D)
    (hv : ContDiffOn ℝ ∞ v Ω) (huv : u =ᵐ[volume.restrict Ω] v) :
    D =ᵐ[volume.restrict Ω] ClassicalGradient v ∧
      (∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian v x : S0).val = bulkGradient a (v x)) := by
  have hD := hu.ae_eq_classicalGradient hΩ (hv.of_le (by simp)) huv
  exact ⟨hD, eulerLagrange_pointwise_of_weak a ε hΩ hv (h.congr_ae huv hD)⟩

/-- The distributional equation `Δu = F`, with the actual weak derivative `D`. -/
structure IsWeakPoisson (Ω : Set Point) (D : Point → Gradient) (F : Point → Tensor) : Prop where
  locallyIntegrable : LocallyIntegrableOn F Ω volume
  test : ∀ (i j : Fin 3) (φ : Point → ℝ), SmoothTest Ω φ →
    (∑ k : Fin 3, ∫ x, coordDeriv k φ x * (D x k : Tensor) i j) +
      (∫ x, φ x * F x i j) = 0

/-- Interior Poisson regularity on open subsets of three-dimensional Euclidean
space, in the two forms used by the semilinear bootstrap. -/
structure InteriorPoissonRegularity : Prop where
  continuousRepresentative :
    ∀ {Ω : Set Point} {u : Point → S0} {D : Point → Gradient} {F : Point → Tensor},
      IsOpen Ω → MemH1Loc Ω u D → IsWeakPoisson Ω D F →
      (∃ M : ℝ, ∀ᵐ x ∂volume.restrict Ω, ‖F x‖ ≤ M) →
      ∃ v : Point → S0, u =ᵐ[volume.restrict Ω] v ∧ ContinuousOn v Ω
  contDiffOn_succ :
    ∀ {Ω : Set Point} {u : Point → S0} {D : Point → Gradient} {F : Point → Tensor} (n : ℕ),
      IsOpen Ω → MemH1Loc Ω u D → IsWeakPoisson Ω D F →
      ContinuousOn u Ω → ContDiffOn ℝ n F Ω → ContDiffOn ℝ (↑(n + 1) : WithTop ℕ∞) u Ω

theorem IsWeakEulerLagrange.isWeakPoisson
    {a : BulkCoefficients} {ε : ElasticScale} {u : Point → S0} {D : Point → Gradient}
    (h : IsWeakEulerLagrange a ε Ω u D)
    (hF : LocallyIntegrableOn (fun x => (ε : ℝ)⁻¹ ^ 2 • bulkGradient a (u x)) Ω volume) :
    IsWeakPoisson Ω D (fun x => (ε : ℝ)⁻¹ ^ 2 • bulkGradient a (u x)) := by
  refine ⟨hF, fun i j φ hφ => ?_⟩
  let G : ℝ := ∑ k : Fin 3, ∫ x, coordDeriv k φ x * (D x k : Tensor) i j
  let B : ℝ := ∫ x, φ x * bulkGradient a (u x) i j
  have hEL : (ε : ℝ) ^ 2 * G + B = 0 := h i j φ hφ
  have hcancel : (ε : ℝ)⁻¹ ^ 2 * (ε : ℝ) ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt ε.2.1), one_pow]
  change G + (∫ x, φ x * ((ε : ℝ)⁻¹ ^ 2 * bulkGradient a (u x) i j)) = 0
  simp_rw [mul_left_comm (φ _) ((ε : ℝ)⁻¹ ^ 2), integral_const_mul]
  change G + (ε : ℝ)⁻¹ ^ 2 * B = 0
  calc
    _ = (ε : ℝ)⁻¹ ^ 2 * ((ε : ℝ) ^ 2 * G + B) := by rw [mul_add, ← mul_assoc, hcancel, one_mul]
    _ = 0 := by rw [hEL, mul_zero]

private theorem locallyIntegrableOn_scaled_bulkGradient_of_bound
    (a : BulkCoefficients) (s : ℝ) {u : Point → S0} {D : Point → Gradient}
    (hΩ : IsOpen Ω) (hu : MemH1Loc Ω u D) {M : ℝ}
    (hBound : ∀ᵐ x ∂volume.restrict Ω, ‖u x‖ ≤ M) :
    LocallyIntegrableOn (fun x => s • bulkGradient a (u x)) Ω volume := by
  apply locallyIntegrableOn_of_integrableOn_comparison_balls hΩ
  intro c r _ hcl
  let B := Metric.ball c r
  letI := measure_ball_finite c r
  have huH := hu B Metric.isOpen_ball (comparisonBall_compactlyContained hcl)
  have hBW : B ⊆ Ω := Metric.ball_subset_closedBall.trans hcl
  have huFive : MemLp u (5 : ℕ) (volume.restrict B) :=
    MemLp.of_bound huH.1.1 M (ae_restrict_of_ae_restrict_of_subset hBW hBound)
  exact Integrable.smul s ((polynomialGrowth_bulkGradient a).integrable_comp
    (continuous_bulkGradient a) huFive)

/-- A bounded weak solution has a smooth representative, using only generic
interior Poisson regularity. Its classical gradient agrees with the original
weak gradient almost everywhere, and its equation holds pointwise. -/
theorem IsWeakEulerLagrange.exists_smoothRepresentative_of_eLpNorm_top_le
    {a : BulkCoefficients} {ε : ElasticScale} {u : Point → S0} {D : Point → Gradient}
    (h : IsWeakEulerLagrange a ε Ω u D) (hΩ : IsOpen Ω) (hu : MemH1Loc Ω u D)
    (hReg : InteriorPoissonRegularity) {M : ℝ}
    (hBound : eLpNorm u ⊤ (volume.restrict Ω) ≤ ENNReal.ofReal M) :
    ∃ v : Point → S0, u =ᵐ[volume.restrict Ω] v ∧ ContDiffOn ℝ ∞ v Ω ∧
      D =ᵐ[volume.restrict Ω] ClassicalGradient v ∧
      (∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian v x : S0).val = bulkGradient a (v x)) := by
  let s : ℝ := (ε : ℝ)⁻¹ ^ 2
  let F (w : Point → S0) (x : Point) : Tensor := s • bulkGradient a (w x)
  have hAEBound := ae_norm_le_of_eLpNorm_top_le hBound
  have hForceInt : LocallyIntegrableOn (F u) Ω volume :=
    locallyIntegrableOn_scaled_bulkGradient_of_bound a s hΩ hu hAEBound
  obtain ⟨K, _, hK⟩ := exists_bound_bulkGradient_on_norm_le a (le_max_left 0 M)
  have hForceBound : ∀ᵐ x ∂volume.restrict Ω, ‖F u x‖ ≤ s * K := by
    refine hAEBound.mono fun x hx => ?_
    change ‖s • bulkGradient a (u x)‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ s from sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hK (u x) hx) (sq_nonneg _)
  obtain ⟨v, huv, hvC⟩ := hReg.continuousRepresentative hΩ hu (h.isWeakPoisson hForceInt)
    ⟨_, hForceBound⟩
  have hV := hu.congr_ae huv Filter.EventuallyEq.rfl
  have hW := h.congr_ae huv Filter.EventuallyEq.rfl
  have hFv : LocallyIntegrableOn (F v) Ω volume :=
    (((continuous_bulkGradient a).comp_continuousOn hvC).const_smul s).locallyIntegrableOn hΩ.measurableSet
  have hP : IsWeakPoisson Ω D (F v) := hW.isWeakPoisson hFv
  have hv : ContDiffOn ℝ ∞ v Ω := by
    rw [contDiffOn_infty]
    intro n
    induction n with
    | zero => exact contDiffOn_zero.mpr hvC
    | succ n hn =>
      have hFn : ContDiffOn ℝ n (F v) Ω :=
        (((contDiff_infty.mp (contDiff_bulkGradient a)) n).comp_contDiffOn hn).const_smul s
      exact hReg.contDiffOn_succ n hΩ hV hP hvC hFn
  exact ⟨v, huv, hv, h.classical_of_ae_representative hΩ hu hv huv⟩

theorem exists_smoothRepresentative_of_localEnergyMinimizer_of_eLpNorm_top_le
    (a : BulkCoefficients) (ε : ElasticScale) {u : Point → S0} {D : Point → Gradient}
    (hΩ : IsOpen Ω) (hu : IsLocalEnergyMinimizer a ε Ω u D)
    (hReg : InteriorPoissonRegularity) {M : ℝ}
    (hBound : eLpNorm u ⊤ (volume.restrict Ω) ≤ ENNReal.ofReal M) :
    ∃ v : Point → S0, u =ᵐ[volume.restrict Ω] v ∧ ContDiffOn ℝ ∞ v Ω ∧
      D =ᵐ[volume.restrict Ω] ClassicalGradient v ∧
      (∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian v x : S0).val = bulkGradient a (v x)) :=
  let h := isWeakEulerLagrange_of_localEnergyMinimizer_of_eLpNorm_top_le a ε hΩ hu hBound
  h.exists_smoothRepresentative_of_eLpNorm_top_le hΩ hu.1 hReg hBound

/-- The scaled interior gradient estimate for the Poisson equation at the center
of a Euclidean ball. The constant is uniform in the center, radius, and data. -/
@[expose] def InteriorPoissonGradientEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (x : Point) (r : ℝ), 0 < r →
      ∀ (v : Point → S0) (F : Point → Tensor) (M K : ℝ),
        ContDiffOn ℝ 2 v (Metric.ball x r) →
        (∀ y ∈ Metric.ball x r, (laplacian v y : S0).val = F y) →
        (∀ y ∈ Metric.ball x r, ‖v y‖ ≤ M) →
        (∀ y ∈ Metric.ball x r, ‖F y‖ ≤ K) →
        r * Real.sqrt (gradientNormSq (ClassicalGradient v x)) ≤ C * (M + r ^ 2 * K)

/-- For fixed material parameters, field bound, and interior localization,
one scaled gradient bound works for all elastic scales and smooth solutions. -/
theorem exists_uniform_scaledGradient_bound
    (a : BulkCoefficients) {U : Set Point} (hΩ : IsOpen Ω)
    (hU : CompactlyContained U Ω) (hEstimate : InteriorPoissonGradientEstimate) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε : ElasticScale) (v : Point → S0), ContDiffOn ℝ ∞ v Ω →
        (∀ x ∈ Ω, ‖v x‖ ≤ max 0 M) →
        (∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian v x : S0).val = bulkGradient a (v x)) →
        ∀ x ∈ U, (ε : ℝ) * Real.sqrt (gradientNormSq (ClassicalGradient v x)) ≤ C := by
  obtain ⟨C₁, hC₁, hgrad⟩ := hEstimate
  obtain ⟨δ, hδ, hδΩ⟩ := hU.1.exists_thickening_subset_open hΩ hU.2
  let L : ℝ := max 1 δ⁻¹
  let M₀ := max 0 M
  have hL : 0 ≤ L := (zero_le_one : (0 : ℝ) ≤ 1).trans (le_max_left 1 δ⁻¹)
  have hM₀ : 0 ≤ M₀ := le_max_left 0 M
  obtain ⟨F₀, hF₀, hForce⟩ := exists_bound_bulkGradient_on_norm_le a hM₀
  refine ⟨L * (C₁ * (M₀ + F₀)) + 1,
    add_pos_of_nonneg_of_pos (mul_nonneg hL (mul_nonneg hC₁.le (add_nonneg hM₀ hF₀))) zero_lt_one, ?_⟩
  intro ε v hv hvBound hEq x hx
  let r := min (ε : ℝ) δ
  let s : ℝ := (ε : ℝ)⁻¹ ^ 2
  let F (y : Point) := s • bulkGradient a (v y)
  have hε : 0 < (ε : ℝ) := ε.2.1
  have hr : 0 < r := lt_min hε hδ
  have hsub : Metric.ball x r ⊆ Ω :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans
      ((Metric.ball_subset_thickening (subset_closure hx) δ).trans hδΩ)
  have hs : 0 ≤ s := sq_nonneg _
  have hinv : s * (ε : ℝ) ^ 2 = 1 := by
    change (ε : ℝ)⁻¹ ^ 2 * (ε : ℝ) ^ 2 = 1
    rw [← mul_pow, inv_mul_cancel₀ hε.ne', one_pow]
  have hEq' (y : Point) (hy : y ∈ Metric.ball x r) :
      (laplacian v y : S0).val = F y := by
    calc
      _ = s • ((ε : ℝ) ^ 2 • (laplacian v y : S0).val) := by
        rw [← mul_smul, hinv, one_smul]
      _ = F y := congrArg (s • ·) (hEq y (hsub hy))
  have hF (y : Point) (hy : y ∈ Metric.ball x r) : ‖F y‖ ≤ s * F₀ := by
    change ‖s • bulkGradient a (v y)‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left (hForce (v y) (hvBound y (hsub hy))) hs
  have hsmall : r * (ε : ℝ)⁻¹ ≤ 1 :=
    (mul_le_mul_of_nonneg_right (min_le_left (ε : ℝ) δ) (inv_nonneg.mpr hε.le)).trans_eq
      (mul_inv_cancel₀ hε.ne')
  have hscaledF : r ^ 2 * (s * F₀) ≤ F₀ := by
    calc
      _ = (r * (ε : ℝ)⁻¹) ^ 2 * F₀ := by unfold s; ring
      _ ≤ 1 ^ 2 * F₀ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg hr.le (inv_nonneg.mpr hε.le)) hsmall 2) hF₀
      _ = _ := by rw [one_pow, one_mul]
  have hεr : (ε : ℝ) ≤ L * r := by
    change (ε : ℝ) ≤ L * min (ε : ℝ) δ
    rcases le_total (ε : ℝ) δ with h | h
    · rw [min_eq_left h]
      exact le_mul_of_one_le_left hε.le (le_max_left _ _)
    · rw [min_eq_right h]
      exact ε.2.2.le.trans ((inv_mul_cancel₀ hδ.ne').symm.le.trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 δ⁻¹) hδ.le))
  have hq := hgrad x r hr v F M₀ (s * F₀) (((contDiffOn_infty.mp hv) 2).mono hsub) hEq'
    (fun y hy => hvBound y (hsub hy)) hF
  let g := Real.sqrt (gradientNormSq (ClassicalGradient v x))
  calc
    (ε : ℝ) * g ≤ (L * r) * g := mul_le_mul_of_nonneg_right hεr (Real.sqrt_nonneg _)
    _ = L * (r * g) := mul_assoc _ _ _
    _ ≤ L * (C₁ * (M₀ + r ^ 2 * (s * F₀))) := mul_le_mul_of_nonneg_left hq hL
    _ ≤ L * (C₁ * (M₀ + F₀)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hscaledF) hC₁.le) hL
    _ ≤ _ := le_add_of_nonneg_right zero_le_one

theorem pointwise_norm_le_of_ae_bound {v : Point → S0} {M : ℝ}
    (hΩ : IsOpen Ω) (hv : ContinuousOn v Ω)
    (hBound : ∀ᵐ x ∂volume.restrict Ω, ‖v x‖ ≤ M) :
    ∀ x ∈ Ω, ‖v x‖ ≤ M := by
  have h : (fun x => ‖v x‖) =ᵐ[volume.restrict Ω] fun x => min ‖v x‖ M :=
    hBound.mono fun _ hx => (min_eq_left hx).symm
  intro x hx
  have heq := Measure.eqOn_open_of_ae_eq h hΩ hv.norm (hv.norm.inf continuousOn_const) hx
  exact heq.trans_le (min_le_right _ _)

/-- Interior smoothness and the uniform scaled gradient estimate for bounded
weak Euler–Lagrange solutions. -/
theorem exists_uniform_scaledGradient_bound_for_weakSolutions
    (a : BulkCoefficients) {U : Set Point} (hΩ : IsOpen Ω) (hU : CompactlyContained U Ω)
    (hReg : InteriorPoissonRegularity) (hEstimate : InteriorPoissonGradientEstimate) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ElasticScale) (u : Point → S0) (D : Point → Gradient),
      MemH1Loc Ω u D → IsWeakEulerLagrange a ε Ω u D →
      eLpNorm u ⊤ (volume.restrict Ω) ≤ ENNReal.ofReal M →
      ∃ v : Point → S0, u =ᵐ[volume.restrict Ω] v ∧ ContDiffOn ℝ ∞ v Ω ∧
        D =ᵐ[volume.restrict Ω] ClassicalGradient v ∧
        (∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian v x : S0).val = bulkGradient a (v x)) ∧
        (∀ x ∈ U, (ε : ℝ) * Real.sqrt (gradientNormSq (ClassicalGradient v x)) ≤ C) ∧
        ENNReal.ofReal (ε : ℝ) *
          eLpNorm (fun x => Real.sqrt (gradientNormSq (D x))) ⊤ (volume.restrict U) ≤
            ENNReal.ofReal C := by
  have hUcl : CompactlyContained (closure U) Ω := by
    simpa only [CompactlyContained, closure_closure] using hU
  obtain ⟨C, hC, hGrad⟩ := exists_uniform_scaledGradient_bound a hΩ hUcl hEstimate M
  refine ⟨C, hC, fun ε u D hu hWeak hBound => ?_⟩
  obtain ⟨v, huv, hv, hD, hEq⟩ :=
    hWeak.exists_smoothRepresentative_of_eLpNorm_top_le hΩ hu hReg hBound
  have hAEBound : ∀ᵐ x ∂volume.restrict Ω, ‖v x‖ ≤ max 0 M := by
    filter_upwards [ae_norm_le_of_eLpNorm_top_le hBound, huv] with x hx heq
    simpa only [heq] using hx
  have hPoint := pointwise_norm_le_of_ae_bound hΩ hv.continuousOn hAEBound
  have hG := hGrad ε v hv hPoint hEq
  refine ⟨v, huv, hv, hD, hEq, fun x hx => hG x (subset_closure hx), ?_⟩
  have hεn : ‖(ε : ℝ)‖ₑ = ENNReal.ofReal (ε : ℝ) :=
    (ofReal_norm (ε : ℝ)).symm.trans (congrArg ENNReal.ofReal (Real.norm_of_nonneg ε.2.1.le))
  rw [← hεn, ← eLpNorm_const_smul, eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  refine ae_restrict_of_ae_restrict_of_subset subset_closure ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hU.2 hD,
    ae_restrict_mem isClosed_closure.measurableSet] with x hDx hx
  change ‖(ε : ℝ) * Real.sqrt (gradientNormSq (D x))‖ ≤ C
  rw [Real.norm_of_nonneg (mul_nonneg ε.2.1.le (Real.sqrt_nonneg _)), hDx]
  exact hG x hx

/-- Smooth representatives of bounded local minimizers satisfy the scaled gradient
bound with one constant for the whole family of elastic scales and minimizers. -/
theorem exists_uniform_scaledGradient_bound_for_localEnergyMinimizers
    (a : BulkCoefficients) {U : Set Point} (hΩ : IsOpen Ω) (hU : CompactlyContained U Ω)
    (hReg : InteriorPoissonRegularity) (hEstimate : InteriorPoissonGradientEstimate) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ElasticScale) (u : Point → S0) (D : Point → Gradient),
      IsLocalEnergyMinimizer a ε Ω u D →
      eLpNorm u ⊤ (volume.restrict Ω) ≤ ENNReal.ofReal M →
      ∃ v : Point → S0, u =ᵐ[volume.restrict Ω] v ∧ ContDiffOn ℝ ∞ v Ω ∧
        D =ᵐ[volume.restrict Ω] ClassicalGradient v ∧
        (∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian v x : S0).val = bulkGradient a (v x)) ∧
        (∀ x ∈ U, (ε : ℝ) * Real.sqrt (gradientNormSq (ClassicalGradient v x)) ≤ C) ∧
        ENNReal.ofReal (ε : ℝ) *
          eLpNorm (fun x => Real.sqrt (gradientNormSq (D x))) ⊤ (volume.restrict U) ≤
            ENNReal.ofReal C := by
  obtain ⟨C, hC, hGrad⟩ :=
    exists_uniform_scaledGradient_bound_for_weakSolutions a hΩ hU hReg hEstimate M
  refine ⟨C, hC, fun ε u D hMin hBound => ?_⟩
  exact hGrad ε u D hMin.1
    (isWeakEulerLagrange_of_localEnergyMinimizer_of_eLpNorm_top_le a ε hΩ hMin hBound) hBound

end Thesis

end

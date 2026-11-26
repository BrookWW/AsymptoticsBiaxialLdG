module

public import Thesis.Variational.CorrectionClosureBounds
public import Thesis.External.FractionalDirichlet
public import Thesis.Variational.WeakCorrectionInverse
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Thesis.Variational.BoundaryPoissonEstimate

/-! Uniform smooth-limit bounds for the actual averaged correction coefficients. -/

public section

open Filter MeasureTheory Metric Set Topology
open scoped BigOperators ContDiff ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance correctionCoefficientStateOperatorNormed : NormedAddCommGroup ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance correctionCoefficientStateOperatorSpace : NormedSpace ℝ ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance correctionCoefficientMaterialColumnNormed : NormedAddCommGroup (S0 →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance correctionCoefficientMaterialColumnSpace : NormedSpace ℝ (S0 →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance correctionCoefficientMaterialColumnSMul : ContinuousSMul ℝ (S0 →L[ℝ] S0) :=
  letI : IsBoundedSMul ℝ (S0 →L[ℝ] S0) :=
    IsBoundedSMul.of_norm_smul_le (correctionCoefficientMaterialColumnSpace.norm_smul_le)
  IsBoundedSMul.continuousSMul

local instance correctionCoefficientColumnDerivativeNormed :
    NormedAddCommGroup (Point →L[ℝ] S0 →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance correctionCoefficientPointTensorOperatorNormed :
    NormedAddCommGroup (Point →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance correctionCoefficientPointTensorOperatorSpace :
    NormedSpace ℝ (Point →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance correctionCoefficientStateFieldDerivativeNormed :
    NormedAddCommGroup (Point →L[ℝ] (S0 × Gradient)) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

@[expose] def correctionStateField (Q : Point → S0) (x : Point) : S0 × Gradient :=
  (Q x, ClassicalGradient Q x)

@[expose] def averagedCorrectionCoefficient (a : BulkCoefficients) (q Q : Point → S0)
    (x : Point) : (S0 × Gradient) →L[ℝ] S0 :=
  averagedHarmonicLinearization a (correctionStateField q x) (correctionStateField Q x)

private theorem exists_bound_eLpNorm_of_nonnegative_constant
    {U : Set Point} (hU : IsBoundedDomain U) (p : ℝ≥0∞) (K : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ MemLp (fun _ : Point => K) p (volume.restrict U) ∧
      eLpNorm (fun _ : Point => K) p (volume.restrict U) = ENNReal.ofReal L := by
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hU.2.2.measure_lt_top.ne
  have hK : MemLp (fun _ : Point => K) p (volume.restrict U) := memLp_const K
  refine ⟨(eLpNorm (fun _ : Point => K) p (volume.restrict U)).toReal,
    ENNReal.toReal_nonneg, hK, ?_⟩
  exact (ENNReal.ofReal_toReal hK.2.ne).symm

/-- Subtract the actual fixed Dirichlet lift and apply the global
second-derivative estimate with constants independent of the solution. -/
theorem exists_uniform_secondDerivativeLp_bound_of_fixedTrace
    (hPoisson : External.GlobalDirichletPoissonSecondDerivativeLp)
    {U : Set Point} (hU : IsSmoothDomain U) {b : Point → S0}
    (hb : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) b) (p M : ℝ) (hp : 1 < p) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Point → S0, ContDiffOn ℝ 2 v (closure U) → EqOn v b (frontier U) →
      (∀ x ∈ U, ‖v x‖ ≤ M ∧ ‖laplacian v x‖ ≤ M) →
      MemLp (fun x => ‖iteratedFDeriv ℝ 2 v x‖) (ENNReal.ofReal p) (volume.restrict U) ∧
        eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 v x‖) (ENNReal.ofReal p) (volume.restrict U) ≤ ENNReal.ofReal C := by
  obtain ⟨K, hK, hReg⟩ := hPoisson U hU p hp
  have hb₂ : ContDiff ℝ 2 b := hb.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨L, F, hL, hF, hbVal, hbΔ⟩ := exists_value_laplacian_bound_of_contDiffOn_closure hU hb₂.contDiffOn
  have hbD : Continuous (iteratedFDeriv ℝ 2 b) := hb.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨B, hB⟩ := hU.1.2.2.isCompact_closure.exists_bound_of_continuousOn
    hbD.continuousOn
  obtain ⟨N, hN, hnM, hnEq⟩ := exists_bound_eLpNorm_of_nonnegative_constant hU.1
    (ENNReal.ofReal p) (max B 0)
  let C := K*((M+L)+(M+F)) + N
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hp₁ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  refine ⟨C, hC, ?_⟩
  intro v hv hTrace hvBounds
  let w (x : Point) := v x - b x
  have hw : ContDiffOn ℝ 2 w (closure U) := hv.sub hb₂.contDiffOn
  have hwZero : EqOn w (fun _ => 0) (frontier U) := fun x hx => sub_eq_zero.mpr (hTrace hx)
  have hWV (x : Point) (hx : x ∈ U) : ‖w x‖ ≤ M+L :=
    (norm_sub_le _ _).trans (add_le_add (hvBounds x hx).1 (hbVal x hx))
  have hWF (x : Point) (hx : x ∈ U) : ‖laplacian w x‖ ≤ M+F := by
    change ‖laplacian (fun y => v y - b y) x‖ ≤ _
    rw [laplacian_sub_of_contDiffOn hU.1.1 (hv.mono subset_closure) hb₂.contDiffOn hx]
    exact (norm_sub_le _ _).trans (add_le_add (hvBounds x hx).2 (hbΔ x hx))
  obtain ⟨hMem,hNorm⟩ := hReg w hw hwZero (M+L) (M+F) (add_nonneg hM hL) (add_nonneg hM hF) hWV hWF
  let G (x : Point) := ‖iteratedFDeriv ℝ 2 w x‖ + max B 0
  have hG : MemLp G (ENNReal.ofReal p) (volume.restrict U) := hMem.add hnM
  have hMeas : AEStronglyMeasurable (fun x => ‖iteratedFDeriv ℝ 2 v x‖) (volume.restrict U) :=
    ((ContinuousOn.continuousOn_iteratedFDeriv (hv.mono subset_closure) hU.1.1 (by norm_num)).norm).aestronglyMeasurable
      hU.1.1.measurableSet
  have hDom : ∀ᵐ x ∂volume.restrict U, ‖‖iteratedFDeriv ℝ 2 v x‖‖ ≤ ‖G x‖ := by
    filter_upwards [ae_restrict_mem (μ := volume) hU.1.1.measurableSet] with x hx
    have hAt := ((hv.mono subset_closure) x hx).contDiffAt (hU.1.1.mem_nhds hx)
    have hSub : iteratedFDeriv ℝ 2 w x = iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 b x :=
      iteratedFDeriv_sub_apply hAt hb₂.contDiffAt
    have hV : iteratedFDeriv ℝ 2 v x = iteratedFDeriv ℝ 2 w x + iteratedFDeriv ℝ 2 b x :=
      (eq_sub_iff_add_eq.mp hSub).symm
    have hG₀ : 0 ≤ G x := add_nonneg (norm_nonneg _) (le_max_right _ _)
    rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg hG₀, hV]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((hB x (subset_closure hx)).trans (le_max_left _ _)))
  refine ⟨hG.of_le hMeas hDom, ?_⟩
  refine (eLpNorm_mono_ae hDom).trans ?_
  change eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 w x‖ + max B 0) (ENNReal.ofReal p) (volume.restrict U) ≤ _
  refine (eLpNorm_add_le hMem.1 hnM.1 hp₁).trans ?_
  rw [hnEq]
  exact (add_le_add hNorm le_rfl).trans_eq
    (ENNReal.ofReal_add (mul_nonneg hK.le (add_nonneg (add_nonneg hM hL) (add_nonneg hM hF))) hN).symm

theorem contDiffOn_correctionStateField
    {U : Set Point} (hU : IsOpen U) {Q : Point → S0}
    (hQ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (correctionStateField Q) U := by
  apply hQ.prodMk
  rw [contDiffOn_pi]
  intro j
  have hQd : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fderiv ℝ Q) U :=
    hQ.fderiv_of_isOpen hU (le_of_eq (by simp))
  exact (ContinuousLinearMap.apply ℝ S0 (axis j)).contDiff.comp_contDiffOn hQd

/-- The literal averaged coefficient field is smooth on the domain
where both matrix fields are smooth. -/
theorem contDiffOn_averagedCorrectionCoefficient
    (a : BulkCoefficients) {U : Set Point} (hU : IsOpen U) {q Q : Point → S0}
    (hq : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) q U)
    (hQ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (averagedCorrectionCoefficient a q Q) U := by
  have hZ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω)
      (fun x : Point => (correctionStateField q x, correctionStateField Q x)) U :=
    (contDiffOn_correctionStateField hU hq).prodMk (contDiffOn_correctionStateField hU hQ)
  exact (contDiff_averagedHarmonicLinearization a).comp_contDiffOn hZ

private theorem norm_fderiv_correctionStateField_le
    {U : Set Point} (hU : IsOpen U) {Q : Point → S0}
    (hQ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U) {x : Point} (hx : x ∈ U) :
    ‖fderiv ℝ (correctionStateField Q) x‖ ≤
      Real.sqrt (gradientNormSq (ClassicalGradient Q x)) + ‖iteratedFDeriv ℝ 2 Q x‖ := by
  have hAt := (hQ x hx).contDiffAt (hU.mem_nhds hx)
  have hQ₂ : ContDiffAt ℝ 2 Q x := hAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hF := (hQ₂.fderiv_right_succ (n := 1)).differentiableAt one_ne_zero
  have hGrad : DifferentiableAt ℝ (ClassicalGradient Q) x := by
    apply differentiableAt_pi.mpr
    intro i
    let L := ContinuousLinearMap.apply ℝ S0 (axis i)
    change DifferentiableAt ℝ (L ∘ fderiv ℝ Q) x
    exact L.differentiableAt.comp x hF
  have hAt₁ : DifferentiableAt ℝ Q x := hQ₂.differentiableAt two_ne_zero
  have hD := (hAt₁.hasFDerivAt.prodMk hGrad.hasFDerivAt).fderiv
  change fderiv ℝ (correctionStateField Q) x = _ at hD
  let H := Real.sqrt (gradientNormSq (ClassicalGradient Q x))
  let F := ‖iteratedFDeriv ℝ 2 Q x‖
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hF₀ : 0 ≤ F := norm_nonneg _
  change ‖fderiv ℝ (correctionStateField Q) x‖ ≤ H+F
  rw [hD]
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hH hF₀)
  intro z
  rw [ContinuousLinearMap.prod_apply, Prod.norm_def]
  apply max_le
  · have hN := norm_gradientFromColumns_le (ClassicalGradient Q x) z
    rw [gradientFromColumns_classicalGradient] at hN
    exact hN.trans (by have := mul_nonneg hF₀ (norm_nonneg z); dsimp only [H]; nlinarith)
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg (add_nonneg hH hF₀) (norm_nonneg z))).2
    intro i
    let E := ContinuousLinearMap.apply ℝ S0 (axis i)
    let P : Gradient →L[ℝ] S0 := ContinuousLinearMap.proj i
    have hi := ((P.hasFDerivAt (x := ClassicalGradient Q x)).comp x hGrad.hasFDerivAt).fderiv
    have hv := ((E.hasFDerivAt (x := fderiv ℝ Q x)).comp x hF.hasFDerivAt).fderiv
    have hEq : (fderiv ℝ (ClassicalGradient Q) x z) i =
        (fderiv ℝ (fderiv ℝ Q) x z) (axis i) :=
      (DFunLike.congr_fun hi z).symm.trans (DFunLike.congr_fun hv z)
    have hPair : (fderiv ℝ (fderiv ℝ Q) x z) (axis i) = iteratedFDeriv ℝ 2 Q x ![z, axis i] := by
      rw [iteratedFDeriv_two_apply]
      rfl
    change ‖(fderiv ℝ (ClassicalGradient Q) x z) i‖ ≤ _
    rw [hEq, hPair]
    have hAxis : ‖axis i‖ = 1 := by simp [axis]
    have hN := (iteratedFDeriv ℝ 2 Q x).le_opNorm ![z, axis i]
    have hV : ‖iteratedFDeriv ℝ 2 Q x ![z, axis i]‖ ≤ F * ‖z‖ := by
      simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hAxis, mul_one] using hN
    exact hV.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hH) (norm_nonneg _))

/-- The averaged first-order coefficients and their \(L^p\) derivatives
are uniformly controlled by the actual state and second-derivative norms. -/
theorem exists_boundedDirichletCorrectionCoefficients_of_secondDerivativeLp
    (a : BulkCoefficients) {U : Set Point} (hU : IsBoundedDomain U)
    (p M N : ℝ) (hp : 1 < p) (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q Q : Point → S0,
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) q U → ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U →
      (∀ x ∈ U, ‖q x‖ ≤ M ∧ Real.sqrt (gradientNormSq (ClassicalGradient q x)) ≤ M ∧
        ‖Q x‖ ≤ M ∧ Real.sqrt (gradientNormSq (ClassicalGradient Q x)) ≤ M) →
      MemLp (fun x => ‖iteratedFDeriv ℝ 2 q x‖) (ENNReal.ofReal p) (volume.restrict U) →
      MemLp (fun x => ‖iteratedFDeriv ℝ 2 Q x‖) (ENNReal.ofReal p) (volume.restrict U) →
      eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 q x‖) (ENNReal.ofReal p) (volume.restrict U) ≤ ENNReal.ofReal N →
      eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 Q x‖) (ENNReal.ofReal p) (volume.restrict U) ≤ ENNReal.ofReal N →
      HasBoundedDirichletCorrectionCoefficients U p C (averagedCorrectionCoefficient a q Q) := by
  let E := (S0 × Gradient) × (S0 × Gradient)
  let L (z : E) := averagedHarmonicLinearization a z.1 z.2
  let B (j : Fin 3) (z : E) : S0 →L[ℝ] S0 :=
    (L z).comp ((ContinuousLinearMap.inr ℝ S0 Gradient).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => S0) j))
  let D := Metric.closedBall (0 : E) M
  letI : NormedAddCommGroup (E →L[ℝ] S0 →L[ℝ] S0) :=
    ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)
  letI : NormedAddCommGroup (Point →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)
  have hL : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) L := contDiff_averagedHarmonicLinearization a
  have hB (j : Fin 3) : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (B j) := hL.clm_comp contDiff_const
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E) M).exists_bound_of_continuousOn hL.continuous.continuousOn
  have hBd (j : Fin 3) : ∃ C, ∀ z ∈ D, ‖fderiv ℝ (B j) z‖ ≤ C :=
    (isCompact_closedBall (0 : E) M).exists_bound_of_continuousOn ((hB j).continuous_fderiv (by simp)).continuousOn
  choose Kj hKj using hBd
  let A := ∑ j : Fin 3, max (Kj j) 0
  have hA : 0 ≤ A := Finset.sum_nonneg fun j _ => le_max_right _ _
  have hAK (j : Fin 3) (z : E) (hz : z ∈ D) : ‖fderiv ℝ (B j) z‖ ≤ A :=
    ((hKj j z hz).trans (le_max_left _ _)).trans (Finset.single_le_sum (fun i _ => le_max_right _ _) (Finset.mem_univ j))
  obtain ⟨K₀, hK₀, hK₀Mem, hK₀Norm⟩ := exists_bound_eLpNorm_of_nonnegative_constant hU (ENNReal.ofReal p) M
  let C := max K 0 + A*(K₀+N+N)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro q Q hq hQ hData hq₂ hQ₂ hqNorm hQNorm
  let z (x : Point) := (correctionStateField q x, correctionStateField Q x)
  have hz : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) z U :=
    (contDiffOn_correctionStateField hU.1 hq).prodMk (contDiffOn_correctionStateField hU.1 hQ)
  have hCL : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (averagedCorrectionCoefficient a q Q) U :=
    hL.comp_contDiffOn hz
  have hG (x : Point) (hx : x ∈ U) : z x ∈ D := by
    apply mem_closedBall_zero_iff.mpr
    have hGrad (Q : Point → S0) (hG : Real.sqrt (gradientNormSq (ClassicalGradient Q x)) ≤ M) :
        ‖ClassicalGradient Q x‖ ≤ M := by
      apply (pi_norm_le_iff_of_nonneg hM).2
      intro j
      refine (Real.le_sqrt_of_sq_le ?_).trans hG
      rw [gradientNormSq_eq_sum_norm_sq]
      exact Finset.single_le_sum (f := fun i : Fin 3 => ‖ClassicalGradient Q x i‖^2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    rw [Prod.norm_def, Prod.norm_def, Prod.norm_def]
    exact max_le (max_le (hData x hx).1 (hGrad q (hData x hx).2.1))
      (max_le (hData x hx).2.2.1 (hGrad Q (hData x hx).2.2.2))
  have hCoeff : ∀ᵐ x ∂volume.restrict U, ‖averagedCorrectionCoefficient a q Q x‖ ≤ C := by
    filter_upwards [ae_restrict_mem (μ := volume) hU.1.measurableSet] with x hx
    exact ((hK (z x) (hG x hx)).trans (le_max_left _ _)).trans
      (le_add_of_nonneg_right (mul_nonneg hA (by positivity)))
  refine ⟨hCL.continuousOn.aestronglyMeasurable hU.1.measurableSet, hCoeff, ?_⟩
  intro j
  let G (x : Point) := M + ‖iteratedFDeriv ℝ 2 q x‖ + ‖iteratedFDeriv ℝ 2 Q x‖
  have hG₀ (x : Point) : 0 ≤ G x := by dsimp only [G]; positivity
  have hGLp : MemLp G (ENNReal.ofReal p) (volume.restrict U) := (hK₀Mem.add hq₂).add hQ₂
  have hp₁ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hGL : eLpNorm G (ENNReal.ofReal p) (volume.restrict U) ≤ ENNReal.ofReal (K₀+N+N) := by
    refine (eLpNorm_add_le (hK₀Mem.add hq₂).1 hQ₂.1 hp₁).trans ?_
    refine (add_le_add ((eLpNorm_add_le hK₀Mem.1 hq₂.1 hp₁).trans (add_le_add hK₀Norm.le hqNorm)) hQNorm).trans_eq ?_
    rw [ENNReal.ofReal_add (add_nonneg hK₀ hN) hN, ENNReal.ofReal_add hK₀ hN]
  let F (x : Point) := ‖fderiv ℝ (correctionFirstOrderColumn (averagedCorrectionCoefficient a q Q) j) x‖
  have hb : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (correctionFirstOrderColumn (averagedCorrectionCoefficient a q Q) j) U :=
    (hB j).comp_contDiffOn hz
  have hFm : AEStronglyMeasurable F (volume.restrict U) :=
    ((hb.continuousOn_fderiv_of_isOpen hU.1 (by simp)).norm).aestronglyMeasurable hU.1.measurableSet
  have hDom : ∀ᵐ x ∂volume.restrict U, ‖F x‖ ≤ A * ‖G x‖ := by
    filter_upwards [ae_restrict_mem (μ := volume) hU.1.measurableSet] with x hx
    have hD : fderiv ℝ (correctionFirstOrderColumn (averagedCorrectionCoefficient a q Q) j) x =
        (fderiv ℝ (B j) (z x)).comp (fderiv ℝ z x) :=
      fderiv_comp x ((hB j).differentiable (by simp) (z x))
        (((hz x hx).contDiffAt (hU.1.mem_nhds hx)).differentiableAt (by simp))
    have hZ' : ‖fderiv ℝ z x‖ ≤ G x := by
      have hd := (((contDiffOn_correctionStateField hU.1 hq x hx).contDiffAt (hU.1.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.prodMk
        (((contDiffOn_correctionStateField hU.1 hQ x hx).contDiffAt (hU.1.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
      have hdEq := hd.fderiv
      change fderiv ℝ z x = _ at hdEq
      rw [hdEq]
      apply ContinuousLinearMap.opNorm_le_bound _ (hG₀ x)
      intro v
      rw [ContinuousLinearMap.prod_apply, Prod.norm_def]
      apply max_le
      · refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg v))
        exact (norm_fderiv_correctionStateField_le hU.1 hq hx).trans (by
          dsimp only [G]
          linarith only [(hData x hx).2.1, norm_nonneg (iteratedFDeriv ℝ 2 Q x)])
      · refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg v))
        exact (norm_fderiv_correctionStateField_le hU.1 hQ hx).trans (by
          dsimp only [G]
          linarith only [(hData x hx).2.2.2, norm_nonneg (iteratedFDeriv ℝ 2 q x)])
    change ‖‖fderiv ℝ (correctionFirstOrderColumn (averagedCorrectionCoefficient a q Q) j) x‖‖ ≤ _
    rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (hG₀ x), hD]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hAK j (z x) (hG x hx)) hZ' (norm_nonneg _) hA)
  refine ⟨hb.of_le (WithTop.coe_le_coe.mpr le_top), hGLp.of_le_mul hFm hDom, ?_⟩
  refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hDom _).trans ?_
  calc
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (K₀+N+N) := mul_le_mul_right hGL _
    _ = ENNReal.ofReal (A*(K₀+N+N)) := (ENNReal.ofReal_mul hA).symm
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (le_max_right K 0))

end Thesis

end

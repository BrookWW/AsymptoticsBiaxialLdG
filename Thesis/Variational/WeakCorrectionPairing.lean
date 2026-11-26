module

public import Thesis.Variational.WeakInverse
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-! Bounded weak correction operators on the frozen zero-trace Sobolev graph. -/

public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal Matrix Matrix.Norms.Frobenius RealInnerProductSpace

set_option autoImplicit false
noncomputable section

namespace Thesis

private abbrev CorrectionState := S0 × Gradient
private abbrev TensorL2 (U : Set Point) := Lp S0 2 (volume.restrict U)
private abbrev StateL2 (U : Set Point) := Lp CorrectionState 2 (volume.restrict U)
private abbrev CoordL2 (U : Set Point) := Lp (EuclideanSpace ℝ (Fin 5)) 2 (volume.restrict U)

local instance correctionPairingL2Fact : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

local instance correctionStateActionNorm : NormedAddCommGroup ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance correctionStateInsertNorm : NormedAddCommGroup (S0 →L[ℝ] (S0 × Gradient)) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance correctionGradientInsertNorm : NormedAddCommGroup (S0 →L[ℝ] Gradient) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance correctionHMinusOneNormed (U : Set Point) : NormedAddCommGroup (HMinusOne U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance correctionHMinusOneNormedSpace (U : Set Point) : NormedSpace ℝ (HMinusOne U) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance weakCorrectionPairingInverseNormed (U : Set Point) :
    NormedAddCommGroup (HMinusOne U →L[ℝ] H10 U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance weakCorrectionPairingOperatorNormed (U : Set Point) :
    NormedAddCommGroup (H10 U →L[ℝ] HMinusOne U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance weakCorrectionPairingTensorComplete : CompleteSpace S0 := complete_of_proper

local instance weakCorrectionPairingH10Complete (U : Set Point) : CompleteSpace (H10 U) :=
  isClosed_closure.completeSpace_coe

private def h10ValueL2 (U : Set Point) : H10 U →L[ℝ] TensorL2 U :=
  (ContinuousLinearMap.fst ℝ (TensorL2 U) (Fin 3 → TensorL2 U)).comp (h10Submodule U).subtypeL

private def h10ColumnL2 (U : Set Point) (j : Fin 3) : H10 U →L[ℝ] TensorL2 U :=
  (ContinuousLinearMap.proj j).comp
    ((ContinuousLinearMap.snd ℝ (TensorL2 U) (Fin 3 → TensorL2 U)).comp (h10Submodule U).subtypeL)

private theorem norm_h10ValueL2_le {U : Set Point} (v : H10 U) : ‖h10ValueL2 U v‖ ≤ ‖v‖ := by
  change ‖v.val.1‖ ≤ ‖v.val‖
  rw [Prod.norm_def]
  exact le_max_left _ _

private theorem norm_h10ColumnL2_le {U : Set Point} (v : H10 U) (j : Fin 3) :
    ‖h10ColumnL2 U j v‖ ≤ ‖v‖ := by
  change ‖v.val.2 j‖ ≤ ‖v.val‖
  rw [Prod.norm_def]
  exact (norm_le_pi_norm v.val.2 j).trans (le_max_right _ _)

private def stateInsertValue : S0 →L[ℝ] CorrectionState := ContinuousLinearMap.inl ℝ S0 Gradient

private def stateInsertColumn (j : Fin 3) : S0 →L[ℝ] CorrectionState :=
  (ContinuousLinearMap.inr ℝ S0 Gradient).comp (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => S0) j)

private def h10StateL2 (U : Set Point) : H10 U →L[ℝ] StateL2 U :=
  (stateInsertValue.compLpL 2 (volume.restrict U)).comp (h10ValueL2 U) +
    ∑ j : Fin 3, ((stateInsertColumn j).compLpL 2 (volume.restrict U)).comp (h10ColumnL2 U j)

private theorem h10StateL2_ae {U : Set Point} (v : H10 U) :
    (h10StateL2 U v : Point → CorrectionState) =ᵐ[volume.restrict U]
      fun x => (h10Value v x, h10Gradient v x) := by
  classical
  let V := stateInsertValue.compLpL 2 (volume.restrict U) (h10ValueL2 U v)
  let G (j : Fin 3) := (stateInsertColumn j).compLpL 2 (volume.restrict U) (h10ColumnL2 U j v)
  have hL : h10StateL2 U v = V + ∑ j, G j := by
    simp only [h10StateL2, add_apply, sum_apply, ContinuousLinearMap.comp_apply, V, G]
  rw [hL]
  have hV := ContinuousLinearMap.coeFn_compLpL stateInsertValue (h10ValueL2 U v)
  have hG (j : Fin 3) : (G j : Point → CorrectionState) =ᵐ[volume.restrict U]
      fun x => stateInsertColumn j (h10ColumnL2 U j v x) :=
    ContinuousLinearMap.coeFn_compLpL (stateInsertColumn j) (h10ColumnL2 U j v)
  filter_upwards [Lp.coeFn_add V (∑ j, G j), Lp.coeFn_finsetSum Finset.univ G, hV,
    Filter.eventually_all.mpr hG] with x h₁ h₂ h₃ h₄
  change (V + ∑ j, G j) x = (h10Value v x, h10Gradient v x)
  rw [h₁]
  change V x + (∑ j, G j) x = _
  rw [h₂]
  change V x + (∑ j, G j x) = _
  rw [h₃, Finset.sum_congr rfl (fun j _ => h₄ j)]
  change (h10Value v x, (0 : Gradient)) + (∑ j : Fin 3, ((0 : S0), Pi.single j (h10Gradient v x j))) = _
  apply Prod.ext
  · simp [Prod.fst_sum]
  · funext j
    simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

private theorem norm_h10StateL2_le {U : Set Point} (v : H10 U) : ‖h10StateL2 U v‖ ≤ 4 * ‖v‖ := by
  have hV : ‖stateInsertValue.compLpL 2 (volume.restrict U) (h10ValueL2 U v)‖ ≤ ‖v‖ := by
    exact (stateInsertValue.norm_compLp_le _).trans
      ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_inl_le_one (𝕜 := ℝ) (E := S0)
          (F := Gradient)) (norm_nonneg _)).trans (by simpa only [one_mul] using norm_h10ValueL2_le v))
  have hG (j : Fin 3) : ‖(stateInsertColumn j).compLpL 2 (volume.restrict U) (h10ColumnL2 U j v)‖ ≤ ‖v‖ := by
    have hC : ‖stateInsertColumn j‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ) (E := S0) (F := Gradient))
        (ContinuousLinearMap.norm_single_le_one ℝ (fun _ : Fin 3 => S0) j)
        (norm_nonneg (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => S0) j)) zero_le_one).trans_eq
        (one_mul _))
    exact ((stateInsertColumn j).norm_compLp_le _).trans
      ((mul_le_mul_of_nonneg_right hC (norm_nonneg _)).trans (by simpa only [one_mul] using norm_h10ColumnL2_le v j))
  simp only [h10StateL2, add_apply, sum_apply, ContinuousLinearMap.comp_apply]
  refine (norm_add_le _ _).trans (add_le_add hV ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hG j))) |>.trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  ring

private def tensorCoordinateL2 (U : Set Point) : TensorL2 U →L[ℝ] CoordL2 U :=
  frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 (volume.restrict U)

private theorem tensorCoordinateL2_ae {U : Set Point} (u : TensorL2 U) :
    (tensorCoordinateL2 U u : Point → EuclideanSpace ℝ (Fin 5)) =ᵐ[volume.restrict U]
      fun x => frobeniusCoordinateEquiv (u x) :=
  ContinuousLinearMap.coeFn_compLpL frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap u

private theorem norm_tensorCoordinateL2_le {U : Set Point} (u : TensorL2 U) :
    ‖tensorCoordinateL2 U u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [tensorCoordinateL2_ae u] with x hx
  rw [hx, LinearIsometryEquiv.norm_map]

private def h10PullbackInner {U : Set Point} (A B : H10 U →L[ℝ] CoordL2 U) : H10 U →L[ℝ] HMinusOne U :=
  let I : CoordL2 U →L[ℝ] CoordL2 U →L[ℝ] ℝ := innerSL ℝ
  ((ContinuousLinearMap.precompR (H10 U) I).flip B).comp A

private theorem h10PullbackInner_apply {U : Set Point} (A B : H10 U →L[ℝ] CoordL2 U) (v w : H10 U) :
    h10PullbackInner A B v w = inner ℝ (A v) (B w) := rfl

/-- The actual gradient column as an element of the Frobenius Hilbert coordinate space. -/
def h10FrobeniusColumnL2 (U : Set Point) (j : Fin 3) : H10 U →L[ℝ]
    Lp (EuclideanSpace ℝ (Fin 5)) 2 (volume.restrict U) :=
  (tensorCoordinateL2 U).comp (h10ColumnL2 U j)

theorem norm_h10FrobeniusColumnL2 {U : Set Point} (j : Fin 3) (v : H10 U) :
    ‖h10FrobeniusColumnL2 U j v‖ = ‖v.val.2 j‖ := by
  change ‖tensorCoordinateL2 U (h10ColumnL2 U j v)‖ = ‖h10ColumnL2 U j v‖
  refine le_antisymm (norm_tensorCoordinateL2_le _) (Lp.norm_le_norm_of_ae_le ?_)
  filter_upwards [tensorCoordinateL2_ae (h10ColumnL2 U j v)] with x hx
  rw [hx,LinearIsometryEquiv.norm_map]

/-- The pure Dirichlet Laplacian on the actual zero-trace Sobolev graph. -/
def h10PrincipalPart (U : Set Point) : H10 U →L[ℝ] HMinusOne U :=
  -∑ j : Fin 3, h10PullbackInner ((tensorCoordinateL2 U).comp (h10ColumnL2 U j))
    ((tensorCoordinateL2 U).comp (h10ColumnL2 U j))

theorem h10PrincipalPart_apply_coordinate_inner {U : Set Point} (v w : H10 U) :
    h10PrincipalPart U v w =
      -(∑ j : Fin 3, inner ℝ (h10FrobeniusColumnL2 U j v) (h10FrobeniusColumnL2 U j w)) := by
  simp only [h10PrincipalPart, neg_apply, sum_apply, h10PullbackInner_apply, h10FrobeniusColumnL2]

theorem h10PrincipalPart_apply {U : Set Point} (v w : H10 U) :
    h10PrincipalPart U v w = ∫ x in U, -(∑ j, frobeniusS0 (h10Gradient v x j) (h10Gradient w x j)) := by
  have hI (j : Fin 3) :
      IntegrableOn (fun x => frobeniusS0 (h10Gradient v x j) (h10Gradient w x j)) U volume := by
    have h := L2.integrable_inner (𝕜 := ℝ) (tensorCoordinateL2 U (h10ColumnL2 U j v))
      (tensorCoordinateL2 U (h10ColumnL2 U j w))
    apply h.congr
    filter_upwards [tensorCoordinateL2_ae (h10ColumnL2 U j v), tensorCoordinateL2_ae (h10ColumnL2 U j w)]
      with x hx hy
    rw [hx, hy, frobeniusCoordinateEquiv_inner]
    rfl
  have hE (j : Fin 3) :
      h10PullbackInner ((tensorCoordinateL2 U).comp (h10ColumnL2 U j))
        ((tensorCoordinateL2 U).comp (h10ColumnL2 U j)) v w =
      ∫ x in U, frobeniusS0 (h10Gradient v x j) (h10Gradient w x j) := by
    rw [h10PullbackInner_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [tensorCoordinateL2_ae (h10ColumnL2 U j v), tensorCoordinateL2_ae (h10ColumnL2 U j w)]
      with x hx hy
    change inner ℝ (tensorCoordinateL2 U (h10ColumnL2 U j v) x)
      (tensorCoordinateL2 U (h10ColumnL2 U j w) x) = _
    rw [hx, hy, frobeniusCoordinateEquiv_inner]
    rfl
  simp only [h10PrincipalPart, neg_apply, sum_apply, hE, integral_neg, integral_finsetSum _ (fun j _ => hI j)]

private theorem memLp_action_on_h10State {U : Set Point}
    (A : Point → CorrectionState →L[ℝ] S0)
    (hA : AEStronglyMeasurable A (volume.restrict U))
    {M : ℝ} (hM : ∀ᵐ x ∂volume.restrict U, ‖A x‖ ≤ M)
    (v : H10 U) :
    MemLp (fun x => A x (h10StateL2 U v x)) 2 (volume.restrict U) := by
  apply (Lp.memLp (h10StateL2 U v)).of_le_mul
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk (Lp.aestronglyMeasurable _))
  · filter_upwards [hM] with x hx
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

private def lowerActionOnH10 {U : Set Point}
    (A : Point → CorrectionState →L[ℝ] S0) (hA : AEStronglyMeasurable A (volume.restrict U))
    (M : ℝ) (hM₀ : 0 ≤ M) (hM : ∀ᵐ x ∂volume.restrict U, ‖A x‖ ≤ M) :
    H10 U →L[ℝ] TensorL2 U := by
  let T (v : H10 U) := (memLp_action_on_h10State A hA hM v).toLp _
  have hT (v : H10 U) : (T v : Point → S0) =ᵐ[volume.restrict U]
      fun x => A x (h10StateL2 U v x) := (memLp_action_on_h10State A hA hM v).coeFn_toLp
  let L : H10 U →ₗ[ℝ] TensorL2 U :=
    { toFun := T
      map_add' := by
        intro v w
        apply Lp.ext
        have hadd := Lp.coeFn_add (h10StateL2 U v) (h10StateL2 U w)
        filter_upwards [hT (v + w), hT v, hT w, Lp.coeFn_add (T v) (T w), hadd]
          with x h₁ h₂ h₃ h₄ h₅
        have h₆ : h10StateL2 U (v + w) x = h10StateL2 U v x + h10StateL2 U w x := by
          rw [map_add]
          exact h₅
        change T (v + w) x = (T v + T w) x
        rw [h₁, h₆, map_add, h₄]
        exact congrArg₂ (· + ·) h₂.symm h₃.symm
      map_smul' := by
        intro c v
        apply Lp.ext
        have hsmul := Lp.coeFn_smul c (h10StateL2 U v)
        filter_upwards [hT (c • v), hT v, Lp.coeFn_smul c (T v), hsmul] with x h₁ h₂ h₃ h₄
        have h₅ : h10StateL2 U (c • v) x = c • h10StateL2 U v x := by
          rw [map_smul]
          exact h₄
        change T (c • v) x = (c • T v) x
        rw [h₁, h₅, map_smul, h₃]
        exact congrArg (c • ·) h₂.symm }
  refine L.mkContinuous (4 * M) fun v => ?_
  change ‖T v‖ ≤ 4 * M * ‖v‖
  have hNorm : ‖T v‖ ≤ M * ‖h10StateL2 U v‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hT v, hM] with x h₁ h₂
    rw [h₁]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h₂ (norm_nonneg _))
  exact hNorm.trans ((mul_le_mul_of_nonneg_left (norm_h10StateL2_le v) hM₀).trans_eq (by ring))

private theorem lowerActionOnH10_ae {U : Set Point}
    (A : Point → CorrectionState →L[ℝ] S0) (hA : AEStronglyMeasurable A (volume.restrict U))
    (M : ℝ) (hM₀ : 0 ≤ M) (hM : ∀ᵐ x ∂volume.restrict U, ‖A x‖ ≤ M) (v : H10 U) :
    (lowerActionOnH10 A hA M hM₀ hM v : Point → S0) =ᵐ[volume.restrict U]
      fun x => A x (h10Value v x, h10Gradient v x) := by
  have h := (memLp_action_on_h10State A hA hM v).coeFn_toLp
  exact h.trans ((h10StateL2_ae v).mono fun x hx => congrArg (A x) hx)

private theorem norm_lowerActionOnH10_le {U : Set Point}
    (A : Point → CorrectionState →L[ℝ] S0) (hA : AEStronglyMeasurable A (volume.restrict U))
    (M : ℝ) (hM₀ : 0 ≤ M) (hM : ∀ᵐ x ∂volume.restrict U, ‖A x‖ ≤ M) (v : H10 U) :
    ‖lowerActionOnH10 A hA M hM₀ hM v‖ ≤ 4 * M * ‖v‖ := by
  refine (ContinuousLinearMap.le_opNorm _ v).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  unfold lowerActionOnH10
  exact LinearMap.mkContinuous_norm_le _ (mul_nonneg (by norm_num) hM₀) _

private theorem exists_lowerOperator_on_H10 {U : Set Point}
    (A : Point → CorrectionState →L[ℝ] S0) (hA : AEStronglyMeasurable A (volume.restrict U))
    (M : ℝ) (hM₀ : 0 ≤ M) (hM : ∀ᵐ x ∂volume.restrict U, ‖A x‖ ≤ M) :
    ∃ P : H10 U →L[ℝ] HMinusOne U, ‖P‖ ≤ 4 * M ∧ ∀ v w : H10 U,
      IntegrableOn (fun x => frobeniusS0 (A x (h10Value v x, h10Gradient v x)) (h10Value w x)) U volume ∧
      P v w = ∫ x in U, frobeniusS0 (A x (h10Value v x, h10Gradient v x)) (h10Value w x) := by
  let L := lowerActionOnH10 A hA M hM₀ hM
  let V := (tensorCoordinateL2 U).comp L
  let W := (tensorCoordinateL2 U).comp (h10ValueL2 U)
  let P := h10PullbackInner V W
  refine ⟨P, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hM₀)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg (by norm_num) hM₀) (norm_nonneg _))
    intro w
    change |P v w| ≤ 4 * M * ‖v‖ * ‖w‖
    rw [show P v w = inner ℝ (V v) (W w) from h10PullbackInner_apply V W v w]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul
      ((norm_tensorCoordinateL2_le (L v)).trans (norm_lowerActionOnH10_le A hA M hM₀ hM v))
      ((norm_tensorCoordinateL2_le (h10ValueL2 U w)).trans (norm_h10ValueL2_le w))
      (norm_nonneg _) (by positivity))
  · intro v w
    have hAe : (fun x => inner ℝ (V v x) (W w x)) =ᵐ[volume.restrict U]
        fun x => frobeniusS0 (A x (h10Value v x, h10Gradient v x)) (h10Value w x) := by
      filter_upwards [tensorCoordinateL2_ae (L v), tensorCoordinateL2_ae (h10ValueL2 U w),
        lowerActionOnH10_ae A hA M hM₀ hM v] with x hx₁ hx₂ hx₃
      change inner ℝ (tensorCoordinateL2 U (L v) x) (tensorCoordinateL2 U (h10ValueL2 U w) x) = _
      rw [hx₁, hx₂, hx₃, frobeniusCoordinateEquiv_inner]
      rfl
    have hInt := (L2.integrable_inner (𝕜 := ℝ) (V v) (W w)).congr hAe
    refine ⟨hInt, ?_⟩
    rw [show P v w = inner ℝ (V v) (W w) from h10PullbackInner_apply V W v w, L2.inner_def]
    exact integral_congr_ae hAe

/-- The literal weak pairing for the componentwise Laplacian and the
first-order coefficient acting on the actual value and gradient columns. -/
@[expose] def weakCorrectionPairing (U : Set Point) (A : Point → (S0 × Gradient) →L[ℝ] S0)
    (v w : H10 U) : ℝ :=
  ∫ x in U, -(∑ j, frobeniusS0 (h10Gradient v x j) (h10Gradient w x j)) +
    frobeniusS0 (A x (h10Value v x, h10Gradient v x)) (h10Value w x)

private theorem integrable_principalDensity {U : Set Point} (v w : H10 U) :
    IntegrableOn (fun x => -(∑ j, frobeniusS0 (h10Gradient v x j) (h10Gradient w x j))) U volume := by
  apply Integrable.neg
  apply integrable_finsetSum
  intro j _
  have h := L2.integrable_inner (𝕜 := ℝ) (tensorCoordinateL2 U (h10ColumnL2 U j v))
    (tensorCoordinateL2 U (h10ColumnL2 U j w))
  apply h.congr
  filter_upwards [tensorCoordinateL2_ae (h10ColumnL2 U j v), tensorCoordinateL2_ae (h10ColumnL2 U j w)]
    with x hx hy
  rw [hx, hy, frobeniusCoordinateEquiv_inner]
  rfl

/-- Essentially bounded first-order coefficients define a bounded operator on
the actual zero-trace Sobolev graph. -/
theorem exists_weakCorrectionOperator {U : Set Point}
    (A : Point → (S0 × Gradient) →L[ℝ] S0) (hA : AEStronglyMeasurable A (volume.restrict U))
    (M : ℝ) (hM₀ : 0 ≤ M) (hM : ∀ᵐ x ∂volume.restrict U, ‖A x‖ ≤ M) :
    ∃ P : H10 U →L[ℝ] HMinusOne U, ∀ v w : H10 U, P v w = weakCorrectionPairing U A v w := by
  obtain ⟨L, _, hL⟩ := exists_lowerOperator_on_H10 A hA M hM₀ hM
  refine ⟨h10PrincipalPart U + L, ?_⟩
  intro v w
  have hw := hL v w
  simp only [add_apply, h10PrincipalPart_apply, hw.2, weakCorrectionPairing]
  exact (integral_add (integrable_principalDensity v w) hw.1).symm

/-- The weak Jacobi pairing agrees with the bounded operator induced by the
Fréchet derivative of the projected polynomial at a vacuum-valued field. -/
theorem weakCorrectionPairing_fderiv_eq_linearizedPairing
    (a : BulkCoefficients) (U : Set Point) (q : Point → S0) (D : Point → Gradient)
    (hq : TakesVacuumValues a U q) (v w : H10 U) :
    weakCorrectionPairing U
      (fun x => fderiv ℝ (fun p : S0 × Gradient => projectedHarmonicNonlinearity a p.1 p.2) (q x, D x))
      v w = linearizedPairing a U q D v w := by
  rw [linearizedPairing_eq_harmonicFirstOrderLinearization a U q D hq v w]
  unfold weakCorrectionPairing
  apply integral_congr_ae
  filter_upwards [] with x
  rw [fderiv_projectedHarmonicNonlinearity_apply]

private theorem weakCorrectionPairing_add_coefficient_increment
    {U : Set Point} {A B : Point → (S0 × Gradient) →L[ℝ] S0} (v w : H10 U)
    (hA : IntegrableOn (fun x => frobeniusS0 (A x (h10Value v x, h10Gradient v x)) (h10Value w x)) U volume)
    (hB : IntegrableOn (fun x =>
      frobeniusS0 ((B x - A x) (h10Value v x, h10Gradient v x)) (h10Value w x)) U volume) :
    weakCorrectionPairing U A v w +
      (∫ x in U, frobeniusS0 ((B x - A x) (h10Value v x, h10Gradient v x)) (h10Value w x)) =
        weakCorrectionPairing U B v w := by
  unfold weakCorrectionPairing
  let g (x : Point) := -(∑ j, frobeniusS0 (h10Gradient v x j) (h10Gradient w x j)) +
    frobeniusS0 (A x (h10Value v x, h10Gradient v x)) (h10Value w x)
  let h (x : Point) := frobeniusS0 ((B x - A x) (h10Value v x, h10Gradient v x)) (h10Value w x)
  have hg : IntegrableOn g U volume := (integrable_principalDensity v w).add hA
  refine (show (∫ x in U, g x) + (∫ x in U, h x) = ∫ x in U, g x + h x from
    (integral_add hg hB).symm).trans ?_
  apply integral_congr_ae
  filter_upwards [] with x
  let Y := (h10Value v x, h10Gradient v x)
  let W := h10Value w x
  have hLin : frobeniusS0 (A x Y) W + frobeniusS0 ((B x - A x) Y) W = frobeniusS0 (B x Y) W := by
    simp only [← frobeniusCoordinateEquiv_inner, sub_apply, map_sub, inner_sub_left]
    ring
  change -(∑ j, frobeniusS0 (h10Gradient v x j) (h10Gradient w x j)) +
      frobeniusS0 (A x Y) W + frobeniusS0 ((B x - A x) Y) W =
    -(∑ j, frobeniusS0 (h10Gradient v x j) (h10Gradient w x j)) + frobeniusS0 (B x Y) W
  rw [add_assoc]
  exact congrArg (fun t : ℝ => -(∑ j, frobeniusS0 (h10Gradient v x j) (h10Gradient w x j)) + t) hLin

theorem exists_continuousEquiv_of_weakCorrectionPairing
    {U : Set Point} (A : Point → (S0 × Gradient) →L[ℝ] S0)
    (hA : AEStronglyMeasurable A (volume.restrict U))
    (M : ℝ) (hM₀ : 0 ≤ M) (hM : ∀ᵐ x ∂volume.restrict U, ‖A x‖ ≤ M)
    (hBase : ∃ L : H10 U →ₗ[ℝ] HMinusOne U, Function.Bijective L ∧
      ∀ v w : H10 U, L v w = weakCorrectionPairing U A v w) :
    ∃ L : H10 U ≃L[ℝ] HMinusOne U, ∀ v w : H10 U, L v w = weakCorrectionPairing U A v w := by
  obtain ⟨P₀, hBij, hEq⟩ := hBase
  obtain ⟨P, hP⟩ := exists_weakCorrectionOperator A hA M hM₀ hM
  have hIs : ⇑P = ⇑P₀ := funext fun v => ContinuousLinearMap.ext fun w => (hP v w).trans (hEq v w).symm
  have hBijP : Function.Bijective P := hIs.symm ▸ hBij
  let L := ContinuousLinearEquiv.ofBijective P
    (LinearMap.ker_eq_bot.mpr hBijP.1) (LinearMap.range_eq_top.mpr hBijP.2)
  have hLp : L.toContinuousLinearMap = P := ContinuousLinearEquiv.coe_ofBijective ..
  refine ⟨L, ?_⟩
  intro v w
  exact (DFunLike.congr_fun (DFunLike.congr_fun hLp v) w).trans (hP v w)

private theorem exists_difference_operator_on_H10 {U : Set Point}
    (A B : Point → CorrectionState →L[ℝ] S0)
    (hA : AEStronglyMeasurable A (volume.restrict U)) (hB : AEStronglyMeasurable B (volume.restrict U))
    (δ : ℝ) (hδ : 0 ≤ δ) (hSub : ∀ᵐ x ∂volume.restrict U, ‖B x - A x‖ ≤ δ) :
    ∃ P : H10 U →L[ℝ] HMinusOne U, ‖P‖ ≤ 4 * δ ∧ ∀ v w : H10 U,
      IntegrableOn (fun x =>
        frobeniusS0 ((B x - A x) (h10Value v x, h10Gradient v x)) (h10Value w x)) U volume ∧
      P v w = ∫ x in U, frobeniusS0 ((B x - A x) (h10Value v x, h10Gradient v x)) (h10Value w x) := by
  let D (x : Point) : CorrectionState →L[ℝ] S0 := B x - A x
  have hMeas : AEStronglyMeasurable D (volume.restrict U) := hB.sub hA
  exact exists_lowerOperator_on_H10 (U := U) D hMeas δ hδ hSub

/-- The weak increment induced by the actual coefficient difference. -/
theorem exists_weakCorrectionPairing_coefficient_increment
    {U : Set Point} (A B : Point → (S0 × Gradient) →L[ℝ] S0)
    (hA : AEStronglyMeasurable A (volume.restrict U)) (hB : AEStronglyMeasurable B (volume.restrict U))
    (M : ℝ) (hM₀ : 0 ≤ M) (hM : ∀ᵐ x ∂volume.restrict U, ‖A x‖ ≤ M)
    (δ : ℝ) (hδ : 0 ≤ δ) (hSub : ∀ᵐ x ∂volume.restrict U, ‖B x - A x‖ ≤ δ) :
    ∃ Q : H10 U →L[ℝ] HMinusOne U, ‖Q‖ ≤ 4 * δ ∧ ∀ v w : H10 U,
      weakCorrectionPairing U A v w + Q v w = weakCorrectionPairing U B v w := by
  obtain ⟨_, _, h₁⟩ := exists_lowerOperator_on_H10 A hA M hM₀ hM
  obtain ⟨Q, hQ, hQEq⟩ := exists_difference_operator_on_H10 A B hA hB δ hδ hSub
  refine ⟨Q, hQ, ?_⟩
  intro v w
  rw [(hQEq v w).2]
  exact weakCorrectionPairing_add_coefficient_increment v w (h₁ v w).1 (hQEq v w).1

/-- A square-integrable forcing defines the actual weak forcing
functional on the zero-trace graph. -/
theorem exists_H10_forcingFunctional_of_memLp
    {U : Set Point} {F : Point → S0} (hF : MemLp F 2 (volume.restrict U)) :
    ∃ W : HMinusOne U, ∀ v : H10 U,
      IntegrableOn (fun x => frobeniusS0 (F x) (h10Value v x)) U volume ∧
      W v = ∫ x in U, frobeniusS0 (F x) (h10Value v x) := by
  let X := tensorCoordinateL2 U (hF.toLp F)
  let L := (tensorCoordinateL2 U).comp (h10ValueL2 U)
  let I : CoordL2 U →L[ℝ] ℝ := innerSL ℝ X
  refine ⟨I.comp L, ?_⟩
  intro v
  have hEq : (fun x => inner ℝ (X x) (L v x)) =ᵐ[volume.restrict U]
      fun x => frobeniusS0 (F x) (h10Value v x) := by
    filter_upwards [tensorCoordinateL2_ae (hF.toLp F), tensorCoordinateL2_ae (h10ValueL2 U v), hF.coeFn_toLp]
      with x h₁ h₂ h₃
    change inner ℝ (tensorCoordinateL2 U (hF.toLp F) x) (tensorCoordinateL2 U (h10ValueL2 U v) x) = _
    rw [h₁, h₂, h₃, frobeniusCoordinateEquiv_inner]
    rfl
  refine ⟨(L2.integrable_inner (𝕜 := ℝ) X (L v)).congr hEq, ?_⟩
  change inner ℝ X (L v) = _
  rw [L2.inner_def]
  exact integral_congr_ae hEq

end Thesis

end

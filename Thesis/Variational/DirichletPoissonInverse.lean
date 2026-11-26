module

public import Thesis.Variational.WeakCorrectionPairing
import Thesis.Variational.H10Poincare
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp

/-! The pure weak Dirichlet inverse on the literal zero-trace graph. -/

public section

noncomputable section

open Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Matrix.Norms.Frobenius RealInnerProductSpace

namespace Thesis

local instance dirichletPoissonTensorComplete : CompleteSpace S0 := complete_of_proper

local instance dirichletPoissonH10Complete (U : Set Point) : CompleteSpace (H10 U) :=
  isClosed_closure.completeSpace_coe

local instance dirichletPoissonHMinusOneNormed (U : Set Point) : NormedAddCommGroup (HMinusOne U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance dirichletPoissonHMinusOneSpace (U : Set Point) : NormedSpace ℝ (HMinusOne U) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

/-- The three Frobenius-coordinate columns with the Hilbert product norm. -/
abbrev DirichletGradientCoordinates (U : Set Point) :=
  PiLp 2 (fun _ : Fin 3 => Lp (EuclideanSpace ℝ (Fin 5)) 2 (volume.restrict U))

/-- The actual gradient coordinates of a zero-trace graph. -/
@[expose] def h10GradientCoordinates (U : Set Point) : H10 U →L[ℝ] DirichletGradientCoordinates U :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => Lp (EuclideanSpace ℝ (Fin 5))
     2 (volume.restrict U))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (h10FrobeniusColumnL2 U))

theorem h10GradientCoordinates_apply {U : Set Point} (u : H10 U) (j : Fin 3) :
    h10GradientCoordinates U u j = h10FrobeniusColumnL2 U j u := rfl

theorem norm_h10GradientCoordinates_eq {U : Set Point} (u : H10 U) :
    ‖h10GradientCoordinates U u‖ = Real.sqrt (∑ j : Fin 3, ‖u.val.2 j‖ ^ 2) := by
  have hSq : ‖h10GradientCoordinates U u‖ ^ 2 = ∑ j : Fin 3, ‖u.val.2 j‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [h10GradientCoordinates_apply,norm_h10FrobeniusColumnL2]
  rw [← hSq,Real.sqrt_sq (norm_nonneg _)]

theorem exists_antilipschitz_h10GradientCoordinates {U : Set Point}
    (hU : MeasurableSet U) (hB : Bornology.IsBounded U) :
    ∃ C : ℝ≥0, AntilipschitzWith C (h10GradientCoordinates U) := by
  obtain ⟨C,hC,hBound⟩ := exists_H10_value_poincare hU hB
  let K : ℝ≥0 := ⟨C,zero_le_one.trans hC⟩
  refine ⟨K,ContinuousLinearMap.antilipschitz_of_bound _ ?_⟩
  intro u
  change ‖u.val‖ ≤ C * ‖h10GradientCoordinates U u‖
  rw [Prod.norm_def]
  refine max_le (by rw [norm_h10GradientCoordinates_eq]; exact hBound u) ?_
  have hDir : ‖u.val.2‖ ≤ ‖h10GradientCoordinates U u‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    rw [← norm_h10FrobeniusColumnL2 j u, ← h10GradientCoordinates_apply u j]
    exact PiLp.norm_apply_le _ _
  exact hDir.trans (le_mul_of_one_le_left (norm_nonneg _) hC)

theorem h10PrincipalPart_eq_neg_gradientCoordinate_inner {U : Set Point} (u v : H10 U) :
    h10PrincipalPart U u v = -inner ℝ (h10GradientCoordinates U u) (h10GradientCoordinates U v) := by
  rw [h10PrincipalPart_apply_coordinate_inner,PiLp.inner_apply]
  simp only [h10GradientCoordinates_apply]

/-- The zero-trace graph is continuously equivalent to its closed gradient range. -/
theorem exists_gradientCoordinateEquiv {U : Set Point} (hU : MeasurableSet U)
    (hB : Bornology.IsBounded U) :
    ∃ (G : Submodule ℝ (DirichletGradientCoordinates U)),
      IsClosed (G : Set (DirichletGradientCoordinates U)) ∧
      ∃ L : H10 U ≃L[ℝ] G, ∀ u, (L u).val = h10GradientCoordinates U u := by
  let A := h10GradientCoordinates U
  let G := A.range
  obtain ⟨_,hAnti⟩ := exists_antilipschitz_h10GradientCoordinates hU hB
  have hClosed : IsClosed (G : Set (DirichletGradientCoordinates U)) :=
    hAnti.isClosed_range A.uniformContinuous
  letI : CompleteSpace G := hClosed.completeSpace_coe
  let T : H10 U →L[ℝ] G := A.codRestrict G (fun u => LinearMap.mem_range_self _ u)
  have hTI : Injective T := fun u v h => hAnti.injective
    (congrArg (fun x : G => (x : DirichletGradientCoordinates U)) h)
  have hTS : Surjective T := by
    rintro ⟨z,hz⟩
    obtain ⟨u,hu⟩ := hz
    exact ⟨u,Subtype.ext hu⟩
  have hKer : T.ker = ⊥ := LinearMap.ker_eq_bot.mpr hTI
  have hRange : T.range = ⊤ := LinearMap.range_eq_top.mpr hTS
  let L := ContinuousLinearEquiv.ofBijective T hKer hRange
  have hTL : L.toContinuousLinearMap = T := ContinuousLinearEquiv.coe_ofBijective T hKer hRange
  refine ⟨G,hClosed,L,fun u => ?_⟩
  have hu : L u = T u := DFunLike.congr_fun hTL u
  exact congrArg Subtype.val hu

private theorem bijective_of_negative_innerProduct_pullback {H G : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (L : H ≃L[ℝ] G) (P : H →L[ℝ] (H →L[ℝ] ℝ))
    (hInner : ∀ u w, P u w = -inner ℝ (L u) (L w)) : Bijective P := by
  constructor
  · intro u w h
    let z := u - w
    have hPz : P z = 0 := by rw [show z = u-w from rfl,map_sub,h,sub_self]
    have hD : inner ℝ (L z) (L z) = 0 := by
      have h0 : P z z = 0 := by rw [hPz]; rfl
      rw [hInner,neg_eq_zero] at h0
      exact h0
    have hZ : L z = 0 := inner_self_eq_zero.mp hD
    exact sub_eq_zero.mp (L.injective (hZ.trans (map_zero L).symm))
  · intro f
    let J : G →L[ℝ] ℝ := -(f.comp L.symm.toContinuousLinearMap)
    let y := (InnerProductSpace.toDual ℝ G).symm J
    let u := L.symm y
    refine ⟨u,ContinuousLinearMap.ext (fun w => ?_)⟩
    have hR : inner ℝ y (L w) = J (L w) :=
      InnerProductSpace.toDual_symm_apply (x := L w) (y := J)
    have hI : inner ℝ y (L w) = -(f w) := by
      simpa only [J,neg_apply,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply] using hR
    rw [hInner,show L u = y from L.apply_symm_apply y,hI,neg_neg]

/-- The pure Dirichlet Laplacian is a continuous isomorphism from the
zero-trace Sobolev graph to its full dual on a bounded measurable set. -/
theorem exists_H10_dirichletPoissonEquiv {U : Set Point} (hU : MeasurableSet U)
    (hB : Bornology.IsBounded U) :
    ∃ E : H10 U ≃L[ℝ] HMinusOne U, ∀ u : H10 U, E u = h10PrincipalPart U u := by
  obtain ⟨G,hClosed,L,hL⟩ := exists_gradientCoordinateEquiv hU hB
  letI : CompleteSpace G := hClosed.completeSpace_coe
  let P := h10PrincipalPart U
  have hInner (u w : H10 U) : P u w = -inner ℝ (L u) (L w) := by
    have he : inner ℝ (L u) (L w) =
        inner ℝ (h10GradientCoordinates U u) (h10GradientCoordinates U w) := by
      change inner ℝ (L u).val (L w).val = _
      rw [hL,hL]
    exact (h10PrincipalPart_eq_neg_gradientCoordinate_inner u w).trans (congrArg Neg.neg he.symm)
  have hP := bijective_of_negative_innerProduct_pullback L P hInner
  have hKer : P.ker = ⊥ := LinearMap.ker_eq_bot.mpr hP.injective
  have hRange : P.range = ⊤ := LinearMap.range_eq_top.mpr hP.surjective
  let E := ContinuousLinearEquiv.ofBijective P hKer hRange
  exact ⟨E,fun u => DFunLike.congr_fun (ContinuousLinearEquiv.coe_ofBijective P hKer hRange) u⟩

/-- A square-integrable force has a unique solution in the actual
zero-trace graph for the componentwise weak Dirichlet equation. -/
theorem exists_unique_H10_dirichletPoisson_of_memLp {U : Set Point} (hU : MeasurableSet U)
    (hB : Bornology.IsBounded U) {f : Point → S0} (hf : MemLp f 2 (volume.restrict U)) :
    ∃! u : H10 U, ∀ v : H10 U,
      (∫ x in U, -(∑ j, frobeniusS0 (h10Gradient u x j) (h10Gradient v x j))) =
        ∫ x in U, frobeniusS0 (f x) (h10Value v x) := by
  obtain ⟨E,hE⟩ := exists_H10_dirichletPoissonEquiv hU hB
  obtain ⟨F,hF⟩ := exists_H10_forcingFunctional_of_memLp hf
  let u := E.symm F
  refine ⟨u,?_,fun v hv => E.injective ?_⟩
  · intro v
    have h : h10PrincipalPart U u = F := (hE u).symm.trans (E.apply_symm_apply F)
    rw [← h10PrincipalPart_apply,h,(hF v).2]
  · rw [hE v,E.apply_symm_apply]
    apply ContinuousLinearMap.ext
    intro w
    rw [h10PrincipalPart_apply,hv,(hF w).2]

end Thesis

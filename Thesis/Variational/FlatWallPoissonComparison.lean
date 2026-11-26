module

public import Thesis.Variational.FlatWallCoordinates

/-! Pointwise small perturbation of the Laplacian in a tangent wall chart. -/

public section

noncomputable section

open Filter Function Metric Set Topology
open scoped ContDiff RealInnerProductSpace

namespace Thesis

private theorem norm_hessian_difference_diagonal {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x u v : E) :
    ‖iteratedFDeriv ℝ 2 f x ![u,u] - iteratedFDeriv ℝ 2 f x ![v,v]‖ ≤
      ‖iteratedFDeriv ℝ 2 f x‖ * ‖u-v‖ * (‖u‖+‖v‖) := by
  let H := iteratedFDeriv ℝ 2 f x
  have hE : H ![u,u] - H ![v,v] = H ![u-v,u] + H ![v,u-v] := by
    simp only [H,iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,map_sub,sub_apply]
    abel
  rw [hE]
  refine (norm_add_le _ _).trans ?_
  have hu := H.le_opNorm ![u-v,u]
  have hv := H.le_opNorm ![v,u-v]
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] at hu hv
  exact (add_le_add hu hv).trans_eq (by ring)

private theorem norm_axis_one (j : Fin 3) : ‖axis j‖ = 1 := by simp [axis]

namespace RegularWallGraphPatch

variable {U : Set Point}

theorem derivative_flatChart_symm_close (P : RegularWallGraphPatch U)
    (hP : ContDiff ℝ 2 P.height) {η : ℝ} (hη : 0 ≤ η)
    (hSlope : ∀ y ∈ P.base, ‖fderiv ℝ P.height y‖ ≤ η) {z : Point} (hz : z ∈ P.flatBox) (v : Point) :
    ‖fderiv ℝ P.flatChart.symm (P.flatChart z) v - P.frame.repr v‖ ≤ η * ‖v‖ := by
  rw [P.fderiv_flatChart_symm hP]
  have he : P.frame.repr v - (fderiv ℝ P.height (wallHorizontal z))
      (wallHorizontal (P.frame.repr v)) • axis 2 - P.frame.repr v =
      -((fderiv ℝ P.height (wallHorizontal z)) (wallHorizontal (P.frame.repr v)) • axis 2) := by abel
  rw [he,norm_neg,norm_smul,norm_axis_one,mul_one]
  let L := fderiv ℝ P.height (wallHorizontal z)
  have hBase : wallHorizontal z ∈ P.base := hz.1
  have hProj : ‖wallHorizontal (P.frame.repr v)‖ ≤ ‖v‖ :=
    (wallHorizontal_norm_le _).trans_eq (P.frame.repr.norm_map v)
  exact (L.le_opNorm _).trans (mul_le_mul (hSlope _ hBase) hProj (norm_nonneg _) hη)

theorem derivative_flatChart_symm_norm_le (P : RegularWallGraphPatch U)
    (hP : ContDiff ℝ 2 P.height) {η : ℝ} (hη : 0 ≤ η)
    (hSlope : ∀ y ∈ P.base, ‖fderiv ℝ P.height y‖ ≤ η) {z : Point} (hz : z ∈ P.flatBox) (v : Point) :
    ‖fderiv ℝ P.flatChart.symm (P.flatChart z) v‖ ≤ (1+η)*‖v‖ := by
  have hC := P.derivative_flatChart_symm_close hP hη hSlope hz v
  calc
    _ ≤ ‖fderiv ℝ P.flatChart.symm (P.flatChart z) v - P.frame.repr v‖ + ‖P.frame.repr v‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (fderiv ℝ P.flatChart.symm (P.flatChart z) v - P.frame.repr v) (P.frame.repr v)
    _ ≤ η*‖v‖ + ‖v‖ := add_le_add hC ((P.frame.repr.norm_map v).le)
    _ = _ := by ring

private theorem hessian_flatChart_symm_apply_norm_le (P : RegularWallGraphPatch U)
    (hP : ContDiff ℝ 2 P.height) {H : ℝ} (hH : 0 ≤ H)
    (hHess : ∀ y ∈ P.base, ‖iteratedFDeriv ℝ 2 P.height y‖ ≤ H) {z : Point} (hz : z ∈ P.flatBox) (u v : Point) :
    ‖iteratedFDeriv ℝ 2 P.flatChart.symm (P.flatChart z) ![u,v]‖ ≤ H*‖u‖*‖v‖ := by
  rw [P.iteratedFDeriv_two_flatChart_symm hP,norm_smul,norm_axis_one,mul_one,norm_neg]
  let B := iteratedFDeriv ℝ 2 P.height (wallHorizontal z)
  have hBase : wallHorizontal z ∈ P.base := hz.1
  have hProj (x : Point) : ‖wallHorizontal (P.frame.repr x)‖ ≤ ‖x‖ :=
    (wallHorizontal_norm_le _).trans_eq (P.frame.repr.norm_map x)
  have hP := B.le_opNorm ![wallHorizontal (P.frame.repr u),wallHorizontal (P.frame.repr v)]
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] at hP
  exact hP.trans ((mul_le_mul (hHess _ hBase)
    (mul_le_mul (hProj u) (hProj v) (norm_nonneg _) (norm_nonneg _)) (by positivity) hH).trans_eq
      (by ring))

/-- The flattened Laplacian differs from the physical Laplacian by a
small coefficient times the flattened Hessian and the bounded drift.
The original physical Hessian is also controlled by the same graph. -/
theorem exists_flatWall_poisson_comparison (P : RegularWallGraphPatch U)
    (hP : ContDiff ℝ 2 P.height) {η : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hSlope : ∀ y ∈ P.base, ‖fderiv ℝ P.height y‖ ≤ η) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (f : Point → ℝ) (z : Point), z ∈ P.flatBox →
      ContDiffAt ℝ 2 f (P.flatChart z) →
      let F := f ∘ P.flatChart
      ‖laplacian F z - laplacian f (P.flatChart z)‖ ≤
        9*η*‖iteratedFDeriv ℝ 2 F z‖ + 3*H*‖fderiv ℝ F z‖ ∧
      ‖iteratedFDeriv ℝ 2 f (P.flatChart z)‖ ≤
        4*‖iteratedFDeriv ℝ 2 F z‖ + H*‖fderiv ℝ F z‖ ∧
      ‖fderiv ℝ f (P.flatChart z)‖ ≤ 2 * ‖fderiv ℝ F z‖ := by
  obtain ⟨H₀,hH₀⟩ := (isCompact_closedBall (0 : Plane) P.baseRadius).exists_bound_of_continuousOn
    ((hP.continuous_iteratedFDeriv le_rfl).continuousOn)
  let H := max H₀ 0
  have hH : 0 ≤ H := le_max_right _ _
  have hBound (y : Plane) (hy : y ∈ P.base) :
      ‖iteratedFDeriv ℝ 2 P.height y‖ ≤ H :=
    (hH₀ y (ball_subset_closedBall hy)).trans (le_max_left _ _)
  refine ⟨H,hH,?_⟩
  intro f z hz hf
  let F := f ∘ P.flatChart
  let Ψ := P.flatChart.symm
  let x := P.flatChart z
  let DF := fderiv ℝ F z
  let DD := iteratedFDeriv ℝ 2 F z
  let J := fderiv ℝ Ψ x
  let ι := (EuclideanSpace.basisFun (Fin 3) ℝ)
  let B := ι.map P.frame.repr
  have hInv : Ψ x = z := P.flatChart.symm_apply_apply z
  have hΦ : ContDiffAt ℝ 2 (P.flatChart : Point → Point) z := (P.flatChart_contDiff_two hP).contDiffAt
  have hΨ : ContDiffAt ℝ 2 (Ψ : Point → Point) x := (P.flatChart_symm_contDiff_two hP).contDiffAt
  have hF : ContDiffAt ℝ 2 F z := hf.comp z hΦ
  have hF' : ContDiffAt ℝ 2 F (Ψ x) := hInv.symm ▸ hF
  have hEq : f = F ∘ Ψ := by
    funext x
    change f x = f (P.flatChart (Ψ x))
    rw [P.flatChart.apply_symm_apply]
  have hClose (v : Point) : ‖J v - P.frame.repr v‖ ≤ η*‖v‖ :=
    P.derivative_flatChart_symm_close hP hη hSlope hz v
  have hJ (v : Point) : ‖J v‖ ≤ 2*‖v‖ :=
    (P.derivative_flatChart_symm_norm_le hP hη hSlope hz v).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hη₁]) (norm_nonneg _))
  have hJ₂ (u v : Point) : ‖iteratedFDeriv ℝ 2 Ψ x ![u,v]‖ ≤ H*‖u‖*‖v‖ :=
    P.hessian_flatChart_symm_apply_norm_le hP hH hBound hz u v
  have hChain (u v : Point) : iteratedFDeriv ℝ 2 f x ![u,v] =
      DD ![J u,J v] + DF (iteratedFDeriv ℝ 2 Ψ x ![u,v]) := by
    have h := iteratedFDeriv_two_comp_apply_of_contDiffAt hF' hΨ u v
    rw [← hEq,hInv] at h
    exact h
  have hEach (i : Fin 3) :
      ‖iteratedFDeriv ℝ 2 f x ![axis i,axis i] - DD ![B i,B i]‖ ≤
        3*η*‖DD‖ + H*‖DF‖ := by
    have hB : B i = P.frame.repr (axis i) := by
      rw [OrthonormalBasis.map_apply,EuclideanSpace.basisFun_apply]
      rfl
    have hNorm : ‖B i‖ = 1 := B.orthonormal.norm_eq_one i
    have hJ' : ‖J (axis i)‖ ≤ 2 := by simpa only [norm_axis_one,mul_one] using hJ (axis i)
    have hC' : ‖J (axis i) - B i‖ ≤ η := by
      simpa only [hB,norm_axis_one,mul_one] using hClose (axis i)
    have hD := norm_hessian_difference_diagonal F z (J (axis i)) (B i)
    have hOp := DF.le_opNorm (iteratedFDeriv ℝ 2 Ψ x ![axis i,axis i])
    have hJ₂' : ‖iteratedFDeriv ℝ 2 Ψ x ![axis i,axis i]‖ ≤ H := by
      simpa only [norm_axis_one,mul_one] using hJ₂ (axis i) (axis i)
    rw [hChain,show DD ![J (axis i),J (axis i)] + DF (iteratedFDeriv ℝ 2 Ψ x ![axis i,axis i]) - DD ![B i,B i] =
      (DD ![J (axis i),J (axis i)] - DD ![B i,B i]) + DF (iteratedFDeriv ℝ 2 Ψ x ![axis i,axis i]) by abel]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine hD.trans ?_
      have h := mul_le_mul (mul_le_mul_of_nonneg_left hC' (norm_nonneg DD)) (add_le_add hJ' hNorm.le)
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg (norm_nonneg _) hη)
      exact h.trans_eq (by ring)
    · exact (hOp.trans (mul_le_mul_of_nonneg_left hJ₂' (norm_nonneg DF))).trans_eq (mul_comm _ _)
  refine ⟨?_,?_,?_⟩
  · change ‖laplacian F z - laplacian f x‖ ≤ _
    have hfEq := laplacian_eq_second_derivative_basis_of_contDiffAt hf ι
    have hFEq := laplacian_eq_second_derivative_basis_of_contDiffAt hF B
    dsimp only [ι] at hfEq
    simp only [EuclideanSpace.basisFun_apply] at hfEq
    change laplacian f x = ∑ i : Fin 3, iteratedFDeriv ℝ 2 f x ![axis i,axis i] at hfEq
    rw [norm_sub_rev,hfEq,hFEq,← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hEach i).trans_eq ?_)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    push_cast
    ring
  · change ‖iteratedFDeriv ℝ 2 f x‖ ≤ 4*‖DD‖+H*‖DF‖
    apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
    intro v
    have hT : v = ![v 0,v 1] := by funext i; fin_cases i <;> rfl
    rw [hT,hChain,Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    refine (norm_add_le _ _).trans ?_
    have h1 := DD.le_opNorm ![J (v 0),J (v 1)]
    simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] at h1
    have h2 := (DF.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hJ₂ (v 0) (v 1)) (norm_nonneg DF))
    have h3 := h1.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul (hJ (v 0)) (hJ (v 1)) (norm_nonneg _) (by positivity)) (norm_nonneg DD))
    exact (add_le_add h3 h2).trans_eq (by ring)
  · change ‖fderiv ℝ f x‖ ≤ 2*‖DF‖
    have hD : fderiv ℝ f x = DF.comp J := by
      have h := fderiv_comp x (hF'.differentiableAt two_ne_zero) (hΨ.differentiableAt two_ne_zero)
      rw [← hEq,hInv] at h
      exact h
    rw [hD]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    exact ((DF.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hJ v) (norm_nonneg DF))).trans_eq (by ring)

/-- Pulling a field supported in one chart back to the closed half-space
retains its (C^2) differentiability at the original boundary. -/
theorem contDiffOn_two_flat_pullback (P : RegularWallGraphPatch U) (hU : IsOpen U)
    (hP : ContDiff ℝ 2 P.height) {f : Point → ℝ}
    (hf : ContDiffOn ℝ 2 f (closure U)) (hs : tsupport f ⊆ P.neighborhood) :
    ContDiffOn ℝ 2 (f ∘ P.flatChart) closedWallHalf := by
  intro z hz
  by_cases hzB : z ∈ P.flatBox
  · apply (contDiffWithinAt_inter (P.flatBox_isOpen.mem_nhds hzB)).1
    have hMaps : MapsTo P.flatChart (closedWallHalf ∩ P.flatBox) (closure U) :=
      fun v hv => P.flatChart_mem_closure hU hv.2 hv.1
    exact (hf.comp (P.flatChart_contDiff_two hP).contDiffOn hMaps) z ⟨hz,hzB⟩
  · have hN : P.flatChart z ∉ P.neighborhood := by
      rw [← P.flatChart_image_flatBox]
      rintro ⟨y,hy,he⟩
      exact hzB (P.flatChart.injective he ▸ hy)
    have hHide : P.flatChart z ∉ tsupport f := fun h => hN (hs h)
    have hIn : ∀ᶠ x in 𝓝 z, P.flatChart x ∉ tsupport f :=
      P.flatChart.continuous.continuousAt ((isClosed_tsupport f).isOpen_compl.mem_nhds hHide)
    have hEq : f ∘ P.flatChart =ᶠ[𝓝 z] (0 : Point → ℝ) :=
      hIn.mono fun x hx => show f (P.flatChart x) = 0 from image_eq_zero_of_notMem_tsupport hx
    exact (contDiffAt_const.congr_of_eventuallyEq hEq).contDiffWithinAt

theorem flat_pullback_wall_zero (P : RegularWallGraphPatch U) (hU : IsOpen U)
    {f : Point → ℝ} (hZero : EqOn f 0 (frontier U)) (hs : tsupport f ⊆ P.neighborhood) :
      EqOn (f ∘ P.flatChart) 0 {z : Point | z 2 = 0} := by
  intro z hz
  by_cases hzB : z ∈ P.flatBox
  · exact hZero ((P.flatChart_mem_frontier hU hzB).2 hz)
  · have hOff : P.flatChart z ∉ tsupport f := by
      intro h
      obtain ⟨y,hy,he⟩ := (P.flatChart_image_flatBox).symm ▸ hs h
      exact hzB (P.flatChart.injective he ▸ hy)
    exact show f (P.flatChart z) = 0 from image_eq_zero_of_notMem_tsupport hOff

theorem flat_pullback_hasCompactSupport (P : RegularWallGraphPatch U)
    {f : Point → ℝ} (hC : HasCompactSupport f) : HasCompactSupport (f ∘ P.flatChart) := by
  have hK : IsCompact (P.flatChart.symm '' tsupport f) := hC.image P.flatChart.symm.continuous
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro z hz
  exact ⟨P.flatChart z,subset_closure hz,P.flatChart.symm_apply_apply z⟩

end RegularWallGraphPatch

end Thesis

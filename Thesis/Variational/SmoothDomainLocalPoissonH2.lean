module

public import Thesis.Variational.FlatBoundaryEllipticH2
public import Thesis.Upstream.GradientPullbackSecondColumns

/-! Local second weak gradients of zero-extended Dirichlet data on a smooth domain. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal RealInnerProductSpace

namespace Thesis

/-- The actual whole-space zero extension and weak Poisson identity. -/
structure AmbientDirichletPoissonData {q : ℕ} (U : Set Point)
    (u : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q) (f : Point → Ambient q) : Prop where
  sobolev : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D
  force : MemLp f 2 volume
  outside : ∀ x ∉ U, u x = 0 ∧ D x = 0
  equation : HasWeakPackedDivergenceEq U (fun x => packAmbientGradient (D x)) f

theorem AmbientDirichletPoissonData.gradient_memLp {q : ℕ} {U : Set Point}
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q} {f : Point → Ambient q}
    (h : AmbientDirichletPoissonData U u D f) (j : Fin 3) :
    MemLp (fun x => D x j) 2 volume := by
  simpa only [Measure.restrict_univ] using h.sobolev.2.2 j

/-- The actual local weak graph of every displayed first derivative. -/
@[expose] def HasLocalSecondWeakColumns {q : ℕ} (V : OpenDomain 3)
    (D : Point → HarmonicMaps.Gradient 3 q) (B : ℝ) : Prop :=
  ∃ H : Point → Fin 3 → HarmonicMaps.Gradient 3 q,
    ∀ j, MemW12 V (fun x => D x j) (fun x => H x j) ∧
      ∀ i, lpNorm (fun x => H x j i) 2 (volume.restrict V.val) ≤ B

private theorem ambientPoissonL2Size_pullback_le {q : ℕ}
    (F : Point ≃ₜ Point) (hMP : MeasurePreserving F (volume : Measure Point) volume)
    (D : Point → HarmonicMaps.Gradient 3 q) (f : Point → Ambient q)
    {C : ℝ} (hC : 0 ≤ C)
    (h : (∫ x, hsNormSq (ambientGradientPullback F D x)) ≤
      C^2 * ∫ x, hsNormSq (D x)) :
    ambientPoissonL2Size (ambientGradientPullback F D) (f ∘ F) ≤
      max 1 C * ambientPoissonL2Size D f := by
  have hM : 1 ≤ max 1 C := le_max_left _ _
  have hM₀ : 0 ≤ max 1 C := zero_le_one.trans hM
  have hF : (∫ x, ‖(f ∘ F) x‖^2) = ∫ x, ‖f x‖^2 :=
    hMP.integral_comp F.toMeasurableEquiv.measurableEmbedding (fun x => ‖f x‖^2)
  apply (sq_le_sq₀ (ambientPoissonL2Size_nonneg _ _) (mul_nonneg hM₀ (ambientPoissonL2Size_nonneg _ _))).1
  rw [mul_pow,ambientPoissonL2Size_sq,ambientPoissonL2Size_sq,hF,mul_add]
  exact add_le_add (h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hC (le_max_right _ _) 2) (integral_nonneg fun _ => hsNormSq_nonneg _)))
    (le_mul_of_one_le_left (integral_nonneg fun _ => sq_nonneg _)
      (show 1 ≤ (max 1 C)^2 by
        simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hM 2))

private theorem exists_boundary_secondWeakColumns {q : ℕ}
    {U : Set Point} (hU : IsSmoothDomain U) {a : Point} (ha : a ∈ frontier U) :
    ∃ (O : OpenDomain 3) (C : ℝ), a ∈ O.val ∧ 0 ≤ C ∧
      ∀ {u f : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q},
        AmbientDirichletPoissonData U u D f →
        HasLocalSecondWeakColumns ⟨O.val ∩ U,O.property.inter hU.1.1⟩ D
          (C*ambientPoissonL2Size D f) := by
  obtain ⟨B,hBa⟩ := hU.exists_epigraph_box ha
  let F := B.normalEuclideanChart
  have hF : ContDiff ℝ ∞ (F : Point → Point) := B.normalEuclideanChart_smooth
  have hInv : ContDiff ℝ ∞ (F.symm : Point → Point) := B.normalEuclideanChart_inverse_smooth
  have hMP : MeasurePreserving F (volume : Measure Point) volume := B.normalEuclideanChart_measurePreserving
  let R := B.radius / 2
  have hR : 0 < R := half_pos B.radius_pos
  let W : OpenDomain 3 := ⟨ball 0 (R/4) ∩ upperCoordinateHalfSpace.val,
    isOpen_ball.inter upperCoordinateHalfSpace.property⟩
  let O : OpenDomain 3 := ⟨F '' ball 0 (R/4),F.isOpenMap _ isOpen_ball⟩
  let V : OpenDomain 3 := ⟨O.val ∩ U,O.property.inter hU.1.1⟩
  have hFlat (x : Point) (hx : x ∈ ball (0 : Point) R) :
      F x ∈ U ↔ x ∈ upperCoordinateHalfSpace.val :=
    B.normalEuclideanChart_mem_domain_iff_of_mem_closedBall (ball_subset_closedBall hx)
  have hSmall : ball (0 : Point) (R/4) ⊆ ball 0 R := ball_subset_ball (by linarith only [hR])
  have hV : V.val = F '' W.val := by
    ext x
    constructor
    · rintro ⟨⟨y,hy,rfl⟩,hFy⟩
      exact ⟨y,⟨hy,(hFlat y (hSmall hy)).1 hFy⟩,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy.1,rfl⟩,(hFlat y (hSmall hy.1)).2 hy.2⟩
  have hMaps : MapsTo F.symm V.val W.val := by
    rw [hV]
    rintro _ ⟨y,hy,rfl⟩
    simpa only [F.symm_apply_apply] using hy
  have hMPR : MeasurePreserving F (volume.restrict W.val) (volume.restrict V.val) := by
    have hPre : F ⁻¹' V.val = W.val := hV ▸ preimage_image_eq W.val F.injective
    simpa only [hPre] using hMP.restrict_preimage V.property.measurableSet
  have hBound : Bornology.IsBounded V.val := by
    apply ((isCompact_closedBall (0 : Point) (R/4)).image F.continuous).isBounded.subset
    exact inter_subset_left.trans (image_mono ball_subset_closedBall)
  obtain ⟨L,hL,hRet⟩ := exists_memW12_secondColumns_of_gradientPullback (q := q)
    F hF hInv V W hBound hMaps (hMPR.symm F.toMeasurableEquiv)
  obtain ⟨C,hC,hFull⟩ := exists_flatBoundary_secondWeakColumns (q := q) F hF hInv hR
  have hComp : IsCompact (closure U) := hU.1.2.2.isCompact_closure
  obtain ⟨K,hK,hSob⟩ := exists_memW12_global_volumePreserving_pullback (q := q) F hF hMP _ hComp
  have haO : a ∈ O.val := ⟨0,mem_ball_self (by positivity),B.normalEuclideanChart_zero.trans hBa⟩
  have hM : 0 ≤ max 1 K := zero_le_one.trans (le_max_left _ _)
  refine ⟨O,L*C*max 1 K,haO,mul_nonneg (mul_nonneg hL (zero_le_one.trans hC)) hM,?_⟩
  intro u f D hData
  let D' := ambientGradientPullback F D
  let f' := f ∘ F
  have hSupp (x : Point) (hx : x ∉ closure U) : D x = 0 :=
    (hData.outside x (fun hy => hx (subset_closure hy))).2
  obtain ⟨hu',hEnergy⟩ := hSob hData.sobolev hSupp
  have hf' : MemLp f' 2 volume := hData.force.comp_measurePreserving hMP
  have hD' (j : Fin 3) : MemLp (fun x => D' x j) 2 volume := by
    simpa only [D',Measure.restrict_univ] using hu'.2.2 j
  have hD'Supp (x : Point) (hx : x ∉ F ⁻¹' closure U) : D' x = 0 := by
    funext j
    simp only [D',ambientGradientPullback,hSupp (F x) hx,Pi.zero_apply,smul_zero,Finset.sum_const_zero]
  have hA : Continuous (fun x : Point => ambientGradientMetric 3 q (fderiv ℝ F.symm (F x))) :=
    (contDiff_ambientGradientMetric (n := 3) (q := q) (p := ∞)).continuous.comp
      ((hInv.continuous_fderiv (by simp)).comp F.continuous)
  have hFlux := memLp_ambient_coordinate_operator_of_compact_gradient hA hD' (F.isCompact_preimage.2 hComp) hD'Supp
  have hInto : MapsTo F (ball 0 R ∩ upperCoordinateHalfSpace.val) U :=
    fun x hx => (hFlat x hx.1).2 hx.2
  have hWeak := hData.equation.metric_pullback F hF hInv hMP hInto
  have hZero (x : Point) (hx : x ∈ ball (0 : Point) R) (hSide : x ∉ upperCoordinateHalfSpace.val) :
      (u ∘ F) x = 0 ∧ D' x = 0 := by
    have hx' := hData.outside (F x) (fun h => hSide ((hFlat x hx).1 h))
    refine ⟨hx'.1,funext fun j => ?_⟩
    simp only [D',ambientGradientPullback,hx'.2,Pi.zero_apply,smul_zero,Finset.sum_const_zero]
  obtain ⟨H,hH⟩ := hFull hu' hf' hFlux hWeak hZero
  let E := ambientPoissonL2Size D' f'
  have hE : 0 ≤ E := ambientPoissonL2Size_nonneg _ _
  obtain ⟨G,hG⟩ := hRet D H (C*E) (fun j => (hH j).1)
    (fun j => (ambient_lpNorm_grad_column_le_poisson_size f' hD' W.val j).trans
      (le_mul_of_one_le_left hE hC)) (fun j => (hH j).2)
  refine ⟨G,fun j => ⟨(hG j).1,fun i => (hG j).2 i |>.trans ?_⟩⟩
  have hEt := ambientPoissonL2Size_pullback_le F hMP D f hK hEnergy
  simpa only [E, D', f',mul_assoc] using
    mul_le_mul_of_nonneg_left hEt (mul_nonneg hL (zero_le_one.trans hC))

private theorem exists_interior_secondWeakColumns {q : ℕ}
    {U : Set Point} (hU : IsOpen U) {a : Point} (ha : a ∈ U) :
    ∃ (O : OpenDomain 3) (C : ℝ), a ∈ O.val ∧ 0 ≤ C ∧
      ∀ {u f : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q},
        AmbientDirichletPoissonData U u D f →
        HasLocalSecondWeakColumns ⟨O.val ∩ U,O.property.inter hU⟩ D
          (C*ambientPoissonL2Size D f) := by
  obtain ⟨R,hR,hRinto⟩ := Metric.isOpen_iff.mp hU a ha
  let S : OpenDomain 3 := ⟨univ,isOpen_univ⟩
  let A : Point → AmbientGradientHilbert 3 q →L[ℝ] AmbientGradientHilbert 3 q :=
    fun _ => ContinuousLinearMap.id ℝ _
  have hEll (x : Point) (_ : x ∈ closedBall a R) (y : AmbientGradientHilbert 3 q) :
      1*‖y‖^2 ≤ inner ℝ (A x y) y := by simp [A]
  have hn : (ball a R ∩ S.val).Nonempty := ⟨a,mem_ball_self hR,mem_univ _⟩
  obtain ⟨C,hC,hColumns⟩ := exists_local_second_weak_column_invariant_direction hR zero_lt_one
    S convex_univ hn A contDiff_const hEll
  let O : OpenDomain 3 := ⟨ball a (R/4),isOpen_ball⟩
  have hO : O.val ⊆ U := (ball_subset_ball (by linarith only [hR])).trans hRinto
  letI : IsFiniteMeasure ((volume : Measure Point).restrict O.val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  refine ⟨O,Real.sqrt C,mem_ball_self (by positivity),Real.sqrt_nonneg _,?_⟩
  intro u f D hData
  have hFlux : MemLp (fun x => A x (packAmbientGradient (D x))) 2 volume :=
    memLp_packAmbientGradient hData.gradient_memLp
  have hWeak : HasWeakPackedDivergenceEq (ball a R ∩ S.val)
      (fun x => A x (packAmbientGradient (D x))) f := hData.equation.mono (inter_subset_left.trans hRinto)
  have hZero (x : Point) (_ : x ∈ ball a R) (hx : x ∉ S.val) : u x = 0 ∧ D x = 0 :=
    (hx (mem_univ _)).elim
  have hT (i : Fin 3) : ∃ G : Point → HarmonicMaps.Gradient 3 q, ∀ j,
      MemLp (fun x => G x j) 2 (volume.restrict O.val) ∧
      (∫ x in O.val, ‖G x j‖^2) ≤ C*((∫ x, hsNormSq (D x)) + ∫ x, ‖f x‖^2) ∧
      IsWeakAmbientCoordinatePartial O.val i (fun x => D x j) (fun x => G x j) := by
    simpa only [S,inter_univ,O] using hColumns hData.sobolev hData.force hFlux hWeak hZero i (fun _ _ => Iff.rfl)
  choose G hG using hT
  have h' : HasLocalSecondWeakColumns O D (Real.sqrt C*ambientPoissonL2Size D f) := by
    refine ⟨fun x j i => G i x j,fun j => ⟨?_,fun i => ?_⟩⟩
    · exact memW12_of_ambient_coordinate_partials O
        ((hData.gradient_memLp j).mono_measure Measure.restrict_le_self)
        (fun i => (hG i j).1) (fun i => (hG i j).2.2)
    · exact ambient_lpNorm_le_mul_poisson_size_of_sq (hG i j).1 hC (hG i j).2.1
  simpa only [inter_eq_left.mpr hO] using h'

/-- Each point of the domain closure has a fixed physical neighborhood
on which the Dirichlet Hessian estimate holds for all weak data. -/
theorem exists_smoothDomain_local_secondWeakColumns {q : ℕ}
    {U : Set Point} (hU : IsSmoothDomain U) {a : Point} (ha : a ∈ closure U) :
    ∃ (O : OpenDomain 3) (C : ℝ), a ∈ O.val ∧ 0 ≤ C ∧
      ∀ {u f : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q},
        AmbientDirichletPoissonData U u D f →
        HasLocalSecondWeakColumns ⟨O.val ∩ U,O.property.inter hU.1.1⟩ D
          (C*ambientPoissonL2Size D f) := by
  rw [closure_eq_self_union_frontier,mem_union] at ha
  exact ha.elim (exists_interior_secondWeakColumns hU.1.1) (exists_boundary_secondWeakColumns hU)

end Thesis

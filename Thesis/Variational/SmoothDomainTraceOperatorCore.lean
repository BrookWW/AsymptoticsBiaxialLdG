module

public import Thesis.Variational.SmoothDomainSurfaceCoordinates
import Thesis.Variational.SmoothDomainNormalTrace
import Thesis.Variational.SmoothDomainSobolevDensity
import Thesis.Variational.WholeWallEnergy
import HarmonicMaps.Analysis.SmoothWeakGradient
import HarmonicMaps.Analysis.VariableMollificationL2
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! The bounded linear trace on the actual Hilbert space of Sobolev
coordinates. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set Topology
open scoped BigOperators ContDiff ENNReal NNReal

namespace Thesis

variable {Ω : Set Point}

theorem IsSmoothDomain.isFiniteMeasure_frontierSurface (hΩ : IsSmoothDomain Ω) :
    IsFiniteMeasure (frontierSurfaceMeasure Ω) := by
  constructor
  rw [← isometry_subtype_coe.euclideanHausdorffMeasure_image, image_univ, Subtype.range_coe_subtype, setOf_mem_eq]
  exact hΩ.frontier_euclideanHausdorffMeasure_lt_top

private theorem memLp_of_continuousOn_closure {q : ℕ} (hΩ : IsSmoothDomain Ω)
    {f : Point → Ambient q} (hf : Continuous f) : MemLp f 2 (volume.restrict Ω) := by
  letI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩ.1.2.2.measure_lt_top.ne
  obtain ⟨M,hM⟩ := hΩ.1.2.2.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable M ((ae_restrict_mem hΩ.1.1.measurableSet).mono
    (fun x hx => hM x (subset_closure hx)))

theorem IsSmoothDomain.memW12_of_smooth (hΩ : IsSmoothDomain Ω) {q : ℕ}
    {f : Point → Ambient q} (hf : ContDiff ℝ ∞ f) :
    MemW12 ⟨Ω,hΩ.1.1⟩ f (fun x i => coordinateDerivative f hf i x) :=
  memW12_of_contDiff ⟨Ω,hΩ.1.1⟩ hf (memLp_of_continuousOn_closure hΩ hf.continuous)
    (fun i => memLp_of_continuousOn_closure hΩ ((hf.continuous_fderiv (by simp)).clm_apply continuous_const))

theorem IsSmoothDomain.memLp_continuous_frontier (hΩ : IsSmoothDomain Ω) {q : ℕ}
    {f : Point → Ambient q} (hf : Continuous f) :
    MemLp (fun x : frontier Ω => f x) 2 (frontierSurfaceMeasure Ω) := by
  letI := hΩ.isFiniteMeasure_frontierSurface
  obtain ⟨M,hM⟩ := hΩ.1.2.2.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound (hf.comp continuous_subtype_val).aestronglyMeasurable M
    (Eventually.of_forall fun x => hM _ (frontier_subset_closure x.property))

/-- The native weak map and its actual three Euclidean columns in the
same product used by the tensor trace interface. -/
@[expose] def nativeSobolevL2Point (hΩ : IsOpen Ω)
    {u : Point → Ambient 5} {D : Point → HarmonicMaps.Gradient 3 5}
    (hu : MemW12 ⟨Ω,hΩ⟩ u D) : SobolevL2Coordinates Ω :=
  WithLp.toLp 2 (Fin.cases (hu.2.1.toLp u) (fun j : Fin 3 => (hu.2.2 j).toLp (fun x => D x j)))

theorem nativeSobolevL2Point_norm_sq (hΩ : IsOpen Ω)
    {u : Point → Ambient 5} {D : Point → HarmonicMaps.Gradient 3 5}
    (hu : MemW12 ⟨Ω,hΩ⟩ u D) :
    ‖nativeSobolevL2Point hΩ hu‖ ^ 2 = (∫ x in Ω, ‖u x‖ ^ 2) + ∫ x in Ω, hsNormSq (D x) := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  simp only [nativeSobolevL2Point, PiLp.toLp_apply, Fin.cases_zero, Fin.cases_succ,
    Lp.norm_toLp, ← integral_norm_sq_eq_eLpNorm_two_toReal_sq hu.2.1,
    ← integral_norm_sq_eq_eLpNorm_two_toReal_sq (hu.2.2 _)]
  congr 1
  unfold hsNormSq
  rw [integral_finsetSum]
  intro i _
  exact (memLp_two_iff_integrable_sq_norm (hu.2.2 i).aestronglyMeasurable).mp (hu.2.2 i)

private theorem integral_sq_on_wallRange_le {q : ℕ}
    (B : SmoothDomainEpigraphBox Ω) {f : Point → Ambient q}
    (hfBase : MemLp (fun y => f (B.normalParameter (y,0))) 2 (volume.restrict B.planeDomain.val)) :
    (∫ x in range B.wallMap, ‖f (x : Point)‖ ^ 2 ∂frontierSurfaceMeasure Ω) ≤
      (B.lip : ℝ)^2 * (∫ y in B.planeDomain.val, ‖f (B.normalParameter (y,0))‖ ^ 2) := by
  let σ := B.wallBaseMeasure
  let A := (frontierSurfaceMeasure Ω).restrict (range B.wallMap)
  let μ := Measure.map B.wallMap σ
  let g (x : frontier Ω) := ‖f (x : Point)‖ ^ 2
  have hgBase : Integrable (fun y : Plane => ‖f (B.normalParameter (y,0))‖ ^ 2)
      (volume.restrict B.planeDomain.val) := (memLp_two_iff_integrable_sq_norm hfBase.1).mp hfBase
  have hgPull : Integrable (g ∘ B.wallMap) σ :=
    B.wallBaseMeasure_coe.integrable_comp_of_integrable hgBase
  have hg : Integrable g μ := (B.measurableEmbedding_wallMap.integrable_map_iff).2 hgPull
  have hEq :
      (∫ x, g x ∂μ) = ∫ y in B.planeDomain.val, ‖f (B.normalParameter (y,0))‖ ^ 2 := by
    rw [B.measurableEmbedding_wallMap.integral_map]
    exact B.wallBaseMeasure_coe.integral_comp (MeasurableEmbedding.subtype_coe B.planeDomain.property.measurableSet)
      (fun y : Plane => ‖f (B.normalParameter (y,0))‖ ^ 2)
  calc
    (∫ x, g x ∂A) ≤ ∫ x, g x ∂((B.lip : ℝ≥0∞)^2 • μ) :=
      integral_mono_measure B.surfaceMeasure_le_map_wallBase (Eventually.of_forall fun _ => sq_nonneg _)
        (hg.smul_measure (by simp))
    _ = _ := by
      rw [integral_smul_measure, hEq]
      simp only [ENNReal.toReal_pow, ENNReal.coe_toReal, smul_eq_mul]

private theorem integral_le_sum_of_measurable_cover {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {μ : Measure X} (A : ι → Set X) (hCover : ⋃ i, A i = univ)
    {g : X → ℝ} (hg : Integrable g μ) (hg₀ : ∀ x, 0 ≤ g x) :
    (∫ x, g x ∂μ) ≤ ∑ i, ∫ x in A i, g x ∂μ := by
  classical
  have hμ : μ ≤ ∑ i, μ.restrict (A i) := by
    refine Measure.le_iff.2 fun t ht => ?_
    rw [Measure.finsetSum_apply _ _ t]
    simp_rw [Measure.restrict_apply ht]
    have h := measure_iUnion_fintype_le (μ := μ) (fun i => t ∩ A i)
    simpa only [← inter_iUnion, hCover, inter_univ] using h
  have hgI (i : ι) : Integrable g (μ.restrict (A i)) := hg.restrict
  calc
    _ ≤ ∫ x, g x ∂(∑ i, μ.restrict (A i)) :=
      integral_mono_measure hμ (Eventually.of_forall hg₀)
        (integrable_finsetSum_measure.2 (fun i _ => hgI i))
    _ = _ := integral_finsetSum_measure fun i _ => hgI i

/-- The original smooth restriction is bounded in the exact ambient graph
norm. Surface measure is the normalized Hausdorff measure of the physical
frontier. -/
theorem IsSmoothDomain.exists_smooth_boundary_norm_bound (hΩ : IsSmoothDomain Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : Point → Ambient 5} (hf : ContDiff ℝ ∞ f),
      ‖(hΩ.memLp_continuous_frontier hf.continuous).toLp (fun x : frontier Ω => f x)‖ ≤
        C * ‖nativeSobolevL2Point hΩ.1.1 (hΩ.memW12_of_smooth hf)‖ := by
  classical
  have hLocal (x : frontier Ω) := hΩ.exists_epigraph_box x.property
  choose B hCenter using hLocal
  let A (x : frontier Ω) := range (B x).wallMap
  have hCover : (univ : Set (frontier Ω)) ⊆ ⋃ x,A x := fun x _ =>
    mem_iUnion.2 ⟨x,(B x).mem_range_wallMap_center (hCenter x)⟩
  have hK : IsCompact (univ : Set (frontier Ω)) := by
    letI : CompactSpace (frontier Ω) := isCompact_iff_compactSpace.mp
      (hΩ.1.2.2.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure)
    exact isCompact_univ
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover A (fun x => (B x).isOpen_range_wallMap) hCover
  have hSubCover : (⋃ i : I, A i) = univ := by
    rw [iUnion_subtype]
    exact eq_univ_of_univ_subset hI
  have hGeom (i : I) := (B i).exists_normalTrace_bound (q := 5) hΩ.1.1 (B i).radius_pos le_rfl
  choose K hK hTr using hGeom
  let C₀ := ∑ i : I, ((B i).lip : ℝ)^2 * K i
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hK i)
  refine ⟨Real.sqrt C₀,Real.sqrt_nonneg _,?_⟩
  intro f hf
  let p := nativeSobolevL2Point hΩ.1.1 (hΩ.memW12_of_smooth hf)
  let hF := hΩ.memLp_continuous_frontier hf.continuous
  have hSex (i : I) : (∫ x in A i, ‖f (x : Point)‖ ^ 2 ∂frontierSurfaceMeasure Ω) ≤
      (((B i).lip : ℝ)^2 * K i) * ‖p‖^2 := by
    obtain ⟨H,hH,hBound⟩ := hTr i (hΩ.memW12_of_smooth hf)
    let o : Icc (0 : ℝ) (B i).radius := ⟨0,le_rfl,(B i).radius_pos.le⟩
    obtain ⟨hs,hCls⟩ := hH.eq_raw_of_continuous (B := B i) (B i).radius_pos le_rfl hf.continuous o
    have hE : (∫ y in (B i).planeDomain.val, ‖f ((B i).normalParameter (y,0))‖^2) = ‖H o‖^2 := by
      rw [hCls, Lp.norm_toLp]
      exact integral_norm_sq_eq_eLpNorm_two_toReal_sq hs
    have h := integral_sq_on_wallRange_le (B i) hs
    rw [hE] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (hBound o) (sq_nonneg _)).trans_eq (by
      rw [nativeSobolevL2Point_norm_sq hΩ.1.1 (hΩ.memW12_of_smooth hf) |> Eq.symm]
      ring))
  have hIt : (∫ x : frontier Ω, ‖f (x : Point)‖ ^ 2 ∂frontierSurfaceMeasure Ω) ≤ C₀ * ‖p‖ ^ 2 := by
    have hInt := (memLp_two_iff_integrable_sq_norm hF.1).mp hF
    apply (integral_le_sum_of_measurable_cover (fun i : I => A i) hSubCover hInt (fun _ => sq_nonneg _)).trans
    unfold C₀
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hSex i
  have hSq : ‖hF.toLp (fun x : frontier Ω => f x)‖ ^ 2 ≤ C₀ * ‖p‖^2 := by
    rwa [Lp.norm_toLp, ← integral_norm_sq_eq_eLpNorm_two_toReal_sq hF]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
  rw [mul_pow, Real.sq_sqrt hC₀]
  exact hSq

private def smoothAmbientSubmodule : Submodule ℝ (Point → Ambient 5) where
  carrier := {f | ContDiff ℝ ∞ f}
  zero_mem' := by
    change ContDiff ℝ ∞ (fun _ : Point => (0 : Ambient 5))
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ g at hg
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiff ℝ ∞ f at hf
    exact hf.const_smul c

private theorem smoothAmbientSubmodule.contDiff (f : smoothAmbientSubmodule) :
    ContDiff ℝ ∞ (f : Point → Ambient 5) := f.property

private theorem smoothGraph_coordinateDerivative_add
    (f g : smoothAmbientSubmodule) (x : Point) (i : Fin 3) :
    coordinateDerivative (↑(f+g) : Point → Ambient 5) (f+g).property i x =
      coordinateDerivative (f : Point → Ambient 5) f.property i x +
      coordinateDerivative (g : Point → Ambient 5) g.property i x := by
  have hf : ContDiff ℝ ∞ (f : Point → Ambient 5) := f.property
  have hg : ContDiff ℝ ∞ (g : Point → Ambient 5) := g.property
  change fderiv ℝ ((f : Point → Ambient 5) + (g : Point → Ambient 5)) x (EuclideanSpace.single i 1) =
    fderiv ℝ (f : Point → Ambient 5) x (EuclideanSpace.single i 1) +
      fderiv ℝ (g : Point → Ambient 5) x (EuclideanSpace.single i 1)
  rw [fderiv_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x), add_apply]

private theorem smoothGraph_coordinateDerivative_const_smul
    (c : ℝ) (f : smoothAmbientSubmodule) (x : Point) (i : Fin 3) :
    coordinateDerivative (↑(c • f) : Point → Ambient 5) (c • f).property i x =
      c • coordinateDerivative (f : Point → Ambient 5) f.property i x := by
  have hf : ContDiff ℝ ∞ (f : Point → Ambient 5) := f.property
  change fderiv ℝ (c • (f : Point → Ambient 5)) x (EuclideanSpace.single i 1) =
    c • fderiv ℝ (f : Point → Ambient 5) x (EuclideanSpace.single i 1)
  rw [fderiv_const_smul (hf.differentiable (by simp) x), smul_apply]

private def smoothGraphLinearMap (hΩ : IsSmoothDomain Ω) :
    smoothAmbientSubmodule →ₗ[ℝ] SobolevL2Coordinates Ω where
  toFun f := nativeSobolevL2Point hΩ.1.1 (hΩ.memW12_of_smooth f.property)
  map_add' f g := by
    ext1 i
    let hu := hΩ.memW12_of_smooth f.property
    let hv := hΩ.memW12_of_smooth g.property
    let hsum := hΩ.memW12_of_smooth (f+g).property
    refine Fin.cases ?_ (fun j => ?_) i
    · change hsum.2.1.toLp (↑(f+g)) = hu.2.1.toLp _ + hv.2.1.toLp _
      rw [← hu.2.1.toLp_add hv.2.1]
      exact MemLp.toLp_congr _ _ (Eventually.of_forall fun _ => rfl)
    · change (hsum.2.2 j).toLp _ = (hu.2.2 j).toLp _ + (hv.2.2 j).toLp _
      rw [← (hu.2.2 j).toLp_add (hv.2.2 j)]
      exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => smoothGraph_coordinateDerivative_add f g x j)
  map_smul' c f := by
    ext1 i
    let hu := hΩ.memW12_of_smooth f.property
    let hmul := hΩ.memW12_of_smooth (c • f).property
    refine Fin.cases ?_ (fun j => ?_) i
    · change hmul.2.1.toLp (↑(c • f)) = c • hu.2.1.toLp _
      rw [← hu.2.1.toLp_const_smul c]
      exact MemLp.toLp_congr _ _ (Eventually.of_forall fun _ => rfl)
    · change (hmul.2.2 j).toLp _ = c • (hu.2.2 j).toLp _
      rw [← (hu.2.2 j).toLp_const_smul c]
      exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => smoothGraph_coordinateDerivative_const_smul c f x j)

private def smoothRestrictionLinearMap (hΩ : IsSmoothDomain Ω) :
    smoothAmbientSubmodule →ₗ[ℝ] SobolevTraceL2 Ω where
  toFun f := (hΩ.memLp_continuous_frontier (smoothAmbientSubmodule.contDiff f).continuous).toLp
    (fun x : frontier Ω => (f : Point → Ambient 5) x)
  map_add' f g := by
    let hf := hΩ.memLp_continuous_frontier (smoothAmbientSubmodule.contDiff f).continuous
    let hg := hΩ.memLp_continuous_frontier (smoothAmbientSubmodule.contDiff g).continuous
    change (hΩ.memLp_continuous_frontier (smoothAmbientSubmodule.contDiff (f+g)).continuous).toLp _ =
      hf.toLp _ + hg.toLp _
    rw [← hf.toLp_add hg]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun _ => rfl)
  map_smul' c f := by
    let hf := hΩ.memLp_continuous_frontier (smoothAmbientSubmodule.contDiff f).continuous
    change (hΩ.memLp_continuous_frontier (smoothAmbientSubmodule.contDiff (c • f)).continuous).toLp _ =
      c • hf.toLp _
    rw [← hf.toLp_const_smul c]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun _ => rfl)

private theorem exists_graph_extension {M H E : Type*}
    [AddCommGroup M] [Module ℝ M]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (J : M →ₗ[ℝ] H) (L : M →ₗ[ℝ] E) (hL : ∃ C : ℝ, ∀ f, ‖L f‖ ≤ C * ‖J f‖) :
    ∃ T : H →L[ℝ] E, ∀ f, T (J f) = L f := by
  let S := LinearMap.range J
  let K := S.topologicalClosure
  letI : CompleteSpace K := (Submodule.isClosed_topologicalClosure S).isComplete.completeSpace_coe
  let ι : S →L[ℝ] K :=
    { toLinearMap := S.inclusion (Submodule.le_topologicalClosure S)
      cont := continuous_subtype_val.subtype_mk _ }
  have hI : IsUniformInducing ι := (show Isometry ι from Isometry.of_dist_eq fun _ _ => rfl).isUniformInducing
  have hDense : DenseRange ι := by
    intro x
    rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    change (x : H) ∈ closure (Subtype.val '' range ι)
    have hR : (Subtype.val : K → H) '' range ι = (S : Set H) := by
      ext y
      constructor
      · rintro ⟨_,⟨z,rfl⟩,rfl⟩
        exact z.property
      · intro hy
        exact ⟨ι ⟨y,hy⟩,mem_range_self _,rfl⟩
    rw [hR]
    exact x.property
  let R := L.compLeftInverse J
  let T := (R.extend ι).comp K.orthogonalProjectionOnto
  refine ⟨T,?_⟩
  intro f
  let y : S := ⟨J f,LinearMap.mem_range_self J f⟩
  have hProjection : K.orthogonalProjectionOnto (J f) = ι y :=
    K.orthogonalProjectionOnto_mem_subspace_eq_self (ι y)
  change R.extend ι (K.orthogonalProjectionOnto (J f)) = L f
  rw [hProjection, R.extend_eq hDense hI]
  exact L.compLeftInverse_apply_of_bdd J hL f (J f) rfl

/-- The trace specified on globally smooth fields has a bounded linear
extension to the ambient Hilbert product of Sobolev coordinates. -/
theorem IsSmoothDomain.exists_smoothTraceExtension (hΩ : IsSmoothDomain Ω) :
    ∃ T : SobolevL2Coordinates Ω →L[ℝ] SobolevTraceL2 Ω,
      ∀ {f : Point → Ambient 5} (hf : ContDiff ℝ ∞ f),
        T (nativeSobolevL2Point hΩ.1.1 (hΩ.memW12_of_smooth hf)) =
          (hΩ.memLp_continuous_frontier hf.continuous).toLp (fun x : frontier Ω => f x) := by
  obtain ⟨C,_,hC⟩ := hΩ.exists_smooth_boundary_norm_bound
  let J := smoothGraphLinearMap hΩ
  let L := smoothRestrictionLinearMap hΩ
  have hBound (f : smoothAmbientSubmodule) : ‖L f‖ ≤ C * ‖J f‖ := by
    dsimp only [J,L,smoothGraphLinearMap,smoothRestrictionLinearMap,LinearMap.coe_mk,AddHom.coe_mk]
    exact hC (smoothAmbientSubmodule.contDiff f)
  obtain ⟨T,hT⟩ := exists_graph_extension J L ⟨C,hBound⟩
  refine ⟨T,?_⟩
  intro f hf
  have h := hT ⟨f,hf⟩
  dsimp only [J,L,smoothGraphLinearMap,smoothRestrictionLinearMap,LinearMap.coe_mk,AddHom.coe_mk] at h
  exact h

end Thesis

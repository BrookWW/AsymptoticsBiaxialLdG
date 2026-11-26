module

public import Thesis.Variational.BoundaryPohozaev
import Thesis.Variational.PiecewiseBoundaryFluxData
import Thesis.Variational.RegularWallGraphFlux
import Thesis.Variational.HalfSpaceFlux
import Thesis.Variational.HausdorffNullSeamCutoff
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.Regular

/-! Coordinate Gauss–Green on a bounded Lipschitz domain with regular wall almost everywhere. -/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal Manifold

namespace Thesis

private def regularWallNeighborhoods (U : Set Point) : Set Point :=
  ⋃ P : RegularWallGraphPatch U, P.neighborhood

private def exceptionalWall (U : Set Point) : Set Point :=
  closure U \ (U ∪ regularWallNeighborhoods U)

private theorem isCompact_exceptionalWall {U : Set Point} {ν : Point → Point}
    (hU : PiecewiseRegularBoundary U ν) : IsCompact (exceptionalWall U) := by
  apply hU.isBounded.isCompact_closure.diff
  exact hU.isOpen.union (isOpen_iUnion fun P => P.isOpen_neighborhood)

private theorem exceptionalWall_subset_frontier {U : Set Point} (hU : IsOpen U) :
    exceptionalWall U ⊆ frontier U := by
  rw [frontier, hU.interior_eq]
  exact fun x hx => ⟨hx.1,fun h => hx.2 (Or.inl h)⟩

private theorem exceptionalWall_surface_null {U : Set Point} {ν : Point → Point}
    (hU : PiecewiseRegularBoundary U ν) :
    Measure.euclideanHausdorffMeasure 2 (exceptionalWall U) = 0 := by
  have hComp := isCompact_exceptionalWall hU
  let μ : Measure Point := Measure.euclideanHausdorffMeasure 2
  have hOff : ∀ᵐ x ∂μ.restrict (frontier U), x ∉ exceptionalWall U := by
    filter_upwards [hU.normal_ae] with x hx
    obtain ⟨P,hP⟩ := hx.exists_graph_patch
    intro h
    exact h.2 (Or.inr (mem_iUnion.2 ⟨P,hP ▸ P.center_mem_neighborhood⟩))
  rw [ae_iff] at hOff
  have hK : (μ.restrict (frontier U)) (exceptionalWall U) = 0 := by simpa only [not_not,setOf_mem_eq] using hOff
  rw [Measure.restrict_apply hComp.isClosed.measurableSet,
    inter_eq_left.mpr (exceptionalWall_subset_frontier hU.isOpen)] at hK
  exact hK

private theorem isBounded_graph_neighborhood {U : Set Point} (P : RegularWallGraphPatch U) :
    Bornology.IsBounded P.neighborhood := by
  have hK : IsCompact (closedBall (0 : Plane) P.baseRadius ×ˢ Icc (-P.halfHeight) P.halfHeight) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  exact (hK.image P.chart.continuous).isBounded.subset
    (image_mono (prod_mono ball_subset_closedBall Ioo_subset_Icc_self))

private theorem integral_coordinate_derivative_eq_zero_of_supported_interior {U : Set Point}
    (hU : IsOpen U) {f : Point → ℝ} (hf : ContDiffOn ℝ 1 f (closure U))
    (hCap : HasCompactSupport f) (hS : tsupport f ⊆ U) (j : Fin 3) :
    (∫ x in U, coordDeriv j f x) = 0 := by
  have hC : ContDiff ℝ 1 f := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact (hf _ (subset_closure hx)).contDiffAt (mem_of_superset (hU.mem_nhds hx) subset_closure)
    · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1
        (fun h => hx (hS h)))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    unfold coordDeriv
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hS h)),zero_apply])]
  exact integral_fderiv_apply_eq_zero_of_compactSupport hC hCap (axis j)

private inductive FluxLocation (U : Set Point)
  | interior
  | graph (P : RegularWallGraphPatch U)
  | outsideSupport

private def FluxLocation.openSet {U : Set Point} (f : Point → ℝ) : FluxLocation U → Set Point
  | .interior => U
  | .graph P => P.neighborhood
  | .outsideSupport => (tsupport f)ᶜ

private theorem flux_eq_of_support_disjoint_exceptionalWall {U : Set Point} {ν : Point → Point}
    (hU : PiecewiseRegularBoundary U ν) {f : Point → ℝ} (hf : ContDiffOn ℝ 1 f (closure U))
    (hS : Disjoint (tsupport f) (exceptionalWall U)) (j : Fin 3) :
    (∫ x in U, coordDeriv j f x) =
      ∫ x in frontier U, f x * ν x j ∂(Measure.euclideanHausdorffMeasure 2) := by
  classical
  let W : FluxLocation U → Set Point := FluxLocation.openSet f
  have hW (i : FluxLocation U) : IsOpen (W i) := by
    cases i with
    | interior => exact hU.isOpen
    | graph P => exact P.isOpen_neighborhood
    | outsideSupport => exact (isClosed_tsupport f).isOpen_compl
  have hCover : closure U ⊆ ⋃ i, W i := by
    intro x hx
    by_cases h : x ∈ U ∪ regularWallNeighborhoods U
    · rcases h with h | h
      · exact mem_iUnion.2 ⟨FluxLocation.interior,h⟩
      · obtain ⟨P,hP⟩ := mem_iUnion.1 h
        exact mem_iUnion.2 ⟨FluxLocation.graph P,hP⟩
    · exact mem_iUnion.2 ⟨FluxLocation.outsideSupport,
        fun hn => Set.disjoint_left.mp hS hn ⟨hx,h⟩⟩
  obtain ⟨I,hI⟩ := hU.isBounded.isCompact_closure.elim_finite_subcover W hW hCover
  have hIF : closure U ⊆ ⋃ i : I, W i := by rwa [iUnion_subtype]
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Point)
    isClosed_closure (fun i : I => W i) (fun i => hW i) hIF
  let p (i : I) (x : Point) := ρ i x * f x
  have hpC (i : I) : ContDiffOn ℝ 1 (p i) (closure U) :=
    (((ρ i).contMDiff.contDiff).of_le (by simp)).contDiffOn.mul hf
  have hpS (i : I) : tsupport (p i) ⊆ W i :=
    (tsupport_mul_subset_left (f := fun x => ρ i x) (g := f)).trans (hρ i)
  have hpEq (x : Point) (hx : x ∈ closure U) : ∑ i : I, p i x = f x := by
    have hR : ∑ i : I, ρ i x = 1 := ρ.sum_finsupport' x hx (Finset.subset_univ _)
    simp only [p, ← Finset.sum_mul, hR,one_mul]
  have hpD (x : Point) (hx : x ∈ U) : coordDeriv j f x = ∑ i : I, coordDeriv j (p i) x := by
    have hE : f =ᶠ[𝓝 x] (fun y => ∑ i : I, p i y) :=
      (show ∀ᶠ y in 𝓝 x, y ∈ U from hU.isOpen.mem_nhds hx).mono fun y hy => (hpEq y (subset_closure hy)).symm
    have hD (i : I) : DifferentiableAt ℝ (p i) x :=
      (((hpC i) x (subset_closure hx)).contDiffAt
        (mem_of_superset (hU.isOpen.mem_nhds hx) subset_closure)).differentiableAt one_ne_zero
    simp only [coordDeriv]
    rw [hE.fderiv_eq, fderiv_fun_sum (fun i _ => hD i), sum_apply]
  have hPieces (i : I) :
      (∫ x in U, coordDeriv j (p i) x) =
        ∫ x in frontier U, p i x * ν x j ∂(Measure.euclideanHausdorffMeasure 2) := by
    cases hLoc : (i : FluxLocation U) with
    | interior =>
      have hpU : tsupport (p i) ⊆ U := by simpa only [W,hLoc,FluxLocation.openSet] using hpS i
      have hK : HasCompactSupport (p i) :=
        hU.isBounded.isCompact_closure.of_isClosed_subset (isClosed_tsupport _) (hpU.trans subset_closure)
      rw [integral_coordinate_derivative_eq_zero_of_supported_interior hU.isOpen (hpC i) hK hpU]
      symm
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      have hxU : x ∉ U := by
        have h := hx.2
        rwa [hU.isOpen.interior_eq] at h
      rw [image_eq_zero_of_notMem_tsupport (fun h => hxU (hpU h)),zero_mul]
    | graph P =>
      have hpP : tsupport (p i) ⊆ P.neighborhood := by
        simpa only [W,hLoc,FluxLocation.openSet] using hpS i
      have hK : HasCompactSupport (p i) :=
        (isBounded_graph_neighborhood P).isCompact_closure.of_isClosed_subset
          (isClosed_tsupport _) (hpP.trans subset_closure)
      exact P.gaussGreen_supported_graph hU.isOpen hU.normal_ae (hpC i) hK hpP j
    | outsideSupport =>
      have hpO : tsupport (p i) ⊆ (tsupport f)ᶜ := by simpa only [W,hLoc,FluxLocation.openSet] using hpS i
      have hpF : tsupport (p i) ⊆ tsupport f := tsupport_mul_subset_right
      have hz : p i = 0 := by
        funext x
        apply image_eq_zero_of_notMem_tsupport
        intro h
        exact hpO h (hpF h)
      rw [hz]
      simp [coordDeriv]
  calc
    _ = ∫ x in U, ∑ i : I, coordDeriv j (p i) x :=
      setIntegral_congr_fun hU.isOpen.measurableSet hpD
    _ = ∑ i : I, ∫ x in U, coordDeriv j (p i) x :=
      integral_finsetSum _ fun i _ => (hU.integrable_coordinate_flux (hpC i) j).1
    _ = ∑ i : I, ∫ x in frontier U, p i x * ν x j ∂(Measure.euclideanHausdorffMeasure 2) :=
      Finset.sum_congr rfl fun i _ => hPieces i
    _ = ∫ x in frontier U, ∑ i : I, p i x * ν x j ∂(Measure.euclideanHausdorffMeasure 2) :=
      (integral_finsetSum _ fun i _ => (hU.integrable_coordinate_flux (hpC i) j).2).symm
    _ = _ := setIntegral_congr_fun isClosed_frontier.measurableSet fun x hx => by
      rw [← Finset.sum_mul, hpEq x (frontier_subset_closure hx)]

private theorem coordDeriv_cutoff_mul {U : Set Point} (hU : IsOpen U) {f χ : Point → ℝ}
    (hf : ContDiffOn ℝ 1 f (closure U)) (hχ : ContDiff ℝ ∞ χ)
    {x : Point} (hx : x ∈ U) (j : Fin 3) :
    coordDeriv j (fun y => χ y * f y) x = χ x * coordDeriv j f x + f x * coordDeriv j χ x := by
  have hD := ((hf _ (subset_closure hx)).contDiffAt
    (mem_of_superset (hU.mem_nhds hx) subset_closure)).differentiableAt one_ne_zero
  simp only [coordDeriv]
  rw [fderiv_fun_mul (hχ.differentiable (by simp) x) hD, add_apply,smul_apply,smul_apply,
    smul_eq_mul,smul_eq_mul]

private theorem cutoff_error_volume {U : Set Point} {ν : Point → Point}
    (hU : PiecewiseRegularBoundary U ν) {f χ : Point → ℝ}
    (hf : ContDiffOn ℝ 1 f (closure U)) (hχ : ContDiff ℝ ∞ χ)
    (M η : ℝ) (hM : 0 ≤ M)
    (hF : ∀ x ∈ closure U, ‖f x‖ ≤ M) (j : Fin 3)
    (hD : ∀ x ∈ U, ‖coordDeriv j f x‖ ≤ M)
    (hχI : Integrable (fun x => χ x - 1)) (hχL : (∫ x, ‖χ x - 1‖) ≤ η)
    (hJ : Integrable (coordDeriv j χ)) (hJL : (∫ x, ‖coordDeriv j χ x‖) ≤ η) :
    ‖(∫ x in U, coordDeriv j (fun y => χ y * f y) x) -
      (∫ x in U, coordDeriv j f x)‖ ≤ 2 * M * η := by
  let g (x : Point) := χ x * f x
  have hg : ContDiffOn ℝ 1 g (closure U) := ((hχ.of_le (by simp)).contDiffOn.mul hf)
  have hI := (hU.integrable_coordinate_flux hg j).1.sub (hU.integrable_coordinate_flux hf j).1
  have hχJV : IntegrableOn (fun x => M * (‖χ x - 1‖ + ‖coordDeriv j χ x‖)) U volume :=
    ((hχI.norm.add hJ.norm).const_mul M).integrableOn
  have hPt (x : Point) (hx : x ∈ U) :
      ‖coordDeriv j g x - coordDeriv j f x‖ ≤ M * (‖χ x - 1‖ + ‖coordDeriv j χ x‖) := by
    change ‖coordDeriv j (fun y => χ y * f y) x - coordDeriv j f x‖ ≤ _
    rw [coordDeriv_cutoff_mul hU.isOpen hf hχ hx]
    have hEq : χ x * coordDeriv j f x + f x * coordDeriv j χ x - coordDeriv j f x =
        (χ x - 1) * coordDeriv j f x + f x * coordDeriv j χ x := by ring
    rw [hEq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul,norm_mul,mul_add,mul_comm M ‖χ x - 1‖]
    exact add_le_add (mul_le_mul_of_nonneg_left (hD x hx) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (hF x (subset_closure hx)) (norm_nonneg _))
  change ‖(∫ x in U, coordDeriv j g x) - (∫ x in U, coordDeriv j f x)‖ ≤ _
  rw [← integral_sub (hU.integrable_coordinate_flux hg j).1 (hU.integrable_coordinate_flux hf j).1]
  calc
    _ ≤ ∫ x in U, ‖coordDeriv j g x - coordDeriv j f x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in U, M * (‖χ x - 1‖ + ‖coordDeriv j χ x‖) :=
      setIntegral_mono_on hI.norm hχJV hU.isOpen.measurableSet hPt
    _ = M * ((∫ x in U, ‖χ x - 1‖) + (∫ x in U, ‖coordDeriv j χ x‖)) := by
      rw [integral_const_mul, integral_add hχI.norm.integrableOn hJ.norm.integrableOn]
    _ ≤ M * (η + η) := mul_le_mul_of_nonneg_left
      (add_le_add ((setIntegral_le_integral hχI.norm (Eventually.of_forall fun _ => norm_nonneg _)).trans hχL)
        ((setIntegral_le_integral hJ.norm (Eventually.of_forall fun _ => norm_nonneg _)).trans hJL)) hM
    _ = _ := by ring

private theorem cutoff_error_frontier {U : Set Point} {ν : Point → Point}
    (hU : PiecewiseRegularBoundary U ν) {f χ : Point → ℝ}
    (hf : ContDiffOn ℝ 1 f (closure U)) (hχ : ContDiff ℝ ∞ χ)
    (M η : ℝ) (hM : 0 ≤ M) (hF : ∀ x ∈ closure U, ‖f x‖ ≤ M)
    (hχRange : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {O : Set Point} (hO : MeasurableSet O)
    (hχO : ∀ x ∉ O, χ x = 1) (hVol : ((Measure.euclideanHausdorffMeasure 2).restrict (frontier U)) O ≤
      ENNReal.ofReal η) (hη : 0 ≤ η) (j : Fin 3) :
    ‖(∫ x in frontier U, (χ x * f x) * ν x j ∂(Measure.euclideanHausdorffMeasure 2)) -
      ∫ x in frontier U, f x * ν x j ∂(Measure.euclideanHausdorffMeasure 2)‖ ≤ M * η := by
  let σ := (Measure.euclideanHausdorffMeasure 2).restrict (frontier U)
  letI : IsFiniteMeasure σ := isFiniteMeasure_restrict.2 hU.area_lt_top.ne
  let g (x : Point) := χ x * f x
  have hg : ContDiffOn ℝ 1 g (closure U) := ((hχ.of_le (by simp)).contDiffOn.mul hf)
  have hI := (hU.integrable_coordinate_flux hg j).2.sub (hU.integrable_coordinate_flux hf j).2
  have hPt : ∀ᵐ x ∂σ, ‖g x * ν x j - f x * ν x j‖ ≤ O.indicator (fun _ => M) x := by
    filter_upwards [hU.normal_ae] with x hx
    by_cases h : x ∈ O
    · rw [indicator_of_mem h]
      have hNu : ‖ν x j‖ ≤ 1 := (PiLp.norm_apply_le _ j).trans_eq hx.2.1
      have hC : ‖χ x - 1‖ ≤ 1 := by
        rw [norm_sub_rev,Real.norm_of_nonneg (sub_nonneg.mpr (hχRange x).2)]
        exact sub_le_self _ (hχRange x).1
      rw [show g x * ν x j - f x * ν x j = ((χ x - 1) * f x) * ν x j by unfold g; ring,
        norm_mul,norm_mul]
      calc
        _ ≤ (1 * M) * 1 := mul_le_mul
          (mul_le_mul hC (hF x (frontier_subset_closure hx.1)) (norm_nonneg _) zero_le_one)
          hNu (norm_nonneg _) (mul_nonneg zero_le_one hM)
        _ = _ := by ring
    · rw [indicator_of_notMem h]
      simp [g,hχO x h]
  change ‖(∫ x, g x * ν x j ∂σ) - ∫ x, f x * ν x j ∂σ‖ ≤ _
  rw [← integral_sub (hU.integrable_coordinate_flux hg j).2 (hU.integrable_coordinate_flux hf j).2]
  have hOI : Integrable (O.indicator (fun _ : Point => M)) σ :=
    (integrable_const _).indicator hO
  calc
    _ ≤ ∫ x, ‖g x * ν x j - f x * ν x j‖ ∂σ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, O.indicator (fun _ : Point => M) x ∂σ := integral_mono_ae hI.norm hOI hPt
    _ = M * σ.real O := by rw [integral_indicator hO,setIntegral_const,smul_eq_mul,mul_comm]
    _ ≤ M * η := mul_le_mul_of_nonneg_left
      (by simpa only [measureReal_def,ENNReal.toReal_ofReal hη] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hVol) hM

/-- The coordinate Gauss–Green theorem for the original Lipschitz domain,
with Lebesgue volume and normalized Euclidean surface measure. -/
theorem lipschitzGaussGreen : External.LipschitzGaussGreen := by
  intro U ν hU f hf j
  obtain ⟨hIU,hIS⟩ := hU.integrable_coordinate_flux hf j
  refine ⟨hIU,hIS,?_⟩
  let K := exceptionalWall U
  let σ := (Measure.euclideanHausdorffMeasure 2).restrict (frontier U)
  letI : IsFiniteMeasure σ := isFiniteMeasure_restrict.2 hU.area_lt_top.ne
  have hK : IsCompact K := isCompact_exceptionalWall hU
  have hK0 : Measure.euclideanHausdorffMeasure 2 K = 0 := exceptionalWall_surface_null hU
  have hKσ : σ K = 0 := by
    rw [Measure.restrict_apply hK.isClosed.measurableSet,
      inter_eq_left.mpr (exceptionalWall_subset_frontier hU.isOpen)]
    exact hK0
  obtain ⟨M,hM,hF,hD⟩ := hU.exists_uniform_value_coordDeriv_bound hf
  let A := ∫ x in U, coordDeriv j f x
  let B := ∫ x in frontier U, f x * ν x j ∂(Measure.euclideanHausdorffMeasure 2)
  have hNear (η : ℝ) (hη : 0 < η) : ‖A - B‖ ≤ 3 * M * η := by
    have hE : σ K < ENNReal.ofReal η := by rw [hKσ]; exact ENNReal.ofReal_pos.mpr hη
    obtain ⟨O,hKO,hO,hVol⟩ := hK.exists_isOpen_lt_of_lt (μ := σ) _ hE
    obtain ⟨χ,hχ,hRange,hZero,hχO,hχI,hχL,hGrad⟩ :=
      exists_cutoff_excluding_hausdorffTwo_null hK hK0 hO hKO hη
    let g (x : Point) := χ x * f x
    have hg : ContDiffOn ℝ 1 g (closure U) := ((hχ.of_le (by simp)).contDiffOn.mul hf)
    have hG : Disjoint (tsupport g) K := by
      apply Set.disjoint_left.mpr
      intro x hx hxK
      have he : g =ᶠ[𝓝 x] (0 : Point → ℝ) := (hZero x hxK).mono fun y hy => by
        change χ y * f y = 0
        rw [show χ y = 0 from hy,zero_mul]
      exact (notMem_tsupport_iff_eventuallyEq.mpr he) hx
    let A' := ∫ x in U, coordDeriv j g x
    let B' := ∫ x in frontier U, g x * ν x j ∂(Measure.euclideanHausdorffMeasure 2)
    have hEqual : A' = B' := flux_eq_of_support_disjoint_exceptionalWall hU hg hG j
    have hVA : ‖A' - A‖ ≤ 2 * M * η :=
      cutoff_error_volume hU hf hχ M η hM hF j (fun x hx => hD x hx j)
        hχI hχL (hGrad j).1 (hGrad j).2
    have hVB : ‖B' - B‖ ≤ M * η :=
      cutoff_error_frontier hU hf hχ M η hM hF hRange hO.measurableSet hχO hVol.le hη.le j
    calc
      _ ≤ ‖A - A'‖ + ‖A' - B‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * M * η + M * η := by
        apply add_le_add
        · rw [norm_sub_rev A A']
          exact hVA
        · rw [hEqual]
          exact hVB
      _ = _ := by ring
  have hZ : ‖A - B‖ ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let η := ε / (1 + 3 * M)
    have hD : 0 < 1 + 3 * M := by positivity
    have hη : 0 < η := div_pos hε hD
    have hBound := hNear η hη
    rw [zero_add]
    refine hBound.trans ?_
    have hEq : (1 + 3 * M) * η = ε := by
      dsimp only [η]
      field_simp [hD.ne']
    linarith only [hEq,hη.le]
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hZ (norm_nonneg _)))

end Thesis

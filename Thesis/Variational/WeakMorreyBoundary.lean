module

public import Thesis.Variational.WeakMorreyInterior
public import Thesis.Variational.SmoothDomainTraceChart
import Thesis.Variational.MorreyDomainCharts
import StratificationTheory.Foundation.CoordinateRectangleTrace
import StratificationTheory.Foundation.ReflectedRectangleTraceGluing
import HarmonicMaps.Analysis.SobolevAECongruence

/-! The local even reflection of a weak graph preserves integrability of
each first column on both sides of the flattened wall. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory Topology
open scoped ContDiff ENNReal

namespace Thesis

private theorem normalCoordinate_reflection (x : Point) :
    normalCoordinateEquiv (normalReflection x) =
      ((normalCoordinateEquiv x).1, -(normalCoordinateEquiv x).2) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> rfl
  · ext i
    fin_cases i
    rfl

private theorem memLp_flatRectangle_piecewise {q : ℕ} {A B : Point → Ambient q}
    (P : OpenDomain 2) {d : ℝ} (hd : 0 < d) {p : ℝ≥0∞}
    (hA : MemLp A p (volume.restrict
      {x | (normalCoordinateEquiv x).1 ∈ P.val ∧ (normalCoordinateEquiv x).2 0 ∈ Ioo (-d) 0}))
    (hB : MemLp B p (volume.restrict
      {x | (normalCoordinateEquiv x).1 ∈ P.val ∧ (normalCoordinateEquiv x).2 0 ∈ Ioo 0 d})) :
    MemLp (fun x => if (normalCoordinateEquiv x).2 0 < 0 then A x else B x) p
      (volume.restrict {x | (normalCoordinateEquiv x).1 ∈ P.val ∧ (normalCoordinateEquiv x).2 0 ∈ Ioo (-d) d}) := by
  have hMeas (a b : ℝ) : MeasurableSet
      {x : Point | (normalCoordinateEquiv x).1 ∈ P.val ∧ (normalCoordinateEquiv x).2 0 ∈ Ioo a b} :=
    (P.property.measurableSet.preimage (continuous_fst.comp normalCoordinateEquiv.continuous).measurable).inter
      (measurableSet_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp normalCoordinateEquiv.continuous)).measurable)
  have hL := (memLp_indicator_iff_restrict (hMeas (-d) 0)).2 hA
  have hR := (memLp_indicator_iff_restrict (hMeas 0 d)).2 hB
  have hAE := coordinate_rectangle_piecewise_indicator_ae P.val (neg_lt_zero.mpr hd) hd A B
  exact (memLp_indicator_iff_restrict (hMeas (-d) d)).1 ((hL.add hR).ae_eq hAE.symm)

private theorem memLp_columns_of_even_reflection
    {Ω : Set Point} (B : SmoothDomainEpigraphBox Ω) {d : ℝ} (hd : 0 < d) (hdB : d ≤ B.radius) {p : ℝ≥0∞} {q : ℕ}
    {u : Point → Ambient q} {D G : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 (B.flatSlab d) u D)
    (hD : ∀ j, MemLp (fun x => D x j) p (volume.restrict (B.flatSlab d).val))
    (hG : MemW12 (B.flatRectangle (-d) d)
      (fun x => if (normalCoordinateEquiv x).2 0 < 0 then u (normalReflection x) else u x) G) :
    ∀ j, MemLp (fun x => G x j) p (volume.restrict (B.flatRectangle (-d) d).val) := by
  let P := B.flatSlab d
  let N := B.flatRectangle (-d) 0
  let W := B.flatRectangle (-d) d
  let R := normalReflection
  let J := ambientGradientPullback R D
  let w := fun x : Point => if (normalCoordinateEquiv x).2 0 < 0 then u (R x) else u x
  have hPre : R ⁻¹' P.val = N.val := by
    ext x
    change ((normalCoordinateEquiv (R x)).1 ∈ B.planeDomain.val ∧
      (normalCoordinateEquiv (R x)).2 0 ∈ Ioo 0 d) ↔
      ((normalCoordinateEquiv x).1 ∈ B.planeDomain.val ∧ (normalCoordinateEquiv x).2 0 ∈ Ioo (-d) 0)
    rw [normalCoordinate_reflection]
    simp only [PiLp.neg_apply,mem_Ioo]
    constructor
    · rintro ⟨h,hl,hr⟩
      exact ⟨h,by linarith only [hr],by linarith only [hl]⟩
    · rintro ⟨h,hl,hr⟩
      exact ⟨h,by linarith only [hr],by linarith only [hl]⟩
  have hMap : MeasurePreserving R (volume.restrict N.val) (volume.restrict P.val) := by
    rw [← hPre]
    exact R.measurePreserving.restrict_preimage P.property.measurableSet
  have hInto : MapsTo R N.val P.val := by
    intro x hx
    change x ∈ R ⁻¹' P.val
    rwa [hPre]
  have hGraphL : MemW12 N (u ∘ R) J := by
    apply memW12_smooth_open_domain_pullback hu N R R.contDiff.contDiffOn hInto 1
    · intro x _
      simpa only [NNReal.coe_one] using norm_fderiv_le_of_lipschitz ℝ R.isometry.lipschitz (x₀ := x)
    · exact ENNReal.one_ne_top
    · rw [one_smul,hMap.map_eq]
  have hDL : ∀ j, MemLp (fun x => J x j) p (volume.restrict N.val) := by
    apply memLp_ambientGradientPullback_of_map_le R R.contDiff N P
      (B.isBounded_flatRectangle (neg_le_neg hdB) B.radius_pos.le) ENNReal.one_ne_top _ D hD
    rw [one_smul,hMap.map_eq]
  have hLeftSub : N.val ⊆ W.val := fun _ hx => ⟨hx.1,hx.2.1,hx.2.2.trans hd⟩
  have hRightSub : P.val ⊆ W.val := fun _ hx => ⟨hx.1,(neg_lt_zero.mpr hd).trans hx.2.1,hx.2.2⟩
  have hLeftAE : w =ᵐ[volume.restrict N.val] u ∘ R := by
    filter_upwards [ae_restrict_mem N.property.measurableSet] with x hx
    exact if_pos hx.2.2
  have hRightAE : w =ᵐ[volume.restrict P.val] u := by
    filter_upwards [ae_restrict_mem P.property.measurableSet] with x hx
    exact if_neg (not_lt_of_gt hx.2.1)
  have hGLE : G =ᵐ[volume.restrict N.val] J :=
    (hG.1.mono hLeftSub).ae_eq_of_ae_eq_map hGraphL.1 hLeftAE
  have hGRE : G =ᵐ[volume.restrict P.val] D :=
    (hG.1.mono hRightSub).ae_eq_of_ae_eq_map hu.1 hRightAE
  have hSplit : G =ᵐ[volume.restrict W.val]
      (fun x j => if (normalCoordinateEquiv x).2 0 < 0 then J x j else D x j) := by
    have hNoWall : ∀ᵐ x ∂volume.restrict W.val, (normalCoordinateEquiv x).2 0 ≠ 0 :=
      ae_restrict_of_ae (ae_native_time_ne 2 0)
    have hL : ∀ᵐ x ∂(volume : Measure Point), x ∈ N.val → G x = J x :=
      (ae_restrict_iff' N.property.measurableSet).mp hGLE
    have hR : ∀ᵐ x ∂(volume : Measure Point), x ∈ P.val → G x = D x :=
      (ae_restrict_iff' P.property.measurableSet).mp hGRE
    filter_upwards [ae_restrict_of_ae hL,ae_restrict_of_ae hR,hNoWall,
      ae_restrict_mem W.property.measurableSet] with x hqL hqR h0 hx
    funext j
    by_cases hNeg : (normalCoordinateEquiv x).2 0 < 0
    · exact (congrFun (hqL ⟨hx.1,hx.2.1,hNeg⟩) j).trans (if_pos hNeg).symm
    · have hPos : 0 < (normalCoordinateEquiv x).2 0 := lt_of_le_of_ne (le_of_not_gt hNeg) h0.symm
      exact (congrFun (hqR ⟨hx.1,hPos,hx.2.2⟩) j).trans (if_neg hNeg).symm
  intro j
  apply (memLp_flatRectangle_piecewise B.planeDomain hd (hDL j) (hD j)).ae_eq
  exact hSplit.symm.mono fun _ hx => congrFun hx j

/-- Reflection through the actual smooth wall preserves each displayed
(L^p) first column of a weak graph. -/
theorem SmoothDomainEpigraphBox.exists_local_reflected_memW12_with_lp_columns
    {Ω : Set Point} (B : SmoothDomainEpigraphBox Ω) (hΩ : IsOpen Ω)
    {q : ℕ} {p : ℝ≥0∞} {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 ⟨Ω,hΩ⟩ u D) (hD : ∀ j, MemLp (fun x => D x j) p (volume.restrict Ω)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ B.radius ∧
      ∃ (w : Point → Ambient q) (G : Point → HarmonicMaps.Gradient 3 q),
        MemW12 (B.physicalRectangle (-δ) δ) w G ∧
        EqOn w u (Ω ∩ (B.physicalRectangle (-δ) δ).val) ∧
        ∀ j, MemLp (fun x => G x j) p (volume.restrict (B.physicalRectangle (-δ) δ).val) := by
  letI := B.isFiniteMeasure_planeDomain
  let F := B.normalEuclideanChart
  let v : Point → Ambient q := u ∘ F
  let J := ambientGradientPullback F D
  have hv : MemW12 (B.flatSlab B.radius) v J := B.memW12_normalChart hΩ le_rfl hu
  have hMap : Measure.map F (volume.restrict (B.flatSlab B.radius).val) ≤
      (1 : ℝ≥0∞) • volume.restrict Ω := by
    rw [one_smul,(B.flatSlab_measurePreserving B.radius).map_eq]
    apply Measure.restrict_mono_set
    rintro _ ⟨x,hx,rfl⟩
    exact B.flatSlab_mapsTo_domain le_rfl hx
  have hLpJ : ∀ j, MemLp (fun x => J x j) p (volume.restrict (B.flatSlab B.radius).val) :=
    memLp_ambientGradientPullback_of_map_le F B.normalEuclideanChart_smooth (B.flatSlab B.radius)
      (⟨Ω,hΩ⟩ : OpenDomain 3) (B.isBounded_flatSlab le_rfl) ENNReal.one_ne_top hMap D hD
  obtain ⟨H,hH,_⟩ := exists_unique_L2_trace_of_memW12_rectangle B.planeDomain B.radius_pos hv
  obtain ⟨δ,hδ,G,hG⟩ := exists_reflected_rectangle_weak_gluing B.planeDomain
    B.radius_pos B.radius_pos v v J J hv hv H H hH hH rfl
  let d := min δ B.radius
  have hd : 0 < d := lt_min hδ B.radius_pos
  have hdB : d ≤ B.radius := min_le_right _ _
  let W := B.flatRectangle (-d) d
  let w := fun x : Point => if (normalCoordinateEquiv x).2 0 < 0 then v (normalReflection x) else v x
  have hWbig : W.val ⊆ (B.flatRectangle (-δ) δ).val := fun _ hx =>
    ⟨hx.1,(neg_le_neg (min_le_left _ _)).trans_lt hx.2.1,hx.2.2.trans_le (min_le_left _ _)⟩
  have hG' : MemW12 W w G := by
    have hEq (x : Point) : normalCoordinateEquiv.symm ((normalCoordinateEquiv x).1,-(normalCoordinateEquiv x).2) =
        normalReflection x := by
      apply normalCoordinateEquiv.injective
      rw [normalCoordinateEquiv.apply_symm_apply,normalCoordinate_reflection]
    have hSub : MemW12 W
        (fun x => if (normalCoordinateEquiv x).2 0 < 0 then
          v (normalCoordinateEquiv.symm ((normalCoordinateEquiv x).1,-(normalCoordinateEquiv x).2)) else v x) G :=
      ⟨hG.1.mono hWbig,hG.2.1.mono_measure (Measure.restrict_mono_set _ hWbig),
        fun j => (hG.2.2 j).mono_measure (Measure.restrict_mono_set _ hWbig)⟩
    simpa only [hEq] using hSub
  have hPosSub : (B.flatSlab d).val ⊆ (B.flatSlab B.radius).val :=
    fun _ hx => ⟨hx.1,hx.2.1,hx.2.2.trans_le hdB⟩
  have hVsmall : MemW12 (B.flatSlab d) v J :=
    ⟨hv.1.mono hPosSub,hv.2.1.mono_measure (Measure.restrict_mono_set _ hPosSub),
      fun j => (hv.2.2 j).mono_measure (Measure.restrict_mono_set _ hPosSub)⟩
  have hGLp := memLp_columns_of_even_reflection B hd hdB hVsmall
    (fun j => (hLpJ j).mono_measure (Measure.restrict_mono_set _ hPosSub)) hG'
  let V := B.physicalRectangle (-d) d
  have hPhys : MemW12 V (w ∘ F.symm) (ambientGradientPullback F.symm G) :=
    B.memW12_physicalRectangle (neg_le_neg hdB) hdB hG'
  have hMP := (B.flatRectangle_measurePreserving (-d) d).symm F.toMeasurableEquiv
  have hMap' : Measure.map F.symm (volume.restrict V.val) ≤ (1 : ℝ≥0∞) • volume.restrict W.val := by
    rw [one_smul]
    exact hMP.map_eq.le
  have hPhysLp := memLp_ambientGradientPullback_of_map_le F.symm B.normalEuclideanChart_inverse_smooth
    V W (B.isBounded_physicalRectangle (neg_le_neg hdB) hdB) ENNReal.one_ne_top hMap' G hGLp
  refine ⟨d,hd,hdB,w ∘ F.symm,ambientGradientPullback F.symm G,hPhys,?_,hPhysLp⟩
  rintro x ⟨hxΩ,y,hy,rfl⟩
  have hY := (B.normalEuclideanChart_mem_domain_iff (neg_le_neg hdB) hdB hy).1 hxΩ
  change w (F.symm (F y)) = u (F y)
  rw [F.symm_apply_apply]
  exact if_neg (not_lt_of_gt hY)

end Thesis

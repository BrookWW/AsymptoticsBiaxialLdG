module

public import Thesis.Interpolation.SphericalChartMeasure
public import StratificationTheory.Foundation.SmoothDomainPullbackEnergy

/-! Sobolev and energy transport from the physical parameter box to the actual shell cell. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal Topology Matrix.Norms.Frobenius

namespace Thesis

private theorem sphericalCellNativeParameter_symm_contDiff :
    ContDiff ℝ ∞ (sphericalCellNativeParameter.symm : SphericalCellParameter → Point) := by
  have hEq (p : SphericalCellParameter) : sphericalCellNativeParameter.symm p =
      p.1.1 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
        p.1.2 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) +
          p.2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [sphericalCellNativeParameter, PiLp.add_apply, PiLp.smul_apply]
  rw [funext hEq]
  fun_prop

/-- The open native domain of one chart has all three physical lengths equal to `h`. -/
@[expose] def sphericalCellNativeOpenDomain (h : ℝ) : OpenDomain 3 :=
  ⟨interior (sphericalCellNativeBox h), isOpen_interior⟩

/-- Open domain of the actual projected shell cell. -/
@[expose] noncomputable def sphericalCellOpenDomain (c : Point) (h : ℝ) (f : TensorGridSquare) : OpenDomain 3 :=
  ⟨interior (sphericalClosedCell c h f), isOpen_interior⟩

/-- The native inverse extends smoothly around each point of the actual cell.
It has uniform differential and volume distortion bounds on its interior. -/
theorem exists_sphericalCellNativeInverse {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) :
    let U := (sphericalCellNativeOpenDomain h).val
    let V := (sphericalCellOpenDomain c h f).val
    let F := sphericalCellNativePoint c h f
    ∃ G : Point → Point, MapsTo F U V ∧ MapsTo G V U ∧
      LeftInvOn G F (sphericalCellNativeBox h) ∧ RightInvOn G F (sphericalClosedCell c h f) ∧
      ContDiffOn ℝ ∞ G (sphericalClosedCell c h f) ∧
      (∀ z ∈ V, ‖fderiv ℝ G z‖ ≤ 204) ∧
      Measure.map G (volume.restrict V) ≤ (65 ^ 3 : ℝ≥0∞) • volume.restrict U := by
  intro U V F
  obtain ⟨e, he, hBox, hCell, hImg, _, hSm⟩ := exists_sphericalCellOpenChart hh' hc hm hf
  let p := sphericalCellNativeParameter
  let G : Point → Point := p.symm ∘ e.symm
  have hF (x : Point) : F x = e (p x) := by rw [he]; rfl
  have hPU : U = p ⁻¹' interior (sphericalCellParameterBox h) :=
    (p.preimage_interior (sphericalCellParameterBox h)).symm
  have hBoxU : U ⊆ sphericalCellNativeBox h := interior_subset
  have hCellV : V ⊆ sphericalClosedCell c h f := interior_subset
  have hFU : MapsTo F U V := by
    intro x hx
    rw [hF]
    have hInt : p x ∈ interior (sphericalCellParameterBox h) := by
      change x ∈ p ⁻¹' interior (sphericalCellParameterBox h)
      rwa [← hPU]
    exact hImg.interior.apply_mem_iff (hBox (hBoxU hx)) |>.mpr hInt
  have hGV : MapsTo G V U := by
    intro z hz
    rw [hPU]
    change p (p.symm (e.symm z)) ∈ interior (sphericalCellParameterBox h)
    rw [p.apply_symm_apply]
    exact hImg.interior.symm_apply_mem_iff (hCell (hCellV hz)) |>.mpr hz
  have hLeft : LeftInvOn G F (sphericalCellNativeBox h) := by
    intro x hx
    change p.symm (e.symm (F x)) = x
    rw [hF, e.left_inv (hBox hx), p.symm_apply_apply]
  have hRight : RightInvOn G F (sphericalClosedCell c h f) := by
    intro z hz
    rw [hF]
    change e (p (p.symm (e.symm z))) = z
    rw [p.apply_symm_apply, e.right_inv (hCell hz)]
  have hGSmooth : ContDiffOn ℝ ∞ G (sphericalClosedCell c h f) :=
    sphericalCellNativeParameter_symm_contDiff.comp_contDiffOn (hSm.mono hCell)
  have hLipF : LipschitzOnWith 65 F U := LipschitzOnWith.of_dist_le_mul fun _ hx _ hy =>
    (sphericalCellNativePoint_dist_bounds hh hh' hc hm hf (hBoxU hx) (hBoxU hy)).1
  have hLipG : LipschitzOnWith 204 G V := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hb := (sphericalCellNativePoint_dist_bounds hh hh' hc hm hf (hBoxU (hGV hx)) (hBoxU (hGV hy))).2
    change dist (G x) (G y) ≤ 204 * dist (F (G x)) (F (G y)) at hb
    rwa [hRight (hCellV hx), hRight (hCellV hy)] at hb
  refine ⟨G, hFU, hGV, hLeft, hRight, hGSmooth, ?_, ?_⟩
  · exact fun z hz => norm_fderiv_le_of_lipschitzOn ℝ (isOpen_interior.mem_nhds hz) hLipG
  · have hUOpen : IsOpen U := isOpen_interior
    have hVOpen : IsOpen V := isOpen_interior
    have hGMeas : AEMeasurable G (volume.restrict V) := hLipG.continuousOn.aemeasurable hVOpen.measurableSet
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.map_apply_of_aemeasurable hGMeas hA, Measure.restrict_apply' hVOpen.measurableSet,
      Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]
    have hImgSet : G ⁻¹' A ∩ V = F '' (A ∩ U) := by
      ext z
      constructor
      · intro hz
        exact ⟨G z, ⟨hz.1, hGV hz.2⟩, hRight (hCellV hz.2)⟩
      · rintro ⟨x, hx, rfl⟩
        refine ⟨?_, hFU hx.2⟩
        change G (F x) ∈ A
        rw [hLeft (hBoxU hx.2)]
        exact hx.1
    rw [hImgSet]
    have hVol := euclideanHausdorff_lipschitzOn_image_le_volume hLipF (S := A ∩ U) inter_subset_right
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume, finrank_euclideanSpace_fin] at hVol
    exact hVol

/-- The actual inverse chart transports a native Sobolev graph with the chain
rule, arbitrary a.e. value constraints, and uniform Dirichlet and bulk bounds. -/
theorem exists_sphericalCellNative_sobolev_transport {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) :
    let U := sphericalCellNativeOpenDomain h
    let V := sphericalCellOpenDomain c h f
    let F := sphericalCellNativePoint c h f
    ∃ G : Point → Point, LeftInvOn G F (sphericalCellNativeBox h) ∧
      RightInvOn G F (sphericalClosedCell c h f) ∧
      ∀ {q : ℕ} {u : Point → Ambient q} {Du : Point → HarmonicMaps.Gradient 3 q}, MemW12 U u Du →
        let W := u ∘ G
        let D : Point → HarmonicMaps.Gradient 3 q := fun z i =>
          ∑ j : Fin 3, (fderiv ℝ G z (EuclideanSpace.single i 1)) j • Du (G z) j
        MemW12 V W D ∧
          HarmonicMaps.dirichletEnergy D V.val ≤
            (9 * 204 ^ 2 * 65 ^ 3 : ℝ≥0∞) * HarmonicMaps.dirichletEnergy Du U.val ∧
          (∀ P : Ambient q → Prop, (∀ᵐ p ∂volume.restrict U.val, P (u p)) →
            ∀ᵐ z ∂volume.restrict V.val, P (W z)) ∧
          ∀ b : Ambient q → ℝ≥0∞, AEMeasurable (b ∘ u) (volume.restrict U.val) →
            (∫⁻ z in V.val, b (W z)) ≤ (65 ^ 3 : ℝ≥0∞) * ∫⁻ p in U.val, b (u p) := by
  intro U V F
  obtain ⟨G, _, hMaps, hLInv, hRInv, hSmooth, hDF, hMap⟩ := exists_sphericalCellNativeInverse hh hh' hc hm hf
  refine ⟨G, hLInv, hRInv, fun {q u Du} hu => ?_⟩
  intro W D
  have hSmoothV : ContDiffOn ℝ ∞ G V.val := hSmooth.mono interior_subset
  obtain ⟨hWeak, _, hDir, hVal⟩ := StratificationTheory.memW12_smooth_open_domain_pullback_energy
    hu V G hSmoothV hMaps 204 hDF (65 ^ 3) (by norm_num) hMap
  refine ⟨hWeak, ?_, hVal, ?_⟩
  · have hC : ENNReal.ofReal ((↑(3 : ℕ) : ℝ) * ↑(3 : ℕ) * 204 ^ 2) = (9 * 204 ^ 2 : ℝ≥0∞) := by norm_num
    simpa only [hC] using hDir
  · intro b hb
    have hMeas : AEMeasurable G (volume.restrict V.val) := hSmoothV.continuousOn.aemeasurable V.property.measurableSet
    have hbMap := hb.mono_ac (Measure.absolutelyContinuous_of_le_smul hMap)
    calc
      _ = ∫⁻ y, b (u y) ∂Measure.map G (volume.restrict V.val) := (lintegral_map' hbMap hMeas).symm
      _ ≤ ∫⁻ y, b (u y) ∂((65 ^ 3 : ℝ≥0∞) • volume.restrict U.val) := lintegral_mono' hMap le_rfl
      _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]

end Thesis

module

public import Thesis.MeasureGeometry.PlanarPerimeterCircle
public import Thesis.MeasureGeometry.PeripheralWordReduction
public import Mathlib.Topology.Compactification.OnePoint.Sphere

/-! A smooth finite chart of a physical sphere, with a separate point at infinity. -/

public section

noncomputable section

open Function Metric OnePoint Set
open scoped ContDiff RealInnerProductSpace Topology

namespace Thesis.MeasureGeometry

/-- Euclidean stereographic coordinates on a sphere, with the finite chart
considered as an ambient smooth embedding. -/
structure CompactifiedSphericalChart (c : Point) (R : ℝ) where
  homeo : OnePoint (ℝ × ℝ) ≃ₜ sphere c R
  smooth : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × ℝ => (homeo z).val)
  derivative_injective : ∀ z : ℝ × ℝ,
    Function.Injective (fderiv ℝ (fun y : ℝ × ℝ => (homeo y).val) z)

private theorem onePointHyperplaneHomeoUnitSphere_coe {v : Point} (hv : ‖v‖ = 1)
    (x : (ℝ ∙ v)ᗮ) : onePointHyperplaneHomeoUnitSphere hv x = stereoInvFun hv x := by
  rw [onePointHyperplaneHomeoUnitSphere,OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe]
  rfl

private theorem onePointHyperplaneHomeoUnitSphere_infty {v : Point} (hv : ‖v‖ = 1)
    (v₀ : sphere (0 : Point) 1) (hv₀ : v₀.val = v) :
    onePointHyperplaneHomeoUnitSphere hv ∞ = v₀ := by
  subst v
  rw [onePointHyperplaneHomeoUnitSphere,OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty]

private theorem contDiff_inverseStereo {v : Point} (hv : ‖v‖ = 1)
    (L : (ℝ × ℝ) ≃L[ℝ] (ℝ ∙ v)ᗮ) {c : Point} {R : ℝ} (hR : 0 < R) :
    let J := (L.toHomeomorph.onePointCongr.trans (onePointHyperplaneHomeoUnitSphere hv)).trans
      (positiveSphereNormalize c R hR).symm
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × ℝ => (J z).val) ∧
      ∀ z : ℝ × ℝ, Function.Injective (fderiv ℝ (fun y : ℝ × ℝ => (J y).val) z) := by
  intro J
  let f (z : ℝ × ℝ) : Point := (J z).val
  have hF (z : ℝ × ℝ) : f z = c + R • ((stereoInvFun hv (L z) : sphere (0 : Point) 1) : Point) := by
    change ((positiveSphereNormalize c R hR).symm
      ((onePointHyperplaneHomeoUnitSphere hv) (L z))).val = _
    rw [onePointHyperplaneHomeoUnitSphere_coe]
    rfl
  have hSmooth : ContDiff ℝ (⊤ : ℕ∞) f := by
    have h : ContDiff ℝ (⊤ : ℕ∞) (stereoInvFunAux v ∘
        (Submodule.subtypeL ((ℝ ∙ v)ᗮ)).comp L.toContinuousLinearMap) :=
      contDiff_stereoInvFunAux.comp (((ℝ ∙ v)ᗮ.subtypeL).comp L.toContinuousLinearMap).contDiff
    have he : f = fun z => c + R • (stereoInvFunAux v
        (((ℝ ∙ v)ᗮ.subtypeL).comp L.toContinuousLinearMap z)) := funext hF
    rw [he]
    exact contDiff_const.add (h.const_smul R)
  refine ⟨hSmooth,fun z => ?_⟩
  let N (y : Point) := R⁻¹ • (y-c)
  let g (y : Point) := L.symm (stereoToFun v (N y))
  have hNF (y : ℝ × ℝ) : N (f y) = (stereoInvFun hv (L y) : Point) := by
    rw [hF]
    change R⁻¹ • ((c+R • (stereoInvFun hv (L y) : Point))-c) = _
    rw [add_sub_cancel_left,smul_smul,inv_mul_cancel₀ hR.ne',one_smul]
  have hg (x : ℝ × ℝ) : g (f x) = x := by
    change L.symm (stereoToFun v (N (f x))) = x
    rw [hNF,stereo_right_inv hv,L.symm_apply_apply]
  have hN : ContDiff ℝ 1 N := (contDiff_id.sub contDiff_const).const_smul _
  have hNNorm : ‖N (f z)‖ = 1 := by
    rw [hNF]
    exact mem_sphere_zero_iff_norm.mp (stereoInvFun hv (L z)).property
  have hNNe : N (f z) ≠ v := by
    intro he
    apply stereoInvFun_ne_north_pole hv (L z)
    apply Subtype.ext
    exact (hNF z).symm.trans he
  have hNe : innerSL ℝ v (N (f z)) ≠ (1 : ℝ) :=
    ((inner_lt_one_iff_real_of_norm_eq_one hv hNNorm).mpr hNNe.symm).ne
  let U := {x : Point | innerSL ℝ v x ≠ (1 : ℝ)}
  have hU : IsOpen U := isOpen_ne_fun (innerSL ℝ v).continuous continuous_const
  have hStereo : DifferentiableAt ℝ (stereoToFun v) (N (f z)) :=
    (((contDiffOn_stereoToFun (n := 1) (v := v)) _ hNe).contDiffAt
      (hU.mem_nhds hNe)).differentiableAt one_ne_zero
  have hgD : DifferentiableAt ℝ g (f z) :=
    (L.symm.differentiable _).comp _ (hStereo.comp _ (hN.differentiable one_ne_zero _))
  have hfD : DifferentiableAt ℝ f z := (hSmooth.differentiable (by simp)) z
  have hLeft := (hgD.hasFDerivAt.comp z hfD.hasFDerivAt).fderiv
  have hEq : g ∘ f = id := funext hg
  rw [hEq,fderiv_id] at hLeft
  intro y w hYW
  have he (u : ℝ × ℝ) : fderiv ℝ g (f z) (fderiv ℝ f z u) = u :=
    (congrArg (fun A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => A u) hLeft).symm
  exact (he y).symm.trans ((congrArg (fderiv ℝ g (f z)) hYW).trans (he w))

/-- Any point of a positive-radius sphere may serve as its point at infinity. -/
theorem exists_compactifiedSphericalChart {c : Point} {R : ℝ} (hR : 0 < R)
    (p : sphere c R) : ∃ J : CompactifiedSphericalChart c R, J.homeo ∞ = p := by
  let e := positiveSphereNormalize c R hR
  let v := e p
  have hv : ‖v.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  have hV : v.val ≠ 0 := by
    intro he
    rw [he,norm_zero] at hv
    exact zero_ne_one hv
  letI : Fact (Module.finrank ℝ Point = 2+1) := ⟨finrank_euclideanSpace_fin⟩
  let f : (ℝ ∙ v.val)ᗮ ≃ₗᵢ[ℝ] Plane := (OrthonormalBasis.fromOrthogonalSpanSingleton 2 hV).repr
  let L := planePairCoordinates.symm.trans f.symm.toContinuousLinearEquiv
  let J := (L.toHomeomorph.onePointCongr.trans (onePointHyperplaneHomeoUnitSphere hv)).trans e.symm
  obtain ⟨hS,hD⟩ := contDiff_inverseStereo hv L hR
  refine ⟨⟨J,hS,hD⟩,?_⟩
  change e.symm (onePointHyperplaneHomeoUnitSphere hv ∞) = p
  rw [onePointHyperplaneHomeoUnitSphere_infty hv v rfl]
  exact e.symm_apply_apply p

/-- Precompose the finite coordinates by a linear change and keep the same point at infinity. -/
def CompactifiedSphericalChart.precompose {c : Point} {R : ℝ}
    (J : CompactifiedSphericalChart c R) (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    CompactifiedSphericalChart c R := by
  let e := L.toHomeomorph.onePointCongr.trans J.homeo
  let f (z : ℝ × ℝ) := (J.homeo z).val
  have hF : (fun z : ℝ × ℝ => (e z).val) = f ∘ L := rfl
  refine ⟨e,?_,?_⟩
  · rw [hF]
    exact J.smooth.comp L.contDiff
  · intro z
    rw [hF]
    have hD := J.smooth.differentiable (by simp)
    rw [fderiv_comp z (hD (L z)) (L.differentiable z),ContinuousLinearEquiv.fderiv]
    exact (J.derivative_injective (L z)).comp L.injective

theorem CompactifiedSphericalChart.precompose_infty {c : Point} {R : ℝ}
    (J : CompactifiedSphericalChart c R) (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    (J.precompose L).homeo ∞ = J.homeo ∞ := by
  unfold CompactifiedSphericalChart.precompose
  rfl

theorem CompactifiedSphericalChart.precompose_coe {c : Point} {R : ℝ}
    (J : CompactifiedSphericalChart c R) (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (x : ℝ × ℝ) :
    (J.precompose L).homeo x = J.homeo (L x) := by
  unfold CompactifiedSphericalChart.precompose
  rfl

end Thesis.MeasureGeometry

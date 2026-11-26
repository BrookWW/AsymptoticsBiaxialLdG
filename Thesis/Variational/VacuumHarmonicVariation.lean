module

public import Thesis.Variational.HarmonicEquation
public import Thesis.Upstream.MinimizingSobolev
public import Thesis.Foundation.VacuumTube
public import Thesis.Foundation.LinearizedBulk
import Thesis.Variational.ProjectedLaplacian
import Thesis.Variational.BoundarySubsolution
import HolderToCK.Geometry.ProjectionCoefficients
import HolderToCK.Analysis.ClassicalEquation
import HarmonicMaps.Analysis.SobolevPostcompositionLocal
import HarmonicMaps.Analysis.SobolevAECongruence
import HarmonicMaps.Frozen.OuterVariation

/-! The weak harmonic equation for the biaxial vacuum target. -/

public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius RealInnerProductSpace

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance vacuumHarmonicVariationContinuousENormS0 : ContinuousENorm S0 :=
  SeminormedAddGroup.toContinuousENorm
local instance vacuumHarmonicVariationContinuousENormTensor : ContinuousENorm Tensor :=
  SeminormedAddGroup.toContinuousENorm

private theorem exists_vacuum_curve_with_velocity
    {a : BulkCoefficients} {A B : S0} (hA : A ∈ vacuum a) (hB : vacuumInvariantDerivative A B = 0) :
    ∃ γ : ℝ → S0, γ 0 = A ∧ HasDerivAt γ B 0 ∧ ∀ᶠ t in 𝓝 0, γ t ∈ vacuum a := by
  letI : FiniteDimensional ℝ S0 := Module.Finite.of_basis frobeniusBasis
  let e : ↥(vacuumInvariantDerivative A).ker ≃L[ℝ] Point :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := ↥(vacuumInvariantDerivative A).ker) (F := Point)
      ((vacuumInvariantKernel_finrank hA).trans finrank_euclideanSpace_fin.symm)
  let L := (vacuumInvariantSplit hA).trans ((ContinuousLinearEquiv.refl ℝ (ℝ × ℝ)).prodCongr e)
  let P : S0 →L[ℝ] Point := (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Point).comp L.toContinuousLinearMap
  let f (X : S0) := (vacuumInvariants X, P X)
  have hf : HasStrictFDerivAt f (L : S0 →L[ℝ] (ℝ × ℝ) × Point) A := by
    refine ((hasStrictFDerivAt_vacuumInvariants A).prodMk (P.hasStrictFDerivAt (x := A))).congr_fderiv ?_
    ext X <;> rfl
  let v := L B
  let y (t : ℝ) := f A + t • v
  have hy0 : y 0 = f A := by simp [y]
  have hy : HasDerivAt y v 0 := by
    simpa only [y, id_eq, one_smul] using! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (f A)
  let g := hf.localInverse f L A
  let γ := g ∘ y
  have hγ0 : γ 0 = A := by
    change g (y 0) = A
    rw [hy0]
    exact hf.localInverse_apply_image
  have hg := hf.to_localInverse.hasFDerivAt
  have hg' : HasFDerivAt g L.symm.toContinuousLinearMap (y 0) := hy0.symm ▸ hg
  have hγ : HasDerivAt γ B 0 := by
    have h := hg'.comp_hasDerivAt (0 : ℝ) hy
    change HasDerivAt γ (L.symm (L B)) 0 at h
    rwa [ContinuousLinearEquiv.symm_apply_apply] at h
  refine ⟨γ, hγ0, hγ, ?_⟩
  have hR : ∀ᶠ t in 𝓝 0, f (g (y t)) = y t :=
    (hy0 ▸ hy.continuousAt.tendsto).eventually hf.eventually_right_inverse
  have hLvl : vacuumInvariants A = (2 * vacuumRadius a^2, 0) := by
    simpa only [vacuum_eq_invariant_level, mem_preimage, mem_singleton_iff] using hA
  filter_upwards [hR] with t ht
  have hfst := congrArg Prod.fst ht
  change vacuumInvariants (γ t) = vacuumInvariants A + t • vacuumInvariantDerivative A B at hfst
  simpa only [hB, smul_zero, add_zero, hLvl, vacuum_eq_invariant_level, mem_preimage,
    mem_singleton_iff] using hfst

private theorem VacuumTubularProjection.extend_vacuum
    {a : BulkCoefficients} (p : VacuumTubularProjection a) {A : S0} (hA : A ∈ vacuum a) :
    p.extend A = A :=
  (p.extend_eq ⟨A, vacuum_subset_vacuumTube a p.radius_pos hA⟩).trans
    (congrArg Subtype.val (p.project_of_mem hA))

private theorem VacuumTubularProjection.fderiv_extend_eq_self_of_tangent
    {a : BulkCoefficients} (p : VacuumTubularProjection a) {A B : S0}
    (hA : A ∈ vacuum a) (hB : vacuumInvariantDerivative A B = 0) :
    fderiv ℝ p.extend A B = B := by
  obtain ⟨γ, hγ0, hγ, hγVac⟩ := exists_vacuum_curve_with_velocity hA hB
  have hEq : p.extend ∘ γ =ᶠ[𝓝 (0 : ℝ)] γ := hγVac.mono fun _ ht => p.extend_vacuum ht
  have hD := (p.contDiff_extend.differentiable (by simp) (γ 0)).hasFDerivAt.comp_hasDerivAt 0 hγ
  rw [hγ0] at hD
  exact hD.unique (hγ.congr_of_eventuallyEq hEq)

private theorem VacuumTubularProjection.fderiv_extend_spectral_eq_zero
    {a : BulkCoefficients} (p : VacuumTubularProjection a) {A : S0} (hA : A ∈ vacuum a) (u v : ℝ) :
    fderiv ℝ p.extend A (u • A + v • traceFreeSquare A) = 0 := by
  let B := u • A + v • traceFreeSquare A
  let γ (t : ℝ) := A + t • B
  have hγ0 : γ 0 = A := by simp [γ]
  have hγ : HasDerivAt γ B 0 := by
    simpa only [γ, id_eq, one_smul] using! ((hasDerivAt_id (0 : ℝ)).smul_const B).const_add A
  have hA' := vacuum_subset_vacuumTube a p.radius_pos hA
  have hSimple := vacuumTube_vacuumRadius_half_subset_simpleSpectrum a
    (vacuum_subset_vacuumTube a (half_pos (vacuumRadius_pos a)) hA)
  have hEq : p.extend ∘ γ =ᶠ[𝓝 (0 : ℝ)] (fun _ => p.extend A) :=
    eventually_vacuum_projection_constant_along_spectral_direction p hA' hSimple u v
  have hD := (p.contDiff_extend.differentiable (by simp) (γ 0)).hasFDerivAt.comp_hasDerivAt 0 hγ
  rw [hγ0] at hD
  exact hD.unique ((hasDerivAt_const 0 (p.extend A)).congr_of_eventuallyEq hEq)

/-- The derivative of the nearest vacuum projection is the tangent projector
at a vacuum point. -/
theorem VacuumTubularProjection.fderiv_extend_eq_tangentProjector
    {a : BulkCoefficients} (p : VacuumTubularProjection a) {A : S0} (hA : A ∈ vacuum a) :
    fderiv ℝ p.extend A = vacuumTangentProjector a A := by
  apply ContinuousLinearMap.ext
  intro X
  let v := vacuumInvariantDerivative A X
  let N := vacuumInvariantRightInverse a A v
  have hNv : vacuumInvariantDerivative A N = v := vacuumInvariantRightInverse_isRightInverse hA v
  have hTN : vacuumInvariantDerivative A (X - N) = 0 := by rw [map_sub, hNv, sub_self]
  have hT : fderiv ℝ p.extend A (X - N) = X - N := p.fderiv_extend_eq_self_of_tangent hA hTN
  have hN : fderiv ℝ p.extend A N = 0 := by
    change fderiv ℝ p.extend A (vacuumInvariantRightInverse a A v) = 0
    rw [vacuumInvariantRightInverse_apply]
    exact p.fderiv_extend_spectral_eq_zero hA _ _
  rw [map_sub, hN, sub_zero] at hT
  exact hT

private def columnLinearMap (D : Gradient) : Point →L[ℝ] S0 :=
  ∑ j : Fin 3, (EuclideanSpace.proj j : Point →L[ℝ] ℝ).smulRight (D j)

private theorem columnLinearMap_axis (D : Gradient) (j : Fin 3) :
    columnLinearMap D (axis j) = D j := by
  simp only [columnLinearMap, sum_apply, ContinuousLinearMap.smulRight_apply]
  have h (i : Fin 3) : (EuclideanSpace.proj i : Point →L[ℝ] ℝ) (axis j) =
      if i = j then 1 else 0 := by
    change (EuclideanSpace.single j (1 : ℝ)) i = _
    rw [PiLp.single_apply]
  simp [h, ite_smul]

private theorem coordDeriv_const_add_clm (A : S0) (L : Point →L[ℝ] S0) (j : Fin 3) (x : Point) :
    coordDeriv j (fun y => A + L y) x = L (axis j) := by
  have h := ((hasFDerivAt_const A x).add L.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => A + L y) x = 0 + L at h
  exact DFunLike.congr_fun (h.trans (zero_add L)) (axis j)

private theorem laplacian_const_add_clm (A : S0) (L : Point →L[ℝ] S0) (x : Point) :
    laplacian (fun y => A + L y) x = 0 := by
  have h (j : Fin 3) : coordDeriv j (fun y => A + L y) = fun _ => L (axis j) :=
    funext fun y => coordDeriv_const_add_clm A L j y
  simp only [laplacian, h, coordDeriv, fderiv_const_apply, zero_apply, Finset.sum_const_zero]

/-- Evaluating the projection Hessian on actual tangent columns gives the
quadratic harmonic-map normal force. -/
theorem VacuumTubularProjection.hessian_sum_eq_harmonicRhs
    {a : BulkCoefficients} (p : VacuumTubularProjection a) {A : S0} (hA : A ∈ vacuum a)
    (D : Gradient) (hD : ∀ j, vacuumInvariantDerivative A (D j) = 0) :
    (↑(∑ j, (fderiv ℝ (fderiv ℝ p.extend) A) (D j) (D j) : S0) : Tensor) =
      harmonicRhs a (fun _ => A) (fun _ => D) 0 := by
  let L := columnLinearMap D
  let v (y : Point) := A + L y
  let U := v ⁻¹' vacuumTube a p.radius
  let u := p.extend ∘ v
  have hv0 : v 0 = A := by simp [v]
  have hv : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) v := contDiff_const.add L.contDiff
  have hU : IsOpen U := (isOpen_vacuumTube a p.radius).preimage hv.continuous
  have h0 : (0 : Point) ∈ U := by
    change v 0 ∈ vacuumTube a p.radius
    rw [hv0]
    exact vacuum_subset_vacuumTube a p.radius_pos hA
  have hu : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) u := p.contDiff_extend.comp hv
  have hu2 : ContDiffOn ℝ 2 u U := (hu.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hv2 : ContDiffOn ℝ 2 v U := (hv.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have huVac : MapsTo u U (vacuum a) := by
    intro y hy
    change p.extend (v y) ∈ vacuum a
    rw [p.extend_eq ⟨v y, hy⟩]
    exact (p.project ⟨v y, hy⟩).property
  have hu0 : u 0 = A := by
    change p.extend (v 0) = A
    rw [hv0, p.extend_vacuum hA]
  have hvD (j : Fin 3) : coordDeriv j v 0 = D j :=
    (coordDeriv_const_add_clm A L j 0).trans (columnLinearMap_axis D j)
  have huD (j : Fin 3) : coordDeriv j u 0 = D j := by
    have h := (p.contDiff_extend.differentiable (by simp) (v 0)).hasFDerivAt.comp
      0 (hv.differentiable (by simp) 0).hasFDerivAt
    have hDer := DFunLike.congr_fun h.fderiv (axis j)
    change coordDeriv j u 0 = fderiv ℝ p.extend (v 0) (coordDeriv j v 0) at hDer
    rw [hDer, hv0, hvD]
    exact p.fderiv_extend_eq_self_of_tangent hA (hD j)
  have hH : laplacian u 0 = ∑ j, (fderiv ℝ (fderiv ℝ p.extend) A) (D j) (D j) := by
    have h := laplacian_comp_smooth_map p.contDiff_extend hU hv2 h0
    rw [hv0, laplacian_const_add_clm A L 0, map_zero, zero_add] at h
    simp only [hvD] at h
    exact h
  have hEq : p.extend ∘ u =ᶠ[𝓝 (0 : Point)] u := by
    filter_upwards [hU.mem_nhds h0] with y hy
    exact p.extend_vacuum (huVac hy)
  have hChain := laplacian_comp_smooth_map p.contDiff_extend hU hu2 h0
  rw [laplacian_eq_of_eventuallyEq hEq, hu0] at hChain
  simp only [huD] at hChain
  let H : S0 := ∑ j, (fderiv ℝ (fderiv ℝ p.extend) A) (D j) (D j)
  have hH' : laplacian u 0 = H := hH
  change laplacian u 0 = (fderiv ℝ p.extend A) (laplacian u 0) + H at hChain
  have hTan : vacuumTangentProjector a A (laplacian u 0) = 0 := by
    rw [← p.fderiv_extend_eq_tangentProjector hA]
    exact add_right_cancel (hChain.symm.trans (hH'.trans (zero_add H).symm))
  have hNormal (B : S0) (hB : B ∈ (vacuumInvariantDerivative (u 0)).ker) :
      frobeniusS0 B (laplacian u 0) = 0 := by
    rw [hu0] at hB
    obtain ⟨h₁, h₂⟩ := (mem_vacuumInvariantKernel_iff A B).1 hB
    have hB₁ : inner ℝ (frobeniusCoordinateEquiv B) (frobeniusCoordinateEquiv A) = 0 := by
      rw [real_inner_comm, frobeniusCoordinateEquiv_inner, h₁]
    have hB₂ : inner ℝ (frobeniusCoordinateEquiv B) (frobeniusCoordinateEquiv (traceFreeSquare A)) = 0 := by
      rw [real_inner_comm, frobeniusCoordinateEquiv_inner, h₂]
    have hN : laplacian u 0 =
        vacuumInvariantRightInverse a A (vacuumInvariantDerivative A (laplacian u 0)) :=
      sub_eq_zero.mp hTan
    rw [← frobeniusCoordinateEquiv_inner, hN, vacuumInvariantRightInverse_apply, map_add,
      map_smul, map_smul, inner_add_right, real_inner_smul_right, real_inner_smul_right, hB₁, hB₂]
    simp
  have h := laplacian_eq_harmonicRhs_of_normal hU hu2 huVac h0 hNormal
  change (↑H : Tensor) = _
  rw [← hH']
  unfold harmonicRhs at h ⊢
  have hGrad : ClassicalGradient u 0 = D := funext huD
  simpa only [hu0, hGrad, gradientTraceMul] using h

private theorem exists_coordinate_projection_germ
    {a : BulkCoefficients} (p : VacuumTubularProjection a) :
    let N := vacuumCompactSmoothEmbeddedTarget a
    let e := frobeniusCoordinateEquiv
    ∃ (Q : HarmonicMaps.Ambient 5 → HarmonicMaps.Ambient 5) (C : ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q ∧ (∀ z, ‖fderiv ℝ Q z‖ ≤ C) ∧
      (∀ (z : N.Carrier) (hz : z.val ∈ HarmonicMaps.tubularTube 5 N),
        fderiv ℝ (fderiv ℝ Q) z.val = HarmonicMaps.tubularProjectionSecondDerivative 5 N ⟨z.val, hz⟩) ∧
      (∀ A ∈ vacuum a, Q ∘ e =ᶠ[𝓝 A] e ∘ p.extend) := by
  let N := vacuumCompactSmoothEmbeddedTarget a
  let e := frobeniusCoordinateEquiv
  obtain ⟨ρ, hρ, _, hSub, _, _, _, _, _, _, _, _, _, Q, hQ, hQeq, C, _, _, _, hC, _⟩ :=
    HarmonicMaps.tubularProjection_complete 5 N
  refine ⟨Q, C, hQ, hC, HolderToCK.projectionExtension_hessian_eq_on_target N hρ Q hQ hQeq, ?_⟩
  intro A hA
  let d := min p.radius ρ
  have hd : 0 < d := lt_min p.radius_pos hρ
  have h₁ := (isOpen_vacuumTube a d).mem_nhds (vacuum_subset_vacuumTube a hd hA)
  filter_upwards [h₁] with B hB
  change Metric.infDist B (vacuum a) < d at hB
  have hBTube : B ∈ vacuumTube a p.radius := by
    change Metric.infDist B (vacuum a) < p.radius
    exact hB.trans_le (min_le_left _ _)
  have hBρ : Metric.infDist (e B) N.carrierSet < ρ := by
    rw [infDist_frobeniusCoordinateEquiv_vacuum]
    exact hB.trans_le (min_le_right _ _)
  let z : HarmonicMaps.tubularTube 5 N := ⟨e B, hSub (hBρ.trans (by linarith only [hρ]))⟩
  let P : vacuum a := p.project ⟨B, hBTube⟩
  let Y : N.Carrier := ⟨e P.val, (vacuumCompactSmoothEmbeddedTarget_carrierSet a).symm ▸
    (show e P.val ∈ e '' vacuum a from mem_image_of_mem _ P.property)⟩
  have hY : Y = HarmonicMaps.tubularProjection 5 N z := by
    apply ((HarmonicMaps.tubularProjection_characterization 5 N).2.2.1 z).2
    intro Y'
    let P' : vacuum a := ⟨e.symm Y'.val, mem_vacuumCompactSmoothEmbeddedTarget_iff.1 Y'.property⟩
    have h := p.nearest ⟨B, hBTube⟩ P'
    rw [← e.isometry.dist_eq B P.val, ← e.isometry.dist_eq B P'.val] at h
    change dist (e B) (e P.val) ≤ dist (e B) (e (e.symm Y'.val)) at h
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h
  change Q (e B) = e (p.extend B)
  rw [hQeq z hBρ, p.extend_eq ⟨B, hBTube⟩]
  exact (congrArg Subtype.val hY).symm

private theorem coordinate_projection_derivative
    {a : BulkCoefficients} (p : VacuumTubularProjection a) (A B : S0)
    {Q : HarmonicMaps.Ambient 5 → HarmonicMaps.Ambient 5}
    (hQ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q)
    (hG : Q ∘ frobeniusCoordinateEquiv =ᶠ[𝓝 A] frobeniusCoordinateEquiv ∘ p.extend) :
    fderiv ℝ Q (frobeniusCoordinateEquiv A) (frobeniusCoordinateEquiv B) =
      frobeniusCoordinateEquiv (fderiv ℝ p.extend A B) := by
  let E := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h₁ := (hQ.differentiable (by simp) (E A)).hasFDerivAt.comp A E.hasFDerivAt
  have h₂ := (E.hasFDerivAt (x := p.extend A)).comp A
    (p.contDiff_extend.differentiable (by simp) A).hasFDerivAt
  have h := (h₁.congr_of_eventuallyEq hG.symm).unique h₂
  exact DFunLike.congr_fun h B

private theorem coordinate_projection_hessian_sum
    {a : BulkCoefficients} (p : VacuumTubularProjection a) (A : S0) (D : Gradient)
    {Q : HarmonicMaps.Ambient 5 → HarmonicMaps.Ambient 5}
    (hQ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q)
    (hG : Q ∘ frobeniusCoordinateEquiv =ᶠ[𝓝 A] frobeniusCoordinateEquiv ∘ p.extend) :
    let e := frobeniusCoordinateEquiv
    (∑ j, fderiv ℝ (fderiv ℝ Q) (e A) (e (D j)) (e (D j))) =
      e (∑ j, fderiv ℝ (fderiv ℝ p.extend) A (D j) (D j)) := by
  let E := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let L := columnLinearMap D
  let v (y : Point) := A + L y
  let c := E ∘ v
  let u := p.extend ∘ v
  have hv0 : v 0 = A := by simp [v]
  have hv : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) v := contDiff_const.add L.contDiff
  have hv2 : ContDiffOn ℝ 2 v (Set.univ : Set Point) :=
    (hv.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hc2 : ContDiffOn ℝ 2 c (Set.univ : Set Point) := E.contDiff.comp_contDiffOn hv2
  have hu2 : ContDiffOn ℝ 2 u (Set.univ : Set Point) :=
    (p.contDiff_extend.of_le (WithTop.coe_le_coe.mpr le_top)).comp_contDiffOn hv2
  have h0 : (0 : Point) ∈ (Set.univ : Set Point) := mem_univ _
  have hvL : laplacian v 0 = 0 := laplacian_const_add_clm A L 0
  have hcL : laplacian c 0 = 0 := by
    change laplacian (fun y => E (v y)) 0 = 0
    rw [laplacian_compCLM isOpen_univ hv2 h0 E, hvL, map_zero]
  have hc0 : c 0 = E A := congrArg E hv0
  have hvD (j : Fin 3) : coordDeriv j v 0 = D j :=
    (coordDeriv_const_add_clm A L j 0).trans (columnLinearMap_axis D j)
  have hcD (j : Fin 3) : coordDeriv j c 0 = E (D j) := by
    change coordDeriv j (fun y => E (v y)) 0 = _
    rw [coordDeriv_compCLM E (hv.differentiable (by simp) 0) j, hvD]
  have hGv : Q ∘ c =ᶠ[𝓝 (0 : Point)] E ∘ u := by
    have hT : Tendsto v (𝓝 (0 : Point)) (𝓝 A) := hv0 ▸ hv.continuous.continuousAt.tendsto
    exact hG.comp_tendsto hT
  have h₁ := laplacian_comp_smooth_map hQ isOpen_univ hc2 h0
  rw [hc0, hcL, map_zero, zero_add] at h₁
  simp only [hcD] at h₁
  have h₂ := laplacian_comp_smooth_map p.contDiff_extend isOpen_univ hv2 h0
  rw [hv0, hvL, map_zero, zero_add] at h₂
  simp only [hvD] at h₂
  change (∑ j, fderiv ℝ (fderiv ℝ Q) (E A) (E (D j)) (E (D j))) =
    E (∑ j, fderiv ℝ (fderiv ℝ p.extend) A (D j) (D j))
  exact h₁.symm.trans ((laplacian_eq_of_eventuallyEq hGv).trans
    ((laplacian_compCLM isOpen_univ hu2 h0 E).trans (congrArg E h₂)))

private theorem weakPoissonOn_scalar_tests
    {Ω : HarmonicMaps.OpenDomain 3} {D : Point → HarmonicMaps.Gradient 3 5}
    {F : Point → HarmonicMaps.Ambient 5}
    (h : HolderToCK.WeakPoissonOn Ω D F)
    (hD : ∀ j, LocallyIntegrableOn (fun x => D x j) Ω.val volume)
    (φ : Point → ℝ) (hφ : SmoothTest Ω.val φ) :
    (∑ j : Fin 3, ∫ x in Ω.val, coordDeriv j φ x • D x j) = -(∫ x in Ω.val, φ x • F x) := by
  apply PiLp.ext
  intro i
  let E : HarmonicMaps.Ambient 5 := EuclideanSpace.single i 1
  let π : HarmonicMaps.Ambient 5 →L[ℝ] ℝ := EuclideanSpace.proj i
  let ψ (x : Point) := φ x • E
  have hψ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) ψ := hφ.1.smul contDiff_const
  have hψc : HasCompactSupport ψ := hφ.2.1.smul_right
  have hψS : tsupport ψ ⊆ Ω.val := (tsupport_smul_subset_left φ (fun _ : Point => E)).trans hφ.2.2
  have hψD (j : Fin 3) (x : Point) :
      fderiv ℝ ψ x (EuclideanSpace.single j 1) = coordDeriv j φ x • E :=
    DFunLike.congr_fun (((hφ.1.differentiable (by simp) x).hasFDerivAt).smul_const E).fderiv (axis j)
  have hPair (t : ℝ) (B : HarmonicMaps.Ambient 5) :
      inner ℝ B (t • E) = π (t • B) := by
    rw [real_inner_smul_right, map_smul]
    change t * inner ℝ B (EuclideanSpace.single i 1) = t * B i
    rw [EuclideanSpace.inner_single_right]
    change t * (1 * star (B i)) = t * B i
    rw [star_trivial, one_mul]
  have hDI (j : Fin 3) :
      IntegrableOn (fun x => coordDeriv j φ x • D x j) Ω.val volume :=
    ((hφ.coordDeriv j).integrable_smul (hD j)).integrableOn
  have hFI : IntegrableOn (fun x => φ x • F x) Ω.val volume :=
    (hφ.integrable_smul h.1).integrableOn
  have hT := (h.2 ψ hψ hψc hψS).2.2
  simp only [hψD, hPair, ψ, integral_finsetSum _ (fun j _ => π.integrable_comp (hDI j)),
    π.integral_comp_comm (hDI _), π.integral_comp_comm hFI] at hT
  change π (∑ j : Fin 3, ∫ x in Ω.val, coordDeriv j φ x • D x j) = π (-(∫ x in Ω.val, φ x • F x))
  simpa only [map_sum, map_neg] using hT

private theorem weakPoissonOn_to_tensor
    {Ω : HarmonicMaps.OpenDomain 3} {D : Point → Gradient} {F : Point → HarmonicMaps.Ambient 5}
    (h : HolderToCK.WeakPoissonOn Ω (frobeniusGradient D) F)
    (hD : ∀ j, LocallyIntegrableOn (fun x => D x j) Ω.val volume) :
    let R := fun x => (↑(frobeniusCoordinateEquiv.symm (F x)) : Tensor)
    LocallyIntegrableOn R Ω.val volume ∧ WeakLaplacianEq Ω.val D R := by
  let E := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let L := symmetricTraceless.subtypeL.comp
    frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hDI (j : Fin 3) : LocallyIntegrableOn (fun x => frobeniusGradient D x j) Ω.val volume :=
    E.locallyIntegrableOn_comp (hD j)
  have hF := L.locallyIntegrableOn_comp h.1
  refine ⟨hF, ?_⟩
  intro φ hφ
  have hL (j : Fin 3) :
      L (∫ x in Ω.val, coordDeriv j φ x • frobeniusGradient D x j) =
        ∫ x in Ω.val, coordDeriv j φ x • (D x j : Tensor) := by
    have hI : IntegrableOn (fun x => coordDeriv j φ x • frobeniusGradient D x j) Ω.val volume :=
      ((hφ.coordDeriv j).integrable_smul (hDI j)).integrableOn
    refine (L.integral_comp_comm hI).symm.trans ?_
    apply integral_congr_ae
    filter_upwards [] with x
    exact (L.map_smul (coordDeriv j φ x) (frobeniusGradient D x j)).trans
      (congrArg (fun A : Tensor => coordDeriv j φ x • A)
        (congrArg Subtype.val (frobeniusCoordinateEquiv.symm_apply_apply (D x j))))
  have hR :
      L (∫ x in Ω.val, φ x • F x) =
        ∫ x in Ω.val, φ x • (↑(frobeniusCoordinateEquiv.symm (F x)) : Tensor) := by
    have hI : IntegrableOn (fun x => φ x • F x) Ω.val volume :=
      (hφ.integrable_smul h.1).integrableOn
    refine (L.integral_comp_comm hI).symm.trans ?_
    exact integral_congr_ae (Eventually.of_forall fun x => L.map_smul (φ x) (F x))
  have hT := congrArg L (weakPoissonOn_scalar_tests h hDI φ hφ)
  rw [map_sum, map_neg, hR] at hT
  simpa only [hL] using hT

private theorem exists_coordinate_harmonic_forcing
    (a : BulkCoefficients) {U : Set Point} (hU : IsOpen U) {u : Point → S0} {D : Point → Gradient}
    (hMin : IsLocalDirichletMinimizer a U u D) :
    let Ω : HarmonicMaps.OpenDomain 3 := ⟨U, hU⟩
    ∃ F : Point → HarmonicMaps.Ambient 5,
      HolderToCK.WeakPoissonOn Ω (frobeniusGradient D) F ∧
      (∀ᵐ x ∂volume.restrict U,
        (↑(frobeniusCoordinateEquiv.symm (F x)) : Tensor) = harmonicRhs a u D x) := by
  let Ω : HarmonicMaps.OpenDomain 3 := ⟨U, hU⟩
  let N := vacuumCompactSmoothEmbeddedTarget a
  let e := frobeniusCoordinateEquiv
  let p := vacuumTubularProjection a
  let v := frobeniusField u
  let G := frobeniusGradient D
  obtain ⟨hv, hvN, hvMin⟩ := (isLocalDirichletMinimizer_iff_upstream a Ω N
    (vacuumCompactSmoothEmbeddedTarget_carrierSet a) u D).1 hMin
  obtain ⟨Q, C, hQ, hC, hQH, hGerm⟩ := exists_coordinate_projection_germ p
  have hPost := HarmonicMaps.MemW12Loc.postcompose hv Q hQ C hC
  have hFix : Q ∘ v =ᵐ[volume.restrict U] v := by
    filter_upwards [hMin.2.1] with x hx
    have hP : Q (e (u x)) = e (p.extend (u x)) := (hGerm (u x) hx).eq_of_nhds
    exact hP.trans (congrArg e (p.extend_vacuum hx))
  have hPostD := hPost.1.ae_eq_of_ae_eq_map hv.1 hFix
  obtain ⟨F, hFi, hFformula, hFweak⟩ :=
    HarmonicMaps.outerVariation_weakEquation 5 N 3 (by decide) Ω v G hv hvN hvMin
  refine ⟨F, ⟨hFi, hFweak⟩, ?_⟩
  filter_upwards [hFformula, hMin.2.1, hvN, hPostD] with x hx huVac hvVac hDx
  obtain ⟨hxTube, hxEq, _⟩ := hx
  let A := u x
  have hTan (j : Fin 3) : vacuumInvariantDerivative A (D x j) = 0 := by
    have hEq := (coordinate_projection_derivative p A (D x j) hQ (hGerm A huVac)).symm.trans
      (congrFun hDx j)
    have hProj := e.injective hEq
    rw [p.fderiv_extend_eq_tangentProjector huVac] at hProj
    change D x j - vacuumInvariantRightInverse a A (vacuumInvariantDerivative A (D x j)) = D x j at hProj
    have hR := sub_eq_self.mp hProj
    exact (vacuumInvariantRightInverse_isRightInverse huVac _).symm.trans
      ((congrArg (vacuumInvariantDerivative A) hR).trans (map_zero _))
  have hHessian := hQH ⟨v x, hvVac⟩ hxTube
  change F x = ∑ j, HarmonicMaps.tubularProjectionSecondDerivative 5 N ⟨v x, hxTube⟩
    (G x j) (G x j) at hxEq
  rw [← hHessian] at hxEq
  have hF : F x = e (∑ j, fderiv ℝ (fderiv ℝ p.extend) A (D x j) (D x j)) :=
    hxEq.trans (coordinate_projection_hessian_sum p A (D x) hQ (hGerm A huVac))
  rw [hF, LinearIsometryEquiv.symm_apply_apply]
  exact p.hessian_sum_eq_harmonicRhs huVac (D x) hTan

/-- The native outer variation yields the actual matrix-valued weak harmonic
equation on the entire open domain, using the original weak columns. -/
theorem IsLocalDirichletMinimizer.weakLaplacianEq_harmonicRhs
    {a : BulkCoefficients} {U : Set Point} (hU : IsOpen U) {u : Point → S0} {D : Point → Gradient}
    (hMin : IsLocalDirichletMinimizer a U u D) :
    LocallyIntegrableOn (harmonicRhs a u D) U volume ∧ WeakLaplacianEq U D (harmonicRhs a u D) := by
  obtain ⟨F, hF, hR⟩ := exists_coordinate_harmonic_forcing a hU hMin
  obtain ⟨hInt, hEq⟩ := weakPoissonOn_to_tensor hF (hMin.1.locallyIntegrableOn_gradient hU)
  refine ⟨hInt.congr hR, ?_⟩
  intro φ hφ
  have h := hEq φ hφ
  exact h.trans (congrArg Neg.neg (integral_congr_ae
    (hR.mono fun x hx => congrArg (fun A : Tensor => φ x • A) hx)))

private theorem continuousOn_harmonicRhs_classical
    (a : BulkCoefficients) {W : Set Point} (hW : IsOpen W) {q : Point → S0}
    (hq : ContDiffOn ℝ 2 q W) :
    ContinuousOn (harmonicRhs a q (ClassicalGradient q)) W := by
  have hA : ContinuousOn (fun x => (q x : Tensor)) W :=
    symmetricTraceless.subtypeL.continuous.comp_continuousOn hq.continuousOn
  have hq₁ : ContDiffOn ℝ 1 q W := hq.of_le (by norm_num)
  have hD (j : Fin 3) : ContinuousOn (coordDeriv j q) W := continuousOn_coordDeriv hW hq₁ j
  have hDt (j : Fin 3) : ContinuousOn (fun x => (↑(coordDeriv j q x) : Tensor)) W :=
    symmetricTraceless.subtypeL.continuous.comp_continuousOn (hD j)
  have hGrad : ContinuousOn (fun x => gradientNormSq (ClassicalGradient q x)) W := by
    simp only [gradientNormSq_eq_sum_norm_sq, ClassicalGradient]
    exact continuousOn_finsetSum _ fun j _ => ((hD j).norm).pow 2
  have hTrace : ContinuousOn
      (fun x => gradientTraceMul (ClassicalGradient q) (ClassicalGradient q) (q x : Tensor) x) W := by
    unfold gradientTraceMul ClassicalGradient
    exact continuousOn_finsetSum _ fun j _ => tensorTraceCLM.continuous.comp_continuousOn
      (((hDt j).mul (hDt j)).mul hA)
  have hB : ContinuousOn (fun x => biaxialQuadratic a (q x : Tensor)) W :=
    (hA.pow 2).sub continuousOn_const
  unfold harmonicRhs
  exact ((hGrad.div_const _).neg.smul hA).sub ((continuousOn_const.mul hTrace).smul hB)

/-- On an open set where the minimizer has a C² representative, the weak
columns agree with its classical gradient and its Laplacian is the
pointwise biaxial harmonic-map expression. -/
theorem IsLocalDirichletMinimizer.harmonicRhs_of_regularRepresentative
    {a : BulkCoefficients} {U W : Set Point} (hU : IsOpen U) (hW : IsOpen W) (hSub : W ⊆ U)
    {u q : Point → S0} {D : Point → Gradient} (hMin : IsLocalDirichletMinimizer a U u D)
    (hq : ContDiffOn ℝ 2 q W) (huq : u =ᵐ[volume.restrict W] q) :
    D =ᵐ[volume.restrict W] ClassicalGradient q ∧
      ∀ x ∈ W, (↑(laplacian q x) : Tensor) = harmonicRhs a q (ClassicalGradient q) x := by
  let V : HarmonicMaps.OpenDomain 3 := ⟨W, hW⟩
  let e := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let L := symmetricTraceless.subtypeL.comp
    frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hv2 : ContDiffOn ℝ 2 (frobeniusField q) W := e.contDiff.comp_contDiffOn hq
  have hSob := (hMin.1.mono hSub).congr_ae huq EventuallyEq.rfl
  have hvSob := (memH1Loc_iff_memW12Loc V q D).1 hSob
  have hD := hSob.ae_eq_classicalGradient hW (hq.of_le (by norm_num)) EventuallyEq.rfl
  obtain ⟨F, hF, hR⟩ := exists_coordinate_harmonic_forcing a hU hMin
  have hFV : HolderToCK.WeakPoissonOn V (frobeniusGradient D) F := hF.mono hSub
  have hDelta := hFV.laplacian_ae_eq_of_contDiffOn_two hvSob.1 hv2
  have hL (x : Point) (hx : x ∈ W) :
      (↑(laplacian q x) : Tensor) = L (Laplacian.laplacian (frobeniusField q) x) := by
    have h₁ : Laplacian.laplacian (frobeniusField q) x = laplacian (frobeniusField q) x :=
      HolderToCK.laplacian_eq_coordinateSum_of_contDiffAt_two (frobeniusField q) x
        ((hv2 x hx).contDiffAt (hW.mem_nhds hx))
    have h₂ : laplacian (frobeniusField q) x = e (laplacian q x) :=
      laplacian_compCLM hW hq hx e
    exact ((congrArg L (h₁.trans h₂)).trans
      (congrArg Subtype.val (frobeniusCoordinateEquiv.symm_apply_apply (laplacian q x)))).symm
  have hLC : ContinuousOn (fun x => (↑(laplacian q x) : Tensor)) W :=
    (L.continuous.comp_continuousOn (HolderToCK.continuousOn_laplacian_of_contDiffOn_two V hv2)).congr hL
  have hLocR := ae_restrict_of_ae_restrict_of_subset hSub hR
  have hAE : (fun x => (↑(laplacian q x) : Tensor)) =ᵐ[volume.restrict W]
      harmonicRhs a q (ClassicalGradient q) := by
    filter_upwards [hDelta, hLocR, huq, hD, ae_restrict_mem hW.measurableSet] with x h₁ h₂ h₃ h₄ hx
    calc
      _ = L (Laplacian.laplacian (frobeniusField q) x) := hL x hx
      _ = L (F x) := congrArg L h₁
      _ = harmonicRhs a u D x := h₂
      _ = _ := by simp only [harmonicRhs, gradientTraceMul, h₃, h₄]
  exact ⟨hD, fun _ hx => Measure.eqOn_open_of_ae_eq hAE hW hLC
    (continuousOn_harmonicRhs_classical a hW hq) hx⟩

end Thesis

end

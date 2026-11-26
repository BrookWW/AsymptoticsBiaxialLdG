module

public import Thesis.MeasureGeometry.PlanarExteriorScaling
public import Thesis.MeasureGeometry.PlanarSpectralCoarea
public import Mathlib.MeasureTheory.Measure.Prod

/-! Actual spectral projections on the positive gap levels. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis

/-- A measurable real-valued map has area-null levels for almost every
level parameter. -/
theorem ae_volume_preimage_singleton_null {f : Plane → ℝ} (hf : Measurable f) :
    ∀ᵐ t : ℝ ∂volume, (volume : Measure Plane) {x | f x = t} = 0 := by
  have hGraph : MeasurableSet {p : Plane × ℝ | f p.1 ≠ p.2} :=
    (measurableSet_eq_fun (hf.comp measurable_fst) measurable_snd).compl
  have h₀ : ∀ᵐ x : Plane ∂volume, ∀ᵐ t : ℝ ∂volume, f x ≠ t := by
    apply ae_of_all
    intro x
    rw [ae_iff]
    simpa only [not_ne_iff, eq_comm, setOf_eq_eq_singleton] using
      (measure_singleton (μ := (volume : Measure ℝ)) (f x))
  have h := (Measure.ae_ae_comm (μ := (volume : Measure Plane)) (ν := volume) hGraph).1 h₀
  filter_upwards [h] with t ht
  simpa only [ae_iff, not_ne_iff] using ht

theorem ae_volume_ball_level_null {f : Plane → ℝ} {R : ℝ}
    (hf : ContinuousOn f (ball (0 : Plane) R)) :
    ∀ᵐ t : ℝ ∂volume, (volume : Measure Plane) (ball (0 : Plane) R ∩ {x | f x = t}) = 0 := by
  classical
  let B := ball (0 : Plane) R
  let F := B.indicator f
  have hF : Measurable F := hf.measurable_piecewise continuousOn_const measurableSet_ball
  filter_upwards [ae_volume_preimage_singleton_null hF] with t ht
  apply measure_mono_null _ ht
  intro x hx
  change F x = t
  rw [show F x = f x from indicator_of_mem hx.1 _]
  exact hx.2

private theorem planar_circle_dilation_norm {R : ℝ} (hR : 0 ≤ R) (z : NativeCircle) :
    ‖R • z.val‖ = R := by
  rw [norm_smul, Real.norm_of_nonneg hR, mem_sphere_zero_iff_norm.mp z.property, mul_one]

/-- The actual circle obtained by projecting the simple-spectrum trace of
a tensor map at radius R. -/
def planarSpectralCircleTrace (a : BulkCoefficients) (Q : Plane → S0) {R : ℝ} (hR : 0 ≤ R)
    (hQ : ContinuousOn Q (closedBall (0 : Plane) R))
    (hSimple : ∀ z : NativeCircle, Q (R • z.val) ∈ simpleSpectrumLocus) : C(NativeCircle, vacuum a) := by
  have hRay : Continuous (fun z : NativeCircle => R • z.val) := by fun_prop
  have hC : Continuous (fun z : NativeCircle => Q (R • z.val)) :=
    hQ.comp_continuous hRay (fun z => by
      rw [mem_closedBall, dist_zero_right, planar_circle_dilation_norm hR z])
  have hProj : Continuous (fun z : NativeCircle => (spectralVacuumPoint a (Q (R • z.val))).val) :=
    (contDiffOn_spectralVacuumPoint a).continuousOn.comp_continuous hC hSimple
  exact ⟨fun z => spectralVacuumPoint a (Q (R • z.val)), hProj.subtype_mk _⟩

/-- The actual spectral circle restrictions at both sides of a
simple-spectrum annulus are freely homotopic. -/
theorem planarSpectralCircleTrace_homotopic (a : BulkCoefficients) (Q : Plane → S0)
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (hQ : ContinuousOn Q (closedBall (0 : Plane) R))
    (hSimple : ∀ x : Plane, r ≤ ‖x‖ → ‖x‖ ≤ R → Q x ∈ simpleSpectrumLocus)
    (hS₀ : ∀ z : NativeCircle, Q (r • z.val) ∈ simpleSpectrumLocus)
    (hS₁ : ∀ z : NativeCircle, Q (R • z.val) ∈ simpleSpectrumLocus) :
    (planarSpectralCircleTrace a Q hr (hQ.mono (closedBall_subset_closedBall hrR)) hS₀).Homotopic
      (planarSpectralCircleTrace a Q (hr.trans hrR) hQ hS₁) := by
  let s (t : unitInterval) := r + t.val * (R - r)
  have hs (t : unitInterval) : s t ∈ Icc r R := by
    constructor
    · dsimp only [s]; linarith only [mul_nonneg t.property.1 (sub_nonneg.mpr hrR)]
    · dsimp only [s]
      nlinarith only [mul_le_mul_of_nonneg_right t.property.2 (sub_nonneg.mpr hrR)]
  let H (p : unitInterval × NativeCircle) := s p.1 • p.2.val
  have hH : Continuous H := by dsimp only [H, s]; fun_prop
  have hRay (p : unitInterval × NativeCircle) : ‖H p‖ = s p.1 :=
    planar_circle_dilation_norm (hr.trans (hs p.1).1) p.2
  have hC : Continuous (Q ∘ H) := hQ.comp_continuous hH (fun p => by
    rw [mem_closedBall, dist_zero_right, hRay]
    exact (hs p.1).2)
  have hSQ (p : unitInterval × NativeCircle) : (Q ∘ H) p ∈ simpleSpectrumLocus := by
    apply hSimple (H p) <;> rw [hRay]
    exacts [(hs p.1).1, (hs p.1).2]
  have hP : Continuous (fun p => (spectralVacuumPoint a ((Q ∘ H) p)).val) :=
    (contDiffOn_spectralVacuumPoint a).continuousOn.comp_continuous hC hSQ
  refine ⟨⟨⟨fun p => spectralVacuumPoint a (Q (H p)), hP.subtype_mk _⟩, ?_, ?_⟩⟩
  · intro z
    change spectralVacuumPoint a (Q (H (0, z))) = spectralVacuumPoint a (Q (r • z.val))
    simp [H, s]
  · intro z
    change spectralVacuumPoint a (Q (H (1, z))) = spectralVacuumPoint a (Q (R • z.val))
    simp [H, s]

/-- The projected Dirichlet energy on strict positive superlevels uses the
same tensor and the exact two Frobenius derivative columns. -/
def planarProjectionLevelEnergy (a : BulkCoefficients) (τ : GapSmoothingParameter)
    (Q : Plane → S0) (R t : ℝ) : ℝ :=
  ∫ x in ball (0 : Plane) R ∩ {x | t < modifiedSpectralGap a τ (Q x)},
    planarSpectralProjectionGradientSq a Q x

/-- The actual projected level energy controls its outer circle charge
through the compact strict sublevel core. -/
theorem planarProjectionLevel_energy_lower (a : BulkCoefficients) (τ : GapSmoothingParameter)
    (Q : Plane → S0) {U : Set Plane} (hU : IsOpen U) (hQ : ContDiffOn ℝ 1 Q U)
    {R μ ℓ t A : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ) (hμ : μ ≤ R - 2 * ℓ)
    (hBall : closedBall (0 : Plane) R ⊆ U) (ht : t ∈ Ioo 0 A)
    (hAnn : ∀ x : Plane, μ ≤ ‖x‖ → ‖x‖ ≤ R → A ≤ modifiedSpectralGap a τ (Q x))
    (hSimple : ∀ z : NativeCircle, Q (R • z.val) ∈ simpleSpectrumLocus)
    (hNull : (volume : Measure Plane)
      (ball (0 : Plane) R ∩ {x | modifiedSpectralGap a τ (Q x) = t}) = 0) :
    let f (x : Plane) := modifiedSpectralGap a τ (Q x)
    let e := nativeVacuumCircleCost a (planarSpectralCircleTrace a Q hR.le (hQ.continuousOn.mono hBall) hSimple)
    let K := planarSublevelCore f R t
    (0 < e → 0 < planarCoverRadius K) ∧
      2 * e * Real.log (ℓ / planarCoverRadius K) ≤ planarProjectionLevelEnergy a τ Q R t := by
  intro f e K
  have hμR : μ < R := by linarith only [hμ, hℓ]
  have hf : ContinuousOn f U := (continuous_modifiedSpectralGap a τ).comp_continuousOn hQ.continuousOn
  have hK : (K : Set Plane) ⊆ closedBall (0 : Plane) (R - 2 * ℓ) :=
    (planarSublevelCore_inside_and_radius_le (hf.mono hBall) hμR.le
      (fun x hx hxr => ht.2.trans_le (hAnn x hx hxr))).1.trans (ball_subset_closedBall.trans (closedBall_subset_closedBall hμ))
  let V := U ∩ {x | 0 < f x}
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact inter_mem (hU.mem_nhds hx.1) ((hf.continuousAt (hU.mem_nhds hx.1)).preimage_mem_nhds (Ioi_mem_nhds hx.2))
  let Kgood := closedBall (0 : Plane) R ∩ {x | t ≤ f x}
  have hKGc : IsCompact Kgood := by
    let B := closedBall (0 : Plane) R
    have hSub : IsClosed ((fun z : B => f z.val) ⁻¹' Ici t) :=
      isClosed_Ici.preimage (continuousOn_iff_continuous_restrict.mp (hf.mono hBall))
    have hC := isClosed_closedBall.isClosedMap_subtype_val _ hSub
    have hEq : Kgood = Subtype.val '' ((fun z : B => f z.val) ⁻¹' Ici t) := by
      ext x
      constructor
      · exact fun hx => ⟨⟨x, hx.1⟩, hx.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property, hy⟩
    exact (isCompact_closedBall _ _).of_isClosed_subset (hEq ▸ hC) inter_subset_left
  have hKGV : Kgood ⊆ V := fun _ hx => ⟨hBall hx.1, ht.1.trans_le hx.2⟩
  let p (x : Plane) := (spectralVacuumPoint a (Q x)).val
  obtain ⟨P, hP, hNear⟩ := exists_contDiff_eq_near_compact hV hKGc hKGV
    (contDiffOn_planarSpectralProjection_pos_locus a τ hQ)
  have hKG (x : Plane) (hx : x ∈ closedBall (0 : Plane) R) (hxK : x ∉ (K : Set Plane)) : x ∈ Kgood := by
    refine ⟨hx, ?_⟩
    change t ≤ f x
    by_contra! hxt
    have hxn : ‖x‖ ≤ R := by simpa only [dist_zero_right] using mem_closedBall.mp hx
    by_cases hxI : ‖x‖ < R
    · apply hxK
      exact subset_closure ⟨by simpa only [mem_ball, dist_zero_right] using hxI, hxt⟩
    · exact hxt.not_ge (ht.2.le.trans (hAnn x (hμR.le.trans (le_of_not_gt hxI)) hxn))
  have hPVac (x : Plane) (hx : x ∈ closedBall (0 : Plane) R) (hxK : x ∉ (K : Set Plane)) :
      P x ∈ vacuum a := by
    rw [(hNear x (hKG x hx hxK)).eq_of_nhds]
    exact (spectralVacuumPoint a (Q x)).property
  have hBKG (z : NativeCircle) : R • z.val ∈ Kgood := by
    have hx : ‖R • z.val‖ = R := planar_circle_dilation_norm hR.le z
    refine ⟨by rw [mem_closedBall, dist_zero_right, hx], ht.2.le.trans (hAnn (R • z.val) ?_ ?_)⟩
    · rw [hx]
      exact hμR.le
    · rw [hx]
  have hPB (z : NativeCircle) : P (0 + R • z.val) ∈ vacuum a := by
    rw [zero_add, (hNear _ (hBKG z)).eq_of_nhds]
    exact (spectralVacuumPoint a (Q _)).property
  have hTrace : planarVacuumCircleTrace a P hP.continuous 0 R hPB =
      planarSpectralCircleTrace a Q hR.le (hQ.continuousOn.mono hBall) hSimple := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    change P (0 + R • z.val) = p (R • z.val)
    rw [zero_add, (hNear _ (hBKG z)).eq_of_nhds]
  have h := planarVacuum_centered_exterior_lower a P hP K hR hℓ hK hPVac hPB
  dsimp only at h
  rw [hTrace] at h
  refine ⟨h.1, ?_⟩
  let G := ball (0 : Plane) R ∩ {x | t < f x}
  have hG : IsOpen G := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hxU := hBall (ball_subset_closedBall hx.1)
    exact inter_mem (isOpen_ball.mem_nhds hx.1) ((hf.continuousAt (hU.mem_nhds hxU)).preimage_mem_nhds (Ioi_mem_nhds hx.2))
  have hInt : IntegrableOn (planarSmoothDirichletDensity P) G :=
    ((continuous_planarSmoothDirichletDensity hP).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Plane) R)).mono_set (inter_subset_left.trans ball_subset_closedBall)
  have hSubAE : ball (0 : Plane) R \ (K : Set Plane) ≤ᵐ[volume] G := by
    have hAe : ∀ᵐ x ∂(volume : Measure Plane),
        x ∉ ball (0 : Plane) R ∩ {x | f x = t} := compl_mem_ae_iff.mpr hNull
    filter_upwards [hAe] with x hx hxK
    have hxt : t ≤ f x := (hKG x (ball_subset_closedBall hxK.1) hxK.2).2
    exact ⟨hxK.1, lt_of_le_of_ne hxt (fun he => hx ⟨hxK.1, he.symm⟩)⟩
  have hComp : planarDiskExteriorEnergy P K ⟨0, R, hR⟩ ≤
      ∫ x in G, planarSmoothDirichletDensity P x :=
    setIntegral_mono_set hInt (Eventually.of_forall (planarSmoothDirichletDensity_nonneg P)) hSubAE
  have hD : EqOn (planarSmoothDirichletDensity P)
      (fun x => (1 / 2 : ℝ) * planarSpectralProjectionGradientSq a Q x) G := by
    intro x hx
    have hxKG : x ∈ Kgood := ⟨ball_subset_closedBall hx.1, (show t < f x from hx.2).le⟩
    have hD : fderiv ℝ (fun y => (P y : Tensor)) x =
        fderiv ℝ (fun y => (p y : Tensor)) x := ((hNear x hxKG).fun_comp (fun A : S0 => (A : Tensor))).fderiv_eq
    unfold planarSmoothDirichletDensity planarSpectralProjectionGradientSq
    rw [hD]
  have hE : (∫ x in G, planarSmoothDirichletDensity P x) =
      (1 / 2 : ℝ) * planarProjectionLevelEnergy a τ Q R t := by
    rw [setIntegral_congr_fun hG.measurableSet hD, integral_const_mul]
    rfl
  have hFinal := h.2.trans (hComp.trans_eq hE)
  change Real.log (ℓ / planarCoverRadius K) * e ≤ _ at hFinal
  linarith only [hFinal]

end Thesis

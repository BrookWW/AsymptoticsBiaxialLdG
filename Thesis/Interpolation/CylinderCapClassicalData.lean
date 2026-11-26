module

public import Thesis.Interpolation.CylinderBoundaryTrace
public import Thesis.Interpolation.CylinderRecoveryBand

/-! The smooth outer disks and physical walls of the terminal comparisons. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

def planarClassicalColumns {q : ℕ} (u : Plane → Ambient q) (y : Plane) : HarmonicMaps.Gradient 2 q :=
  fun i => fderiv ℝ u y (EuclideanSpace.single i 1)

theorem planarCoordinateBulk_integrable_of_bound (a : BulkCoefficients) (r M : ℝ)
    {u : Plane → Ambient 5} (hu : MemLp u 2 (volume.restrict (ball 0 r)))
    (hM : ∀ᵐ y ∂volume.restrict (ball 0 r), ‖u y‖ ≤ M) :
    IntegrableOn (fun y => planarCoordinateBulkPotential a (u y)) (ball (0 : Plane) r) := by
  letI := finite_planarVolume_restrict_ball r
  exact integrable_bulkPotential_of_ae_norm_bound a M
    (frobeniusCoordinateEquiv.symm.continuous.comp_aestronglyMeasurable hu.1)
    (hM.mono fun y hy => by simpa only [frobeniusCoordinateEquiv.symm.norm_map] using hy)

theorem cylinderSlice_nativeGraph (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (a : BulkCoefficients) (ε : ElasticScale) {Ω : Set Point} (hΩ : IsOpen Ω)
    {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω) (r z : ℝ)
    (hSub : ∀ y ∈ closedBall (0 : Plane) r, c + axisChart B (y, z) ∈ Ω) :
    let u := frobeniusCoordinateEquiv ∘ cylinderSliceMap B c Q z
    MemW12 (ballDomain (0 : Plane) r) u (planarClassicalColumns u) ∧
      ContinuousOn u (closedBall (0 : Plane) r) ∧
      planarWeakEnergy a (ε : ℝ) u (planarClassicalColumns u) r =
        planarSmoothEnergy a (ε : ℝ) (cylinderSliceMap B c Q z) r := by
  let G (y : Plane) := c + axisChart B (y, z)
  let U := G ⁻¹' Ω
  let V := cylinderSliceMap B c Q z
  let u := frobeniusCoordinateEquiv ∘ V
  have hG := contDiff_axisChart_horizontal_affine B c z
  have hU : IsOpen U := hΩ.preimage hG.continuous
  have hV : ContDiffOn ℝ ∞ V U := hQ.comp hG.contDiffOn (fun _ hy => hy)
  have hu : ContDiffOn ℝ ∞ u U := frobeniusCoordinateEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn hV
  have hW : MemW12 (ballDomain (0 : Plane) r) u (planarClassicalColumns u) :=
    memW12_of_smooth_on_compact_neighborhood hU hu (isCompact_closedBall 0 r) hSub ball_subset_closedBall
  refine ⟨hW, hu.continuousOn.mono hSub, ?_⟩
  have hInt : IntegrableOn (fun y => planarCoordinateBulkPotential a (u y)) (ball (0 : Plane) r) :=
    (((continuous_planarCoordinateBulkPotential a).comp_continuousOn
      (hu.continuousOn.mono hSub)).integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  change planarWeakEnergy a (ε : ℝ) u (planarClassicalColumns u) r = planarSmoothEnergy a (ε : ℝ) V r
  have hD : IntegrableOn (fun y => hsNormSq (planarClassicalColumns u y)) (ball (0 : Plane) r) :=
    hW.integrable_hsNormSq
  unfold planarWeakEnergy planarSmoothEnergy
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hD.const_mul _) (hInt.const_mul _)]
  apply setIntegral_congr_fun measurableSet_ball
  intro y hy
  exact (planarSmoothEnergyDensity_eq_native_columns a (ε : ℝ)
    (((hV y (hSub y (ball_subset_closedBall hy))).contDiffAt
      (hU.mem_nhds (hSub y (ball_subset_closedBall hy)))).differentiableAt (by simp))).symm

theorem planarSurfaceCost_eq_ofReal_weakEnergy (a : BulkCoefficients) (ε : ElasticScale)
    {r : ℝ} {u : Plane → Ambient 5} {Du : Plane → HarmonicMaps.Gradient 2 5}
    (hu : MemW12 (ballDomain (0 : Plane) r) u Du)
    (hBulk : IntegrableOn (fun y => planarCoordinateBulkPotential a (u y)) (ball (0 : Plane) r)) :
    ENNReal.ofReal (1 / 2 : ℝ) * HarmonicMaps.dirichletEnergy Du (ball (0 : Plane) r) +
      (∫⁻ y in ball (0 : Plane) r, ENNReal.ofReal ((ε : ℝ)⁻¹ ^ 2 * planarCoordinateBulkPotential a (u y))) =
      ENNReal.ofReal (planarWeakEnergy a (ε : ℝ) u Du r) := by
  have hD : 0 ≤ ∫ y in ball (0 : Plane) r, hsNormSq (Du y) :=
    integral_nonneg fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE : 0 ≤ ∫ y in ball (0 : Plane) r, planarCoordinateBulkPotential a (u y) :=
    integral_nonneg fun _ => bulkPotential_nonneg a _
  have hIntD : IntegrableOn (fun y => hsNormSq (Du y)) (ball (0 : Plane) r) := hu.integrable_hsNormSq
  rw [HarmonicMaps.dirichletEnergy_eq_ofReal_integral hIntD,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ofReal_integral_eq_lintegral_ofReal (hBulk.const_mul _)
      (Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _)),
    integral_const_mul, ← ENNReal.ofReal_add (mul_nonneg (by norm_num) hD) (mul_nonneg (sq_nonneg _) hE)]
  rfl

/-- The true wall contribution in annular coordinates. -/
def terminalWallPenalizedEnergy (a : BulkCoefficients) (ε : ElasticScale) (r H : ℝ)
    (u : Plane → Ambient 5) (Du : Plane → HarmonicMaps.Gradient 2 5) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ y in (terminalWallAnnulus r).val,
    ENNReal.ofReal (terminalWallDirichletDensity r H Du y)) +
    ∫⁻ y in (terminalWallAnnulus r).val,
      ENNReal.ofReal (2 * H / ‖y‖) * ENNReal.ofReal ((ε : ℝ)⁻¹ ^ 2 * planarCoordinateBulkPotential a (u y))

theorem terminalCylinderSurfacePenalizedEnergy_eq_faces (a : BulkCoefficients) (ε : ElasticScale)
    {r : ℝ} {hr : 0 < r} (H : ℝ) (D : TerminalCylinderBoundaryData 5 r hr)
    (hLower : IntegrableOn (fun y => planarCoordinateBulkPotential a (D.lower y)) (ball (0 : Plane) r))
    (hUpper : IntegrableOn (fun y => planarCoordinateBulkPotential a (D.upper y)) (ball (0 : Plane) r)) :
    terminalCylinderSurfacePenalizedEnergy a ε H D =
      ENNReal.ofReal (planarWeakEnergy a (ε : ℝ) D.lower D.lowerDerivative r) +
      ENNReal.ofReal (planarWeakEnergy a (ε : ℝ) D.upper D.upperDerivative r) +
      terminalWallPenalizedEnergy a ε r H D.wall D.wallDerivative := by
  unfold terminalCylinderSurfacePenalizedEnergy terminalCylinderSurfaceDirichlet terminalCylinderSurfaceValueIntegral
    terminalWallPenalizedEnergy
  rw [mul_add, mul_add, ← planarSurfaceCost_eq_ofReal_weakEnergy a ε D.lower_memW12 hLower,
    ← planarSurfaceCost_eq_ofReal_weakEnergy a ε D.upper_memW12 hUpper]
  simp only [planarCoordinateBulkPotential]
  abel


/-- The closed parameter annulus of a physical terminal wall. -/
def terminalClosedWallAnnulus (r : ℝ) : Set Plane := closedBall 0 (2 * r) \ ball 0 r

theorem isCompact_terminalClosedWallAnnulus (r : ℝ) : IsCompact (terminalClosedWallAnnulus r) :=
  (isCompact_closedBall _ _).diff isOpen_ball

theorem terminalWallAnnulus_subset_closed (r : ℝ) : (terminalWallAnnulus r).val ⊆ terminalClosedWallAnnulus r := by
  intro y hy
  exact ⟨mem_closedBall_zero_iff.2 hy.2.le, fun h => hy.1.not_ge (mem_ball_zero_iff.1 h).le⟩

theorem terminalWallChart_eq_axisChart (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (r lo hi : ℝ) (y : Plane) :
    terminalWallChart B (cylinderTerminalCenter B c lo hi) r ((hi - lo) / 2) y =
      c + axisChart B (r • NormedSpace.normalize y, lo + (hi - lo) / r * (‖y‖ - r)) := by
  simp only [terminalWallChart, cylinderTerminalCenter, axisChart_eq_plane_add_axis]
  rw [show 2 * ((hi - lo) / 2) = hi - lo by ring,
    show lo + (hi - lo) / r * (‖y‖ - r) =
      (lo + hi) / 2 + ((hi - lo) / r * (‖y‖ - r) - (hi - lo) / 2) by ring, add_smul]
  abel

theorem terminalWallChart_mem_lateral (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {r lo hi : ℝ} (hr : 0 < r) (hH : lo ≤ hi) {K : Set Point}
    (hK : ∀ z ∈ Icc lo hi, ∀ θ : NativeCircle, c + axisChart B (r • θ.val, z) ∈ K)
    {y : Plane} (hy : y ∈ terminalClosedWallAnnulus r) :
    terminalWallChart B (cylinderTerminalCenter B c lo hi) r ((hi - lo) / 2) y ∈ K := by
  have hl : r ≤ ‖y‖ := le_of_not_gt (fun h => hy.2 (mem_ball_zero_iff.2 h))
  have hu : ‖y‖ ≤ 2 * r := mem_closedBall_zero_iff.1 hy.1
  have h0 := norm_pos_iff.1 (hr.trans_le hl)
  let θ : NativeCircle := ⟨NormedSpace.normalize y, mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize h0)⟩
  rw [terminalWallChart_eq_axisChart]
  apply hK _ _ θ
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (sub_nonneg.2 hH) hr.le) (sub_nonneg.2 hl))
  · calc
      _ ≤ lo + (hi - lo) / r * r := add_le_add_right (mul_le_mul_of_nonneg_left
        (by linarith only [hu] : ‖y‖ - r ≤ r) (div_nonneg (sub_nonneg.2 hH) hr.le)) _
      _ = _ := by rw [div_mul_cancel₀ _ hr.ne']; ring

theorem contDiffOn_terminalWallChart (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (r H : ℝ) : ContDiffOn ℝ ∞ (terminalWallChart B c r H) ({0}ᶜ : Set Plane) := by
  intro y hy
  have h0 : y ≠ 0 := hy
  have hN := contDiffAt_norm ℝ (n := ∞) h0
  have hx : ContDiffAt ℝ ∞ (fun y : Plane => r • NormedSpace.normalize y) y :=
    ((hN.inv (norm_ne_zero_iff.2 h0)).smul contDiffAt_id).const_smul r
  have hz : ContDiffAt ℝ ∞ (fun y : Plane => (2 * H / r) * (‖y‖ - r) - H) y :=
    (contDiffAt_const.mul (hN.sub contDiffAt_const)).sub contDiffAt_const
  exact (contDiffAt_const.add ((contDiff_axisChart B).contDiffAt.comp y (hx.prodMk hz))).contDiffWithinAt

theorem terminalWall_radialRims (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {r lo hi : ℝ} (hr : 0 < r) (θ : NativeCircle) :
    terminalWallChart B (cylinderTerminalCenter B c lo hi) r ((hi - lo) / 2) (r • θ.val) =
      c + axisChart B (r • θ.val, lo) ∧
    terminalWallChart B (cylinderTerminalCenter B c lo hi) r ((hi - lo) / 2) ((2 * r) • θ.val) =
      c + axisChart B (r • θ.val, hi) := by
  have hθ := mem_sphere_zero_iff_norm.1 θ.property
  have hθN := NormedSpace.normalize_eq_self_of_norm_eq_one hθ
  have h2r : 0 < 2 * r := by positivity
  constructor
  · rw [terminalWallChart_eq_axisChart, NormedSpace.normalize_smul_of_pos hr, hθN, norm_smul,
      hθ, mul_one, Real.norm_of_nonneg hr.le, sub_self, mul_zero, add_zero]
  · rw [terminalWallChart_eq_axisChart, NormedSpace.normalize_smul_of_pos h2r, hθN, norm_smul,
      hθ, mul_one, Real.norm_of_nonneg h2r.le, show 2 * r - r = r by ring, div_mul_cancel₀ _ hr.ne']
    rw [show lo + (hi - lo) = hi by ring]

theorem terminalWall_annulus_nativeGraph (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {r lo hi : ℝ} (hr : 0 < r) (hI : lo ≤ hi) {U : Set Point} (hU : IsOpen U)
    {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q U)
    (hBand : ∀ z ∈ Icc lo hi, ∀ θ : NativeCircle, c + axisChart B (r • θ.val, z) ∈ U) :
    let w := frobeniusCoordinateEquiv ∘ Q ∘
      terminalWallChart B (cylinderTerminalCenter B c lo hi) r ((hi - lo) / 2)
    MemW12 (terminalWallAnnulus r) w (planarClassicalColumns w) ∧
      ContinuousOn w (terminalClosedWallAnnulus r) := by
  let F := terminalWallChart B (cylinderTerminalCenter B c lo hi) r ((hi - lo) / 2)
  let A : Set Plane := {0}ᶜ
  let V := A ∩ F ⁻¹' U
  have hA : IsOpen A := isOpen_compl_singleton
  have hF : ContDiffOn ℝ ∞ F A := contDiffOn_terminalWallChart B _ _ _
  have hV : IsOpen V := hF.continuousOn.isOpen_inter_preimage hA hU
  have hSub : terminalClosedWallAnnulus r ⊆ V := by
    intro y hy
    have hr' : r ≤ ‖y‖ := le_of_not_gt fun h => hy.2 (mem_ball_zero_iff.2 h)
    exact ⟨norm_pos_iff.1 (hr.trans_le hr'), terminalWallChart_mem_lateral B c hr hI hBand hy⟩
  have hW : ContDiffOn ℝ ∞ (frobeniusCoordinateEquiv ∘ Q ∘ F) V :=
    frobeniusCoordinateEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn
      (hQ.comp (hF.mono inter_subset_left) (fun _ hx => hx.2))
  exact ⟨memW12_of_smooth_on_compact_neighborhood hV hW (isCompact_terminalClosedWallAnnulus r)
      hSub (terminalWallAnnulus_subset_closed r), hW.continuousOn.mono hSub⟩


private theorem continuous_planarQuarterTurn : Continuous planarQuarterTurn := by
  unfold planarQuarterTurn
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  by_cases hi : i = 0
  · simp only [if_pos hi]
    exact (PiLp.continuous_apply 2 _ 1).neg
  · simp only [if_neg hi]
    exact PiLp.continuous_apply 2 _ 0

private theorem exists_terminalWallDensity_bound {r : ℝ} (hr : 0 < r) (H J : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ y ∈ terminalClosedWallAnnulus r,
      ∀ G : HarmonicMaps.Gradient 2 5, ‖G‖ ≤ J →
        terminalWallDirichletDensity r H (fun _ => G) y ≤ C := by
  let A := terminalClosedWallAnnulus r ×ˢ closedBall (0 : HarmonicMaps.Gradient 2 5) J
  have hA : IsCompact A := (isCompact_terminalClosedWallAnnulus r).prod (isCompact_closedBall _ _)
  let f (z : Plane × HarmonicMaps.Gradient 2 5) := terminalWallDirichletDensity r H (fun _ => z.2) z.1
  have hY (p : Plane × HarmonicMaps.Gradient 2 5) (hp : p ∈ A) : ‖p.1‖ ≠ 0 := by
    have hL : r ≤ ‖p.1‖ := le_of_not_gt (fun h => hp.1.2 (mem_ball_zero_iff.2 h))
    exact (hr.trans_le hL).ne'
  have hn : ContinuousOn (fun p : Plane × HarmonicMaps.Gradient 2 5 => NormedSpace.normalize p.1) A :=
    (continuousOn_fst.norm.inv₀ hY).smul continuousOn_fst
  let V (u : (Plane × HarmonicMaps.Gradient 2 5) → Plane) (p : Plane × HarmonicMaps.Gradient 2 5) :=
    ∑ i : Fin 2, u p i • p.2 i
  have hV (u : (Plane × HarmonicMaps.Gradient 2 5) → Plane) (hu : ContinuousOn u A) :
      ContinuousOn (V u) A := continuousOn_finsetSum _ fun i _ =>
    (((PiLp.continuous_apply 2 _ i).comp_continuousOn hu).smul
      ((continuous_apply i).comp continuous_snd).continuousOn)
  have hF : ContinuousOn f A := by
    unfold f terminalWallDirichletDensity
    exact (continuousOn_const.div continuousOn_fst.norm hY).mul
      ((continuousOn_const.mul ((hV _ hn).norm.pow 2)).add
        (((continuousOn_fst.norm.div_const _).pow 2).mul
          ((hV _ (continuous_planarQuarterTurn.comp_continuousOn hn)).norm.pow 2)))
  obtain ⟨C, hC⟩ := hA.exists_bound_of_continuousOn hF
  refine ⟨max C 0, le_max_right _ _, fun y hy G hG => ?_⟩
  have h := hC (y, G) ⟨hy, mem_closedBall_zero_iff.2 hG⟩
  change ‖f (y, G)‖ ≤ C at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))

local instance terminalWallPlaneNorm : Norm (Plane →L[ℝ] Point) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ) (E := Plane) (F := Point)

local instance terminalWallTensorNorm : Norm (Point →L[ℝ] S0) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ) (E := Point) (F := S0)

private theorem norm_planarClassicalColumns_le (u : Plane → Ambient 5) (y : Plane) :
    ‖planarClassicalColumns u y‖ ≤ ‖fderiv ℝ u y‖ := by
  let L : Plane →L[ℝ] Ambient 5 := fderiv ℝ u y
  refine (pi_norm_le_iff_of_nonneg (ContinuousLinearMap.opNorm_nonneg L)).2 ?_
  intro i
  let v := EuclideanSpace.single i (1 : ℝ)
  have hv : ‖v‖ = 1 := by simp [v]
  exact (L.le_opNorm v).trans_eq (by rw [hv, mul_one])

private theorem norm_fderiv_triple_comp_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : F ≃ₗᵢ[ℝ] G) {Q : E → F} {A : Plane → E} {y : Plane}
    (hQ : DifferentiableAt ℝ Q (A y)) (hA : DifferentiableAt ℝ A y) :
    ‖fderiv ℝ (e ∘ Q ∘ A) y‖ ≤ ‖fderiv ℝ Q (A y)‖ * ‖fderiv ℝ A y‖ := by
  let DQ : E →L[ℝ] F := fderiv ℝ Q (A y)
  let DA : Plane →L[ℝ] E := fderiv ℝ A y
  let LQ : Plane →L[ℝ] F := DQ.comp DA
  have hF : fderiv ℝ (Q ∘ A) y = LQ := (hQ.hasFDerivAt.comp y hA.hasFDerivAt).fderiv
  change ‖fderiv ℝ (e ∘ (Q ∘ A)) y‖ ≤ ‖DQ‖ * ‖DA‖
  rw [LinearIsometryEquiv.comp_fderiv e, hF]
  exact (e.toLinearIsometry.norm_toContinuousLinearMap_comp (g := LQ)).le.trans (DQ.opNorm_comp_le DA)

theorem exists_uniform_terminalWall_energy (a : BulkCoefficients)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {r H s D : ℝ}
    (hr : 0 < r) (hH : 0 < H) (hD : 0 ≤ D)
    {Ω K : Set Point} (hΩ : IsOpen Ω) (hKO : K ⊆ Ω)
    (hLat : ∀ z ∈ Icc (-s) s, ∀ θ : NativeCircle, c + axisChart B (r • θ.val, z) ∈ K)
    (ε : ℕ → ElasticScale) {Q : ℕ → Point → S0} (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω)
    (hDensity : ∀ n x, x ∈ K → energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ D) :
    ∃ C ≥ (0 : ℝ), ∀ n {lo hi : ℝ}, -s ≤ lo → hi ≤ s → (hi - lo) / 2 = H →
      let w := frobeniusCoordinateEquiv ∘ Q n ∘ terminalWallChart B (cylinderTerminalCenter B c lo hi) r H
      terminalWallPenalizedEnergy a (ε n) r H w (planarClassicalColumns w) ≤ ENNReal.ofReal C := by
  let T := terminalWallChart B (0 : Point) r H
  have hT := contDiffOn_terminalWallChart B (0 : Point) r H
  have hNZ : terminalClosedWallAnnulus r ⊆ ({0}ᶜ : Set Plane) := by
    intro y hy
    exact norm_pos_iff.1 (hr.trans_le (le_of_not_gt fun h => hy.2 (mem_ball_zero_iff.2 h)))
  obtain ⟨J, hJ⟩ := (isCompact_terminalClosedWallAnnulus r).exists_bound_of_continuousOn
    ((hT.continuousOn_fderiv_of_isOpen isOpen_compl_singleton (by simp)).mono hNZ)
  let L := Real.sqrt (2 * D) * max J 0
  obtain ⟨C₀, hC₀, hC⟩ := exists_terminalWallDensity_bound hr H L
  let μ := (volume : Measure Plane).restrict (terminalWallAnnulus r).val
  have hμ : μ univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (terminalWallAnnulus_subset_closed r)).trans_lt
      (isCompact_terminalClosedWallAnnulus r).measure_lt_top
  let C := ((1 / 2 : ℝ) * C₀ + (2 * H / r) * D) * (μ univ).toReal
  have hC₁ : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC₁, ?_⟩
  intro n lo hi hlo hhi hEq w
  let F := terminalWallChart B (cylinderTerminalCenter B c lo hi) r H
  have hF0 : F = fun y => cylinderTerminalCenter B c lo hi + T y := by
    ext y
    simp only [F, T, terminalWallChart, zero_add]
  have hFdiff := contDiffOn_terminalWallChart B (cylinderTerminalCenter B c lo hi) r H
  have hI : lo ≤ hi := by linarith only [hEq, hH]
  have hFK : MapsTo F (terminalClosedWallAnnulus r) K := by
    intro y hy
    unfold F
    rw [← hEq]
    exact terminalWallChart_mem_lateral B c hr hI
      (fun z hz θ => hLat z ⟨hlo.trans hz.1, hz.2.trans hhi⟩ θ) hy
  have hData (y : Plane) (hy : y ∈ terminalClosedWallAnnulus r) :
      ‖planarClassicalColumns w y‖ ≤ L ∧
      (ε n : ℝ)⁻¹ ^ 2 * planarCoordinateBulkPotential a (w y) ≤ D := by
    have hyK := hFK hy
    have hyΩ := hKO hyK
    have hE := hDensity n (F y) hyK
    have hGrad₀ : 0 ≤ gradientNormSq (ClassicalGradient (Q n) (F y)) := by
      rw [gradientNormSq_eq_sum_norm_sq]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hB₀ : 0 ≤ (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q n (F y)) :=
      mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _)
    change (1 / 2 : ℝ) * gradientNormSq (ClassicalGradient (Q n) (F y)) +
      (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q n (F y)) ≤ D at hE
    have hQD : ‖fderiv ℝ (Q n) (F y)‖ ≤ Real.sqrt (2 * D) :=
      (fderiv_norm_le_sqrt_gradient (Q n) (F y)).trans (Real.sqrt_le_sqrt (by linarith only [hE, hB₀]))
    have hFD : ‖fderiv ℝ F y‖ ≤ max J 0 := by
      rw [hF0, fderiv_const_add]
      exact (hJ y hy).trans (le_max_left _ _)
    have hDiffQ := (((hQ n) _ hyΩ).contDiffAt (hΩ.mem_nhds hyΩ)).differentiableAt (by simp)
    have hDiffF := ((hFdiff y (hNZ hy)).contDiffAt
      (isOpen_compl_singleton.mem_nhds (hNZ hy))).differentiableAt (by simp)
    constructor
    · exact (norm_planarClassicalColumns_le w y).trans ((norm_fderiv_triple_comp_le
          frobeniusCoordinateEquiv hDiffQ hDiffF).trans (mul_le_mul hQD hFD (ContinuousLinearMap.opNorm_nonneg (fderiv ℝ F y)) (Real.sqrt_nonneg _)))
    · change (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm (frobeniusCoordinateEquiv (Q n (F y)))) ≤ D
      rw [frobeniusCoordinateEquiv.symm_apply_apply]
      linarith only [hE, hGrad₀]
  have hWallDir : (∫⁻ y, ENNReal.ofReal
      (terminalWallDirichletDensity r H (planarClassicalColumns w) y) ∂μ) ≤ ENNReal.ofReal C₀ * μ univ := by
    rw [← lintegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := volume) (terminalWallAnnulus r).property.measurableSet] with y hy
    have hy' := terminalWallAnnulus_subset_closed r hy
    exact ENNReal.ofReal_le_ofReal (hC y hy' _ (hData y hy').1)
  have hWallBulk : (∫⁻ y, ENNReal.ofReal (2 * H / ‖y‖) *
      ENNReal.ofReal ((ε n : ℝ)⁻¹ ^ 2 * planarCoordinateBulkPotential a (w y)) ∂μ) ≤
        ENNReal.ofReal ((2 * H / r) * D) * μ univ := by
    rw [← lintegral_const, ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * H / r)]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := volume) (terminalWallAnnulus r).property.measurableSet] with y hy
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by positivity) hr hy.1.le))
      (ENNReal.ofReal_le_ofReal (hData y (terminalWallAnnulus_subset_closed r hy)).2)
  calc
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) * (ENNReal.ofReal C₀ * μ univ) +
        ENNReal.ofReal ((2 * H / r) * D) * μ univ :=
      add_le_add (mul_le_mul_right hWallDir _) hWallBulk
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), ← add_mul,
        ← ENNReal.ofReal_add (mul_nonneg (by norm_num) hC₀) (by positivity),
        ← ENNReal.ofReal_toReal hμ.ne, ← ENNReal.ofReal_mul (by positivity)]


private theorem exists_terminalWallChart_preimage (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) {r lo hi z : ℝ} (hr : 0 < r) (hz : z ∈ Ioo lo hi) (θ : NativeCircle) :
    ∃ y ∈ (terminalWallAnnulus r).val,
      terminalWallChart B (cylinderTerminalCenter B c lo hi) r ((hi - lo) / 2) y =
        c + axisChart B (r • θ.val, z) := by
  let t := (z - lo) / (hi - lo)
  have hh : 0 < hi - lo := sub_pos.2 (hz.1.trans hz.2)
  have ht : 0 < t := div_pos (sub_pos.2 hz.1) hh
  have ht' : t < 1 := (div_lt_one hh).2 (sub_lt_sub_right hz.2 _)
  let ρ := r + r * t
  have hρ₁ : r < ρ := lt_add_of_pos_right _ (mul_pos hr ht)
  have hρ₂ : ρ < 2 * r := by
    have h := mul_lt_mul_of_pos_left ht' hr
    dsimp only [ρ]
    nlinarith only [h]
  have hρ : 0 < ρ := hr.trans hρ₁
  let y := ρ • θ.val
  have hy : ‖y‖ = ρ := by
    rw [show y = ρ • θ.val from rfl, norm_smul, Real.norm_of_nonneg hρ.le,
      mem_sphere_zero_iff_norm.1 θ.property, mul_one]
  have hyN : NormedSpace.normalize y = θ.val := (NormedSpace.normalize_smul_of_pos hρ _).trans
    (NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.1 θ.property))
  refine ⟨y, ⟨by rwa [hy], by rwa [hy]⟩, ?_⟩
  rw [terminalWallChart_eq_axisChart, hy, hyN]
  have hZ : lo + (hi - lo) / r * (ρ - r) = z := by
    dsimp only [ρ, t]
    field_simp [hr.ne', hh.ne']
    ring
  rw [hZ]

/-- The raw wall of the terminal data agrees with the original map on
the open-height physical wall. -/
theorem terminalSurface_wall_eq_original (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) {r lo hi : ℝ} (hr : 0 < r) {Q : Point → S0}
    (D : TerminalCylinderBoundaryData 5 r hr)
    (hWall : D.wall = frobeniusCoordinateEquiv ∘ Q ∘
      terminalWallChart B (cylinderTerminalCenter B c lo hi) r ((hi - lo) / 2)) :
    (fun p : NativeCircle × ℝ => terminalCylinderSurfaceValue B (cylinderTerminalCenter B c lo hi)
      ((hi - lo) / 2) D (c + axisChart B (r • p.1.val, p.2))) =ᵐ[cylinderSideTraceMeasure lo hi]
      fun p => frobeniusField Q (c + axisChart B (r • p.1.val, p.2)) := by
  filter_upwards [ae_cylinderSideTraceMeasure_height_mem lo hi] with p hz
  obtain ⟨y, hy, he⟩ := exists_terminalWallChart_preimage B c hr hz p.1
  have hH : 0 < (hi - lo) / 2 := half_pos (sub_pos.2 (hz.1.trans hz.2))
  rw [← he, terminalCylinderSurfaceValue_wall B _ hH D hy, hWall]
  rfl

/-- The weak boundary data of a terminal cylinder assembled from two
actual disks and the smooth original lateral wall. -/
theorem exists_terminalData_of_original_wall (a : BulkCoefficients) (ε : ElasticScale)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {r lo hi M : ℝ} (hr : 0 < r) (hI : lo ≤ hi) {Ω : Set Point} (hΩ : IsOpen Ω)
    {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hBand : ∀ z ∈ Icc lo hi, ∀ θ : NativeCircle,
      let x := c + axisChart B (r • θ.val, z)
      x ∈ Ω ∧ ‖Q x‖ ≤ M)
    (u v : Plane → Ambient 5) (Du Dv : Plane → HarmonicMaps.Gradient 2 5)
    (hu : MemW12 (ballDomain (0 : Plane) r) u Du) (hv : MemW12 (ballDomain (0 : Plane) r) v Dv)
    (huC : ContinuousOn u (closedPlanarRadialCollar (r / 2) r))
    (hvC : ContinuousOn v (closedPlanarRadialCollar (r / 2) r))
    (huM : ∀ᵐ y ∂volume.restrict (ball 0 r), ‖u y‖ ≤ M)
    (hvM : ∀ᵐ y ∂volume.restrict (ball 0 r), ‖v y‖ ≤ M)
    (hulo : ∀ θ : NativeCircle, u (r • θ.val) = frobeniusField Q (c + axisChart B (r • θ.val, lo)))
    (hvhi : ∀ θ : NativeCircle, v (r • θ.val) = frobeniusField Q (c + axisChart B (r • θ.val, hi))) :
    let H := (hi - lo) / 2
    let w := frobeniusCoordinateEquiv ∘ Q ∘ terminalWallChart B (cylinderTerminalCenter B c lo hi) r H
    ∃ D : TerminalCylinderBoundaryData 5 r hr, D.lower = u ∧ D.upper = v ∧ D.wall = w ∧ D.Bounded M ∧
      terminalCylinderSurfacePenalizedEnergy a ε H D =
        ENNReal.ofReal (planarWeakEnergy a (ε : ℝ) u Du r) +
        ENNReal.ofReal (planarWeakEnergy a (ε : ℝ) v Dv r) +
        terminalWallPenalizedEnergy a ε r H w (planarClassicalColumns w) := by
  let H := (hi - lo) / 2
  let F := terminalWallChart B (cylinderTerminalCenter B c lo hi) r H
  let w := frobeniusCoordinateEquiv ∘ Q ∘ F
  obtain ⟨hw, hwC⟩ := terminalWall_annulus_nativeGraph B c hr hI hΩ hQ (fun z hz θ => (hBand z hz θ).1)
  have hwC' : ContinuousOn w (closedPlanarRadialCollar r (2 * r)) := hwC.mono fun y hy =>
    ⟨mem_closedBall_zero_iff.2 hy.2, fun h => hy.1.not_gt (mem_ball_zero_iff.1 h)⟩
  have hL : ∀ θ : NativeCircle, u (r • θ.val) = w (r • θ.val) := by
    intro θ
    exact (hulo θ).trans (congrArg (frobeniusField Q) (terminalWall_radialRims B c (lo := lo) (hi := hi) hr θ).1.symm)
  have hU : ∀ θ : NativeCircle, v (r • θ.val) = w ((2 * r) • θ.val) := by
    intro θ
    exact (hvhi θ).trans (congrArg (frobeniusField Q) (terminalWall_radialRims B c (lo := lo) (hi := hi) hr θ).2.symm)
  obtain ⟨D, hDu, hDv, hDw, hDDu, hDDv, hDDw⟩ := exists_terminalCylinderBoundaryData_of_continuous_collars
    hr u v w Du Dv (planarClassicalColumns w) hu hv hw huC hvC hwC' (Eventually.of_forall hL) (Eventually.of_forall hU)
  have hwM : ∀ᵐ y ∂volume.restrict (terminalWallAnnulus r).val, ‖w y‖ ≤ M := by
    filter_upwards [ae_restrict_mem (μ := volume) (terminalWallAnnulus r).property.measurableSet] with y hy
    have hK := terminalWallChart_mem_lateral B c hr hI
      (K := {x | ‖Q x‖ ≤ M}) (fun z hz θ => (hBand z hz θ).2) (terminalWallAnnulus_subset_closed r hy)
    rw [show w y = frobeniusCoordinateEquiv (Q (F y)) from rfl, frobeniusCoordinateEquiv.norm_map]
    exact hK
  have hIu := planarCoordinateBulk_integrable_of_bound a r M hu.2.1 huM
  have hIv := planarCoordinateBulk_integrable_of_bound a r M hv.2.1 hvM
  have hBD : D.Bounded M := ⟨hDu.symm ▸ huM, hDv.symm ▸ hvM, hDw.symm ▸ hwM⟩
  refine ⟨D, hDu, hDv, hDw, hBD, ?_⟩
  rw [terminalCylinderSurfacePenalizedEnergy_eq_faces a ε H D (hDu.symm ▸ hIu) (hDv.symm ▸ hIv),
    hDu, hDv, hDw, hDDu, hDDv, hDDw]

end Thesis.MeasureGeometry

module

public import Thesis.Interpolation.MeshFaceNullHomotopy
public import Thesis.Interpolation.ProjectedMeshInnerFamily
public import Thesis.Interpolation.ProjectedInnerSurface
public import Thesis.Interpolation.SphericalShellMismatch

/-! Assembly of the penalized projection layer from the common physical mesh. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

private def shellTraceGradientConstant : ℝ := 9 * 204 ^ 2 * 65 ^ 3

private theorem shellTraceGradientConstant_pos : 0 < shellTraceGradientConstant := by
  unfold shellTraceGradientConstant
  positivity

private theorem shellTraceGradientConstant_ofReal :
    ENNReal.ofReal shellTraceGradientConstant = (9 * 204 ^ 2 * 65 ^ 3 : ℝ≥0∞) := by
  unfold shellTraceGradientConstant
  norm_num

private theorem exists_projectionLayer_from_filled_faces
    {a : BulkCoefficients} {B h C C₀ Cᵢ : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}
    (G : PenalizedSphereFaces a B h v hv) (hBound : ∀ θ, ‖v θ‖ ≤ B) (hSmall : h ≤ 1 / 32)
    (S : PenalizedCellSides G.grid C) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hCᵢ : 0 ≤ Cᵢ)
    (ε : ElasticScale) (hε : (ε : ℝ) ≤ h) {G₀ B₀ : ℝ} (hG₀ : 0 ≤ G₀) (hB₀ : 0 ≤ B₀)
    (hEdgeGrad : (∑ e, ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative e t‖ ^ 2) ≤ C₀ / h * G₀)
    (hEdgeBulk : (∑ e, ∫ t in Ioo (0 : ℝ) h, bulkPotential a (G.grid.trace e t)) ≤ C₀ / h * B₀)
    (hFaceGrad : (∑ f, ∫⁻ x in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (∑ i, ‖G.derivative f x i‖ ^ 2)) ≤
      ENNReal.ofReal (6 * C₀ * G₀))
    (hFaceBulk : (∑ f, ∫⁻ x in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (bulkPotential a (G.face f x))) ≤
      ENNReal.ofReal (6 * C₀ * B₀))
    (I : ∀ f : ShellCellIndex G.grid.level, ProjectedCellInnerFace G f)
    (hCollar : ∀ f, HasContinuousProjectedFaceCollar (I f)) :
    let E := (1 / 2 : ℝ) * G₀ + (ε : ℝ)⁻¹ ^ 2 * B₀
    let M := 6 * C₀ + Cᵢ + 2 * (C₀ * (1 + C ^ 2) + 2 * C * C₀)
    (ENNReal.ofReal (1 / 2 : ℝ) * ∑ f,
      HarmonicMaps.dirichletEnergy (I f).derivative (tensorGridOpenParameterBox 2 h).val) ≤ ENNReal.ofReal (Cᵢ * E) →
    ∃ (p : UnitTensorSphere → S0) (hp : MemSphereH1 p),
      (∀ᵐ θ ∂tensorSphereMeasure, p θ ∈ vacuum a) ∧
      (1 / 2 : ℝ) * sphereGradientEnergy p hp ≤ shellTraceGradientConstant * Cᵢ * E ∧
      sphereL2DifferenceSq v p ≤ (384 * M) * h * E ∧
      ∃ hRadius : 1 - h ≤ 1, ∃ W : SphereAnnularLayer (1 - h) 1 hRadius p v hp hv,
        energy a ε (radialAnnulus 0 (1 - h) 1) W.toFun W.gradient ≤
          ENNReal.ofReal (shellCellEnergyConstant * M * h * E) := by
  intro E M hInner
  obtain ⟨W⟩ := exists_penalizedFilledShell G hBound hSmall S I
  obtain ⟨P⟩ := exists_physicalShellCapClasses W hSmall
  obtain ⟨hp, hGrad⟩ := exists_projectedInnerCap_memSphereH1 P hSmall hCollar
  let p := P.innerTensor
  have hh := G.ht_pos
  have hRadius : 1 - h ≤ 1 := sub_le_self _ hh.le
  have hInnerTrace : P.trace ⟨1 - h, le_rfl, hRadius⟩ =
      hp.1.toLp (fun θ => frobeniusCoordinateEquiv (p θ)) := by
    symm
    apply Lp.ext
    filter_upwards [hp.1.coeFn_toLp] with θ hθ
    exact hθ.trans (frobeniusCoordinateEquiv.apply_symm_apply _)
  let L : SphereAnnularLayer (1 - h) 1 hRadius p v hp hv :=
    ⟨W.tensorField, W.tensorDerivative, W.tensor_memH1, P.trace, P.represents, hInnerTrace, P.outer⟩
  have hW := W.tensor_energy_le_h_input_channels hSmall S hC hC₀ hCᵢ ε hε hG₀ hB₀
    hEdgeGrad hEdgeBulk hFaceGrad hFaceBulk hInner
  have hFace := sum_physicalFacePenalizedEnergy_le_input_channels hSmall S hC hC₀ hCᵢ ε hε hG₀ hB₀
    hEdgeGrad hEdgeBulk hFaceGrad hFaceBulk hInner
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hMismatch := P.mismatch_le_h_face_energy hSmall ε (mul_nonneg hM hE) hFace
  refine ⟨p, hp, P.vacuum_ae, ?_, hMismatch.trans_eq (by ring), hRadius, L, hW⟩
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg shellTraceGradientConstant_pos.le hCᵢ) hE)).1
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    show shellTraceGradientConstant * Cᵢ * E = shellTraceGradientConstant * (Cᵢ * E) by ring,
    ENNReal.ofReal_mul shellTraceGradientConstant_pos.le]
  rw [← shellTraceGradientConstant_ofReal] at hGrad
  refine (mul_le_mul_right hGrad _).trans ?_
  rw [mul_left_comm (ENNReal.ofReal (1 / 2 : ℝ))]
  exact mul_le_mul_right hInner _

private theorem exists_projectionShell_small_scale :
    ∃ ε₀ ∈ Ioo (0 : ℝ) 1, ∀ (ε : ElasticScale), (ε : ℝ) < ε₀ →
      (ε : ℝ) ≤ projectionShellThickness ε ∧ projectionShellThickness ε ≤ 1 / 32 := by
  have hLim : Tendsto (fun e : ℝ => Real.sqrt e * Real.log e⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : 0 < (1 / 2 : ℝ))).neg
    simpa only [Function.comp_def, neg_zero, Real.log_inv, Real.sqrt_eq_rpow, mul_neg, mul_comm] using h
  obtain ⟨d, hd, hD⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hLim (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 32)))
  let e₀ := Real.exp (-160)
  have he₀ : 0 < e₀ := Real.exp_pos _
  have he₁ : e₀ < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  refine ⟨min d e₀, ⟨lt_min hd he₀, (min_le_right _ _).trans_lt he₁⟩, ?_⟩
  intro ε hε
  have hLog : 160 < Real.log ((ε : ℝ)⁻¹) := by
    have h := Real.log_lt_log ε.property.1 (hε.trans_le (min_le_right _ _))
    change Real.log (ε : ℝ) < Real.log (Real.exp (-160)) at h
    simpa only [Real.log_exp, Real.log_inv, lt_neg] using h
  have hmesh : projectionShellThickness ε < 1 / 32 :=
    hD ⟨ε.property.1, hε.trans_le (min_le_left _ _)⟩
  exact ⟨(projectionShell_planarScale ε hLog).1, hmesh.le⟩

/-- The actual projection layer follows from the planar logarithmic
lower bound and the indicated independent Sobolev chart laws. -/
theorem hasPenalizedProjectionLayer_of_planarLogarithmicBound (a : BulkCoefficients)
    (hAngle : External.SquareBoundaryAngularSobolev) (hArc : External.SquareBoundaryAngularMeasure)
    (hPull : External.UnitSquareDiskSobolevPullback) (hPush : External.UnitSquareDiskSobolevPushforward)
    (hCircular : External.PeriodicAngularSobolev) (hP : External.QuaternionSpherePoincare 2 (le_refl 2))
    (hLower : HasUnitDiskNontrivialLogLowerBound a) :
    HasPenalizedProjectionLayer a := by
  classical
  intro B hB
  obtain ⟨C₀, hC₀, hAtlas⟩ := exists_penalizedSphereFaces_with_face_budgets a B hB.le
  obtain ⟨δp, L, hδp, hδpR, hL, hProj⟩ := exists_projected_meshSquareBoundary a
  obtain ⟨δs, C, hδs, _, hC, hSides⟩ := exists_penalizedCellSides a
  obtain ⟨K, hK, hInner⟩ := exists_projectedCellInnerFamily a hAngle hPull hCircular hP
  let δ := min δp (min δs (vacuumRadius a / 4))
  have hδ : 0 < δ := lt_min hδp (lt_min hδs (div_pos (vacuumRadius_pos a) (by norm_num)))
  have hδ₁ : δ ≤ δp := min_le_left _ _
  have hδ₂ : δ ≤ δs := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₃ : δ ≤ vacuumRadius a / 4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨εedge, hεedge, hTube⟩ := exists_meshEdge_tube_threshold (B := B) a hC₀ hδ
  obtain ⟨η₀, εface, hη₀, hεface, hNull⟩ := exists_meshFace_null_threshold a hB.le hC₀
    (hδ₁.trans hδpR) hδ₃ hAngle hArc hPush hLower
  obtain ⟨εsize, hεsize, hScale⟩ := exists_projectionShell_small_scale
  let ε₀ := min εedge (min εface εsize)
  let Cᵢ := 2 * K * L * C₀
  let M := 6 * C₀ + Cᵢ + 2 * (C₀ * (1 + C ^ 2) + 2 * C * C₀)
  let C₁ := max 1 (max (shellTraceGradientConstant * Cᵢ) (max (384 * M) (shellCellEnergyConstant * M)))
  have hCi : 0 ≤ Cᵢ := by dsimp only [Cᵢ]; positivity
  have hC₁ : 1 ≤ C₁ := le_max_left _ _
  have hC₁₀ : 0 < C₁ := zero_lt_one.trans_le hC₁
  refine ⟨η₀, ε₀, C₁, hη₀, ⟨lt_min hεedge.1 (lt_min hεface.1 hεsize.1),
    (min_le_left _ _).trans_lt hεedge.2⟩, hC₁₀, ?_⟩
  intro η hη ε hε u hu huB hBudget
  let h := projectionShellThickness ε
  let G₀ := sphereGradientEnergy u hu
  let B₀ := ∫ θ : UnitTensorSphere, bulkPotential a (u θ) ∂tensorSphereMeasure
  let E := (1 / 2 : ℝ) * G₀ + (ε : ℝ)⁻¹ ^ 2 * B₀
  have hh : 0 < h := projectionShellThickness_pos ε
  have hG₀ : 0 ≤ G₀ := nonneg_sphereGradientEnergy u hu
  have hB₀ : 0 ≤ B₀ := integral_nonneg fun _ => bulkPotential_nonneg a _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hPE : E = spherePenalizedEnergy a ε u hu := by
    unfold spherePenalizedEnergy sphereScaledBulkEnergy
    rw [integral_const_mul]
  have hLog : 0 < Real.log ((ε : ℝ)⁻¹) := Real.log_pos ((one_lt_inv₀ ε.property.1).2 ε.property.2)
  have hENull : E ≤ η₀ * Real.log ((ε : ℝ)⁻¹) :=
    (hPE.trans_le hBudget).trans (mul_le_mul_of_nonneg_right hη.2.le hLog.le)
  have hETube : E ≤ Real.log ((ε : ℝ)⁻¹) :=
    hENull.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hη₀.2.le hLog.le)
  obtain ⟨hεh, hSmall⟩ := hScale ε (hε.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨v, hv, huv, hvB, _, G, hEg, hEb, hFg, hFb⟩ := hAtlas u hu huB hh hSmall
  have hT := hTube ε (hε.trans_le (min_le_left _ _)) G.grid hEg hEb hETube
  have hTp e t (ht : t ∈ Icc (0 : ℝ) h) : G.grid.trace e t ∈ vacuumTube a δp :=
    (show Metric.infDist (G.grid.trace e t) (vacuum a) < δ from hT e t ht).trans_le hδ₁
  have hTs e t (ht : t ∈ Icc (0 : ℝ) h) : G.grid.trace e t ∈ vacuumTube a δs :=
    (show Metric.infDist (G.grid.trace e t) (vacuum a) < δ from hT e t ht).trans_le hδ₂
  let J (f : ShellCellIndex G.grid.level) := Classical.choice (hProj G hh hTp f)
  have hJ := hNull ε (hε.trans_le ((min_le_right _ _).trans (min_le_left _ _))) G hG₀ hB₀ hvB
    hT hEg hEb hFg hFb hENull
  obtain ⟨I, hCollar, hIn⟩ := hInner G hSmall hL.le J (fun f => hJ f (J f))
  obtain ⟨S⟩ := hSides G.grid hh hTs
  have hCollar' (f : ShellCellIndex G.grid.level) : HasContinuousProjectedFaceCollar (I f) := by
    obtain ⟨U, hOpen, hMem, hCont, hVal⟩ := hCollar f
    exact HasContinuousProjectedFaceCollar.of_normalized_edges (I f) U hOpen hCont
      (fun i p x hx => hMem ⟨_, unitSquareSidePoint_mem_boundary i p hx⟩) hVal
  have hIn' : (ENNReal.ofReal (1 / 2 : ℝ) * ∑ f, HarmonicMaps.dirichletEnergy (I f).derivative
      (tensorGridOpenParameterBox 2 h).val) ≤ ENNReal.ofReal (Cᵢ * E) := by
    refine hIn.trans (ENNReal.ofReal_le_ofReal ?_)
    refine (mul_le_mul_of_nonneg_left hEg (by positivity : 0 ≤ K * L * h)).trans ?_
    rw [show K * L * h * (C₀ / h * G₀) = K * L * C₀ * G₀ by field_simp]
    have h2 : G₀ ≤ 2 * E := by dsimp only [E]; nlinarith only [mul_nonneg (sq_nonneg (ε : ℝ)⁻¹) hB₀]
    exact (mul_le_mul_of_nonneg_left h2 (by positivity)).trans_eq (by dsimp only [Cᵢ]; ring)
  obtain ⟨p, hp, hVac, hGrad, hMismatch, hr, W, hShell⟩ := exists_projectionLayer_from_filled_faces
    G hvB hSmall S hC.le hC₀.le hCi ε hεh hG₀ hB₀ hEg hEb hFg hFb I hCollar' hIn'
  have hOut : W.trace ⟨1, hr, le_rfl⟩ = hu.1.toLp (fun θ => frobeniusCoordinateEquiv (u θ)) :=
    W.outer_eq.trans (MemLp.toLp_congr hv.1 hu.1 (huv.symm.mono fun _ hθ => congrArg frobeniusCoordinateEquiv hθ))
  let V : SphereAnnularLayer (1 - h) 1 hr p u hp hu :=
    ⟨W.toFun, W.gradient, W.sobolev, W.trace, W.traceData, W.inner_eq, hOut⟩
  have hGradC : shellTraceGradientConstant * Cᵢ ≤ C₁ :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hMismatchC : 384 * M ≤ C₁ ^ 2 :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans
      (by nlinarith only [mul_nonneg (sub_nonneg.mpr hC₁) hC₁₀.le])
  have hShellC : shellCellEnergyConstant * M ≤ C₁ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨p, hp, hVac, ?_, ?_, hr, V, ?_⟩
  · exact hGrad.trans ((mul_le_mul_of_nonneg_right hGradC hE).trans_eq (congrArg (C₁ * ·) hPE))
  · have hEq : sphereL2DifferenceSq u p = sphereL2DifferenceSq v p :=
      integral_congr_ae (huv.mono fun θ hθ => congrArg (fun z : S0 => ‖z - p θ‖ ^ 2) hθ)
    refine hEq.le.trans (hMismatch.trans ?_)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMismatchC hh.le) hE).trans_eq
      (congrArg ((C₁ ^ 2 * h) * ·) hPE)
  · exact hShell.trans (ENNReal.ofReal_le_ofReal
      ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hShellC hh.le) hE).trans_eq
        (congrArg ((C₁ * h) * ·) hPE)))

end Thesis

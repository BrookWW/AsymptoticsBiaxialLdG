module

public import Thesis.Interpolation.MeshFaceDisk
public import Thesis.Foundation.ModifiedSpectralGap
import Thesis.Foundation.QuaternionSplittingEnergy
import Thesis.Interpolation.EdgeProjectionLayer
import Thesis.Interpolation.PenalizedRadialFill
import Thesis.StressEnergy

/-! The logarithmic disk lower bound consumed by the small-energy mesh. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

/-- The planar lower-bound specialization for nontrivial projected boundary
class and normalized boundary gap at least one half. -/
@[expose] def HasUnitDiskNontrivialLogLowerBound (a : BulkCoefficients) : Prop :=
  ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, 0 < ξ → ξ < 1 / 80 →
    ∀ (w : Plane → Ambient 5) (Dw : Plane → HarmonicMaps.Gradient 2 5),
      MemW12 (ballDomain (0 : Plane) 1) w Dw →
      (∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖frobeniusCoordinateEquiv.symm (w x)‖ ≤ B) →
      ∀ (b : C(NativeCircle, S0)) {s : ℝ}, ∀ (hs : s < 1) (H : VacuumBallTrace 2 s),
        RepresentsVacuumBallTrace w H →
        (∃ hb : MemLp (fun θ => frobeniusCoordinateEquiv (b θ)) 2 (unitBoundarySurface 2),
          H ⟨1, hs.le, le_rfl⟩ = hb.toLp _) →
        let β (t : ℝ) := b (circleNativeParam (t - Real.pi))
        AbsolutelyContinuousOnInterval β 0 (2 * Real.pi) →
        MemLp (deriv β) 2 (volume.restrict (Ioo 0 (2 * Real.pi))) →
        (∀ θ, (1 / 2 : ℝ) ≤ normalizedSpectralGap a (b θ)) →
        ∀ q : C(NativeCircle, vacuum a), (∀ θ, q θ = spectralVacuumPoint a (b θ)) →
          ¬ q.Homotopic (ContinuousMap.const NativeCircle (q nativeCircleLoopBase)) →
          (kappaStar a / 4) * Real.log ξ⁻¹ - C ≤
            ((1 / 2 : ℝ) * (∫ x in ball (0 : Plane) 1, hsNormSq (Dw x)) +
              ξ⁻¹ ^ 2 * (∫ x in ball (0 : Plane) 1, bulkPotential a (frobeniusCoordinateEquiv.symm (w x)))) +
            Real.log 80 * ((1 / 2 : ℝ) * (∫ t in Ioo 0 (2 * Real.pi), ‖deriv β t‖ ^ 2) +
              ξ⁻¹ ^ 2 * ∫ t in Ioo 0 (2 * Real.pi), bulkPotential a (β t))

private theorem meshFace_edge_sum_le_four {m : ℕ}
    (f : ↥(cubeBoundarySquares m)) (E : ↥(cubeBoundaryEdges m) → ℝ) (hE : ∀ e, 0 ≤ E e) :
    (∑ i : Fin 2, ∑ p : Bool, E (tensorSquareCoordinateEdge f i p)) ≤ 4 * ∑ e, E e := by
  classical
  calc
    _ ≤ ∑ _ : Fin 2, ∑ _ : Bool, ∑ e, E e := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro p _
      exact Finset.single_le_sum (fun e _ => hE e) (Finset.mem_univ (tensorSquareCoordinateEdge f i p))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]; ring

/-- At the source thickness scale, the effective planar logarithm is at
least half the original logarithm and the core parameter is admissible. -/
theorem projectionShell_planarScale (ε : ElasticScale)
    (hLog : 160 < Real.log ((ε : ℝ)⁻¹)) :
    let h := projectionShellThickness ε
    let ξ := (ε : ℝ) / (h / 2)
    (ε : ℝ) ≤ h ∧ 0 < ξ ∧ ξ < 1 / 80 ∧
    (1 / 2 : ℝ) * Real.log ((ε : ℝ)⁻¹) ≤ Real.log ξ⁻¹ := by
  intro h ξ
  let L := Real.log ((ε : ℝ)⁻¹)
  have hε := ε.property.1
  have hroot := Real.sqrt_pos.2 hε
  have hSq : Real.sqrt (ε : ℝ) ^ 2 = (ε : ℝ) := Real.sq_sqrt hε.le
  have hRootLe : Real.sqrt (ε : ℝ) ≤ 1 := (Real.sqrt_le_sqrt ε.property.2.le).trans_eq Real.sqrt_one
  have hh := projectionShellThickness_pos ε
  have hhDef : h = Real.sqrt (ε : ℝ) * L := rfl
  have hrHalf : 0 < h / 2 := half_pos hh
  have hE : (ε : ℝ) ≤ h := calc
    _ = Real.sqrt (ε : ℝ) * Real.sqrt (ε : ℝ) := hSq.symm.trans (pow_two _)
    _ ≤ Real.sqrt (ε : ℝ) * L :=
      mul_le_mul_of_nonneg_left (hRootLe.trans (by change 1 ≤ Real.log ((ε : ℝ)⁻¹); linarith only [hLog])) hroot.le
    _ = h := hhDef.symm
  have hξ : 0 < ξ := div_pos hε hrHalf
  have hξLt : ξ < 1 / 80 := by
    change (ε : ℝ) / (h / 2) < 1 / 80
    apply (div_lt_iff₀ hrHalf).2
    have hLess : (160 : ℝ) * Real.sqrt (ε : ℝ) < L :=
      (mul_le_mul_of_nonneg_left hRootLe (by norm_num)).trans_lt (by simpa only [mul_one] using hLog)
    have hStep : 160 * (ε : ℝ) < h := calc
      _ = Real.sqrt (ε : ℝ) * (160 * Real.sqrt (ε : ℝ)) := by nlinarith only [hSq]
      _ < Real.sqrt (ε : ℝ) * L := mul_lt_mul_of_pos_left hLess hroot
      _ = h := hhDef.symm
    linarith only [hStep]
  refine ⟨hE, hξ, hξLt, ?_⟩
  have hInv : ξ⁻¹ = (L / 2) * (Real.sqrt (ε : ℝ))⁻¹ := by
    change ((ε : ℝ) / (h / 2))⁻¹ = _
    calc
      _ = (h / 2) / (ε : ℝ) := inv_div _ _
      _ = ((Real.sqrt (ε : ℝ) * L) / 2) / Real.sqrt (ε : ℝ) ^ 2 :=
        congrArg₂ HDiv.hDiv (congrArg (· / 2) hhDef) hSq.symm
      _ = _ := by field_simp
  have hLogRoot : Real.log ((Real.sqrt (ε : ℝ))⁻¹) = (1 / 2 : ℝ) * L := by
    dsimp only [L]
    rw [Real.log_inv, Real.log_sqrt hε.le, Real.log_inv]
    ring
  have hL : 0 < L / 2 := by dsimp only [L]; linarith only [hLog]
  have hF : 0 ≤ Real.log (L / 2) := Real.log_nonneg (by dsimp only [L]; linarith only [hLog])
  rw [hInv, Real.log_mul hL.ne' (inv_ne_zero hroot.ne'), hLogRoot]
  linarith only [hF]

/-- A genuine tubular boundary meets the planar gap requirement uniformly. -/
theorem half_le_normalizedSpectralGap_of_vacuumDistance_le (a : BulkCoefficients) (A : S0)
    (hDist : Metric.infDist A (vacuum a) ≤ vacuumRadius a / 4) :
    (1 / 2 : ℝ) ≤ normalizedSpectralGap a A := by
  have h := orderedEigenvalue_gaps_ge_half_of_vacuumDistance_le a A hDist
  have hr := vacuumRadius_pos a
  unfold normalizedSpectralGap
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ hr).2
  convert le_min h.1 h.2 using 1
  ring

/-- The joint budget forces every original closed edge into the selected
material tube, uniformly for sufficiently small scales. -/
theorem exists_meshEdge_tube_threshold (a : BulkCoefficients) {B C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) :
    ∃ ε₀ ∈ Ioo (0 : ℝ) 1, ∀ (ε : ElasticScale), (ε : ℝ) < ε₀ →
      let h := projectionShellThickness ε
      ∀ {v : UnitTensorSphere → S0} {hv : MemSphereH1 v} (G : PenalizedSphereGrid a B h v hv)
        {G₀ B₀ : ℝ},
        (∑ e, ∫ t in Ioo (0 : ℝ) h, ‖G.derivative e t‖ ^ 2) ≤ C / h * G₀ →
        (∑ e, ∫ t in Ioo (0 : ℝ) h, bulkPotential a (G.trace e t)) ≤ C / h * B₀ →
        (1 / 2 : ℝ) * G₀ + (ε : ℝ)⁻¹ ^ 2 * B₀ ≤ Real.log ((ε : ℝ)⁻¹) →
        ∀ e t, t ∈ Icc 0 h → G.trace e t ∈ vacuumTube a δ := by
  classical
  obtain ⟨ε₀, hε₀, hTube⟩ := exists_edge_vacuumTube_threshold a B (k := 1) (G := C) one_pos hδ
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε h v hv G G₀ B₀ hG hB hE e
  have hh : 0 < h := projectionShellThickness_pos ε
  have hGD : IntegrableOn (fun t => ‖G.derivative e t‖ ^ 2) (Ioo (0 : ℝ) h) :=
    (G.derivative_memLp e).integrable_norm_pow (by norm_num)
  have hCont : ContinuousOn (G.trace e) (Icc 0 h) :=
    (uIcc_of_le hh.le) ▸ (G.trace_ac e).continuousOn
  have hBD : IntegrableOn (fun t => bulkPotential a (G.trace e t)) (Ioo (0 : ℝ) h) :=
    ((contDiff_bulkPotential a).continuous.comp_continuousOn hCont).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hG' : (∫ t in Ioo (0 : ℝ) h, ‖G.derivative e t‖ ^ 2) ≤ C / h * G₀ :=
    (Finset.single_le_sum (fun _ _ => integral_nonneg fun _ => sq_nonneg _) (Finset.mem_univ e)).trans hG
  have hB' : (∫ t in Ioo (0 : ℝ) h, bulkPotential a (G.trace e t)) ≤ C / h * B₀ :=
    (Finset.single_le_sum (fun _ _ => integral_nonneg fun _ => bulkPotential_nonneg a _) (Finset.mem_univ e)).trans hB
  apply hTube ε hε (l := 0) (r := h) (by simpa only [one_mul, sub_zero] using (le_refl h))
    (G.trace_ac e) (G.derivative_memLp e) (G.trace_increment e)
    ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => G.trace_bound e t (Ioo_subset_Icc_self ht))
  rw [integral_add (hGD.const_mul _) (hBD.const_mul _), integral_const_mul, integral_const_mul]
  calc
    _ ≤ (1 / 2 : ℝ) * (C / h * G₀) + (ε : ℝ)⁻¹ ^ 2 * (C / h * B₀) :=
      add_le_add (mul_le_mul_of_nonneg_left hG' (by norm_num)) (mul_le_mul_of_nonneg_left hB' (sq_nonneg _))
    _ = (C / h) * ((1 / 2 : ℝ) * G₀ + (ε : ℝ)⁻¹ ^ 2 * B₀) := by ring
    _ ≤ (C / h) * Real.log ((ε : ℝ)⁻¹) := mul_le_mul_of_nonneg_left hE (div_nonneg hC.le hh.le)
    _ = _ := by ring

/-- The physical face and its edge loop both inherit the original angular
and bulk energy channels after similarity and the planar chart. -/
private theorem face_disk_budget (a : BulkCoefficients) {B h C₀ D A G₀ B₀ : ℝ}
    {v : UnitTensorSphere → S0} {hv : MemSphereH1 v} {G : PenalizedSphereFaces a B h v hv}
    (f : ↥(cubeBoundarySquares G.grid.level))
    (hC₀ : 0 < C₀) (hD : 0 < D) (hA : 0 < A) (hG₀ : 0 ≤ G₀) (hB₀ : 0 ≤ B₀)
    (hEgrad : (∑ e, ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative e t‖ ^ 2) ≤ C₀ / h * G₀)
    (hEbulk : (∑ e, ∫ t in Ioo (0 : ℝ) h, bulkPotential a (G.grid.trace e t)) ≤ C₀ / h * B₀)
    (hFgrad : (∑ g, ∫⁻ x in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (∑ i, ‖G.derivative g x i‖ ^ 2)) ≤
      ENNReal.ofReal (6 * C₀ * G₀))
    (hFbulk : (∑ g, ∫⁻ x in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (bulkPotential a (G.face g x))) ≤
      ENNReal.ofReal (6 * C₀ * B₀))
    {w : Plane → Ambient 5} {Dw : Plane → HarmonicMaps.Gradient 2 5}
    (hw : MemW12 (ballDomain (0 : Plane) 1) w Dw)
    (hwB : ∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖frobeniusCoordinateEquiv.symm (w x)‖ ≤ B)
    {β : ℝ → S0}
    (hDiskGrad : (∫ x in ball (0 : Plane) 1, hsNormSq (Dw x)) ≤
      D * ∫ x in (tensorGridOpenParameterBox 2 h).val, ∑ i, ‖G.derivative f x i‖ ^ 2)
    (hDiskBulk : (∫⁻ x in ball (0 : Plane) 1, ENNReal.ofReal (bulkPotential a (frobeniusCoordinateEquiv.symm (w x)))) ≤
      ENNReal.ofReal (9 * (h / 2)⁻¹ ^ 2) *
        ∫⁻ x in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (bulkPotential a (G.face f x)))
    (hArcGrad : (∫ t in Ioo 0 (2 * Real.pi), ‖deriv β t‖ ^ 2) ≤ A * (h / 2) * meshSquareEdgeDerivativeEnergy G f)
    (hArcBulk : (∫ t in Ioo 0 (2 * Real.pi), bulkPotential a (β t)) ≤ A * (h / 2)⁻¹ * meshSquareEdgeBulkEnergy G f)
    (ε : ElasticScale) :
    let ξ := (ε : ℝ) / (h / 2)
    ((1 / 2 : ℝ) * (∫ x in ball (0 : Plane) 1, hsNormSq (Dw x)) +
      ξ⁻¹ ^ 2 * (∫ x in ball (0 : Plane) 1, bulkPotential a (frobeniusCoordinateEquiv.symm (w x)))) +
    Real.log 80 * ((1 / 2 : ℝ) * (∫ t in Ioo 0 (2 * Real.pi), ‖deriv β t‖ ^ 2) +
      ξ⁻¹ ^ 2 * ∫ t in Ioo 0 (2 * Real.pi), bulkPotential a (β t)) ≤
      (6 * C₀ * max D 9 + 2 * A * C₀ * Real.log 80) *
        ((1 / 2 : ℝ) * G₀ + (ε : ℝ)⁻¹ ^ 2 * B₀) := by
  classical
  intro ξ
  let U := (tensorGridOpenParameterBox 2 h).val
  let Ω := ball (0 : Plane) 1
  let Fg (x : Plane) := ∑ i, ‖G.derivative f x i‖ ^ 2
  let Fb (x : Plane) := bulkPotential a (G.face f x)
  let Bb (x : Plane) := bulkPotential a (frobeniusCoordinateEquiv.symm (w x))
  let M := 6 * C₀ * max D 9
  have hh := G.ht_pos
  have hξPow : ξ⁻¹ ^ 2 = (h / 2) ^ 2 * (ε : ℝ)⁻¹ ^ 2 := by
    dsimp only [ξ]
    rw [inv_div, div_eq_mul_inv, mul_pow]
  have hGF : (∫ x in U, Fg x) ≤ 6 * C₀ * G₀ := by
    have hEq : (∫⁻ x in U, ENNReal.ofReal (Fg x)) = ENNReal.ofReal (∫ x in U, Fg x) := by
      apply (ofReal_integral_eq_lintegral_ofReal ?_ (ae_of_all _ fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
      change IntegrableOn Fg (tensorGridOpenParameterBox 2 h).val
      simpa only [Fg, hsNormSq, frobeniusCoordinateEquiv.norm_map] using (G.face_memW12 f).integrable_hsNormSq
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 6 * C₀ * G₀)).1
    rw [← hEq]
    exact (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ f)).trans hFgrad
  have hStepB : (∫⁻ x in U, ENNReal.ofReal (Fb x)) ≤ ENNReal.ofReal (6 * C₀ * B₀) :=
    (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ f)).trans hFbulk
  have hBb : IntegrableOn Bb Ω := by
    letI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.2 measure_ball_ne_top
    exact integrable_bulkPotential_of_ae_norm_bound a B
      (frobeniusCoordinateEquiv.symm.continuous.comp_aestronglyMeasurable hw.2.1.1) hwB
  have hUB : (∫ x in Ω, Bb x) ≤ (9 * (h / 2)⁻¹ ^ 2) * (6 * C₀ * B₀) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ (9 * (h / 2)⁻¹ ^ 2) * (6 * C₀ * B₀))).1
    rw [ofReal_integral_eq_lintegral_ofReal hBb (ae_of_all _ fun _ => bulkPotential_nonneg a _),
      ENNReal.ofReal_mul (by positivity : 0 ≤ 9 * (h / 2)⁻¹ ^ 2)]
    exact hDiskBulk.trans (mul_le_mul_right hStepB _)
  have hUG : (∫ x in Ω, hsNormSq (Dw x)) ≤ M * G₀ := calc
    _ ≤ D * (∫ x in U, Fg x) := hDiskGrad
    _ ≤ D * (6 * C₀ * G₀) := mul_le_mul_of_nonneg_left hGF hD.le
    _ ≤ max D 9 * (6 * C₀ * G₀) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = _ := by dsimp only [M]; ring
  have hcanc : (h / 2) ^ 2 * (h / 2)⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ (half_pos hh).ne', one_pow]
  have hUB' : ξ⁻¹ ^ 2 * (∫ x in Ω, Bb x) ≤ M * ((ε : ℝ)⁻¹ ^ 2 * B₀) := calc
    _ ≤ ξ⁻¹ ^ 2 * ((9 * (h / 2)⁻¹ ^ 2) * (6 * C₀ * B₀)) := mul_le_mul_of_nonneg_left hUB (sq_nonneg _)
    _ = 6 * C₀ * 9 * ((ε : ℝ)⁻¹ ^ 2 * B₀) := by
      rw [hξPow]
      linear_combination ((ε : ℝ)⁻¹ ^ 2 * (9 * (6 * C₀ * B₀))) * hcanc
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)) (by positivity)
  have hEdgeG : meshSquareEdgeDerivativeEnergy G f ≤ 4 * (C₀ / h * G₀) :=
    (meshFace_edge_sum_le_four f (fun e => ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative e t‖ ^ 2)
      (fun _ => integral_nonneg fun _ => sq_nonneg _)).trans (mul_le_mul_of_nonneg_left hEgrad (by norm_num))
  have hEdgeB : meshSquareEdgeBulkEnergy G f ≤ 4 * (C₀ / h * B₀) :=
    (meshFace_edge_sum_le_four f (fun e => ∫ t in Ioo (0 : ℝ) h, bulkPotential a (G.grid.trace e t))
      (fun _ => integral_nonneg fun _ => bulkPotential_nonneg a _)).trans (mul_le_mul_of_nonneg_left hEbulk (by norm_num))
  have hArG : (∫ t in Ioo 0 (2 * Real.pi), ‖deriv β t‖ ^ 2) ≤ (2 * A * C₀) * G₀ :=
    hArcGrad.trans ((mul_le_mul_of_nonneg_left hEdgeG (by positivity)).trans_eq (by field_simp; ring))
  have hArB : ξ⁻¹ ^ 2 * (∫ t in Ioo 0 (2 * Real.pi), bulkPotential a (β t)) ≤
      (2 * A * C₀) * ((ε : ℝ)⁻¹ ^ 2 * B₀) := calc
    _ ≤ ξ⁻¹ ^ 2 * ((A * (h / 2)⁻¹) * (4 * (C₀ / h * B₀))) :=
      mul_le_mul_of_nonneg_left (hArcBulk.trans (mul_le_mul_of_nonneg_left hEdgeB (by positivity))) (sq_nonneg _)
    _ = _ := by rw [hξPow]; field_simp; ring
  refine (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hUG (by norm_num)) hUB')
    (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hArG (by norm_num)) hArB)
      (Real.log_nonneg (by norm_num)))).trans_eq ?_
  dsimp only [M]
  ring

/-- Every projected mesh boundary is contractible under the logarithmic
small-energy threshold and the actual planar logarithmic comparison. -/
theorem exists_meshFace_null_threshold (a : BulkCoefficients) {B C₀ δ : ℝ}
    (hB : 0 ≤ B) (hC₀ : 0 < C₀) (hδ : δ ≤ (vacuumTubularProjection a).radius)
    (hδr : δ ≤ vacuumRadius a / 4)
    (hAngle : External.SquareBoundaryAngularSobolev) (hArc : External.SquareBoundaryAngularMeasure)
    (hDisk : External.UnitSquareDiskSobolevPushforward) (hLower : HasUnitDiskNontrivialLogLowerBound a) :
    ∃ η₀ ε₀ : ℝ, η₀ ∈ Ioo (0 : ℝ) 1 ∧ ε₀ ∈ Ioo (0 : ℝ) 1 ∧
      ∀ (ε : ElasticScale), (ε : ℝ) < ε₀ →
        let h := projectionShellThickness ε
        ∀ {v : UnitTensorSphere → S0} {hv : MemSphereH1 v} (G : PenalizedSphereFaces a B h v hv)
          {G₀ B₀ : ℝ}, 0 ≤ G₀ → 0 ≤ B₀ → (∀ θ, ‖v θ‖ ≤ B) →
          (∀ e t, t ∈ Icc 0 h → G.grid.trace e t ∈ vacuumTube a δ) →
          (∑ e, ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative e t‖ ^ 2) ≤ C₀ / h * G₀ →
          (∑ e, ∫ t in Ioo (0 : ℝ) h, bulkPotential a (G.grid.trace e t)) ≤ C₀ / h * B₀ →
          (∑ f, ∫⁻ x in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (∑ i, ‖G.derivative f x i‖ ^ 2)) ≤
            ENNReal.ofReal (6 * C₀ * G₀) →
          (∑ f, ∫⁻ x in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (bulkPotential a (G.face f x))) ≤
            ENNReal.ofReal (6 * C₀ * B₀) →
          (1 / 2 : ℝ) * G₀ + (ε : ℝ)⁻¹ ^ 2 * B₀ ≤ η₀ * Real.log ((ε : ℝ)⁻¹) →
          ∀ (f : ↥(cubeBoundarySquares G.grid.level)) {L : ℝ} (J : ProjectedMeshSquareBoundary G f L),
            let q := squareVacuumBoundaryLoop a J.boundary
            q.Homotopic (ContinuousMap.const NativeCircle (q nativeCircleLoopBase)) := by
  classical
  obtain ⟨C, hC, hLower⟩ := hLower B hB
  obtain ⟨D, hD, hDisk⟩ := exists_meshFaceDisk (a := a) hDisk
  obtain ⟨A, hA, hAngle⟩ := OriginalMeshSquareBoundary.circle_angular_estimates (a := a) hAngle hArc
  let K := 6 * C₀ * max D 9 + 2 * A * C₀ * Real.log 80
  let κ := kappaStar a
  have hκ : 0 < κ := kappaStar_pos a
  have hL : 0 < Real.log 80 := Real.log_pos (by norm_num)
  have hM : 0 < 6 * C₀ * max D 9 := mul_pos (mul_pos (by norm_num) hC₀) (hD.trans_le (le_max_left _ _))
  have hK : 0 < K := add_pos hM (by positivity)
  let m := max 160 (32 * C / κ)
  have hm : 0 < m := (by norm_num : (0 : ℝ) < 160).trans_le (le_max_left _ _)
  let ε₀ := Real.exp (-m)
  let η₀ := min (1 / 2 : ℝ) (κ / (32 * K))
  have hη : η₀ ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_min (by norm_num) (div_pos hκ (by positivity)), (min_le_left _ _).trans_lt (by norm_num)⟩
  have hε₀ : ε₀ ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (neg_lt_zero.2 hm)⟩
  refine ⟨η₀, ε₀, hη, hε₀, ?_⟩
  intro ε hSmall h v hv G G₀ B₀ hG₀ hB₀ hvB hTube hEgrad hEbulk hFgrad hFbulk hBudget f C' J q
  let ℓ := Real.log ((ε : ℝ)⁻¹)
  have hℓ : m < ℓ := by
    have ht := Real.strictMonoOn_log ε.property.1 hε₀.1 hSmall
    change Real.log (ε : ℝ) < Real.log (Real.exp (-m)) at ht
    rw [Real.log_exp] at ht
    simpa only [ℓ, Real.log_inv, lt_neg] using ht
  have hℓ' : 160 < ℓ := (le_max_left _ _).trans_lt hℓ
  have hErr : C < (κ / 32) * ℓ := by
    have hR : 32 * C / κ < ℓ := (le_max_right _ _).trans_lt hℓ
    have hProd := (div_lt_iff₀ hκ).1 hR
    nlinarith only [hProd]
  let ξ := (ε : ℝ) / (h / 2)
  obtain ⟨_, hξ, hξSmall, hξLog⟩ := projectionShell_planarScale ε hℓ'
  obtain ⟨P⟩ := exists_originalMeshSquareBoundary G f
  obtain ⟨w, Dw, s, hs, H, _, _, hw, hwB, hRep, hTrace, hDiskGrad, hDiskBulk⟩ := hDisk hvB P
  obtain ⟨hAC, hSob, hArcGrad, hArcBulk⟩ := hAngle P
  have hGap : ∀ θ, (1 / 2 : ℝ) ≤ normalizedSpectralGap a (P.circle θ) :=
    P.forall_circle (p := fun A => (1 / 2 : ℝ) ≤ normalizedSpectralGap a A)
      fun i p t ht => half_le_normalizedSpectralGap_of_vacuumDistance_le a _
      ((show infDist (G.grid.trace (tensorSquareCoordinateEdge f i p) t) (vacuum a) < δ
        from hTube _ _ ht).le.trans hδr)
  have hProj (θ : NativeCircle) : q θ = spectralVacuumPoint a (P.circle θ) :=
    (P.circle_projection J hδ hTube θ).symm
  by_contra hNull
  have hMin := hLower ξ hξ hξSmall w Dw hw hwB P.circle hs H hRep hTrace hAC hSob hGap q hProj hNull
  have hUpper := face_disk_budget a f hC₀ hD hA hG₀ hB₀ hEgrad hEbulk hFgrad hFbulk
    hw hwB hDiskGrad hDiskBulk hArcGrad hArcBulk ε
  let E := (1 / 2 : ℝ) * G₀ + (ε : ℝ)⁻¹ ^ 2 * B₀
  have hLogξ : (1 / 2 : ℝ) * ℓ ≤ Real.log ξ⁻¹ := hξLog
  have hLo : κ / 8 * ℓ - C ≤ K * E := calc
    _ = κ / 4 * ((1 / 2 : ℝ) * ℓ) - C := by ring
    _ ≤ κ / 4 * Real.log ξ⁻¹ - C :=
      sub_le_sub_right (mul_le_mul_of_nonneg_left hLogξ (by positivity)) _
    _ ≤ _ := hMin.trans hUpper
  have hUp : K * E ≤ (κ / 32) * ℓ := calc
    _ ≤ K * (η₀ * ℓ) := mul_le_mul_of_nonneg_left hBudget hK.le
    _ ≤ K * ((κ / (32 * K)) * ℓ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith only [hℓ'])) hK.le
    _ = _ := by field_simp
  have hκℓ : 0 < κ * ℓ := mul_pos hκ (by linarith only [hℓ'])
  nlinarith only [hLo, hUp, hErr, hκℓ]

end Thesis

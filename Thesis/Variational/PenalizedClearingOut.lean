module

public import Thesis.Variational.ProjectionLayerClearingComparison
public import Thesis.Variational.AffinePenalizedEnergy
import Thesis.Variational.PenalizedGoodRadii
import Thesis.MeasureGeometry.ClearingRadius
import HarmonicMaps.Analysis.AffineBallMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Logarithmic clearing-out for the quadratic elastic energy. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set Thesis.MeasureGeometry
open scoped ENNReal Matrix.Norms.Frobenius

namespace Thesis

private theorem exists_scaled_outer_trace {u : Point → S0} (c : Point) {r ρ : ℝ}
    (hρ : 0 < ρ) (hrρ : r / 2 < ρ) (hρr : ρ < r) (H : RadialL2Trace (r / 2) r)
    (hH : RepresentsRadialL2Trace c u H) :
    ∃ L : RadialL2Trace 1 ((1 + r / ρ) / 2),
      RepresentsRadialL2Trace 0 (fun x => u (c + ρ • x)) L ∧
      L ⟨1, le_rfl, by
        have h : 1 < r / ρ := (lt_div_iff₀ hρ).2 (by simpa using hρr)
        linarith⟩ = H ⟨ρ, hrρ.le, hρr.le⟩ := by
  let R := (1 + r / ρ) / 2
  have hR : 1 < R := by
    have h : 1 < r / ρ := (lt_div_iff₀ hρ).2 (by simpa using hρr)
    dsimp only [R]
    linarith
  have hScaled : ρ * R = (ρ + r) / 2 := by dsimp only [R]; field_simp
  have hUp : ρ * R ≤ r := by rw [hScaled]; linarith
  have hT (s : Icc (1 : ℝ) R) : ρ * s.val ∈ Icc (r / 2) r := ⟨
    hrρ.le.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left s.property.1 hρ.le),
    (mul_le_mul_of_nonneg_left s.property.2 hρ.le).trans hUp⟩
  let T : C(Icc (1 : ℝ) R, Icc (r / 2) r) :=
    ⟨fun s => ⟨ρ * s.val, hT s⟩, (continuous_const.mul continuous_subtype_val).subtype_mk hT⟩
  let L := H.comp T
  have hRaw : RepresentsRadialL2Trace 0 (fun x => u (c + ρ • x)) L := by
    have hPull := ((volume : Measure ℝ).quasiMeasurePreserving_smul hρ.ne').ae hH
    unfold RepresentsRadialL2Trace at hPull ⊢
    dsimp only [smul_eq_mul] at hPull
    filter_upwards [hPull] with s hs hsr
    have hActual : ρ * s ∈ Ioo (r / 2) r := by
      refine ⟨hrρ.trans (by simpa only [mul_one] using mul_lt_mul_of_pos_left hsr.1 hρ), ?_⟩
      exact (mul_lt_mul_of_pos_left hsr.2 hρ).trans_le hUp
    obtain ⟨hp, hEq⟩ := hs hActual
    have hFun : (fun θ : UnitTensorSphere => frobeniusField (fun x => u (c + ρ • x)) (0 + s • θ.val)) =
        (fun θ : UnitTensorSphere => frobeniusField u (c + (ρ * s) • θ.val)) := by
      funext θ
      simp only [frobeniusField, zero_add, smul_smul]
    rw [hFun]
    exact ⟨hp, hEq⟩
  refine ⟨L, hRaw, ?_⟩
  change H (T ⟨1, le_rfl, hR.le⟩) = _
  apply congrArg H
  exact Subtype.ext (mul_one ρ)

/-- The quadratic elastic energy satisfies the manuscript's logarithmic
clearing-out bound relative to the verified-data projection-layer interface. -/
theorem exists_logarithmic_clearing_out_quadratic (a : BulkCoefficients)
    (hProj : HasPenalizedProjectionLayer a) (hDense : External.SmoothVacuumSphereDensity a)
    (hP : External.QuaternionSpherePoincare 3 (by decide : 2 ≤ 3)) (M : ℝ) (hM : 0 < M) :
    ∃ η₀ δ C : ℝ, 0 < η₀ ∧ δ ∈ Ioo 0 1 ∧ 0 < C ∧
      ∀ (ε : ElasticScale) {Ω : Set Point} (_hΩ : IsOpen Ω) (c : Point) (r : ℝ),
        0 < r → closedBall c r ⊆ Ω → ∀ (u : Point → S0) (D : Point → Gradient),
        IsLocalEnergyMinimizer a ε Ω u D →
        (∀ᵐ x ∂volume.restrict (ball c r), ‖u x‖ ≤ M) → (ε : ℝ) ≤ δ * r →
        energy a ε (ball c r) u D ≤ ENNReal.ofReal (η₀ * r * Real.log (r / (ε : ℝ))) →
        energy a ε (ball c (r / 2)) u D ≤ ENNReal.ofReal (C * r) := by
  obtain ⟨η, ε₁, C₀, hη, hε₁, hC₀, hComparison⟩ :=
    exists_unitBall_sublinear_energy_comparison a hProj hDense hP M hM
  let η₀ := η / 8
  let δ := min (1 / 4 : ℝ) (ε₁ / 4)
  have hη₀ : 0 < η₀ := div_pos hη.1 (by norm_num)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε₁.1 (by norm_num))
  have hδ₁ : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨η₀, δ, C₀ + 4 * C₀ ^ 2, hη₀, ⟨hδ, hδ₁⟩, by positivity, ?_⟩
  intro ε Ω hΩ c r hr hClosed u D hLoc hB hε hEnergy
  have hεquarter : (ε : ℝ) ≤ r / 4 := hε.trans (calc
    _ ≤ (1 / 4 : ℝ) * r := mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le
    _ = r / 4 := by ring)
  have hEFin : energy a ε (ball c r) u D ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEnergy
  have hU : MemH1 (ball c r) u D := hLoc.1 _ isOpen_ball (by
    unfold CompactlyContained
    rw [closure_ball _ hr.ne']
    exact ⟨isCompact_closedBall _ _, hClosed⟩)
  let F := penalizedBallIntegral a ε c u D
  let A := η₀ * Real.log (r / (ε : ℝ))
  have hLog : 0 < Real.log (r / (ε : ℝ)) := Real.log_pos ((one_lt_div ε.property.1).2 (by linarith))
  have hA : 0 < A := mul_pos hη₀ hLog
  obtain ⟨g, hg, hgI, hAC, hMono, hMass, hF, hD⟩ := exists_penalizedBall_coarea_density a ε c hr hU hEFin
  have hMass' : (∫ t in Ioo (r / 2) r, g t) ≤ r * A := by
    apply hMass.trans
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hr.le hA.le)).1
    rw [← hF r ⟨hr.le, le_rfl⟩]
    rw [show r * A = η₀ * r * Real.log (r / (ε : ℝ)) by dsimp only [A]; ring]
    exact hEnergy
  let S := Ioo (r / 2) r ∩ {t | g t ≤ 4 * A}
  have hS : MeasurableSet S := measurableSet_Ioo.inter (measurableSet_le hg measurable_const)
  have hSsub : S ⊆ Ioo (r / 2) r := inter_subset_left
  have hSvol : r / 4 ≤ volume.real S := goodRadiusSet_measureReal_ge hr hA hg hgI
    (hD.mono fun _ h => h.2.2) hMass'
  obtain ⟨H, hH, _⟩ := existsUnique_radialL2Trace_of_memH1Loc hΩ hLoc.1 c
    (by linarith : 0 < r / 2) (by linarith : r / 2 < r) hClosed
  have hSub : Ioo (r / 2) r ⊆ Ioo 0 r := fun _ ht => ⟨(by linarith : 0 < r / 2).trans ht.1, ht.2⟩
  have hSlice := ae_restrict_of_ae_restrict_of_subset hSub
    (ae_scaled_spherePenalizedEnergy_le_coarea a ε hΩ c hr hClosed hLoc.1 M hB)
  have hGood : ∀ᵐ ρ ∂volume.restrict (Ioo (r / 2) r), ρ ∈ S → F ρ ≤ C₀ * r * (Real.sqrt (g ρ) + 1) := by
    filter_upwards [hSlice, hD, hH.filter_mono (ae_mono Measure.restrict_le_self)] with ρ hSρ hDρ hHρ
    intro hGoodρ
    have hρ : ρ ∈ Ioo (r / 2) r := hGoodρ.1
    have hρ₀ : 0 < ρ := (hSub hρ).1
    have hgρ : g ρ ≤ 4 * A := hGoodρ.2
    have hEps : (ε : ℝ) / ρ < ε₁ := by
      apply (div_lt_iff₀ hρ₀).2
      have h1 := hε.trans (mul_le_mul_of_nonneg_right (min_le_right (1 / 4 : ℝ) (ε₁ / 4)) hr.le)
      nlinarith only [h1, mul_pos hε₁.1 (sub_pos.2 hρ.1), mul_pos hε₁.1 hρ₀]
    let ε' : ElasticScale := ⟨(ε : ℝ) / ρ, div_pos ε.property.1 hρ₀, hEps.trans hε₁.2⟩
    let b : UnitTensorSphere → S0 := fun θ => u (c + ρ • θ.val)
    obtain ⟨hb, hbBound, hbEnergy⟩ := hSρ
    obtain ⟨hRaw, hRawEq⟩ := hHρ hρ
    obtain ⟨L, hL, hEnd⟩ := exists_scaled_outer_trace c hρ₀ hρ.1 hρ.2 H hH
    let Ω' : Set Point := (fun x : Point => c + ρ • x) ⁻¹' Ω
    let w (x : Point) := u (c + ρ • x)
    let E (x : Point) (i : Fin 3) := ρ • D (c + ρ • x) i
    have hNew : IsLocalEnergyMinimizer a ε' Ω' w E := by
      simpa only [Ω', w, E, sub_zero, Function.comp_def] using
        hLoc.affine_preimage (ε' := ε') c (0 : Point) hρ₀ rfl
    have hBall : closedBall (0 : Point) (r / ρ) ⊆ Ω' := by
      intro x hx
      simpa only [Ω', mem_preimage, sub_zero] using
        hClosed ((HarmonicMaps.affineBall_mem_closedBall_iff c 0 hρ₀ r x).2 hx)
    have hScale (s : ℝ) : energy a ε' (ball 0 (s / ρ)) w E =
        ENNReal.ofReal ρ⁻¹ * energy a ε (ball c s) u D := by
      simpa only [sub_zero] using energy_affine_ball a ε ε' hρ₀ rfl c (0 : Point) s u D
    have hOuterFinite : energy a ε' (ball 0 (r / ρ)) w E ≠ ⊤ := by
      rw [hScale]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEFin
    have hBenergy : spherePenalizedEnergy a ε' b hb ≤ g ρ := by
      rw [hDρ.1]
      exact hbEnergy ε' rfl
    have hSmall : spherePenalizedEnergy a ε' b hb ≤ η * Real.log ((ε' : ℝ)⁻¹) := by
      refine hBenergy.trans (hgρ.trans ?_)
      have hLogCompare := log_radius_div_le_two_log_subradius ε.property.1 hεquarter hρ.1
      change 4 * (η₀ * Real.log (r / (ε : ℝ))) ≤ η * Real.log (((ε : ℝ) / ρ)⁻¹)
      rw [inv_div]
      dsimp only [η₀]
      have h := mul_le_mul_of_nonneg_left hLogCompare (div_nonneg hη.1.le (by norm_num : 0 ≤ (2 : ℝ)))
      linarith only [h]
    have hLend : L ⟨1, le_rfl, by
        have h : 1 < r / ρ := (lt_div_iff₀ hρ₀).2 (by simpa using hρ.2)
        linarith⟩ = hb.1.toLp (fun θ => frobeniusCoordinateEquiv (b θ)) :=
      hEnd.trans hRawEq
    have hCρ := hComparison ε' hEps ((lt_div_iff₀ hρ₀).2 (by simpa using hρ.2)) hBall
      w E hNew hOuterFinite b hb hbBound L hL hLend hSmall
    have hScaleρ : energy a ε' (ball (0 : Point) 1) w E =
        ENNReal.ofReal ρ⁻¹ * energy a ε (ball c ρ) u D := by
      simpa only [div_self hρ₀.ne'] using hScale ρ
    rw [hScaleρ] at hCρ
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ C₀ * r * (Real.sqrt (g ρ) + 1))).1
    rw [← hF ρ ⟨hρ₀.le, hρ.2.le⟩]
    calc
      _ = ENNReal.ofReal ρ * (ENNReal.ofReal ρ⁻¹ * energy a ε (ball c ρ) u D) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hρ₀.le, mul_inv_cancel₀ hρ₀.ne', ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal ρ * ENNReal.ofReal (C₀ * (Real.sqrt (spherePenalizedEnergy a ε' b hb) + 1)) := by
        gcongr
      _ = ENNReal.ofReal (ρ * (C₀ * (Real.sqrt (spherePenalizedEnergy a ε' b hb) + 1))) := by
        rw [ENNReal.ofReal_mul hρ₀.le]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        rw [← mul_assoc, mul_comm ρ C₀]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hρ.2.le hC₀.le)
          (add_le_add (Real.sqrt_le_sqrt hBenergy) le_rfl) (by positivity) (by positivity))
  have hResult := halfRadius_energy_le_of_ae_sublinear_comparison hr hC₀ hAC hMono
    (hD.mono fun _ h => h.2) hS hSsub hSvol hGood
  rw [hF (r / 2) ⟨by linarith, by linarith⟩]
  exact ENNReal.ofReal_le_ofReal hResult

end Thesis

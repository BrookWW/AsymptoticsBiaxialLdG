module

public import Thesis.Interpolation.VacuumBallTensorFill
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The sublinear clearing comparison from a genuine penalized projection layer. -/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Matrix.Norms.Frobenius

namespace Thesis

theorem projectionShellThickness_lt_one (ε : ElasticScale) : projectionShellThickness ε < 1 := by
  let t : ℝ := (ε : ℝ)⁻¹
  let s := Real.sqrt t
  have ht : 0 < t := inv_pos.2 ε.property.1
  have hs : 0 < s := Real.sqrt_pos.2 ht
  have hHalf := Real.log_le_sub_one_of_pos (show 0 < s / 2 by positivity)
  have hTwo := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) (by norm_num : (2 : ℝ) ≠ 1)
  have hLog : Real.log s = Real.log (s / 2) + Real.log 2 := by
    rw [← Real.log_mul (by positivity : (s / 2) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  have heq : Real.log s = Real.log t / 2 := Real.log_sqrt ht.le
  have hlt : Real.log t < s := by linarith [hHalf, hTwo, hLog, heq]
  have he : 0 < Real.sqrt (ε : ℝ) := Real.sqrt_pos.2 ε.property.1
  have hS : Real.sqrt (ε : ℝ) * s = 1 := by
    dsimp only [s, t]
    rw [Real.sqrt_inv, mul_inv_cancel₀ he.ne']
  change Real.sqrt (ε : ℝ) * Real.log t < 1
  exact (mul_lt_mul_of_pos_left hlt he).trans_eq hS

theorem projectionShellThickness_mul_log_le (ε : ElasticScale) :
    projectionShellThickness ε * Real.log ((ε : ℝ)⁻¹) ≤ 16 := by
  let t : ℝ := (ε : ℝ)⁻¹
  have ht : 0 < t := inv_pos.2 ε.property.1
  have ht₁ : 1 ≤ t := ((one_lt_inv₀ ε.property.1).2 ε.property.2).le
  have hPow : t ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt t) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
    congr 1
    norm_num
  have hlog : Real.log t ≤ 4 * Real.sqrt (Real.sqrt t) := by
    calc
      _ ≤ t ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) := Real.log_le_rpow_div ht.le (by norm_num)
      _ = _ := by rw [hPow]; ring
  have hsq := pow_le_pow_left₀ (Real.log_nonneg ht₁) hlog 2
  rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg t)] at hsq
  have he : 0 < Real.sqrt (ε : ℝ) := Real.sqrt_pos.2 ε.property.1
  calc
    _ = Real.sqrt (ε : ℝ) * (Real.log t) ^ 2 := by unfold projectionShellThickness; ring
    _ ≤ Real.sqrt (ε : ℝ) * (4 ^ 2 * Real.sqrt t) := mul_le_mul_of_nonneg_left hsq he.le
    _ = 16 := by
      dsimp only [t]
      rw [Real.sqrt_inv]
      field_simp
      ring

private theorem spherePenalizedEnergy_nonneg (a : BulkCoefficients) (ε : ElasticScale)
    (p : UnitTensorSphere → S0) (hp : MemSphereH1 p) : 0 ≤ spherePenalizedEnergy a ε p hp := by
  have h1 : 0 ≤ sphereGradientEnergy p hp := by
    unfold sphereGradientEnergy
    exact integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : 0 ≤ sphereScaledBulkEnergy a ε p := by
    unfold sphereScaledBulkEnergy
    exact integral_nonneg fun θ => mul_nonneg (by positivity) (bulkPotential_nonneg a (p θ))
  unfold spherePenalizedEnergy
  nlinarith

/-- At a good unit radius the true penalized energy has the required
sublinear bound from the actual matching shell and vacuum comparison. -/
theorem exists_unitBall_sublinear_energy_comparison (a : BulkCoefficients)
    (hProj : HasPenalizedProjectionLayer a) (hDense : External.SmoothVacuumSphereDensity a)
    (hP : External.QuaternionSpherePoincare 3 (by decide : 2 ≤ 3)) (M : ℝ) (hM : 0 < M) :
    ∃ η ε₁ C : ℝ, η ∈ Ioo 0 1 ∧ ε₁ ∈ Ioo 0 1 ∧ 0 < C ∧
      ∀ (ε : ElasticScale), (ε : ℝ) < ε₁ →
      ∀ {Ω : Set Point} {R : ℝ} (hR : 1 < R) (hClosed : closedBall (0 : Point) R ⊆ Ω)
        (u : Point → S0) (D : Point → Gradient),
        IsLocalEnergyMinimizer a ε Ω u D → energy a ε (ball (0 : Point) R) u D ≠ ⊤ →
        ∀ (b : UnitTensorSphere → S0) (hb : MemSphereH1 b),
          (∀ᵐ θ ∂tensorSphereMeasure, ‖b θ‖ ≤ M) →
          ∀ L : RadialL2Trace 1 ((1 + R) / 2), RepresentsRadialL2Trace 0 u L →
            L ⟨1, le_rfl, by linarith⟩ = hb.1.toLp (fun θ => frobeniusCoordinateEquiv (b θ)) →
            spherePenalizedEnergy a ε b hb ≤ η * Real.log ((ε : ℝ)⁻¹) →
            energy a ε (ball (0 : Point) 1) u D ≤
              ENNReal.ofReal (C * (Real.sqrt (spherePenalizedEnergy a ε b hb) + 1)) := by
  obtain ⟨η₀, ε₁, C₁, hη₀, hε₁, hC₁, hLayer⟩ := hProj M hM
  obtain ⟨C₂, hC₂, hFill⟩ := exists_vacuum_twoSphere_tensor_fill a hDense hP
  let η := η₀ / 2
  have hη : η ∈ Ioo 0 η₀ := ⟨by dsimp only [η]; linarith [hη₀.1], by dsimp only [η]; linarith [hη₀.1]⟩
  have hη₁ : η ∈ Ioo 0 1 := ⟨hη.1, hη.2.trans hη₀.2⟩
  let C := C₂ * Real.sqrt (2 * C₁) + 16 * C₁
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨η, ε₁, C, hη₁, hε₁, hC, ?_⟩
  intro ε hε Ω R hR hClosed u D hMin hFinite b hb hB L hL hLend hE
  let e := spherePenalizedEnergy a ε b hb
  have he : 0 ≤ e := spherePenalizedEnergy_nonneg a ε b hb
  obtain ⟨p, hp, hVac, hpGrad, _, hr, W, hWE⟩ := hLayer η hη ε hε b hb hB hE
  let r := 1 - projectionShellThickness ε
  have hr₀ : 0 < r := sub_pos.2 (projectionShellThickness_lt_one ε)
  have hr₁ : r < 1 := sub_lt_self _ (projectionShellThickness_pos ε)
  obtain ⟨v, G, H, hv, hvVac, hH, hHend, hGE⟩ := hFill p hp hVac
  have hComp := energy_le_scaledDirichlet_add_annulus_of_matching_radial_traces a ε (0 : Point)
    hr₀ hr₁ hR hClosed u v W.toFun D G W.gradient hMin hFinite hv hvVac W.sobolev
    H W.trace L hH W.traceData hL (hHend.trans W.inner_eq.symm) (W.outer_eq.trans hLend.symm)
  have hSqrtGrad : Real.sqrt (sphereGradientEnergy p hp) ≤ Real.sqrt (2 * C₁) * Real.sqrt e := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * C₁)]
    apply Real.sqrt_le_sqrt
    change (1 / 2 : ℝ) * sphereGradientEnergy p hp ≤ C₁ * e at hpGrad
    linarith
  have hLog : 0 ≤ Real.log ((ε : ℝ)⁻¹) := Real.log_nonneg
    (((one_lt_inv₀ ε.property.1).2 ε.property.2).le)
  have hBound : projectionShellThickness ε * e ≤ 16 := by
    calc
      _ ≤ projectionShellThickness ε * (η * Real.log ((ε : ℝ)⁻¹)) :=
        mul_le_mul_of_nonneg_left hE (projectionShellThickness_pos ε).le
      _ ≤ projectionShellThickness ε * Real.log ((ε : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hLog hη₁.2.le) (projectionShellThickness_pos ε).le
      _ ≤ _ := projectionShellThickness_mul_log_le ε
  have h1 : ENNReal.ofReal (r / 1) * dirichletEnergy (ball (0 : Point) 1) G ≤
      ENNReal.ofReal ((C₂ * Real.sqrt (2 * C₁)) * Real.sqrt e) := by
    calc
      _ ≤ 1 * dirichletEnergy (ball (0 : Point) 1) G := by
        gcongr
        simpa only [div_one, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr₁.le
      _ ≤ ENNReal.ofReal (C₂ * Real.sqrt (sphereGradientEnergy p hp)) := by simpa only [one_mul] using hGE
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hSqrtGrad hC₂.le)
  have h2 : energy a ε (radialAnnulus 0 r 1) W.toFun W.gradient ≤ ENNReal.ofReal (16 * C₁) :=
    hWE.trans (ENNReal.ofReal_le_ofReal (by
      rw [mul_assoc, mul_comm 16 C₁]
      exact mul_le_mul_of_nonneg_left hBound hC₁.le))
  refine hComp.trans ((add_le_add h1 h2).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  dsimp only [C]
  nlinarith [Real.sqrt_nonneg e, mul_nonneg (by linarith : 0 ≤ 16 * C₁) (Real.sqrt_nonneg e),
    mul_nonneg hC₂.le (Real.sqrt_nonneg (2 * C₁))]

end Thesis

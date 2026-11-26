module

public import Thesis.Interpolation.ScaledPenalizedShell
import Mathlib.Analysis.SpecificLimits.Basic

/-! Physical Luckhaus connectors at one radius with the original two traces. -/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

private theorem exists_sphereMismatchBudget (U : ℕ → UnitTensorSphere → S0) (V : UnitTensorSphere → S0)
    (hL2 : Tendsto (fun k => sphereL2DifferenceSq (U k) V) atTop (𝓝 0)) :
    ∃ σ : ℕ → ℝ, Tendsto σ atTop (𝓝 0) ∧ (∀ k, 0 < σ k) ∧
      ∀ k, (σ k)⁻¹ ^ 2 * sphereL2DifferenceSq (U k) V ≤ 1 := by
  let d (k : ℕ) := sphereL2DifferenceSq (U k) V
  let σ (k : ℕ) := Real.sqrt (d k) + 1 / ((k : ℝ) + 1)
  have hσ (k : ℕ) : 0 < σ k := by dsimp only [σ]; positivity
  refine ⟨σ, ?_, hσ, ?_⟩
  · simpa only [Real.sqrt_zero, add_zero] using
      (hL2.sqrt.add (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0)))
  · intro k
    have hR : Real.sqrt (d k) / σ k ≤ 1 := (div_le_one (hσ k)).2 (by
      dsimp only [σ]
      exact le_add_of_nonneg_right (by positivity))
    have hD : 0 ≤ d k := nonneg_sphereL2DifferenceSq (U k) V
    have hPow := pow_le_pow_left₀ (by positivity : 0 ≤ Real.sqrt (d k) / σ k) hR 2
    rw [div_pow, Real.sq_sqrt hD, div_eq_mul_inv, mul_comm, ← inv_pow, one_pow] at hPow
    exact hPow

/-- A common radius with the original Sobolev traces and bounded sphere
energies supplies physical connectors whose total penalized cost vanishes. -/
theorem exists_annular_connectors_of_common_sphere_data (a : BulkCoefficients)
    (hProj : HasPenalizedProjectionLayer a) (c : Point) {s R : ℝ} (hs : 0 < s) (hsR : s < R)
    (ε ε' : ℕ → ElasticScale) (hε : Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0))
    (hε' : ∀ k, (ε' k : ℝ) = (ε k : ℝ) / s)
    (u : ℕ → Point → S0) (v : Point → S0) :
    let U (k : ℕ) (θ : UnitTensorSphere) := u k (c + s • θ.val)
    let V (θ : UnitTensorSphere) := v (c + s • θ.val)
    ∀ (hu : ∀ k, MemSphereH1 (U k)) (hv : MemSphereH1 V) (M A : ℝ), 0 < M → 0 < A →
      (∀ k, ∀ᵐ θ ∂tensorSphereMeasure, ‖U k θ‖ ≤ M) →
      (∀ᵐ θ ∂tensorSphereMeasure, V θ ∈ vacuum a) →
      (∀ k, spherePenalizedEnergy a (ε' k) (U k) (hu k) ≤ A) →
      Tendsto (fun k => sphereL2DifferenceSq (U k) V) atTop (𝓝 0) →
      ∀ (H : RadialL2Trace (s / 2) s), RepresentsRadialL2Trace c v H →
        H ⟨s, by linarith only [hs], le_rfl⟩ = hv.1.toLp (fun θ => frobeniusCoordinateEquiv (V θ)) →
        ∀ (L : ℕ → RadialL2Trace s ((s + R) / 2)),
          (∀ k, RepresentsRadialL2Trace c (u k) (L k)) →
          (∀ k, L k ⟨s, le_rfl, by linarith only [hsR]⟩ = (hu k).1.toLp (fun θ => frobeniusCoordinateEquiv (U k θ))) →
          ∃ cost : ℕ → ℝ≥0∞, Tendsto cost atTop (𝓝 0) ∧
            ∀ᶠ k in atTop, ∃ W : RadialAnnularConnector c s R hsR (u k) v,
              energy a (ε k) (radialAnnulus c W.radius s) W.toFun W.gradient ≤ cost k := by
  intro U V hu hv M A hM hA hNorm hVac hEnergy hL2 H hH hHend L hL hLend
  obtain ⟨σ, hσ, hσPos, hMismatch⟩ := exists_sphereMismatchBudget U V hL2
  let B := 2 * A + sphereGradientEnergy V hv + 1
  have hB : 0 < B := by
    dsimp only [B]
    have hG := nonneg_sphereGradientEnergy V hv
    positivity
  have hBudget (k : ℕ) : sphereShellBudget a (ε' k) (σ k) (U k) V (hu k) hv ≤ B := by
    have hE := hEnergy k
    change spherePenalizedEnergy a (ε' k) (U k) (hu k) ≤ A at hE
    unfold spherePenalizedEnergy at hE
    unfold sphereShellBudget B
    linarith [hMismatch k, nonneg_sphereScaledBulkEnergy a (ε' k) (U k)]
  have hεlim : Tendsto (fun k => (ε' k : ℝ)) atTop (𝓝 0) := by
    simpa only [hε', zero_div] using hε.div_const s
  obtain ⟨C, hC, hLayer⟩ := eventually_luckhaus2_of_penalizedProjectionLayer a hProj M B hM hB
  let ν (k : ℕ) := penalizedShellThickness (ε' k) (σ k)
  let cost (k : ℕ) := ENNReal.ofReal (s * (C * ν k))
  have hν : Tendsto ν atTop (𝓝 0) := tendsto_penalizedShellThickness ε' σ hεlim hσ
  have hCost : Tendsto cost atTop (𝓝 0) := by
    simpa only [cost, Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (s * (C * 0))).comp ((hν.const_mul C).const_mul s)
  refine ⟨cost, hCost, ?_⟩
  filter_upwards [hLayer atTop ε' σ hεlim hσ hσPos U (fun _ => V) hu (fun _ => hv)
    hNorm (fun _ => hVac) hBudget] with k hk
  obtain ⟨hν₀, hν₁, _, W, hWE⟩ := hk
  let t := 1 - ν k
  have ht : 0 < t := sub_pos.2 hν₁
  have ht₁ : t < 1 := sub_lt_self _ hν₀
  have hst₁ : s * t < s := by simpa only [mul_one] using mul_lt_mul_of_pos_left ht₁ hs
  obtain ⟨w, D, J, hw, hJ, hIn, hOut, hJE⟩ :=
    exists_physical_penalized_annular_layer a (ε k) (ε' k) c hs ht ht₁ (hε' k) W
  let T : RadialAnnularConnector c s R hsR (u k) v :=
    ⟨s * t, mul_pos hs ht, hst₁, w, D, hw, H, J, L k, hH, hJ, hL k,
      hHend.trans hIn.symm, hOut.trans (hLend k).symm⟩
  refine ⟨T, ?_⟩
  change energy a (ε k) (radialAnnulus c (s * t) s) w D ≤ cost k
  rw [hJE]
  have hMUL : ENNReal.ofReal s * energy a (ε' k) (radialAnnulus 0 t 1) W.toFun W.gradient ≤
      ENNReal.ofReal s * ENNReal.ofReal (C * ν k) := by gcongr
  exact hMUL.trans_eq ((ENNReal.ofReal_mul hs.le).symm)

end Thesis

module

public import Thesis.Upstream.MinimizingSobolev
import StratificationTheory.Foundation.AffineDomainSobolevPullback
import HarmonicMaps.Analysis.AffineBallSobolev
import HarmonicMaps.Analysis.AffineZeroBoundary

/-! Translation and dilation of the actual penalized Sobolev variational problem. -/

public section

noncomputable section

open HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal Matrix.Norms.Frobenius

namespace Thesis

private theorem gradientNormSq_smul (t : ℝ) (D : Gradient) :
    gradientNormSq (fun i => t • D i) = t ^ 2 * gradientNormSq D := by
  simp only [gradientNormSq_eq_sum_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Finset.mul_sum]

theorem energy_affine_preimage (a : BulkCoefficients) (ε ε' : ElasticScale) {t : ℝ} (ht : 0 < t)
    (hε : (ε' : ℝ) = (ε : ℝ) / t) (c b : Point) (U : Set Point)
    (u : Point → S0) (D : Point → Gradient) :
    let A : Point → Point := fun x => c + t • (x - b)
    energy a ε' (A ⁻¹' U) (u ∘ A) (fun x i => t • D (A x) i) =
      ENNReal.ofReal t⁻¹ * energy a ε U u D := by
  intro A
  have hDen : ((ε' : ℝ)⁻¹) ^ 2 = t ^ 2 * ((ε : ℝ)⁻¹) ^ 2 := by
    rw [hε, inv_div, div_eq_mul_inv, mul_pow]
  unfold energy
  have hf (x : Point) : energyDensity a ε' ((u ∘ A) x) (fun i => t • D (A x) i) =
      t ^ 2 * energyDensity a ε (u (A x)) (D (A x)) := by
    rw [energyDensity, energyDensity, gradientNormSq_smul, hDen]
    simp only [Function.comp_apply]
    ring
  simp_rw [hf, ENNReal.ofReal_mul (sq_nonneg t)]
  have hEmb : MeasurableEmbedding A := affineBall_measurableEmbedding c b ht.ne'
  have hMap : Measure.map A (volume.restrict (A ⁻¹' U)) =
      ENNReal.ofReal ((t ^ 3)⁻¹) • volume.restrict U := by
    rw [← hEmb.restrict_map volume U, show Measure.map A volume = _ from affineBall_map_volume c b ht,
      Measure.restrict_smul]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← hEmb.lintegral_map (fun x => ENNReal.ofReal (energyDensity a ε (u x) (D x))), hMap,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg t)]
  congr 1
  field_simp

theorem energy_affine_ball (a : BulkCoefficients) (ε ε' : ElasticScale) {t : ℝ} (ht : 0 < t)
    (hε : (ε' : ℝ) = (ε : ℝ) / t) (c b : Point) (r : ℝ) (u : Point → S0) (D : Point → Gradient) :
    energy a ε' (ball b (r / t)) (fun x => u (c + t • (x - b))) (fun x i => t • D (c + t • (x - b)) i) =
      ENNReal.ofReal t⁻¹ * energy a ε (ball c r) u D := by
  have hPre : (fun x : Point => c + t • (x - b)) ⁻¹' ball c r = ball b (r / t) :=
    Set.ext (affineBall_mem_ball_iff c b ht r)
  have h := energy_affine_preimage a ε ε' ht hε c b (ball c r) u D
  dsimp only [Function.comp_def] at h
  rwa [hPre] at h

theorem memH1_affine_preimage {U : Set Point} (hU : IsOpen U) (hFin : (volume : Measure Point) U ≠ ⊤)
    {u : Point → S0} {D : Point → Gradient} (hu : MemH1 U u D) (c b : Point) {t : ℝ} (ht : 0 < t) :
    let A : Point → Point := fun x => c + t • (x - b)
    MemH1 (A ⁻¹' U) (u ∘ A) (fun x i => t • D (A x) i) := by
  intro A
  apply (memH1_iff_memW12 ⟨A ⁻¹' U, hU.preimage (affineBall_contDiff c b t).continuous⟩ _ _).2
  have h := StratificationTheory.memW12_affine_preimage hFin
    ((memH1_iff_memW12 ⟨U, hU⟩ _ _).1 hu) c b ht
  have hMap : frobeniusField (u ∘ A) = (frobeniusField u) ∘ A := rfl
  have hGrad : frobeniusGradient (fun x i => t • D (A x) i) =
      fun x i => t • frobeniusGradient D (A x) i := by
    funext x i
    exact map_smul frobeniusCoordinateEquiv t (D (A x) i)
  rw [hMap, hGrad]
  exact h

theorem SameTrace.affineBall_pullback {c b : Point} {r t : ℝ} (ht : 0 < t)
    {u v : Point → S0} {D G : Point → Gradient} (h : SameTrace (ball c r) v u G D) :
    SameTrace (ball b (r / t))
      (fun x => v (c + t • (x - b))) (fun x => u (c + t • (x - b)))
      (fun x i => t • G (c + t • (x - b)) i) (fun x i => t • D (c + t • (x - b)) i) := by
  have h₀ := (sameTrace_iff_hasZeroBoundaryDifference (ballDomain c r) _ _ _ _).1 h
  have hPush := h₀.affineBall_pullback b ht
  apply (sameTrace_iff_hasZeroBoundaryDifference (ballDomain b (r / t)) _ _ _ _).2
  let A (x : Point) := c + t • (x - b)
  change HasZeroBoundaryValues (ballDomain b (r / t))
    (fun x => frobeniusCoordinateEquiv (v (A x)) - frobeniusCoordinateEquiv (u (A x)))
    (fun x i => frobeniusCoordinateEquiv (t • G (A x) i) - frobeniusCoordinateEquiv (t • D (A x) i))
  simpa only [A, frobeniusField, frobeniusGradient, Pi.sub_apply, map_smul, smul_sub] using hPush

private def penalizedAffineHomeomorph (c b : Point) {t : ℝ} (ht : 0 < t) : Point ≃ₜ Point where
  toFun x := c + t • (x - b)
  invFun y := b + t⁻¹ • (y - c)
  left_inv := affineBall_inverse c b ht.ne'
  right_inv y := by simpa only [inv_inv] using affineBall_inverse b c (inv_ne_zero ht.ne') y
  continuous_toFun := (affineBall_contDiff c b t).continuous
  continuous_invFun := (affineBall_contDiff b c t⁻¹).continuous

/-- Positive affine change of variables transports the local comparison
problem with the scale `ε/t` and its actual weak columns. -/
theorem IsLocalEnergyMinimizer.affine_preimage {a : BulkCoefficients} {ε ε' : ElasticScale}
    {Ω : Set Point} {u : Point → S0} {D : Point → Gradient}
    (hMin : IsLocalEnergyMinimizer a ε Ω u D)
    (c b : Point) {t : ℝ} (ht : 0 < t) (hε : (ε' : ℝ) = (ε : ℝ) / t) :
    let A : Point → Point := fun x => c + t • (x - b)
    IsLocalEnergyMinimizer a ε' (A ⁻¹' Ω) (u ∘ A) (fun x i => t • D (A x) i) := by
  intro A
  let e := penalizedAffineHomeomorph c b ht
  let w := u ∘ A
  let E (x : Point) (i : Fin 3) := t • D (A x) i
  refine ⟨?_, ?_⟩
  · intro V hV hVU
    let W := e '' V
    have hW : IsOpen W := e.isOpenMap _ hV
    have hWCl : CompactlyContained W Ω := by
      unfold CompactlyContained at hVU ⊢
      change IsCompact (closure (e '' V)) ∧ closure (e '' V) ⊆ Ω
      rw [← e.image_closure]
      refine ⟨hVU.1.image e.continuous, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hVU.2 hx
    have hFin : (volume : Measure Point) W ≠ ⊤ :=
      ((measure_mono subset_closure).trans_lt hWCl.1.measure_lt_top).ne
    have h := memH1_affine_preimage hW hFin (hMin.1 W hW hWCl) c b ht
    have hPre : A ⁻¹' W = V := e.injective.preimage_image V
    change MemH1 (A ⁻¹' W) w E at h
    rwa [hPre] at h
  · intro x r hr hClosed v G hV hTrace
    let y := A x
    let r' := t * r
    let J (z : Point) := x + t⁻¹ • (z - y)
    have hi : 0 < t⁻¹ := inv_pos.2 ht
    have hr' : 0 < r' := mul_pos ht hr
    have hR : r / t⁻¹ = r' := by rw [div_inv_eq_mul, mul_comm]
    have hInv (z : Point) : A (J z) = z := by
      change c + t • (x + t⁻¹ • (z - (c + t • (x - b))) - b) = z
      have heq : x + t⁻¹ • (z - (c + t • (x - b))) - b =
          (x - b) + t⁻¹ • (z - (c + t • (x - b))) := by abel
      rw [heq, smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
      abel
    have hY : closedBall y r' ⊆ Ω := by
      intro z hz
      have hz' : J z ∈ closedBall x r := by
        apply (affineBall_mem_closedBall_iff x y hi r z).2
        rwa [hR]
      have h' := hClosed hz'
      change A (J z) ∈ Ω at h'
      rwa [hInv] at h'
    let v₀ := v ∘ J
    let G₀ (z : Point) (i : Fin 3) := t⁻¹ • G (J z) i
    have hV₀ : MemH1 (ball y r') v₀ G₀ := by
      have h := memH1_affine_preimage isOpen_ball measure_ball_ne_top hV x y hi
      have hpre : J ⁻¹' ball x r = ball y r' := Set.ext fun z => by
        change J z ∈ ball x r ↔ _
        rw [← hR]
        exact affineBall_mem_ball_iff x y hi r z
      change MemH1 (J ⁻¹' ball x r) v₀ G₀ at h
      rwa [hpre] at h
    have hT := hTrace.affineBall_pullback (b := y) hi
    have hwInv : (fun z => w (J z)) = u := funext fun z => congrArg u (hInv z)
    have heInv : (fun z i => t⁻¹ • E (J z) i) = D := by
      funext z i
      change t⁻¹ • (t • D (A (J z)) i) = D z i
      rw [hInv, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    have hT₀ : SameTrace (ball y r') v₀ u G₀ D := by
      change SameTrace (ball y (r / t⁻¹)) v₀ (fun z => w (J z)) G₀ (fun z i => t⁻¹ • E (J z) i) at hT
      rwa [hR, hwInv, heInv] at hT
    have hI := hMin.2 y r' hr' hY v₀ G₀ hV₀ hT₀
    have hε₀ : (ε : ℝ) = (ε' : ℝ) / t⁻¹ := by rw [hε]; field_simp
    have hEU := energy_affine_ball a ε' ε hi hε₀ x y r w E
    have hEV := energy_affine_ball a ε' ε hi hε₀ x y r v G
    change energy a ε (ball y (r / t⁻¹)) (fun z => w (J z)) (fun z i => t⁻¹ • E (J z) i) = _ at hEU
    change energy a ε (ball y (r / t⁻¹)) v₀ G₀ = _ at hEV
    rw [hR, hwInv, heInv, inv_inv] at hEU
    rw [hR, inv_inv] at hEV
    rw [hEU, hEV, mul_comm (ENNReal.ofReal t), mul_comm (ENNReal.ofReal t)] at hI
    exact (ENNReal.mul_le_mul_iff_left (by simp [ht]) ENNReal.ofReal_ne_top).1 hI

end Thesis

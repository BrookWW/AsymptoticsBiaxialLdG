module

public import Thesis.MeasureGeometry.CylinderCoordinates
public import Thesis.MeasureGeometry.PlanarSmoothLowerBound

/-! The original limit class on every parallel meridian of a regular cylinder. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

theorem normalizedSpectralGap_eq_one_of_mem_vacuum (a : BulkCoefficients) {A : S0}
    (hA : A ∈ vacuum a) : normalizedSpectralGap a A = 1 := by
  have hDist : infDist A (vacuum a) = 0 := infDist_zero_of_mem hA
  have hSq := infDist_vacuum_sq_eq_orderedEigenvalue a A
  rw [hDist, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hSq
  have h0 : orderedEigenvalue A 0 - vacuumRadius a = 0 := by
    apply sq_eq_zero_iff.mp
    apply le_antisymm _ (sq_nonneg _)
    linarith only [hSq, sq_nonneg (orderedEigenvalue A 1), sq_nonneg (orderedEigenvalue A 2 + vacuumRadius a)]
  have h1 : orderedEigenvalue A 1 = 0 := by
    apply sq_eq_zero_iff.mp
    apply le_antisymm _ (sq_nonneg _)
    linarith only [hSq, sq_nonneg (orderedEigenvalue A 0 - vacuumRadius a),
      sq_nonneg (orderedEigenvalue A 2 + vacuumRadius a)]
  have h2 : orderedEigenvalue A 2 + vacuumRadius a = 0 := by
    apply sq_eq_zero_iff.mp
    apply le_antisymm _ (sq_nonneg _)
    linarith only [hSq, sq_nonneg (orderedEigenvalue A 0 - vacuumRadius a), sq_nonneg (orderedEigenvalue A 1)]
  have ha0 : orderedEigenvalue A 0 = vacuumRadius a := sub_eq_zero.mp h0
  have ha2 : orderedEigenvalue A 2 = -vacuumRadius a := eq_neg_of_add_eq_zero_left h2
  rw [normalizedSpectralGap, ha0, h1, ha2, sub_zero, zero_sub, neg_neg, min_self,
    inv_mul_cancel₀ (vacuumRadius_pos a).ne']

private theorem spectralVacuumPoint_val_of_mem_vacuum (a : BulkCoefficients) {A : S0}
    (hA : A ∈ vacuum a) : (spectralVacuumPoint a A).val = A := by
  have h := spectralVacuumPoint_dist_eq_infDist a A
  rw [infDist_zero_of_mem hA] at h
  exact (dist_eq_zero.mp h).symm

/-- All native vacuum circles have exactly one of the three splitting costs. -/
theorem nativeVacuumCircleCost_mem_three (a : BulkCoefficients) (p : C(NativeCircle, vacuum a)) :
    nativeVacuumCircleCost a p ∈ ({0, kappaStar a, 2 * kappaStar a} : Set ℝ) := by
  obtain ⟨v, hv⟩ := vacuumQuaternionProjection_surjective a (p nativeCircleLoopBase)
  rw [nativeVacuumCircleCost_eq a p v hv, vacuumSplittingCost_eq]
  unfold quaternionSplittingWeight
  split_ifs <;> simp [mul_comm]

private theorem continuous_fixedCylinderCircle (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (r z : ℝ) : Continuous (fun w : NativeCircle => c + axisChart B (r • w.val, z)) := by
  exact continuous_const.add ((continuous_axisChart B).comp (by fun_prop))

/-- On a compact regular lateral cylinder, all the approximating projected
meridians eventually have the class of the original limiting meridian
and possess every fixed normalized gap below one. -/
theorem exists_stable_projectedMeridians_of_uniform_convergence
    (a : BulkCoefficients) (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {K : Set Point} (hK : IsCompact K) {r lo hi : ℝ} (hL : lo ≤ hi)
    (hSide : ∀ z ∈ Icc lo hi, ∀ w : NativeCircle, c + axisChart B (r • w.val, z) ∈ K)
    {Q₀ : Point → S0} {Q : ℕ → Point → S0}
    (hQ₀ : ContinuousOn Q₀ K) (hQ₀Vac : MapsTo Q₀ K (vacuum a))
    (hQ : ∀ n, ContinuousOn (Q n) K) (hConv : TendstoUniformlyOn Q Q₀ atTop K) :
    ∃ p : C(NativeCircle, vacuum a),
      (∀ w, (p w).val = Q₀ (c + axisChart B (r • w.val, (lo + hi) / 2))) ∧
      ∀ g ∈ Ioo (0 : ℝ) 1, ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc lo hi,
        (∀ w : NativeCircle, g ≤ normalizedSpectralGap a (Q n (c + axisChart B (r • w.val, z)))) ∧
        ∃ q : C(NativeCircle, vacuum a),
          (∀ w, q w = spectralVacuumPoint a (Q n (c + axisChart B (r • w.val, z)))) ∧ p.Homotopic q := by
  let Γ (z : ℝ) (w : NativeCircle) := c + axisChart B (r • w.val, z)
  let z₀ := (lo + hi) / 2
  have hz₀ : z₀ ∈ Icc lo hi := by
    change lo ≤ (lo + hi) / 2 ∧ (lo + hi) / 2 ≤ hi
    constructor <;> linarith
  let pAt (z : ℝ) (hz : z ∈ Icc lo hi) : C(NativeCircle, vacuum a) :=
    ⟨fun w => ⟨Q₀ (Γ z w), hQ₀Vac (hSide z hz w)⟩,
      (hQ₀.comp_continuous (continuous_fixedCylinderCircle B c r z) (hSide z hz)).subtype_mk _⟩
  refine ⟨pAt z₀ hz₀, fun _ => rfl, ?_⟩
  intro g hg
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hQ₀
  obtain ⟨d, hd, hU⟩ := Metric.uniformContinuousOn_iff.mp
    (IsCompact.uniformContinuousOn_of_continuous (isCompact_closedBall (0 : S0) (M + 1))
      (continuous_normalizedSpectralGap a).continuousOn) (1 - g) (sub_pos.mpr hg.2)
  have hNear := (tendstoUniformlyOn_iff.mp hConv) (min d 1) (lt_min hd zero_lt_one)
  filter_upwards [hNear] with n hn z hz
  let T (s : unitInterval) (x : Point) := Q₀ x + s.val • (Q n x - Q₀ x)
  have hSeg (s : unitInterval) (x : Point) (hx : x ∈ K) : g ≤ normalizedSpectralGap a (T s x) := by
    have hDist : dist (T s x) (Q₀ x) < min d 1 := by
      rw [dist_eq_norm, show T s x - Q₀ x = s.val • (Q n x - Q₀ x) by dsimp only [T]; abel,
        norm_smul, Real.norm_of_nonneg s.property.1]
      have h := (hn x hx).trans_le (le_refl _)
      have hNorm := (mul_le_mul_of_nonneg_right s.property.2 (norm_nonneg (Q n x - Q₀ x))).trans_eq (one_mul _)
      apply hNorm.trans_lt
      calc
        ‖Q n x - Q₀ x‖ = dist (Q n x) (Q₀ x) := (dist_eq_norm _ _).symm
        _ = dist (Q₀ x) (Q n x) := dist_comm _ _
        _ < min d 1 := h
    have hQb : Q₀ x ∈ closedBall (0 : S0) (M + 1) :=
      mem_closedBall_zero_iff.mpr ((hM x hx).trans (by linarith))
    have hTb : T s x ∈ closedBall (0 : S0) (M + 1) := by
      apply mem_closedBall_zero_iff.mpr
      have h := dist_triangle (T s x) (Q₀ x) 0
      simp only [dist_zero_right] at h
      exact h.trans (by linarith only [hDist.trans_le (min_le_right _ _), hM x hx])
    have hG := hU (T s x) hTb (Q₀ x) hQb (hDist.trans_le (min_le_left _ _))
    rw [normalizedSpectralGap_eq_one_of_mem_vacuum a (hQ₀Vac hx), Real.dist_eq, abs_lt] at hG
    linarith only [hG.1]
  have hGap (w : NativeCircle) : g ≤ normalizedSpectralGap a (Q n (Γ z w)) := by
    simpa [T] using hSeg 1 (Γ z w) (hSide z hz w)
  have hSeqSide : Continuous (fun w : NativeCircle => Q n (Γ z w)) :=
    (hQ n).comp_continuous (continuous_fixedCylinderCircle B c r z) (hSide z hz)
  have hSimple (w : NativeCircle) : Q n (Γ z w) ∈ simpleSpectrumLocus :=
    simpleSpectrum_of_normalizedSpectralGap_pos a (hg.1.trans_le (hGap w))
  have hProj : Continuous (fun w : NativeCircle => (spectralVacuumPoint a (Q n (Γ z w))).val) :=
    (contDiffOn_spectralVacuumPoint a).continuousOn.comp_continuous hSeqSide hSimple
  let qNear : C(NativeCircle, vacuum a) :=
    ⟨fun w => spectralVacuumPoint a (Q n (Γ z w)), hProj.subtype_mk _⟩
  refine ⟨hGap, qNear, fun _ => rfl, ?_⟩
  have hAlong : (pAt z₀ hz₀).Homotopic (pAt z hz) := by
    let Z (s : unitInterval) : ℝ := (1 - s.val) * z₀ + s.val * z
    have hZ : ∀ s : unitInterval, Z s ∈ Icc lo hi := by
      intro s
      exact convex_Icc lo hi hz₀ hz (sub_nonneg.mpr s.property.2) s.property.1 (by ring)
    let ΓZ (v : unitInterval × NativeCircle) := Γ (Z v.1) v.2
    have hΓ : Continuous ΓZ := by
      change Continuous (fun v : unitInterval × NativeCircle =>
        c + axisChart B (r • v.2.val, Z v.1))
      have hCtsZ : Continuous Z := by dsimp only [Z]; fun_prop
      have hY : Continuous (fun v : unitInterval × NativeCircle => r • v.2.val) := by fun_prop
      exact continuous_const.add ((continuous_axisChart B).comp (hY.prodMk (hCtsZ.comp continuous_fst)))
    have hVac (v : unitInterval × NativeCircle) : Q₀ (ΓZ v) ∈ vacuum a :=
      hQ₀Vac (hSide (Z v.1) (hZ v.1) v.2)
    have hC : Continuous (fun v => Q₀ (ΓZ v)) :=
      hQ₀.comp_continuous hΓ (fun v => hSide (Z v.1) (hZ v.1) v.2)
    refine ⟨⟨⟨fun v => ⟨Q₀ (ΓZ v), hVac v⟩, hC.subtype_mk hVac⟩, ?_, ?_⟩⟩
    · intro w; apply Subtype.ext
      change Q₀ (Γ (Z 0) w) = Q₀ (Γ z₀ w)
      simp [Z]
    · intro w; apply Subtype.ext
      change Q₀ (Γ (Z 1) w) = Q₀ (Γ z w)
      simp [Z]
  apply hAlong.trans
  let W (u : unitInterval × NativeCircle) := T u.1 (Γ z u.2)
  have hQ₀Side : Continuous (fun w : NativeCircle => Q₀ (Γ z w)) :=
    hQ₀.comp_continuous (continuous_fixedCylinderCircle B c r z) (hSide z hz)
  have hW : Continuous W := (hQ₀Side.comp continuous_snd).add
    ((continuous_subtype_val.comp continuous_fst).smul ((hSeqSide.sub hQ₀Side).comp continuous_snd))
  have hS (u : unitInterval × NativeCircle) : W u ∈ simpleSpectrumLocus :=
    simpleSpectrum_of_normalizedSpectralGap_pos a (hg.1.trans_le (hSeg u.1 _ (hSide z hz u.2)))
  have hWP : Continuous (fun v => (spectralVacuumPoint a (W v)).val) :=
    (contDiffOn_spectralVacuumPoint a).continuousOn.comp_continuous hW hS
  refine ⟨⟨⟨fun v => spectralVacuumPoint a (W v), hWP.subtype_mk _⟩, ?_, ?_⟩⟩
  · intro w
    apply Subtype.ext
    change (spectralVacuumPoint a (T 0 (Γ z w))).val = Q₀ (Γ z w)
    rw [show T 0 (Γ z w) = Q₀ (Γ z w) by simp [T]]
    exact spectralVacuumPoint_val_of_mem_vacuum a (hQ₀Vac (hSide z hz w))
  · intro w
    change spectralVacuumPoint a (T 1 (Γ z w)) = spectralVacuumPoint a (Q n (Γ z w))
    simp [T]

end Thesis.MeasureGeometry

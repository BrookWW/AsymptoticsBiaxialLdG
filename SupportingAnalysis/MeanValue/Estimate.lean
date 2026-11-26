module

public import SupportingAnalysis.MeanValue.ExponentialLift
public import SupportingAnalysis.MeanValue.Subharmonic

/-! Mean value in an extra Euclidean coordinate and the exact volume ratio. -/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped Topology ContDiff ENNReal Laplacian

set_option autoImplicit false

namespace SupportingAnalysis

/-- The dimension-only factor from comparing a lifted ball with its horizontal
ball and vertical interval. -/
noncomputable def subsolutionMeanVolumeFactor (m : ℕ) : ℝ :=
  2 * (2:ℝ)^m * volume.real (ball (0 : E m) 1) /
    volume.real (ball (0 : MeanLiftSpace m) 1)

theorem subsolutionMeanVolumeFactor_nonneg (m : ℕ) : 0 ≤ subsolutionMeanVolumeFactor m := by
  unfold subsolutionMeanVolumeFactor
  positivity

private theorem positive_volumeReal_ball {E' : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [MeasureSpace E'] [BorelSpace E']
    [(volume : Measure E').IsAddHaarMeasure]
    (x : E') {a : ℝ} (ha : 0 < a) : 0 < volume.real (ball x a) :=
  ENNReal.toReal_pos (measure_ball_pos volume x ha).ne' measure_ball_lt_top.ne

theorem finrank_meanLiftSpace (m : ℕ) : Module.finrank ℝ (MeanLiftSpace m) = m+1 := by
  rw [(WithLp.linearEquiv 2 ℝ (E m × ℝ)).finrank_eq, Module.finrank_prod,
    finrank_euclideanSpace_fin, Module.finrank_self]

theorem subsolutionMean_volume_ratio {m : ℕ} (c : E m) (p : MeanLiftSpace m) {a : ℝ} (ha : 0 < a) :
    (2*a) * volume.real (ball c (2*a)) / volume.real (ball p a) = subsolutionMeanVolumeFactor m := by
  have h2a : 0 < 2*a := by positivity
  have h1 : 0 < volume.real (ball (0 : MeanLiftSpace m) 1) := positive_volumeReal_ball 0 zero_lt_one
  have hB : volume.real (ball c (2*a)) = (2*a)^m * volume.real (ball (0 : E m) 1) := by
    rw [measureReal_def, Measure.addHaar_ball_of_pos volume c h2a, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg h2a.le _)]
    rfl
  have hP : volume.real (ball p a) = a^(m+1) * volume.real (ball (0 : MeanLiftSpace m) 1) := by
    rw [measureReal_def, Measure.addHaar_ball_of_pos volume p ha, finrank_meanLiftSpace,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ha.le _)]
    rfl
  rw [hB, hP, mul_pow, pow_succ]
  unfold subsolutionMeanVolumeFactor
  field_simp [ha.ne', h1.ne']

/-- A closed lifted ball of radius a lies over the open spatial ball of
radius 2a when its center lies over the spatial ball of radius a. -/
theorem subsolutionMean_closedBall_fst_subset {m : ℕ} {c x : E m} {a : ℝ} (hx : x ∈ ball c a) :
    closedBall (WithLp.toLp 2 (x,(0:ℝ)) : MeanLiftSpace m) a ⊆
      WithLp.fst ⁻¹' ball c (2*a) := by
  intro p hp
  have hdist : dist p.fst x ≤ a :=
    (WithLp.dist_fst_le p (WithLp.toLp 2 (x,(0:ℝ)))).trans (mem_closedBall.mp hp)
  apply mem_ball.mpr
  exact (dist_triangle _ x _).trans_lt (by linarith only [hdist, mem_ball.mp hx])

theorem subsolutionMean_ball_subset_box {m : ℕ} {c x : E m} {a : ℝ} (hx : x ∈ ball c a) :
    ball (WithLp.toLp 2 (x,(0:ℝ)) : MeanLiftSpace m) a ⊆
      WithLp.ofLp ⁻¹' (ball c (2*a) ×ˢ Ioo (-a) a) := by
  intro p hp
  have hf := subsolutionMean_closedBall_fst_subset hx (ball_subset_closedBall hp)
  have hs : dist p.snd (0:ℝ) < a :=
    (WithLp.dist_snd_le p (WithLp.toLp 2 (x,(0:ℝ)))).trans_lt (mem_ball.mp hp)
  rw [Real.dist_eq, sub_zero] at hs
  exact ⟨hf, abs_lt.mp hs⟩

/-- The integral over the true (m+1)-ball is bounded by the rectangle
obtained from the spatial ball and the auxiliary interval. -/
theorem subsolutionMeanLift_ball_integral_le {m : ℕ} {c x : E m} {a k : ℝ} (ha : 0 < a)
    (hk : 0 ≤ k) (hx : x ∈ ball c a) {f : E m → ℝ}
    (hf : IntegrableOn f (ball c (2*a))) (hf₀ : ∀ y ∈ ball c (2*a), 0 ≤ f y)
    (hLift : IntegrableOn (subsolutionMeanLift k f)
      (ball (WithLp.toLp 2 (x,(0:ℝ)) : MeanLiftSpace m) a)) :
    (∫ p in ball (WithLp.toLp 2 (x,(0:ℝ)) : MeanLiftSpace m) a, subsolutionMeanLift k f p) ≤
      (2*a) * Real.exp (k*a) * ∫ y in ball c (2*a), f y := by
  let S := ball c (2*a)
  let I := Ioo (-a) a
  let B := ball (WithLp.toLp 2 (x,(0:ℝ)) : MeanLiftSpace m) a
  let Q : Set (MeanLiftSpace m) := WithLp.ofLp ⁻¹' (S ×ˢ I)
  let F := fun p : MeanLiftSpace m => Real.exp (k*a) * f p.fst
  let G := fun z : E m × ℝ => Real.exp (k*a) * f z.1
  have hI : (volume : Measure ℝ) I < ⊤ := by
    change volume (Ioo (-a) a) < ⊤
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have hG : IntegrableOn G (S ×ˢ I) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    have hi : IntegrableOn (fun _ : ℝ => (1:ℝ)) I := integrableOn_const hI.ne
    simpa only [G, mul_one] using (hf.const_mul (Real.exp (k*a))).mul_prod hi
  have hMap : MeasurePreserving (WithLp.ofLp : MeanLiftSpace m → E m × ℝ) :=
    WithLp.volume_preserving_ofLp (E m) ℝ
  have hEmb : MeasurableEmbedding (WithLp.ofLp : MeanLiftSpace m → E m × ℝ) :=
    (MeasurableEquiv.toLp 2 (E m × ℝ)).symm.measurableEmbedding
  have hF : IntegrableOn F Q := (hMap.integrableOn_comp_preimage hEmb).mpr hG
  have hSub : B ⊆ Q := subsolutionMean_ball_subset_box hx
  have hQ : MeasurableSet Q := (measurableSet_ball.prod measurableSet_Ioo).preimage hMap.measurable
  have hF₀ : ∀ᵐ p ∂volume.restrict Q, 0 ≤ F p := by
    filter_upwards [ae_restrict_mem hQ] with p hp
    exact mul_nonneg (Real.exp_nonneg _) (hf₀ _ hp.1)
  have hBound (p : MeanLiftSpace m) (hp : p ∈ B) : subsolutionMeanLift k f p ≤ F p := by
    have hp' := hSub hp
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp'.2.2.le hk)) (hf₀ _ hp'.1)
  have hBox : (∫ p in Q, F p) = (2*a) * Real.exp (k*a) * ∫ y in S, f y := by
    change (∫ p in Q, G (WithLp.ofLp p)) = _
    rw [hMap.setIntegral_preimage_emb hEmb G (S ×ˢ I), Measure.volume_eq_prod]
    have hMul : (fun z : E m × ℝ => G z) =
        fun z => (Real.exp (k*a) * f z.1) * (fun _ : ℝ => (1:ℝ)) z.2 := by simp [G]
    rw [hMul, setIntegral_prod_mul (fun y : E m => Real.exp (k*a)*f y) (fun _ : ℝ => (1:ℝ)) S I,
      integral_const_mul, setIntegral_const,
      measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  calc
    _ ≤ ∫ p in B, F p := setIntegral_mono_on hLift (hF.mono_set hSub) measurableSet_ball hBound
    _ ≤ ∫ p in Q, F p := setIntegral_mono_set hF hF₀ hSub.eventuallyLE
    _ = _ := hBox

/-- A nonnegative spatial function satisfying Δf ≥ -k² f has the desired
ordinary ball mean bound, by the true subharmonic exponential lift. -/
theorem subsolutionMean_of_laplacian_lower {m : ℕ} (hm : 1 ≤ m)
    {c x : E m} {a k : ℝ} (ha : 0 < a) (hk : 0 ≤ k) (hx : x ∈ ball c a)
    {f : E m → ℝ} (hC : ContDiffOn ℝ ∞ f (ball c (2*a))) (hI : IntegrableOn f (ball c (2*a)))
    (h₀ : ∀ y ∈ ball c (2*a), 0 ≤ f y)
    (hΔ : ∀ y ∈ ball c (2*a), 0 ≤ Δ f y + k^2*f y) :
    f x ≤ subsolutionMeanVolumeFactor m * Real.exp (k*a) *
      ((∫ y in ball c (2*a), f y) / volume.real (ball c (2*a))) := by
  let U : Set (MeanLiftSpace m) := WithLp.fst ⁻¹' ball c (2*a)
  let p : MeanLiftSpace m := WithLp.toLp 2 (x,(0:ℝ))
  let F := subsolutionMeanLift k f
  have hU : IsOpen U := isOpen_ball.preimage (WithLp.continuous_fst 2 (E m) ℝ)
  have hF : ContDiffOn ℝ ∞ F U := by
    intro q hq
    exact (contDiffAt_subsolutionMeanLift k (hC.contDiffAt (isOpen_ball.mem_nhds hq))).contDiffWithinAt
  have hFΔ (q : MeanLiftSpace m) (hq : q ∈ U) : 0 ≤ Δ F q := by
    rw [laplacian_subsolutionMeanLift k ((hC.contDiffAt (isOpen_ball.mem_nhds hq)).of_le
      (WithTop.coe_le_coe.mpr le_top))]
    exact mul_nonneg (Real.exp_nonneg _) (hΔ _ hq)
  have hP : closedBall p a ⊆ U := subsolutionMean_closedBall_fst_subset hx
  have hFI : IntegrableOn F (ball p a) :=
    ((hF.continuousOn.mono hP).integrableOn_compact (isCompact_closedBall p a)).mono_set ball_subset_closedBall
  have hv : 0 < volume.real (ball p a) := positive_volumeReal_ball p ha
  let b := (stdOrthonormalBasis ℝ (MeanLiftSpace m)).reindex (finCongr (finrank_meanLiftSpace m))
  have hMean := le_average_ball_of_laplacian_nonneg_isometry
    (by omega : 2 ≤ m + 1) b.repr.symm hU hF hP
    (fun y hy => hFΔ y (hP (ball_subset_closedBall hy)))
  have hLeft : F p = f x := by simp [F, p, subsolutionMeanLift]
  have hMean' : f x ≤ (∫ q in ball p a, F q) / volume.real (ball p a) := by
    rw [← hLeft, le_div_iff₀ hv, mul_comm]
    exact hMean
  have hvBase : 0 < volume.real (ball c (2*a)) := positive_volumeReal_ball c (by positivity)
  have hLiftBound := subsolutionMeanLift_ball_integral_le ha hk hx hI h₀ hFI
  calc
    _ ≤ (∫ q in ball p a, F q) / volume.real (ball p a) := hMean'
    _ ≤ ((2*a) * Real.exp (k*a) * ∫ y in ball c (2*a), f y) / volume.real (ball p a) :=
      div_le_div_of_nonneg_right hLiftBound hv.le
    _ = _ := by
      rw [← subsolutionMean_volume_ratio c p ha]
      field_simp [hv.ne', hvBase.ne']

end SupportingAnalysis

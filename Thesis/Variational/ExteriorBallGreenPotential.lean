module

public import Thesis.Variational.ExteriorBallGreenGeometry
public import Thesis.Variational.ScalarNewtonianPairing
import Thesis.Variational.WeakPoissonMaximum
import Thesis.Variational.BoundaryPoissonEstimate

/-! The positive exterior Green potential and comparison on the physical cap. -/

public section

noncomputable section

open Filter HolderToCK MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal Topology

namespace Thesis

/-- The positive Green potential of the actual nonnegative cap force. -/
@[expose] def exteriorBallGreenPotential (a : Point) (ρ : ℝ) (V : Set Point) (F : Point → ℝ) (x : Point) : ℝ :=
  (euclideanSphereArea 3)⁻¹ * ∫ y in V, exteriorBallNewtonKernel a ρ x y * F y

private theorem integrable_exteriorBallGreen_terms
    {a p x : Point} {ρ s : ℝ} (hρ : 0 < ρ) (hx : ρ ≤ ‖x-a‖)
    {V : Set Point} (hV : MeasurableSet V) (hVs : V ⊆ ball p s)
    (hExt : ∀ y ∈ V, ρ < ‖y-a‖)
    {F : Point → ℝ} (hF : MemLp F 4 (volume.restrict V)) (hFP : ∀ y ∈ V, 0 ≤ F y) :
    IntegrableOn (fun y => poissonInversePower 1 (x-y)*F y) V ∧
    IntegrableOn (fun y => (ρ/‖y-a‖) * poissonInversePower 1 (x-kelvinBallImage a ρ y) * F y) V := by
  let R := max (s+1) (dist x p+1)
  have hR : 0 < R := (by positivity : 0 < dist x p+1).trans_le (le_max_right _ _)
  have hX : x ∈ closedBall p R := mem_closedBall.2 <|
    (le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)
  obtain ⟨_, _, hK⟩ := exists_poissonInversePower_conjugate_bound 1 (by norm_num)
  have hsub : V ⊆ ball p R := hVs.trans (ball_subset_ball
    ((le_add_of_nonneg_right zero_le_one).trans (le_max_left _ _)))
  have hKx : MemLp (fun y => poissonInversePower 1 (x-y)) poissonL4Conjugate (volume.restrict V) :=
    ((hK p x R hR hX).1).mono_measure (Measure.restrict_mono_set volume hsub)
  have hI₁ : IntegrableOn (fun y => poissonInversePower 1 (x-y)*F y) V :=
    integrable_poissonL4_smul hF hKx
  refine ⟨hI₁, hI₁.mono' ?_ ?_⟩
  · have hK := measurable_poissonInversePower 1
    have hN : Measurable (fun y : Point => ρ/‖y-a‖) :=
      measurable_const.div ((continuous_id.sub continuous_const).measurable.norm)
    exact ((hN.mul (hK.comp (measurable_const.sub (measurable_kelvinBallImage a ρ)))).aestronglyMeasurable).mul
      hF.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hV,
      ((volume : Measure Point).ae_ne x).filter_mono (ae_mono Measure.restrict_le_self)] with y hy hxy
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (div_nonneg hρ.le (norm_nonneg _))
      (poissonInversePower_nonneg _ _)) (hFP y hy))]
    have h := sub_nonneg.mp (exteriorBallNewtonKernel_nonneg a x hρ (hExt y hy) hx hxy.symm)
    exact mul_le_mul_of_nonneg_right h (hFP y hy)

private theorem integrable_exteriorBallGreen_kernel_mul
    {a p x : Point} {ρ s : ℝ} (hρ : 0 < ρ) (hx : ρ ≤ ‖x-a‖)
    {V : Set Point} (hV : MeasurableSet V) (hVs : V ⊆ ball p s)
    (hExt : ∀ y ∈ V, ρ < ‖y-a‖)
    {F : Point → ℝ} (hF : MemLp F 4 (volume.restrict V)) (hFP : ∀ y ∈ V, 0 ≤ F y) :
    IntegrableOn (fun y => exteriorBallNewtonKernel a ρ x y * F y) V := by
  obtain ⟨h₁,h₂⟩ := integrable_exteriorBallGreen_terms hρ hx hV hVs hExt hF hFP
  exact Integrable.congr (h₁.sub h₂) (Eventually.of_forall fun y => (sub_mul _ _ _).symm)

theorem exteriorBallGreenPotential_nonneg
    {a x : Point} {ρ : ℝ} (hρ : 0 < ρ) (hx : ρ ≤ ‖x-a‖)
    {V : Set Point} (hV : MeasurableSet V) (hExt : ∀ y ∈ V, ρ < ‖y-a‖)
    {F : Point → ℝ} (hFP : ∀ y ∈ V, 0 ≤ F y) :
    0 ≤ exteriorBallGreenPotential a ρ V F x := by
  apply mul_nonneg (inv_nonneg.mpr (euclideanSphereArea_pos (by decide)).le)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem hV,
    ((volume : Measure Point).ae_ne x).filter_mono (ae_mono Measure.restrict_le_self)] with y hy hxy
  exact mul_nonneg (exteriorBallNewtonKernel_nonneg a x hρ (hExt y hy) hx hxy.symm) (hFP y hy)

theorem exteriorBallGreenPotential_eq_zero_on_sphere
    {a x : Point} {ρ : ℝ} (hρ : 0 < ρ) (hx : ‖x-a‖ = ρ)
    {V : Set Point} (hV : MeasurableSet V) (hExt : ∀ y ∈ V, ρ < ‖y-a‖)
    (F : Point → ℝ) :
    exteriorBallGreenPotential a ρ V F x = 0 := by
  unfold exteriorBallGreenPotential
  have h : (fun y => exteriorBallNewtonKernel a ρ x y * F y) =ᵐ[volume.restrict V]
      (fun _ => 0) := by
    filter_upwards [ae_restrict_mem hV] with y hy
    rw [exteriorBallNewtonKernel_eq_zero_on_sphere a x hρ (hExt y hy) hx, zero_mul]
  rw [integral_congr_ae h, integral_zero, mul_zero]

/-- The actual potential difference is controlled by two inverse-square
integrals against the original cap forcing. -/
theorem exteriorBallGreenPotential_abs_sub_le
    {a p x z : Point} {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s)
    (hx : ρ ≤ ‖x-a‖) (hz : ρ ≤ ‖z-a‖)
    (hxB : x ∈ closedBall p s) (hzB : z ∈ closedBall p s)
    {V : Set Point} (hV : MeasurableSet V) (hVs : V ⊆ ball p s)
    (hExt : ∀ y ∈ V, ρ < ‖y-a‖)
    {F : Point → ℝ} (hF : MemLp F 4 (volume.restrict V)) (hFP : ∀ y ∈ V, 0 ≤ F y)
    {M : ℝ} (hRatio : ∀ y ∈ V, ‖y-a‖/ρ ≤ M) :
    |exteriorBallGreenPotential a ρ V F x - exteriorBallGreenPotential a ρ V F z| ≤
     (euclideanSphereArea 3)⁻¹ * ((1+M)*dist x z/2) *
        ((∫ y in V, poissonInversePower 2 (x-y)*F y) +
          ∫ y in V, poissonInversePower 2 (z-y)*F y) := by
  let κ := (euclideanSphereArea 3)⁻¹
  have hκ : 0 ≤ κ := inv_nonneg.mpr (euclideanSphereArea_pos (by decide)).le
  let K (x y : Point) := exteriorBallNewtonKernel a ρ x y
  let L (x y : Point) := poissonInversePower 2 (x-y)
  let D := (1+M)*dist x z/2
  have hDx : IntegrableOn (fun y => K x y * F y) V :=
    integrable_exteriorBallGreen_kernel_mul hρ hx hV hVs hExt hF hFP
  have hDz : IntegrableOn (fun y => K z y * F y) V :=
    integrable_exteriorBallGreen_kernel_mul hρ hz hV hVs hExt hF hFP
  obtain ⟨_,_,hK⟩ := exists_poissonInversePower_conjugate_bound 2 (by norm_num)
  have hA (w : Point) (hwB : w ∈ closedBall p s) : IntegrableOn (fun y => L w y*F y) V :=
    integrable_poissonL4_smul hF ((hK p w s hs hwB).1.mono_measure (Measure.restrict_mono_set volume hVs))
  have hB : IntegrableOn (fun y => D*(L x y*F y+L z y*F y)) V :=
    ((hA x hxB).add (hA z hzB)).const_mul _
  change |κ*(∫ y in V, K x y*F y)-κ*(∫ y in V, K z y*F y)| ≤
    κ * D * ((∫ y in V, L x y*F y)+∫ y in V, L z y*F y)
  rw [← mul_sub, abs_mul, abs_of_nonneg hκ, ← integral_sub hDx hDz]
  rw [mul_assoc κ D]
  apply mul_le_mul_of_nonneg_left _ hκ
  have hPoint : ∀ᵐ y ∂volume.restrict V, ‖K x y * F y - K z y * F y‖ ≤ D*(L x y*F y+L z y*F y) := by
    filter_upwards [ae_restrict_mem hV,
      ((volume : Measure Point).ae_ne x).filter_mono (ae_mono Measure.restrict_le_self),
      ((volume : Measure Point).ae_ne z).filter_mono (ae_mono Measure.restrict_le_self)] with y hy hxy hzy
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul, abs_of_nonneg (hFP y hy)]
    have h := exteriorBallNewtonKernel_abs_sub_le a x z hρ (hExt y hy) hx hz hxy.symm hzy.symm
    have heq : D*(L x y*F y+L z y*F y) =
        ((1+M)*dist x z*(L x y+L z y)/2) * F y := by dsimp only [D]; ring
    rw [heq]
    refine (mul_le_mul_of_nonneg_right h (hFP y hy)).trans ?_
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (add_le_add le_rfl (hRatio y hy)) dist_nonneg)
          (add_nonneg (poissonInversePower_nonneg _ _) (poissonInversePower_nonneg _ _))) zero_le_two)
      (hFP y hy)
  have h := norm_integral_le_of_norm_le hB hPoint
  rw [integral_const_mul, integral_add (hA x hxB) (hA z hzB)] at h
  exact h

private theorem exteriorBallGreenPotential_continuousOn
    {a p : Point} {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s)
    {V : Set Point} (hV : MeasurableSet V) (hVs : V ⊆ ball p s)
    (hExt : ∀ y ∈ V, ρ < ‖y-a‖) {F : Point → ℝ}
    (hF : MemLp F 4 (volume.restrict V)) (hFP : ∀ y ∈ V, 0 ≤ F y) :
    ContinuousOn (exteriorBallGreenPotential a ρ V F) (closure V) := by
  let M := (s+dist p a)/ρ
  have hM : 0 ≤ M := div_nonneg (add_nonneg hs.le dist_nonneg) hρ.le
  have hRatio (y : Point) (hy : y ∈ V) : ‖y-a‖/ρ ≤ M := by
    rw [← dist_eq_norm]
    exact div_le_div_of_nonneg_right
      ((dist_triangle y p a).trans (add_le_add (mem_ball.1 (hVs hy)).le le_rfl)) hρ.le
  let T := closure V
  have hX (x : Point) (hx : x ∈ T) : ρ ≤ ‖x-a‖ :=
    closure_minimal (fun _ hy => (hExt _ hy).le)
      (isClosed_le continuous_const (continuous_id.sub continuous_const).norm) hx
  have hXB (x : Point) (hx : x ∈ T) : x ∈ closedBall p s :=
    closure_minimal (hVs.trans ball_subset_closedBall) isClosed_closedBall hx
  obtain ⟨C,hC,hK⟩ := exists_poissonInversePower_conjugate_bound 2 (by norm_num)
  let G := (eLpNorm F 4 (volume.restrict V)).toReal
  let A := (euclideanSphereArea 3)⁻¹*(1+M)*(C*s^(9/4-2:ℝ)*G)
  have hA : 0 ≤ A := by dsimp only [A,G]; positivity [euclideanSphereArea_pos (by decide : 0<3)]
  have hInt (x : Point) (hx : x ∈ T) : (∫ y in V, poissonInversePower 2 (x-y)*F y) ≤ C*s^(9/4-2:ℝ)*G := by
    have h := hK p x s hs (hXB x hx)
    have hMon := eLpNorm_mono_measure (fun y => poissonInversePower 2 (x-y)) (Measure.restrict_mono_set volume hVs)
      (p := poissonL4Conjugate)
    have hk := h.1.mono_measure (Measure.restrict_mono_set volume hVs)
    have hE := integral_poissonL4_product_le hF hk (Eventually.of_forall fun _ => poissonInversePower_nonneg _ _)
    have hNorm : (fun y => poissonInversePower 2 (x-y)*‖F y‖) =ᵐ[volume.restrict V]
        fun y => poissonInversePower 2 (x-y)*F y :=
      (ae_restrict_mem hV).mono fun y hy => by
        change poissonInversePower 2 (x-y)*‖F y‖ = poissonInversePower 2 (x-y)*F y
        rw [Real.norm_of_nonneg (hFP y hy)]
    rw [integral_congr_ae hNorm] at hE
    exact hE.trans (mul_le_mul_of_nonneg_right ((ENNReal.toReal_mono h.1.eLpNorm_ne_top hMon).trans h.2)
      ENNReal.toReal_nonneg)
  apply (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal A)
    (f := exteriorBallGreenPotential a ρ V F) (s := T) ?_).continuousOn
  intro x hx z hz
  rw [Real.dist_eq, Real.coe_toNNReal _ hA]
  have h := exteriorBallGreenPotential_abs_sub_le hρ hs (hX x hx) (hX z hz) (hXB x hx) (hXB z hz)
    hV hVs hExt hF hFP hRatio
  exact h.trans ((mul_le_mul_of_nonneg_left (add_le_add (hInt x hx) (hInt z hz))
    (by positivity [euclideanSphereArea_pos (by decide : 0<3)])).trans_eq (by dsimp only [A]; ring))

/-- On the true exterior open set the image contribution has zero
distributional Laplacian. The original force has its exact sign and normalization. -/
theorem exteriorBallGreenPotential_laplacian_pairing
    {a p : Point} {ρ s : ℝ} (hρ : 0 < ρ)
    {V : Set Point} (hV : IsOpen V) (hVs : V ⊆ ball p s) (hExt : ∀ y ∈ V, ρ < ‖y-a‖)
    {F : Point → ℝ} (hF : MemLp F 4 (volume.restrict V)) (hFP : ∀ y ∈ V, 0 ≤ F y)
    {φ : Point → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hSupp : tsupport φ ⊆ V) :
    (∫ x in V, exteriorBallGreenPotential a ρ V F x * laplacian φ x) = -∫ y in V, φ y * F y := by
  let μ := volume.restrict V
  let W := exteriorBallGreenPotential a ρ V F
  let Z := kelvinBallImage a ρ
  let E (y : Point) := (ρ/‖y-a‖)*F y
  let P (x : Point) := ∫ y, newtonianKernelThree (x-y)*F y ∂μ
  let Q (x : Point) := ∫ y, newtonianKernelThree (x-Z y)*E y ∂μ
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top measure_ball_ne_top (measure_mono hVs))
  have hFu : Integrable F μ := hF.integrable (by norm_num)
  have hEu : Integrable E μ := by
    apply hFu.norm.mono'
    · have hD : Measurable (fun y : Point => ρ / ‖y-a‖) := measurable_const.div
        ((continuous_id.sub continuous_const).norm.measurable)
      exact hD.aestronglyMeasurable.mul hFu.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hV.measurableSet] with y hy
      rw [show E y = (ρ/‖y-a‖)*F y from rfl, norm_mul,
        Real.norm_of_nonneg (div_nonneg hρ.le (norm_nonneg _))]
      exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one (hρ.trans (hExt y hy))).2 (hExt y hy).le)
  have hW (x : Point) (hx : x ∈ V) : W x = P x - Q x := by
    obtain ⟨h₁,h₂⟩ := integrable_exteriorBallGreen_terms hρ (hExt x hx).le hV.measurableSet hVs hExt hF hFP
    change (euclideanSphereArea 3)⁻¹ * (∫ y, exteriorBallNewtonKernel a ρ x y*F y ∂μ) = _
    simp only [exteriorBallNewtonKernel, sub_mul]
    rw [integral_sub h₁ h₂, mul_sub]
    unfold P Q
    rw [← integral_const_mul, ← integral_const_mul]
    apply congrArg₂ (· - ·)
    · apply integral_congr_ae (Eventually.of_forall fun y => ?_)
      unfold newtonianKernelThree
      ring
    · apply integral_congr_ae (Eventually.of_forall fun y => ?_)
      unfold newtonianKernelThree E
      ring
  have hZ : ∀ᵐ y ∂μ, ‖Z y‖ ≤ ρ+‖a‖ := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with y hy
    have hT := norm_add_le (Z y - a) a
    rw [sub_add_cancel] at hT
    have hI := (mem_ball.1 (kelvinBallImage_mem_ball a hρ (hExt y hy))).le
    rw [dist_eq_norm] at hI
    exact hT.trans (add_le_add hI le_rfl)
  have hY : ∀ᵐ y ∂μ, ‖y‖ ≤ s+‖p‖ := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with y hy
    have hT := norm_add_le (y-p) p
    rw [sub_add_cancel, ← dist_eq_norm] at hT
    exact hT.trans (add_le_add (mem_ball.1 (hVs hy)).le le_rfl)
  have hP := newtonianKernelThree_source_laplacian_test (μ := μ) id measurable_id hY hFu hφ hc
  have hQ := newtonianKernelThree_source_laplacian_test (μ := μ) Z
    (measurable_kelvinBallImage a ρ) hZ hEu hφ hc
  have hPI : Integrable (fun x => P x*laplacian φ x) volume := hP.1
  have hQI : Integrable (fun x => Q x*laplacian φ x) volume := hQ.1
  have hPE : (∫ x, P x*laplacian φ x) = -(∫ y in V, φ y*F y) := hP.2
  have hQ0 : (∫ x, Q x*laplacian φ x) = 0 := by
    have hZero : (fun y => φ (Z y)*E y) =ᵐ[μ] (fun _ => 0) := by
      filter_upwards [ae_restrict_mem hV.measurableSet] with y hy
      have hI := kelvinBallImage_mem_ball a hρ (hExt y hy)
      have hN : Z y ∉ tsupport φ := fun h => (mem_ball.1 hI).not_ge (by
        rw [dist_eq_norm]
        exact (hExt _ (hSupp h)).le)
      rw [image_eq_zero_of_notMem_tsupport hN, zero_mul]
    rw [hQ.2, integral_congr_ae hZero, integral_zero, neg_zero]
  have hΔS : tsupport (laplacian φ) ⊆ V := laplacian_test_tsupport_subset.trans hSupp
  calc
    _ = ∫ x in V, (P x-Q x)*laplacian φ x :=
      setIntegral_congr_fun hV.measurableSet (fun x hx => congrArg (fun s => s * laplacian φ x) (hW x hx))
    _ = ∫ x, (P x-Q x)*laplacian φ x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hΔS h)), mul_zero]
    _ = _ := by
      simp_rw [sub_mul]
      rw [integral_sub hPI hQI, hPE, hQ0, sub_zero]

/-- A smooth cutoff field vanishing on the cap boundary is bounded by the
positive exterior Green potential of any dominating nonnegative force. -/
theorem abs_le_exteriorBallGreenPotential_of_zero_wall
    {a p : Point} {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s)
    {V : Set Point} (hV : IsOpen V) (hVs : V ⊆ ball p s) (hExt : ∀ y ∈ V, ρ < ‖y-a‖)
    {F w : Point → ℝ} (hF : MemLp F 4 (volume.restrict V)) (hFP : ∀ y ∈ V, 0 ≤ F y)
    (hWC : ContinuousOn w (closure V)) (hW : ContDiffOn ℝ 2 w V)
    (hZero : ∀ x ∈ frontier V, w x = 0) (hForce : ∀ x ∈ V, |laplacian w x| ≤ F x) :
    ∀ x ∈ closure V, |w x| ≤ exteriorBallGreenPotential a ρ V F x := by
  let v := exteriorBallGreenPotential a ρ V F
  have hvC : ContinuousOn v (closure V) :=
    exteriorBallGreenPotential_continuousOn hρ hs hV.measurableSet hVs hExt hF hFP
  have hX (x : Point) (hx : x ∈ closure V) : ρ ≤ ‖x-a‖ :=
    closure_minimal (fun _ h => (hExt _ h).le) (isClosed_le continuous_const (continuous_id.sub continuous_const).norm) hx
  have hvN (x : Point) (hx : x ∈ closure V) : 0 ≤ v x :=
    exteriorBallGreenPotential_nonneg hρ (hX x hx) hV.measurableSet hExt hFP
  have hSide (e : ℝ) (he : |e| = 1) : ∀ x ∈ closure V, e*w x ≤ v x := by
    let q (x : Point) := e*w x - v x
    have hqC : ContinuousOn q (closure V) := ((hWC.const_mul e).sub hvC)
    have hqF (x : Point) (hx : x ∈ frontier V) : q x ≤ 0 := by
      change e*w x - v x ≤ 0
      rw [hZero x hx, mul_zero, zero_sub, neg_nonpos]
      exact hvN x (frontier_subset_closure hx)
    have hqL (φ : Point → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
        (hSupp : tsupport φ ⊆ V) (hPos : ∀ x, 0 ≤ φ x) :
        0 ≤ ∫ x in V, q x*laplacian φ x := by
      have hΔS : tsupport (laplacian φ) ⊆ V := laplacian_test_tsupport_subset.trans hSupp
      have hCΔ : HasCompactSupport (laplacian φ) :=
        hc.of_isClosed_subset (isClosed_tsupport _) laplacian_test_tsupport_subset
      have hI₁ : IntegrableOn (fun x => w x*laplacian φ x) V :=
        (integrable_scalar_mul_smooth_test hV hW.continuousOn (continuous_laplacian_test hφ) hCΔ hΔS).integrableOn
      have hI₂ : IntegrableOn (fun x => v x*laplacian φ x) V :=
        (integrable_scalar_mul_smooth_test hV (hvC.mono subset_closure)
          (continuous_laplacian_test hφ) hCΔ hΔS).integrableOn
      have hWPair : (∫ x in V, w x*laplacian φ x) = ∫ x in V, laplacian w x*φ x := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
            rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hΔS h)), mul_zero]),
          setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
            rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hSupp h)), mul_zero])]
        exact integral_scalar_laplacian_test_eq hV hW hφ hc hSupp
      have hVPair := exteriorBallGreenPotential_laplacian_pairing hρ hV hVs hExt hF hFP hφ hc hSupp
      have hI₃ : IntegrableOn (fun x => laplacian w x*φ x) V :=
        (integrable_scalar_mul_smooth_test hV (continuousOn_laplacian_of_contDiffOn_two hV hW)
          hφ.continuous hc hSupp).integrableOn
      have hFIn : IntegrableOn (fun x => F x*φ x) V := by
        letI : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr
          (ne_top_of_le_ne_top measure_ball_ne_top (measure_mono hVs))
        exact (hF.integrable (by norm_num : (1:ℝ≥0∞) ≤ 4)).mul_of_top_left
          (hφ.continuous.memLp_top_of_hasCompactSupport hc _)
      calc
        0 ≤ ∫ x in V, (e*laplacian w x+F x)*φ x := by
          apply integral_nonneg_of_ae
          filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
          have heL : -|laplacian w x| ≤ e*laplacian w x := by
            have h := neg_abs_le (e*laplacian w x)
            rw [abs_mul, he, one_mul] at h
            exact h
          exact mul_nonneg (by linarith only [heL,hForce x hx]) (hPos x)
        _ = _ := by
          simp_rw [q, sub_mul, add_mul, mul_assoc]
          rw [integral_add (hI₃.const_mul e) hFIn, integral_sub (hI₁.const_mul e) hI₂,
            integral_const_mul, integral_const_mul, hWPair, hVPair, sub_neg_eq_add]
          exact congrArg (fun x => e*(∫ y in V, laplacian w y*φ y)+x)
            (integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _))
    intro x hx
    exact sub_nonpos.mp (nonpos_of_distributional_subharmonic hV hVs hqC hqL hqF x hx)
  intro x hx
  have h₁ := hSide 1 (by norm_num) x hx
  have h₂ := hSide (-1) (by norm_num) x hx
  rw [one_mul] at h₁
  rw [neg_one_mul] at h₂
  exact abs_le.mpr ⟨neg_le.mp h₂,h₁⟩

end Thesis

end

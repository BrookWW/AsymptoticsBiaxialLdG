module

public import Thesis.Foundation.VacuumTube
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Thesis.StressEnergy
import StratificationTheory.Foundation.ClosedTargetACLInheritance
import StratificationTheory.Foundation.IntervalWeakRepresentative

/-! Bulk control of the distance to the vacuum on bounded edge traces. -/

public section

open Filter MeasureTheory Set
open scoped BigOperators Matrix.Norms.Frobenius NNReal Topology

namespace Thesis

/-- On a fixed norm ball, the bulk potential controls squared distance to the vacuum
with a single constant for all tensors. -/
theorem vacuumDistance_sq_le_bulkPotential_of_norm_le (a : BulkCoefficients) (R : ℝ) :
    ∃ C > (0 : ℝ), ∀ A : S0, ‖A‖ ≤ R →
      Metric.infDist A (vacuum a) ^ 2 ≤ C * bulkPotential a A := by
  obtain ⟨c, δ, hc, hδ, hlocal⟩ := exists_bulkPotential_quadratic_lower a
  let K : Set S0 := Metric.closedBall 0 R ∩ {A | δ ≤ Metric.infDist A (vacuum a)}
  have hK : IsCompact K := (isCompact_closedBall (0 : S0) R).inter_right
    (isClosed_le continuous_const (Metric.continuous_infDist_pt (vacuum a)))
  have hnear (A : S0) (hA : Metric.infDist A (vacuum a) < δ) :
      Metric.infDist A (vacuum a) ^ 2 ≤ c⁻¹ * bulkPotential a A := by
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm c] using hlocal A hA
  by_cases hKne : K.Nonempty
  · obtain ⟨P, hP, hmin⟩ := hK.exists_isMinOn hKne (contDiff_bulkPotential a).continuous.continuousOn
    have hPpos : 0 < bulkPotential a P := by
      refine lt_of_le_of_ne (bulkPotential_nonneg a P) ?_
      intro hz
      have hmem := (bulkPotential_eq_zero_iff a P).mp hz.symm
      have hgap := hP.2
      change δ ≤ Metric.infDist P (vacuum a) at hgap
      rw [Metric.infDist_zero_of_mem hmem] at hgap
      exact hδ.not_ge hgap
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
      (Metric.continuous_infDist_pt (vacuum a)).continuousOn
    refine ⟨max c⁻¹ (B ^ 2 / bulkPotential a P), (inv_pos.mpr hc).trans_le (le_max_left _ _), ?_⟩
    intro A hA
    by_cases hδA : Metric.infDist A (vacuum a) < δ
    · exact (hnear A hδA).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (bulkPotential_nonneg a A))
    · have hAK : A ∈ K := ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hA,
        le_of_not_gt hδA⟩
      have hDA : Metric.infDist A (vacuum a) ≤ B := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg Metric.infDist_nonneg] using hB A hAK
      calc
        _ ≤ B ^ 2 := pow_le_pow_left₀ Metric.infDist_nonneg hDA 2
        _ ≤ (B ^ 2 / bulkPotential a P) * bulkPotential a A := by
          calc
            _ = (B ^ 2 / bulkPotential a P) * bulkPotential a P := (div_mul_cancel₀ _ hPpos.ne').symm
            _ ≤ _ := mul_le_mul_of_nonneg_left (hmin hAK) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (bulkPotential_nonneg a A)
  · refine ⟨c⁻¹, inv_pos.mpr hc, fun A hA => hnear A (lt_of_not_ge fun hgap => hKne ⟨A, ?_⟩)⟩
    exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hA, hgap⟩

private theorem ac_comp_lipschitz {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {u : ℝ → E} {l r : ℝ} {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hu : AbsolutelyContinuousOnInterval u l r) : AbsolutelyContinuousOnInterval (f ∘ u) l r := by
  unfold AbsolutelyContinuousOnInterval at hu ⊢
  have hlim := hu.const_mul (K : ℝ)
  simp only [mul_zero] at hlim
  refine squeeze_zero (fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg) (fun E => ?_) hlim
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hf.dist_le_mul (u (E.2 i).1) (u (E.2 i).2)

/-- An interval representative with integral increments has the given derivative
almost everywhere on the open interval. -/
theorem ae_hasDerivAt_of_interval_increments {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {l r : ℝ} (hlr : l < r) {u g : ℝ → E}
    (hg : MemLp g 2 (volume.restrict (Ioo l r)))
    (hinc : ∀ x ∈ Icc l r, ∀ y ∈ Icc l r, u y - u x = ∫ t in x..y, g t) :
    ∀ᵐ t ∂volume.restrict (Ioo l r), HasDerivAt u (g t) t := by
  have hi := StratificationTheory.intervalIntegrable_of_memLp_two hlr.le hg
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hi.ae_hasDerivAt_integral]
    with t ht hder
  have hder' := hder (by rw [uIcc_of_le hlr.le]; exact Ioo_subset_Icc_self ht) l left_mem_uIcc
  apply (hder'.add_const (u l)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
  exact sub_eq_iff_eq_add.mp (hinc l ⟨le_rfl, hlr.le⟩ y (Ioo_subset_Icc_self hy))

private theorem norm_deriv_le_of_lipschitz_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → E} {f : E → ℝ} (hf : LipschitzWith 1 f) {x : ℝ} {d : ℝ} {v : E}
    (hu : HasDerivAt u v x) (hd : HasDerivAt (f ∘ u) d x) : ‖d‖ ≤ ‖v‖ := by
  apply le_of_tendsto_of_tendsto hd.tendsto_slope.norm hu.tendsto_slope.norm
  refine Eventually.of_forall fun y => ?_
  simp only [slope, vsub_eq_sub, Function.comp_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [NNReal.coe_one, one_mul] using hf.norm_sub_le (u y) (u x)) (norm_nonneg _)

private theorem abs_sub_le_integral_of_ac {f H : ℝ → ℝ} {l r : ℝ} (hlr : l < r)
    (hf : AbsolutelyContinuousOnInterval f l r) (hH : IntegrableOn H (Ioo l r))
    (hbound : ∀ᵐ t ∂volume.restrict (Ioo l r), ‖deriv f t‖ ≤ H t)
    {x y : ℝ} (hx : x ∈ Icc l r) (hy : y ∈ Icc l r) :
    |f y - f x| ≤ ∫ t in Ioo l r, H t := by
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm]
    exact this hy hx (le_of_not_ge hxy)
  have hsub : Ioo x y ⊆ Ioo l r := Ioo_subset_Ioo hx.1 hy.2
  have hxyAC : AbsolutelyContinuousOnInterval f x y := hf.mono (by
    rw [uIcc_of_le hxy, uIcc_of_le hlr.le]
    exact Icc_subset_Icc hx.1 hy.2)
  have hDx : IntegrableOn (fun t => ‖deriv f t‖) (Ioo x y) := by
    exact hxyAC.intervalIntegrable_deriv.norm.1.mono_set Ioo_subset_Ioc_self
  have hMono : (∫ t in Ioo x y, ‖deriv f t‖) ≤ ∫ t in Ioo x y, H t :=
    integral_mono_ae hDx (hH.mono_set hsub)
      (hbound.filter_mono (ae_mono (Measure.restrict_mono_set _ hsub)))
  have hNonneg : 0 ≤ᵐ[volume.restrict (Ioo l r)] H :=
    hbound.mono fun _ ht => (norm_nonneg _).trans ht
  rw [← hxyAC.integral_deriv_eq_sub, intervalIntegral.integral_of_le hxy, integral_Ioc_eq_integral_Ioo,
    ← Real.norm_eq_abs]
  exact (norm_integral_le_integral_norm _).trans (hMono.trans (setIntegral_mono_set hH hNonneg
    (Eventually.of_forall hsub)))

private theorem ae_deriv_sq_comp_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {M l r ε : ℝ} {u g : ℝ → E} {D : E → ℝ} {b : ℝ → ℝ}
    (hLip : LipschitzWith 1 D) (hD₀ : ∀ z, 0 ≤ D z) (hb₀ : ∀ x, 0 ≤ b x)
    (hM₁ : 1 ≤ M) (hlr : l < r) (hε : 0 < ε)
    (hu : AbsolutelyContinuousOnInterval u l r)
    (hg : MemLp g 2 (volume.restrict (Ioo l r)))
    (hinc : ∀ x ∈ Icc l r, ∀ y ∈ Icc l r, u y - u x = ∫ s in x..y, g s)
    (hSq : ∀ x ∈ Icc l r, D (u x) ^ 2 ≤ M * b x) :
    let d := D ∘ u
    ∀ᵐ x ∂volume.restrict (Ioo l r), ‖deriv (d ^ 2) x‖ ≤
      (2 * M * ε) * ((1 / 2 : ℝ) * ‖g x‖ ^ 2 + ε⁻¹ ^ 2 * b x) := by
  intro d
  have hdAC : AbsolutelyContinuousOnInterval d l r := ac_comp_lipschitz hLip hu
  have hWeak : ∀ᵐ x ∂volume.restrict (Ioo l r), HasDerivAt u (g x) x :=
    ae_hasDerivAt_of_interval_increments hlr hg hinc
  have hdiff : ∀ᵐ x ∂volume.restrict (Ioo l r), x ∈ uIcc l r → DifferentiableAt ℝ d x :=
    ae_restrict_of_ae hdAC.ae_differentiableAt
  filter_upwards [hWeak, hdiff, ae_restrict_mem measurableSet_Ioo] with x hug hdd hx
  have hdx := (hdd (by rw [uIcc_of_le hlr.le]; exact Ioo_subset_Icc_self hx)).hasDerivAt
  have hdNorm := norm_deriv_le_of_lipschitz_comp hLip hug hdx
  have hdNonneg : 0 ≤ d x := hD₀ (u x)
  have h2 : deriv (d ^ 2) x = 2 * d x * deriv d x := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using (hdx.pow 2).deriv
  have hYoung : 2 * d x * ‖g x‖ ≤ ε * ‖g x‖ ^ 2 + ε⁻¹ * d x ^ 2 := by
    have hprod := mul_nonneg (sq_nonneg (d x - ε * ‖g x‖)) (inv_pos.mpr hε).le
    calc
      _ ≤ 2 * d x * ‖g x‖ + (d x - ε * ‖g x‖) ^ 2 * ε⁻¹ := le_add_of_nonneg_right hprod
      _ = _ := by field_simp [hε.ne']; ring
  have hεM : ε ≤ M * ε := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hM₁ hε.le
  rw [h2, norm_mul, Real.norm_of_nonneg (mul_nonneg (by norm_num) hdNonneg)]
  calc
    _ ≤ 2 * d x * ‖g x‖ := mul_le_mul_of_nonneg_left hdNorm (by positivity)
    _ ≤ ε * ‖g x‖ ^ 2 + ε⁻¹ * d x ^ 2 := hYoung
    _ ≤ (M * ε) * ‖g x‖ ^ 2 + ε⁻¹ * (M * b x) := add_le_add
      (mul_le_mul_of_nonneg_right hεM (sq_nonneg _))
      (mul_le_mul_of_nonneg_left (hSq x (Ioo_subset_Icc_self hx)) (inv_nonneg.mpr hε.le))
    _ ≤ _ := by
      have hM : 0 ≤ M := zero_le_one.trans hM₁
      have hn := mul_nonneg (mul_nonneg hM (inv_nonneg.mpr hε.le)) (hb₀ x)
      calc
        _ ≤ (M * ε) * ‖g x‖ ^ 2 + 2 * (M * ε⁻¹) * b x := by linarith only [hn]
        _ = _ := by field_simp [hε.ne']

private theorem le_integral_div_add_of_pointwise_le {f : ℝ → ℝ} {C L l r : ℝ}
    (hlr : l < r) (hf : IntegrableOn f (Ioo l r))
    (h : ∀ x ∈ Ioo l r, C ≤ f x + L) : C ≤ (∫ x in Ioo l r, f x) / (r - l) + L := by
  have hVol : volume (Ioo l r) ≠ ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hConst := integrableOn_const (C := L) hVol
  have hInt := setIntegral_mono_on (integrableOn_const (C := C) hVol)
    (hf.add hConst) measurableSet_Ioo h
  change (∫ x in Ioo l r, C) ≤ ∫ x in Ioo l r, f x + L at hInt
  rw [setIntegral_const, integral_add hf hConst, setIntegral_const,
    Real.volume_real_Ioo, max_eq_left (sub_nonneg.mpr hlr.le), smul_eq_mul, smul_eq_mul] at hInt
  have hMul : (C - L) * (r - l) ≤ ∫ x in Ioo l r, f x := by linarith only [hInt]
  exact sub_le_iff_le_add.mp ((le_div_iff₀ (sub_pos.mpr hlr)).mpr hMul)

private theorem edge_sq_le_interval_penalizedEnergy {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {M l r ε : ℝ} {u g : ℝ → E} {D : E → ℝ} {b : ℝ → ℝ}
    (hLip : LipschitzWith 1 D) (hD₀ : ∀ z, 0 ≤ D z) (hb₀ : ∀ x, 0 ≤ b x)
    (hM₁ : 1 ≤ M) (hlr : l < r) (hε : 0 < ε)
    (hu : AbsolutelyContinuousOnInterval u l r)
    (hg : MemLp g 2 (volume.restrict (Ioo l r)))
    (hinc : ∀ x ∈ Icc l r, ∀ y ∈ Icc l r, u y - u x = ∫ s in x..y, g s)
    (hSq : ∀ x ∈ Icc l r, D (u x) ^ 2 ≤ M * b x)
    (hbi : IntegrableOn b (Ioo l r)) (t : ℝ) (ht : t ∈ Icc l r) :
    D (u t) ^ 2 ≤ (2 * M) * (ε + ε ^ 2 / (r - l)) *
      ∫ s in Ioo l r, (1 / 2 : ℝ) * ‖g s‖ ^ 2 + ε⁻¹ ^ 2 * b s := by
  let d := D ∘ u
  let e : ℝ → ℝ := fun x => (1 / 2 : ℝ) * ‖g x‖ ^ 2 + ε⁻¹ ^ 2 * b x
  let A := ∫ s in Ioo l r, e s
  have hM : 0 < M := zero_lt_one.trans_le hM₁
  have hLength : 0 < r - l := sub_pos.mpr hlr
  have hdAC : AbsolutelyContinuousOnInterval d l r := ac_comp_lipschitz hLip hu
  have hd2AC : AbsolutelyContinuousOnInterval (d ^ 2) l r := by
    simpa only [pow_two] using hdAC.mul hdAC
  have hgi : IntegrableOn (fun x => ‖g x‖ ^ 2) (Ioo l r) :=
    MemLp.integrable_norm_pow (p := 2) hg (by decide)
  have hei : IntegrableOn e (Ioo l r) := (hgi.const_mul _).add (hbi.const_mul _)
  have hnonneg (x : ℝ) : 0 ≤ e x :=
    add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (hb₀ x))
  have hA : 0 ≤ A := integral_nonneg hnonneg
  have hDeriv : ∀ᵐ x ∂volume.restrict (Ioo l r), ‖deriv (d ^ 2) x‖ ≤ (2 * M * ε) * e x :=
    ae_deriv_sq_comp_le hLip hD₀ hb₀ hM₁ hlr hε hu hg hinc hSq
  have hOsc (s : ℝ) (hs : s ∈ Ioo l r) : d t ^ 2 ≤ M * b s + (2 * M * ε) * A := by
    have hOsc' := abs_sub_le_integral_of_ac hlr hd2AC (hei.const_mul (2 * M * ε)) hDeriv
      (Ioo_subset_Icc_self hs) ht
    rw [integral_const_mul] at hOsc'
    change |d t ^ 2 - d s ^ 2| ≤ (2 * M * ε) * A at hOsc'
    have hSq' : d s ^ 2 ≤ M * b s := hSq s (Ioo_subset_Icc_self hs)
    linarith only [le_abs_self (d t ^ 2 - d s ^ 2), hOsc', hSq']
  have hAvg : d t ^ 2 ≤ M * (∫ s in Ioo l r, b s) / (r - l) + (2 * M * ε) * A := by
    have h := le_integral_div_add_of_pointwise_le hlr (hbi.const_mul M) hOsc
    rwa [integral_const_mul] at h
  have hbA : (∫ s in Ioo l r, b s) ≤ ε ^ 2 * A := by
    have h : ε⁻¹ ^ 2 * (∫ s in Ioo l r, b s) ≤ A := by
      rw [← integral_const_mul]
      apply setIntegral_mono_on (hbi.const_mul _) hei measurableSet_Ioo
      intro x _
      exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (sq_nonneg _))
    have hh := mul_le_mul_of_nonneg_left h (sq_nonneg ε)
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hε.ne', one_pow, one_mul] at hh
    exact hh
  change d t ^ 2 ≤ (2 * M) * (ε + ε ^ 2 / (r - l)) * A
  calc
    _ ≤ _ := hAvg
    _ ≤ M * (ε ^ 2 * A) / (r - l) + (2 * M * ε) * A := add_le_add
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbA hM.le) hLength.le) le_rfl
    _ ≤ _ := by
      have hn := mul_nonneg (div_nonneg (mul_nonneg hM.le (sq_nonneg ε)) hLength.le) hA
      linarith only [hn, show (2 * M) * (ε + ε ^ 2 / (r - l)) * A =
        (2 * M * ε) * A + 2 * (M * ε ^ 2 / (r - l) * A) by ring,
        show M * (ε ^ 2 * A) / (r - l) = M * ε ^ 2 / (r - l) * A by ring]

/-- On a closed edge interval, its original Sobolev derivative and penalized
energy control the distance of every trace value, including the endpoints. -/
theorem edge_vacuumDistance_sq_le_penalizedEnergy (a : BulkCoefficients) (R : ℝ) :
    ∃ C > (0 : ℝ), ∀ {l r : ℝ}, l < r → ∀ {ε : ℝ}, 0 < ε → ∀ {u g : ℝ → S0},
      AbsolutelyContinuousOnInterval u l r →
      MemLp g 2 (volume.restrict (Ioo l r)) →
      (∀ x ∈ Icc l r, ∀ y ∈ Icc l r, u y - u x = ∫ t in x..y, g t) →
      (∀ᵐ t ∂volume.restrict (Ioo l r), ‖u t‖ ≤ R) →
      ∀ t ∈ Icc l r,
        Metric.infDist (u t) (vacuum a) ^ 2 ≤
          C * (ε + ε ^ 2 / (r - l)) *
            ∫ s in Ioo l r, (1 / 2 : ℝ) * ‖g s‖ ^ 2 + ε⁻¹ ^ 2 * bulkPotential a (u s) := by
  obtain ⟨K, _, hcoercive⟩ := vacuumDistance_sq_le_bulkPotential_of_norm_le a R
  let M := max 1 K
  have hM₁ : 1 ≤ M := le_max_left _ _
  refine ⟨2 * M, mul_pos (by norm_num) (zero_lt_one.trans_le hM₁), ?_⟩
  intro l r hlr ε hε u g hu hg hinc hRange t ht
  letI : CompleteSpace S0 := complete_of_proper
  let b : ℝ → ℝ := fun x => bulkPotential a (u x)
  have huRange : ∀ x ∈ Icc l r, ‖u x‖ ≤ R := by
    have hClosed : IsClosed {p : S0 | ‖p‖ ≤ R} := isClosed_le continuous_norm continuous_const
    exact StratificationTheory.absolutelyContinuous_interval_mem_closed_of_ae hlr hu
      EventuallyEq.rfl hClosed hRange
  have hSq (x : ℝ) (hx : x ∈ Icc l r) : Metric.infDist (u x) (vacuum a) ^ 2 ≤ M * b x :=
    (hcoercive _ (huRange x hx)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (bulkPotential_nonneg a _))
  have hbi : IntegrableOn b (Ioo l r) := by
    have hcont : ContinuousOn b (uIcc l r) :=
      (contDiff_bulkPotential a).continuous.comp_continuousOn hu.continuousOn
    exact hcont.intervalIntegrable.1.mono_set Ioo_subset_Ioc_self
  exact edge_sq_le_interval_penalizedEnergy (E := S0) (Metric.lipschitz_infDist_pt (vacuum a))
    (fun _ => Metric.infDist_nonneg) (fun _ => bulkPotential_nonneg a _) hM₁ hlr hε hu hg hinc hSq hbi t ht

end Thesis

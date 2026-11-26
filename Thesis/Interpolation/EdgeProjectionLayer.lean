module

public import Thesis.Interpolation.PenalizedEdge
public import Thesis.Interpolation.PenalizedShell
public import Thesis.Foundation.SpectralProjection
import StratificationTheory.Foundation.IntervalWeakRepresentative

/-! One material tube contains all sampled edges at the projection-layer scale. -/

public section

open Filter MeasureTheory Set
open scoped BigOperators ContDiff Matrix.Norms.Frobenius NNReal Topology

namespace Thesis

private theorem projectionShell_edge_scale (ε : ElasticScale) {k : ℝ} (hk : 0 < k) :
    ((ε : ℝ) + (ε : ℝ) ^ 2 / (k * projectionShellThickness ε)) *
        (Real.log ((ε : ℝ)⁻¹) / projectionShellThickness ε) =
      Real.sqrt (ε : ℝ) + (ε : ℝ) / (k * Real.log ((ε : ℝ)⁻¹)) := by
  let s := Real.sqrt (ε : ℝ)
  let L := Real.log ((ε : ℝ)⁻¹)
  have hs : 0 < s := Real.sqrt_pos.2 ε.property.1
  have hL : 0 < L := Real.log_pos ((one_lt_inv₀ ε.property.1).2 ε.property.2)
  have hsq : s ^ 2 = (ε : ℝ) := Real.sq_sqrt ε.property.1.le
  change ((ε : ℝ) + (ε : ℝ) ^ 2 / (k * (s * L))) * (L / (s * L)) =
    s + (ε : ℝ) / (k * L)
  rw [← hsq]
  field_simp [hs.ne', hL.ne', hk.ne']

private theorem tendsto_projectionShell_edge_scale (k : ℝ) :
    Tendsto (fun ε : ℝ => Real.sqrt ε + ε / (k * Real.log ε⁻¹)) (𝓝[>] 0) (𝓝 0) := by
  have hId : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hS := (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.comp hId
  have hL : Tendsto (fun ε : ℝ => Real.log ε⁻¹) (𝓝[>] 0) atTop := by
    simpa only [Real.log_inv, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hI := hId.mul hL.inv_tendsto_atTop |>.mul_const k⁻¹
  simpa only [Function.comp_def, Real.sqrt_zero, zero_mul, add_zero, div_eq_mul_inv, mul_inv_rev,
    Pi.inv_apply, mul_assoc] using hS.add hI

/-- A single threshold makes the whole family of closed edge intervals lie
in any prescribed material tube. The input edge budgets are the common mesh
bounds after using the logarithmic surface-energy bound. -/
theorem exists_edge_vacuumTube_threshold (a : BulkCoefficients) (R : ℝ) {k G δ : ℝ}
    (hk : 0 < k) (hδ : 0 < δ) :
    ∃ ε₀ ∈ Ioo (0 : ℝ) 1, ∀ (ε : ElasticScale), (ε : ℝ) < ε₀ → ∀ {l r : ℝ},
      k * projectionShellThickness ε ≤ r - l → ∀ {u g : ℝ → S0},
      AbsolutelyContinuousOnInterval u l r →
      MemLp g 2 (volume.restrict (Ioo l r)) →
      (∀ x ∈ Icc l r, ∀ y ∈ Icc l r, u y - u x = ∫ t in x..y, g t) →
      (∀ᵐ t ∂volume.restrict (Ioo l r), ‖u t‖ ≤ R) →
      (∫ t in Ioo l r, (1 / 2 : ℝ) * ‖g t‖ ^ 2 + (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (u t)) ≤
        G * (Real.log ((ε : ℝ)⁻¹) / projectionShellThickness ε) →
      ∀ t ∈ Icc l r, u t ∈ vacuumTube a δ := by
  obtain ⟨C, hC, hBound⟩ := edge_vacuumDistance_sq_le_penalizedEnergy a R
  have hSmall : ∀ᶠ e : ℝ in 𝓝[>] 0,
      C * G * (Real.sqrt e + e / (k * Real.log e⁻¹)) < δ ^ 2 := by
    have h := (tendsto_projectionShell_edge_scale k).const_mul (C * G)
    rw [mul_zero] at h
    exact h (Iio_mem_nhds (pow_pos hδ 2))
  obtain ⟨e₀, he₀, hThreshold⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hSmall
  refine ⟨min e₀ (1 / 2), ⟨lt_min he₀ (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩, ?_⟩
  intro ε hε l r hLength u g hu hg hinc hR hE t ht
  let h := projectionShellThickness ε
  let L := Real.log ((ε : ℝ)⁻¹)
  let E := ∫ t in Ioo l r, (1 / 2 : ℝ) * ‖g t‖ ^ 2 + (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (u t)
  have hh : 0 < h := projectionShellThickness_pos ε
  have hkh : 0 < k * h := mul_pos hk hh
  have hlr : l < r := sub_pos.mp (hkh.trans_le hLength)
  have hD := hBound hlr ε.property.1 hu hg hinc hR t ht
  change Metric.infDist (u t) (vacuum a) ^ 2 ≤ C * ((ε : ℝ) + (ε : ℝ) ^ 2 / (r - l)) * E at hD
  have hDiv : (ε : ℝ) ^ 2 / (r - l) ≤ (ε : ℝ) ^ 2 / (k * h) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hkh hLength
  have hE₀ : 0 ≤ E := integral_nonneg fun t => add_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg _)) (mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _))
  have hU : Metric.infDist (u t) (vacuum a) ^ 2 < δ ^ 2 := calc
    _ ≤ C * ((ε : ℝ) + (ε : ℝ) ^ 2 / (r - l)) * E := hD
    _ ≤ C * ((ε : ℝ) + (ε : ℝ) ^ 2 / (k * h)) * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add le_rfl hDiv) hC.le) hE₀
    _ ≤ C * ((ε : ℝ) + (ε : ℝ) ^ 2 / (k * h)) * (G * (L / h)) :=
      mul_le_mul_of_nonneg_left hE (mul_nonneg hC.le (add_nonneg ε.property.1.le
        (div_nonneg (sq_nonneg _) hkh.le)))
    _ = C * G * (((ε : ℝ) + (ε : ℝ) ^ 2 / (k * h)) * (L / h)) := by ring
    _ = C * G * (Real.sqrt (ε : ℝ) + (ε : ℝ) / (k * L)) := by
      rw [projectionShell_edge_scale ε hk]
    _ < δ ^ 2 := hThreshold ⟨ε.property.1, hε.trans_le (min_le_left _ _)⟩
  exact (sq_lt_sq₀ Metric.infDist_nonneg hδ.le).mp hU

private theorem ac_comp_lipschitzOn {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {u : ℝ → E} {l r : ℝ} {p : E → F} {K : ℝ≥0} {S : Set E}
    (hp : LipschitzOnWith K p S) (huS : MapsTo u (uIcc l r) S)
    (hu : AbsolutelyContinuousOnInterval u l r) : AbsolutelyContinuousOnInterval (p ∘ u) l r := by
  rw [absolutelyContinuousOnInterval_iff] at hu ⊢
  intro ε hε
  have hK : 0 < (K : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, hδE⟩ := hu (ε / ((K : ℝ) + 1)) (div_pos hε hK)
  refine ⟨δ, hδ, fun E hE hSmall => ?_⟩
  have hEach := hE.1
  have hBound : (∑ i ∈ Finset.range E.1, dist (p (u (E.2 i).1)) (p (u (E.2 i).2))) ≤
      ((K : ℝ) + 1) * ∑ i ∈ Finset.range E.1, dist (u (E.2 i).1) (u (E.2 i).2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    obtain ⟨h₁, h₂⟩ := hEach i hi
    exact (hp.dist_le_mul _ (huS h₁) _ (huS h₂)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) dist_nonneg)
  apply hBound.trans_lt
  exact (lt_div_iff₀' hK).1 (hδE E hE hSmall)

private theorem integral_increments_of_ac_ae_hasDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {u g : ℝ → E} {l r : ℝ} (hlr : l < r) (hu : AbsolutelyContinuousOnInterval u l r)
    (hg : MemLp g 2 (volume.restrict (Ioo l r)))
    (hder : ∀ᵐ x ∂volume.restrict (Ioo l r), HasDerivAt u (g x) x) :
    ∀ s ∈ Icc l r, ∀ t ∈ Icc l r, u t - u s = ∫ x in s..t, g x := by
  intro s hs t ht
  have hs' : s ∈ uIcc l r := by rwa [uIcc_of_le hlr.le]
  have ht' : t ∈ uIcc l r := by rwa [uIcc_of_le hlr.le]
  have hInt := StratificationTheory.intervalIntegrable_of_memLp_two hlr.le hg
  let G : ℝ → E := fun y => ∫ x in s..y, g x
  have hG : AbsolutelyContinuousOnInterval G l r :=
    StratificationTheory.intervalPrimitive_absolutelyContinuous hInt hs'
  have hu' := (ae_restrict_iff' measurableSet_Ioo).1 hder
  have hne (a : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a := by
    rw [ae_iff]
    simpa only [ne_eq, not_not, setOf_eq_eq_singleton] using
      (measure_singleton a : volume {a} = 0)
  have hv : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ uIcc l r → HasDerivAt (u - G) 0 x := by
    filter_upwards [hu', hInt.ae_hasDerivAt_integral, hne l, hne r] with x h₁ h₂ hxl hxr hx
    have hx' : x ∈ Icc l r := by rwa [uIcc_of_le hlr.le] at hx
    have hOpen : x ∈ Ioo l r := ⟨lt_of_le_of_ne hx'.1 (Ne.symm hxl), lt_of_le_of_ne hx'.2 hxr⟩
    simpa only [sub_self] using (h₁ hOpen).sub (h₂ hx s hs')
  obtain ⟨C, hC⟩ := (hu.sub hG).const_of_ae_hasDerivAt_zero hv
  have h₁ : u s = C := by simpa only [Pi.sub_apply, G, intervalIntegral.integral_same, sub_zero] using hC s hs'
  have h₂ : u t - G t = u s := (hC t ht').trans h₁.symm
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp h₂).trans (add_comm _ _))

/-- Near the actual vacuum, each of the two consecutive spectral gaps remains
at least half the vacuum radius. -/
theorem orderedEigenvalue_gaps_ge_half_of_vacuumDistance_le (a : BulkCoefficients) (A : S0)
    (hDist : Metric.infDist A (vacuum a) ≤ vacuumRadius a / 4) :
    vacuumRadius a / 2 ≤ orderedEigenvalue A 0 - orderedEigenvalue A 1 ∧
    vacuumRadius a / 2 ≤ orderedEigenvalue A 1 - orderedEigenvalue A 2 := by
  let d := Metric.infDist A (vacuum a)
  let r := vacuumRadius a
  let x := orderedEigenvalue A 0 - r
  let y := orderedEigenvalue A 1
  let z := orderedEigenvalue A 2 + r
  have hd : 0 ≤ d := Metric.infDist_nonneg
  have hsum : d ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := infDist_vacuum_sq_eq_orderedEigenvalue a A
  have hX : |x| ≤ d := (sq_le_sq₀ (abs_nonneg _) hd).mp (by
    rw [sq_abs, hsum]
    linarith only [sq_nonneg y, sq_nonneg z])
  have hY : |y| ≤ d := (sq_le_sq₀ (abs_nonneg _) hd).mp (by
    rw [sq_abs, hsum]
    linarith only [sq_nonneg x, sq_nonneg z])
  have hZ : |z| ≤ d := (sq_le_sq₀ (abs_nonneg _) hd).mp (by
    rw [sq_abs, hsum]
    linarith only [sq_nonneg x, sq_nonneg y])
  obtain ⟨hx, _⟩ := abs_le.mp hX
  obtain ⟨hy, hy'⟩ := abs_le.mp hY
  obtain ⟨_, hz⟩ := abs_le.mp hZ
  change d ≤ r / 4 at hDist
  dsimp only [x, y, z, r] at hx hy hy' hz hDist
  constructor <;> linarith only [hDist, hx, hy, hy', hz]

private theorem smooth_comp_edge {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : ℝ≥0} {l r : ℝ} {u g : ℝ → E} {p : E → F} {S : Set E}
    (hlr : l < r) (hp : ContDiff ℝ 1 p) (hS : Convex ℝ S)
    (hBound : ∀ A ∈ S, ‖fderiv ℝ p A‖₊ ≤ K) (huS : MapsTo u (uIcc l r) S)
    (hu : AbsolutelyContinuousOnInterval u l r) (hg : MemLp g 2 (volume.restrict (Ioo l r)))
    (hinc : ∀ x ∈ Icc l r, ∀ y ∈ Icc l r, u y - u x = ∫ t in x..y, g t) :
    let v := p ∘ u
    let G := fun t => fderiv ℝ p (u t) (g t)
    AbsolutelyContinuousOnInterval v l r ∧ MemLp G 2 (volume.restrict (Ioo l r)) ∧
      (∀ t ∈ Icc l r, ‖G t‖ ≤ (K : ℝ) * ‖g t‖) ∧
      ∀ s ∈ Icc l r, ∀ t ∈ Icc l r, v t - v s = ∫ x in s..t, G x := by
  intro v G
  have hdiff : Differentiable ℝ p := hp.differentiable one_ne_zero
  have hLip := hS.lipschitzOnWith_of_nnnorm_fderiv_le (fun A _ => hdiff A) hBound
  have hv : AbsolutelyContinuousOnInterval v l r := ac_comp_lipschitzOn hLip huS hu
  have hG (t : ℝ) (ht : t ∈ Icc l r) : ‖G t‖ ≤ (K : ℝ) * ‖g t‖ := by
    have ht' : t ∈ uIcc l r := by rwa [uIcc_of_le hlr.le]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (NNReal.coe_le_coe.mpr (hBound _ (huS ht'))) (norm_nonneg _))
  have hU : ContinuousOn u (Ioo l r) := hu.continuousOn.mono (by
    rw [uIcc_of_le hlr.le]
    exact Ioo_subset_Icc_self)
  have hD : ContinuousOn (fun t => fderiv ℝ p (u t)) (Ioo l r) :=
    (hp.continuous_fderiv one_ne_zero).comp_continuousOn hU
  have hEval : Continuous (fun A : (E →L[ℝ] F) × E => A.1 A.2) :=
    continuous_fst.clm_apply continuous_snd
  have hGmeas : AEStronglyMeasurable G (volume.restrict (Ioo l r)) :=
    hEval.comp_aestronglyMeasurable ((hD.aestronglyMeasurable measurableSet_Ioo).prodMk hg.1)
  have hGp : MemLp G 2 (volume.restrict (Ioo l r)) := (hg.norm.const_mul (K : ℝ)).mono' hGmeas
    ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => hG t (Ioo_subset_Icc_self ht))
  have hDer := ae_hasDerivAt_of_interval_increments hlr hg hinc
  have hDerV : ∀ᵐ t ∂volume.restrict (Ioo l r), HasDerivAt v (G t) t :=
    hDer.mono fun t ht => (hdiff (u t)).hasFDerivAt.comp_hasDerivAt t ht
  exact ⟨hv, hGp, hG, integral_increments_of_ac_ae_hasDerivAt hlr hv hGp hDerV⟩

private theorem exists_fderiv_bound_closedBall {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : E → F} (hp : ContDiff ℝ 1 p) (R : ℝ) :
    ∃ K : ℝ≥0, ∀ A ∈ Metric.closedBall (0 : E) R, ‖fderiv ℝ p A‖₊ ≤ K := by
  have hDer := hp.continuous_fderiv one_ne_zero
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hDer.continuousOn
  refine ⟨⟨max L 1, zero_le_one.trans (le_max_right _ _)⟩, fun A hA => ?_⟩
  exact NNReal.coe_le_coe.mp ((hL A hA).trans (le_max_left _ _))

private theorem norm_le_on_projectionTube {a : BulkCoefficients} (p : VacuumTubularProjection a)
    (A : vacuumTube a p.radius) : ‖A.val‖ ≤ Real.sqrt 2 * vacuumRadius a + 1 := by
  let Q := p.project A
  have hQ : ‖Q.val‖ = Real.sqrt 2 * vacuumRadius a := vacuum_norm Q.property
  have hD := p.dist_eq_infDist A
  have hOne : dist A.val Q.val ≤ 1 := by
    rw [hD]
    exact A.property.le.trans p.radius_lt_one.le
  rw [← dist_zero_right]
  calc
    dist A.val 0 ≤ dist A.val Q.val + dist Q.val 0 := dist_triangle _ _ _
    _ ≤ 1 + Real.sqrt 2 * vacuumRadius a := by rw [dist_zero_right, hQ]; exact add_le_add hOne le_rfl
    _ = _ := add_comm _ _

/-- Projection on a model-dependent vacuum tube preserves compatible edge
values and gives the original chain-rule derivative and segment energy control. -/
theorem exists_projected_edge_data (a : BulkCoefficients) :
    let p := vacuumTubularProjection a
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ p.radius ∧ 0 < C ∧
      ∀ {l r : ℝ}, l < r → ∀ {u g : ℝ → S0},
      AbsolutelyContinuousOnInterval u l r → MemLp g 2 (volume.restrict (Ioo l r)) →
      (∀ s ∈ Icc l r, ∀ t ∈ Icc l r, u t - u s = ∫ x in s..t, g x) →
      (∀ t ∈ Icc l r, u t ∈ vacuumTube a δ) →
      let v := p.extend ∘ u
      let G := fun t => fderiv ℝ p.extend (u t) (g t)
      AbsolutelyContinuousOnInterval v l r ∧ MemLp G 2 (volume.restrict (Ioo l r)) ∧
      (∀ s ∈ Icc l r, ∀ t ∈ Icc l r, v t - v s = ∫ x in s..t, G x) ∧
      ∀ t ∈ Icc l r,
        v t ∈ vacuum a ∧ ‖G t‖ ≤ C * ‖g t‖ ∧
        vacuumRadius a / 2 ≤ orderedEigenvalue (u t) 0 - orderedEigenvalue (u t) 1 ∧
        vacuumRadius a / 2 ≤ orderedEigenvalue (u t) 1 - orderedEigenvalue (u t) 2 ∧
        ‖u t - v t‖ ^ 2 ≤ C * bulkPotential a (u t) ∧
        ∀ τ ∈ Icc (0 : ℝ) 1, bulkPotential a (τ • u t + (1 - τ) • v t) ≤
          C * τ ^ 2 * bulkPotential a (u t) := by
  intro p
  obtain ⟨c, U, δ₀, hc, hU, hδ₀, hδTube, hBulk⟩ := bulkPotential_tubular_estimates a
  let δ := min δ₀ (vacuumRadius a / 4)
  have hδ : 0 < δ := lt_min hδ₀ (div_pos (vacuumRadius_pos a) (by norm_num))
  have hδr : δ ≤ p.radius := (min_le_left _ _).trans hδTube
  let B : Set S0 := Metric.closedBall 0 (Real.sqrt 2 * vacuumRadius a + 1)
  have hSmooth : ContDiff ℝ 1 p.extend := p.contDiff_extend.of_le (by simp)
  obtain ⟨K, hK⟩ := exists_fderiv_bound_closedBall (E := S0) (F := S0) hSmooth
    (Real.sqrt 2 * vacuumRadius a + 1)
  let C := max (K : ℝ) (max c⁻¹ U)
  have hC : 0 < C := hU.trans_le ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨δ, C, hδ, hδr, hC, ?_⟩
  intro l r hlr u g hu hg hinc hTube v G
  have hUball : MapsTo u (uIcc l r) B := by
    rw [uIcc_of_le hlr.le]
    intro t ht
    have hz : Metric.infDist (u t) (vacuum a) < δ := hTube t ht
    let A : vacuumTube a p.radius := ⟨u t, hz.trans_le hδr⟩
    simpa only [B, Metric.mem_closedBall, dist_zero_right] using norm_le_on_projectionTube p A
  letI : CompleteSpace S0 := complete_of_proper
  obtain ⟨hv, hG, hGnorm, hVG⟩ := smooth_comp_edge (E := S0) (F := S0) hlr hSmooth
    (convex_closedBall _ _) hK hUball hu hg hinc
  refine ⟨hv, hG, hVG, ?_⟩
  intro t ht
  have hz : Metric.infDist (u t) (vacuum a) < δ := hTube t ht
  let A : vacuumTube a p.radius := ⟨u t, hz.trans_le hδr⟩
  have hExt : v t = (p.project A).val := p.extend_eq A
  have ⟨hLower, hUpper⟩ := hBulk A (hz.trans_le (min_le_left _ _))
  have hDist : ‖u t - v t‖ = Metric.infDist (u t) (vacuum a) := by
    rw [hExt, ← dist_eq_norm]
    exact p.dist_eq_infDist A
  have hCost : ‖u t - v t‖ ^ 2 ≤ c⁻¹ * bulkPotential a (u t) := by
    rw [hDist, ← div_eq_inv_mul]
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm c] using hLower)
  have ⟨hg₁, hg₂⟩ := orderedEigenvalue_gaps_ge_half_of_vacuumDistance_le a (u t)
    (hz.le.trans (min_le_right _ _))
  refine ⟨hExt.symm ▸ (p.project A).property, ?_, hg₁, hg₂, ?_, ?_⟩
  · exact (hGnorm t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · exact hCost.trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
      (bulkPotential_nonneg a (u t)))
  · intro τ hτ
    rw [hExt]
    exact (hUpper τ hτ).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (sq_nonneg _))
      (bulkPotential_nonneg a _))

end Thesis

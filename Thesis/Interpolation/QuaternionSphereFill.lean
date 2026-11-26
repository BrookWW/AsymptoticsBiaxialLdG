module

public import Thesis.Interpolation.QuaternionAmbientCollar
public import Thesis.Interpolation.SphereSobolevProjection
import StratificationTheory.Foundation.BoundedFiberL2Trace
import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Integral.Average

/-! Quaternion sphere filling with the actual radial Sobolev trace. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal

namespace Thesis

abbrev QuaternionBallTrace (n : ℕ) (b : ℝ) :=
  C(Icc b 1, Lp (Ambient 4) 2 (unitBoundarySurface n))

@[expose] def RepresentsQuaternionBallTrace {n : ℕ} {b : ℝ} (u : Domain n → Ambient 4)
    (H : QuaternionBallTrace n b) : Prop :=
  ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo b 1,
    ∃ htLp : MemLp (fun θ : UnitBoundarySphere n => u (t • θ.val)) 2 (unitBoundarySurface n),
      H ⟨t, ht.1.le, ht.2.le⟩ = htLp.toLp _

private theorem exists_corrected_quaternion_collar_trace {n : ℕ} (hn : 2 ≤ n)
    {v : UnitBoundarySphere n → Ambient 4} (hv : MemSphereW12 hn v)
    (hV : ∀ᵐ θ ∂unitBoundarySurface n, ‖v θ‖ = 1) {c : Ambient 4} (hc : ‖c‖ ≤ 1)
    {h : ℝ} (hh : 0 < h) (hh₂ : h ≤ 1 / 2) {y : QuaternionCoordinates} (hy : ‖y‖ < 1 / 4)
    {w : Domain n → Ambient 4}
    (hRaw : ∀ s ∈ Ioo (1 - h) 1, ∀ θ : UnitBoundarySphere n,
      w (s • θ.val) = c + ((s - (1 - h)) / h) • (v θ - c)) :
    ∃ b : ℝ, 0 < b ∧ ∃ hb : b < 1, ∃ H : QuaternionBallTrace n b,
      RepresentsQuaternionBallTrace (correctedSphereProjection y 0 ∘ w) H ∧
      H ⟨1, hb.le, le_rfl⟩ = hv.1.toLp v := by
  let σ := unitBoundarySurface n
  letI : IsFiniteMeasure σ := by
    dsimp only [σ, unitBoundarySurface]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere (by omega : 0 < n)]
    infer_instance
  let b := 1 - h / 8
  have hb : b < 1 := by dsimp only [b]; linarith
  have hb₀ : 0 < b := by dsimp only [b]; linarith
  have hb₁ : 1 - h < b := by dsimp only [b]; linarith
  let t (s : ℝ) := (s - (1 - h)) / h
  let z (θ : UnitBoundarySphere n) (s : ℝ) := c + t s • (v θ - c)
  let F := correctedSphereProjection y 0
  let f (p : UnitBoundarySphere n × ℝ) := F (z p.1 p.2)
  obtain ⟨_, _, hRestore⟩ := exists_fderiv_restoreSphereDirection_bound
  obtain ⟨hR, _⟩ := hRestore y hy.le
  have hF : Measurable F := hR.continuous.measurable.comp (by
    unfold regularizedSphereDirection regularizedSphereRadius
    fun_prop)
  have hMeas (s : ℝ) : AEStronglyMeasurable (fun θ => f (θ,s)) σ :=
    (hF.comp_aemeasurable (aestronglyMeasurable_const.add
      ((hv.1.aestronglyMeasurable.sub aestronglyMeasurable_const).const_smul (t s))).aemeasurable).aestronglyMeasurable
  have hCont : ∀ᵐ θ ∂σ, ContinuousOn (fun s => f (θ,s)) (Icc b 1) := by
    filter_upwards [hV] with θ hθ
    intro s hs
    have ht : 7 / 8 ≤ t s ∧ t s ≤ 1 := by
      refine ⟨(le_div_iff₀ hh).2 ?_, (div_le_one hh).2 ?_⟩
      · have hs₁ := hs.1
        dsimp only [b] at hs₁
        linarith
      · have hs₂ := hs.2
        linarith
    have hDist : ‖v θ - z θ s‖ ≤ 1 / 4 := by
      have hEq : v θ - z θ s = (1 - t s) • (v θ - c) := by
        dsimp only [z]
        rw [sub_smul, one_smul]
        abel
      rw [hEq, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht.2)]
      calc
        _ ≤ (1 - t s) * (‖v θ‖ + ‖c‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (sub_nonneg.mpr ht.2)
        _ ≤ (1 / 8 : ℝ) * (1 + 1) :=
          mul_le_mul (by linarith [ht.1]) (by linarith) (by positivity) (by norm_num)
        _ = _ := by norm_num
    have hZ : z θ s ≠ y := by
      intro hz
      have h := norm_add_le (v θ - z θ s) (z θ s)
      rw [sub_add_cancel, hθ, hz] at h
      rw [hz] at hDist
      linarith
    have hz : Continuous (z θ) := by dsimp only [z, t]; fun_prop
    have hContF : ContinuousAt F (z θ s) :=
      hR.continuous.continuousAt.comp
        (contDiffAt_regularizedSphereDirection (δ := 0) (Or.inl hZ)).continuousAt
    exact (hContF.comp hz.continuousAt).continuousWithinAt
  have hBound : ∀ᵐ θ ∂σ, ∀ s ∈ Icc b 1, ‖f (θ,s)‖ ≤ 2 :=
    ae_of_all _ fun _ _ _ => norm_correctedSphereProjection_le_two hy.le 0 _
  obtain ⟨H, hH, _⟩ := exists_continuous_L2_trace_of_bounded_fiber_continuity σ hb
    (ae_of_all _ fun s _ => hMeas s) hCont hBound
  refine ⟨b, hb₀, hb, H, ?_, ?_⟩
  · refine ae_of_all _ fun s hs => ?_
    obtain ⟨hsLp, hSlice⟩ := hH ⟨s, hs.1.le, hs.2.le⟩
    have hEq : (fun θ => f (θ,s)) = fun θ : UnitBoundarySphere n => F (w (s • θ.val)) := by
      funext θ
      rw [hRaw s ⟨hb₁.trans hs.1, hs.2⟩ θ]
    let hsLp' := hsLp.ae_eq (Eventually.of_forall (congrFun hEq))
    exact ⟨hsLp', hSlice.trans (MemLp.toLp_congr hsLp hsLp' (Eventually.of_forall (congrFun hEq)))⟩
  · obtain ⟨hLp, hSlice⟩ := hH ⟨1, hb.le, le_rfl⟩
    refine hSlice.trans (MemLp.toLp_congr hLp hv.1 ?_)
    filter_upwards [hV] with θ hθ
    change F (z θ 1) = v θ
    have ht : t 1 = 1 := by
      dsimp only [t]
      rw [show 1 - (1 - h) = h by ring, div_self hh.ne']
    rw [show z θ 1 = v θ by dsimp only [z]; rw [ht, one_smul]; abel]
    exact correctedSphereProjection_zero_apply_of_norm_eq_one hy.le hθ

/-- The bounded ambient collar projects to a sphere-valued filling with the
same radial trace and with a uniform two-term Dirichlet energy bound. -/
theorem exists_quaternion_sphere_fill_collar : ∃ K : ℝ, 0 < K ∧
    ∀ {n : ℕ} (hn : 2 ≤ n) (v : UnitBoundarySphere n → Ambient 4) (hv : MemSphereW12 hn v),
      (∀ᵐ θ ∂unitBoundarySurface n, ‖v θ‖ = 1) →
      ∀ c : Ambient 4, ‖c‖ ≤ 1 → ∀ h : ℝ, 0 < h → h ≤ 1 / 2 →
      ∃ (b : ℝ) (hb : b < 1) (u : Domain n → Ambient 4) (Du : Domain n → HarmonicMaps.Gradient n 4)
        (H : QuaternionBallTrace n b),
        0 < b ∧ MemW12 (ballDomain (0 : Domain n) 1) u Du ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ‖u x‖ = 1) ∧
        RepresentsQuaternionBallTrace u H ∧ H ⟨1, hb.le, le_rfl⟩ = hv.1.toLp v ∧
        (∫ x in ball (0 : Domain n) 1, hsNormSq (Du x)) ≤
          K * (h / 2 * quaternionBoundaryEnergy hn v hv +
            h⁻¹ * ∫ θ : UnitBoundarySphere n, ‖v θ - c‖ ^ 2 ∂unitBoundarySurface n) := by
  obtain ⟨K, hK, hProj⟩ := exists_correctedSphereProjection_memW12
  let C := max 1 K.toReal
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨4 * C, mul_pos (by norm_num) hC, ?_⟩
  intro n hn v hv hV c hc h hh hh₂
  obtain ⟨w, Dw, hw, hBound, hRaw, hE⟩ :=
    exists_quaternion_ambient_affine_collar hn v hv (hV.mono fun _ h => h.le) c hc hh hh₂
  let Ω := ballDomain (0 : Domain n) 1
  letI : IsFiniteMeasure (volume.restrict Ω.val) := by
    refine ⟨?_⟩
    change ((volume : Measure (Domain n)).restrict (ball 0 1)) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  obtain ⟨y, hy, hUW, hSphere, hEnergy⟩ := hProj Ω hw hBound
  obtain ⟨b, hb₀, hb, H, hTrace, hEndpoint⟩ :=
    exists_corrected_quaternion_collar_trace hn hv hV hc hh hh₂ hy hRaw
  refine ⟨b, hb, _, _, H, hb₀, hUW, hSphere, hTrace, hEndpoint, ?_⟩
  rw [HarmonicMaps.dirichletEnergy_eq_ofReal_integral hUW.integrable_hsNormSq,
    HarmonicMaps.dirichletEnergy_eq_ofReal_integral hw.integrable_hsNormSq] at hEnergy
  have hNonneg {D : Domain n → HarmonicMaps.Gradient n 4} :
      0 ≤ ∫ x in Ω.val, hsNormSq (D x) := integral_nonneg fun _ => hsNormSq_nonneg _
  have hReal := ENNReal.toReal_mono (ENNReal.mul_lt_top hK ENNReal.ofReal_lt_top).ne hEnergy
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hNonneg, ENNReal.toReal_ofReal hNonneg] at hReal
  refine hReal.trans ((mul_le_mul_of_nonneg_right (le_max_right 1 K.toReal) hNonneg).trans ?_)
  exact (mul_le_mul_of_nonneg_left hE hC.le).trans_eq (by ring)

/-- The standard round-sphere Poincaré inequality for four Euclidean coordinates. -/
@[expose] def External.QuaternionSpherePoincare (n : ℕ) (hn : 2 ≤ n) : Prop :=
  ∃ P : ℝ, 0 < P ∧ ∀ (v : UnitBoundarySphere n → Ambient 4) (hv : MemSphereW12 hn v),
    (∫ θ : UnitBoundarySphere n, ‖v θ - average (unitBoundarySurface n) v‖ ^ 2 ∂unitBoundarySurface n) ≤
      P * quaternionBoundaryEnergy hn v hv

private theorem norm_average_le_one {n : ℕ} (σ : Measure (UnitBoundarySphere n)) [IsFiniteMeasure σ]
    {v : UnitBoundarySphere n → Ambient 4} (hv : ∀ᵐ θ ∂σ, ‖v θ‖ ≤ 1) :
    ‖average σ v‖ ≤ 1 := by
  rw [average_eq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr measureReal_nonneg)]
  by_cases h : σ.real univ = 0
  · simp [h]
  have hI := norm_integral_le_of_norm_le_const hv
  calc
    _ ≤ (σ.real univ)⁻¹ * (1 * σ.real univ) :=
      mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr measureReal_nonneg)
    _ = 1 := by rw [one_mul, inv_mul_cancel₀ h]

/-- One sphere extension has both the linear and quadratic boundary-gradient
energy bounds on the unit ball. -/
theorem exists_quaternion_sphere_fill_unit {n : ℕ} (hn : 2 ≤ n)
    (hP : External.QuaternionSpherePoincare n hn) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : UnitBoundarySphere n → Ambient 4) (hv : MemSphereW12 hn v),
      (∀ᵐ θ ∂unitBoundarySurface n, ‖v θ‖ = 1) →
      ∃ (b : ℝ) (hb : b < 1) (u : Domain n → Ambient 4) (Du : Domain n → HarmonicMaps.Gradient n 4)
        (H : QuaternionBallTrace n b),
        0 < b ∧ MemW12 (ballDomain (0 : Domain n) 1) u Du ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ‖u x‖ = 1) ∧
        RepresentsQuaternionBallTrace u H ∧ H ⟨1, hb.le, le_rfl⟩ = hv.1.toLp v ∧
        (∫ x in ball (0 : Domain n) 1, hsNormSq (Du x)) ≤
          C * min (quaternionBoundaryEnergy hn v hv) (Real.sqrt (quaternionBoundaryEnergy hn v hv)) := by
  obtain ⟨K, hK, hFill⟩ := exists_quaternion_sphere_fill_collar
  obtain ⟨P, hP, hPoincare⟩ := hP
  let σ := unitBoundarySurface n
  letI : IsFiniteMeasure σ := by
    dsimp only [σ, unitBoundarySurface]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere (by omega : 0 < n)]
    infer_instance
  let S := σ.real univ
  let A := max ((1 / 4 : ℝ) + 2 * P) (1 / 4 + 2 * S)
  have hA : 0 < A := (by linarith : 0 < (1 / 4 : ℝ) + 2 * P).trans_le (le_max_left _ _)
  refine ⟨K * A, mul_pos hK hA, ?_⟩
  intro v hv hV
  let E := quaternionBoundaryEnergy hn v hv
  let R := Real.sqrt E
  have hE₀ : 0 ≤ E := by
    dsimp only [E, quaternionBoundaryEnergy]
    exact integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hR₀ : 0 ≤ R := Real.sqrt_nonneg _
  have hR₂ : R ^ 2 = E := Real.sq_sqrt hE₀
  have hChoose : ∃ (c : Ambient 4) (h : ℝ), ‖c‖ ≤ 1 ∧ 0 < h ∧ h ≤ 1 / 2 ∧
      h / 2 * E + h⁻¹ * (∫ θ : UnitBoundarySphere n, ‖v θ - c‖ ^ 2 ∂σ) ≤ A * min E R := by
    by_cases he : E ≤ 1
    · have hr : R ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt he
      have heR : E ≤ R := hR₂ ▸ (by nlinarith [mul_nonneg hR₀ (sub_nonneg.mpr hr)] : R ^ 2 ≤ R)
      let c := average σ v
      refine ⟨c, 1 / 2, norm_average_le_one σ (hV.mono fun _ h => h.le),
        by norm_num, le_rfl, ?_⟩
      rw [min_eq_left heR]
      calc
        _ ≤ (1 / 2 : ℝ) / 2 * E + (1 / 2)⁻¹ * (P * E) :=
          add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hPoincare v hv)
            (by norm_num : 0 ≤ ((1 / 2 : ℝ)⁻¹)))
        _ = (1 / 4 + 2 * P) * E := by norm_num; ring
        _ ≤ A * E := mul_le_mul_of_nonneg_right (le_max_left _ _) hE₀
    · have hr : 1 < R := by nlinarith [lt_of_not_ge he]
      have hrE : R ≤ E := by nlinarith [mul_nonneg hR₀ (sub_nonneg.mpr hr.le)]
      let h : ℝ := (2 * R)⁻¹
      have hh : 0 < h := by dsimp only [h]; positivity
      have hh₂ : h ≤ 1 / 2 := by
        dsimp only [h]
        rw [inv_le_comm₀ (by positivity : 0 < 2 * R) (by norm_num : 0 < (1 / 2 : ℝ))]
        norm_num
        linarith
      refine ⟨0, h, by simp, hh, hh₂, ?_⟩
      have hp : (∫ θ : UnitBoundarySphere n, ‖v θ - (0 : Ambient 4)‖ ^ 2 ∂σ) = S := by
        calc
          _ = ∫ _ : UnitBoundarySphere n, (1 : ℝ) ∂σ := by
            apply integral_congr_ae
            filter_upwards [hV] with θ hθ
            simp only [sub_zero, hθ, one_pow]
          _ = S := by simp only [integral_const, smul_eq_mul, mul_one, S]
      have hLinear : h / 2 * E + h⁻¹ * S = (1 / 4 + 2 * S) * R := by
        dsimp only [h]
        rw [← hR₂, inv_inv]
        field_simp
        ring
      rw [min_eq_right hrE, hp, hLinear]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hR₀
  obtain ⟨c, h, hc, hh, hh₂, hBudget⟩ := hChoose
  obtain ⟨b, hb, u, Du, H, hb₀, hU, hSphere, hTrace, hBoundary, hEnergy⟩ :=
    hFill hn v hv hV c hc h hh hh₂
  exact ⟨b, hb, u, Du, H, hb₀, hU, hSphere, hTrace, hBoundary,
    hEnergy.trans ((mul_le_mul_of_nonneg_left hBudget hK.le).trans_eq (by ring))⟩

end Thesis

module

public import Thesis.Foundation.QuaternionLoopSobolev

/-! Explicit quaternion arcs and their biaxial loop energies. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius Quaternion Topology

namespace Thesis

private def quaternionArc (e : ℍ) (speed t : ℝ) : ℍ :=
  Real.cos (speed * t) • (1 : ℍ) + Real.sin (speed * t) • e

private theorem quaternionArc_unit {e : ℍ} (he : e.re = 0) (hE : ‖e‖ = 1) (speed t : ℝ) :
    ‖quaternionArc e speed t‖ = 1 := by
  have horth : inner ℝ (1 : ℍ) e = 0 := by
    rw [Quaternion.inner_def, one_mul, Quaternion.re_star, he]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [quaternionArc, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, horth]
  simp only [norm_smul, norm_one, hE, mul_one, Real.norm_eq_abs, sq_abs, mul_zero, add_zero, one_pow]
  rw [add_comm, Real.sin_sq_add_cos_sq]

private theorem contDiff_quaternionArc (e : ℍ) (speed : ℝ) :
    ContDiff ℝ ∞ (quaternionArc e speed) := by
  have harg : ContDiff ℝ ∞ (fun t : ℝ => speed * t) := contDiff_const.mul contDiff_id
  exact ((Real.contDiff_cos.comp harg).smul contDiff_const).add
    ((Real.contDiff_sin.comp harg).smul contDiff_const)

private theorem hasDerivAt_quaternionArc {e : ℍ} (he : e.re = 0) (hE : ‖e‖ = 1) (speed t : ℝ) :
    HasDerivAt (quaternionArc e speed) (quaternionArc e speed t * (speed • e)) t := by
  have harg : HasDerivAt (fun s : ℝ => speed * s) speed t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul speed
  have hcos := ((Real.hasDerivAt_cos (speed * t)).comp t harg).smul_const (1 : ℍ)
  have hsin := ((Real.hasDerivAt_sin (speed * t)).comp t harg).smul_const e
  have hd := hcos.add hsin
  have he2 : e * e = -1 := imaginaryUnit_square he hE
  have hvel : quaternionArc e speed t * (speed • e) =
      (-Real.sin (speed * t) * speed) • (1 : ℍ) + (Real.cos (speed * t) * speed) • e := by
    simp only [quaternionArc, mul_smul_comm, add_mul, smul_mul_assoc, one_mul, he2,
      smul_neg, smul_add, smul_smul, mul_comm speed, neg_mul, neg_smul, add_comm]
  rw [hvel]
  exact hd

private theorem quaternionArc_zero (e : ℍ) (speed : ℝ) : quaternionArc e speed 0 = 1 := by
  simp [quaternionArc]

private theorem quaternionArc_quarter_end (e : ℍ) : quaternionArc e (1 / 4) (2 * Real.pi) = e := by
  rw [quaternionArc, show (1 / 4 : ℝ) * (2 * Real.pi) = Real.pi / 2 by ring,
    Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, one_smul, zero_add]

private theorem quaternionArc_half_end (e : ℍ) :
    quaternionArc e (1 / 2) (2 * Real.pi) = -1 := by
  rw [quaternionArc, show (1 / 2 : ℝ) * (2 * Real.pi) = Real.pi by ring,
    Real.cos_pi, Real.sin_pi, zero_smul, add_zero, neg_smul, one_smul]

private theorem vacuumLoopParameter_val_of_mem {T x : ℝ} (hT : 0 < T) (hx : x ∈ Icc 0 T) :
    (vacuumLoopParameter T x : ℝ) = x / T := by
  have hmem : x / T ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hx.1 hT.le, (div_le_one hT).2 hx.2⟩
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one hmem)

private theorem quaternion_arc_loop (a : BulkCoefficients) (v₀ : Sphere3)
    {e : ℍ} (he : e.re = 0) (hE : ‖e‖ = 1) (speed : ℝ) (g : QuaternionGroup 2)
    (hend : quaternionArc e speed (2 * Real.pi) = quaternionWordReal g) :
    ∃ γ : Path (vacuumQuaternionProjection a v₀) (vacuumQuaternionProjection a v₀),
      vacuumFundamentalGroupEquiv a v₀
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = g ∧
      AbsolutelyContinuousOnInterval (vacuumLoopTensor γ (2 * Real.pi)) 0 (2 * Real.pi) ∧
      MemLp (deriv (vacuumLoopTensor γ (2 * Real.pi))) 2 (volume.restrict (Ioo 0 (2 * Real.pi))) ∧
      (∫ x in 0..(2 * Real.pi), (1 / 2 : ℝ) * ‖deriv (vacuumLoopTensor γ (2 * Real.pi)) x‖ ^ 2) =
        (2 * Real.pi) * (4 * vacuumRadius a ^ 2 *
          ((speed • e).imI ^ 2 + (speed • e).imJ ^ 2 + 4 * (speed • e).imK ^ 2)) := by
  let T : ℝ := 2 * Real.pi
  have hT : 0 < T := by dsimp only [T]; positivity
  let q₀ := Quaternion.linearIsometryEquivTuple.symm v₀.val
  have hq₀ : ‖q₀‖ = 1 := quaternionTuple_symm_norm_eq_one v₀
  let q (x : ℝ) := q₀ * quaternionArc e speed x
  have hqUnit (x : ℝ) : ‖q x‖ = 1 := by
    simp only [q, norm_mul, hq₀, quaternionArc_unit he hE, one_mul]
  let v (x : ℝ) : Sphere3 := sphereOfQuaternion (q x) (hqUnit x)
  have hqv (x : ℝ) : Quaternion.linearIsometryEquivTuple.symm (v x).val = q x :=
    quaternion_of_sphereOfQuaternion (q x) (hqUnit x)
  have hqSmooth : ContDiff ℝ ∞ q := contDiff_const.mul (contDiff_quaternionArc e speed)
  have hv : Continuous v := by
    apply Continuous.subtype_mk
    exact Quaternion.linearIsometryEquivTuple.continuous.comp hqSmooth.continuous
  have hv₀ : v 0 = v₀ := by
    apply Subtype.ext
    apply Quaternion.linearIsometryEquivTuple.symm.injective
    rw [hqv]
    change q₀ * quaternionArc e speed 0 = q₀
    rw [quaternionArc_zero, mul_one]
  have hvT : v T = g⁻¹ • v₀ := by
    apply Subtype.ext
    apply Quaternion.linearIsometryEquivTuple.symm.injective
    rw [hqv, quaternionTuple_symm_smul, inv_inv]
    change q₀ * quaternionArc e speed (2 * Real.pi) = q₀ * quaternionWordReal g
    rw [hend]
  let Γ : C(unitInterval, Sphere3) :=
    ⟨fun s => v (T * s.val), hv.comp (continuous_const.mul continuous_subtype_val)⟩
  have hΓ₀ : Γ 0 = v₀ := by change v (T * 0) = v₀; rwa [mul_zero]
  have hΓ₁ : Γ 1 = g⁻¹ • v₀ := by change v (T * 1) = _; rwa [mul_one]
  let γ : Path (vacuumQuaternionProjection a v₀) (vacuumQuaternionProjection a v₀) :=
    { toContinuousMap := ⟨fun s => vacuumQuaternionProjection a (Γ s),
          (continuous_vacuumQuaternionProjection a).comp Γ.continuous⟩
      source' := congrArg (vacuumQuaternionProjection a) hΓ₀
      target' := (congrArg (vacuumQuaternionProjection a) hΓ₁).trans
        (vacuumQuaternionProjection_smul a g⁻¹ v₀) }
  have hclass : vacuumFundamentalGroupEquiv a v₀
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = g := by
    obtain ⟨Γ', hΓ'₀, hΓ'proj, hΓ'end⟩ := vacuumLoop_exists_lift a v₀ γ
    have heq : (fun s => Γ' s) = Γ :=
      (vacuumQuaternionProjection_isCoveringMap a).eq_of_comp_eq
        Γ'.continuous Γ.continuous (funext fun s => hΓ'proj s) 0 (hΓ'₀.trans hΓ₀.symm)
    have h₁ := congrFun heq 1
    rw [h₁, hΓ₁, quaternionTuple_symm_smul, inv_inv] at hΓ'end
    apply quaternionWordReal_injective
    have hnz : q₀ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hq₀
      exact zero_ne_one hq₀
    exact mul_left_cancel₀ hnz hΓ'end.symm
  let Q (x : ℝ) : Tensor := (cover a (v x) : Tensor)
  have hqV : (fun x => Quaternion.linearIsometryEquivTuple.symm (v x).val) = q := funext hqv
  have hQ : ContDiff ℝ ∞ Q := contDiff_cover_curve a v (hqV ▸ hqSmooth)
  have hpath : EqOn (vacuumLoopTensor γ T) Q (Icc 0 T) := by
    intro x hx
    change ((vacuumQuaternionProjection a (v (T * (vacuumLoopParameter T x).val))).val : Tensor) = _
    rw [vacuumLoopParameter_val_of_mem hT hx, show T * (x / T) = x by field_simp,
      vacuumQuaternionProjection_val]
  have hAC : AbsolutelyContinuousOnInterval (vacuumLoopTensor γ T) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hT.le]
    exact (hQ.of_le (by decide : (1 : ℕ∞ω) ≤ ∞)).contDiffOn.congr hpath
  let c : ℝ := 4 * vacuumRadius a ^ 2 *
    ((speed • e).imI ^ 2 + (speed • e).imJ ^ 2 + 4 * (speed • e).imK ^ 2)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hmetric (x : ℝ) (hx : x ∈ Ioo 0 T) :
      (1 / 2 : ℝ) * ‖deriv (vacuumLoopTensor γ T) x‖ ^ 2 = c := by
    have hd : HasDerivAt q (q x * (speed • e)) x := by
      simpa only [q, mul_assoc] using (hasDerivAt_quaternionArc he hE speed x).const_mul q₀
    have hdv : HasDerivAt (fun y => Quaternion.linearIsometryEquivTuple.symm (v y).val)
        (q x * (speed • e)) x := by rwa [hqV]
    have hm := cover_curve_metric a v hdv
    let u := star (Quaternion.linearIsometryEquivTuple.symm (v x).val) * (q x * (speed • e))
    change (1 / 2 : ℝ) * ‖deriv Q x‖ ^ 2 =
      4 * vacuumRadius a ^ 2 * (u.imI ^ 2 + u.imJ ^ 2 + 4 * u.imK ^ 2) at hm
    have hu : u = speed • e := by
      change star (Quaternion.linearIsometryEquivTuple.symm (v x).val) * (q x * (speed • e)) = _
      rw [hqv, ← mul_assoc, quaternionUnit_star_mul (hqUnit x), one_mul]
    rw [hu] at hm
    have hIcc : ∀ᶠ y in 𝓝 x, y ∈ Icc 0 T := Icc_mem_nhds hx.1 hx.2
    have hEventually : vacuumLoopTensor γ T =ᶠ[𝓝 x] Q := hIcc.mono fun _ hy => hpath hy
    have hdn : (1 / 2 : ℝ) * ‖deriv (vacuumLoopTensor γ T) x‖ ^ 2 =
        (1 / 2 : ℝ) * ‖deriv Q x‖ ^ 2 :=
      congrArg (fun D : Tensor => (1 / 2 : ℝ) * ‖D‖ ^ 2) hEventually.deriv_eq
    exact hdn.trans hm
  have hMemLp : MemLp (deriv (vacuumLoopTensor γ T)) 2 (volume.restrict (Ioo 0 T)) := by
    refine (memLp_const (Real.sqrt (2 * c))).mono' (aestronglyMeasurable_deriv _ _) ?_
    apply (ae_restrict_iff' measurableSet_Ioo).2
    filter_upwards with x hx
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity)]
    linarith only [hmetric x hx]
  refine ⟨γ, hclass, hAC, hMemLp, ?_⟩
  change (∫ x in 0..T, (1 / 2 : ℝ) * ‖deriv (vacuumLoopTensor γ T) x‖ ^ 2) = T * c
  rw [intervalIntegral.integral_congr_Ioo_of_le hT.le hmetric, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]

/-- The one-dimensional Sobolev condition in the angular parameter of a vacuum loop. -/
def VacuumLoopH1 {a : BulkCoefficients} {A : vacuum a} (γ : Path A A) : Prop :=
  AbsolutelyContinuousOnInterval (vacuumLoopTensor γ (2 * Real.pi)) 0 (2 * Real.pi) ∧
    MemLp (deriv (vacuumLoopTensor γ (2 * Real.pi))) 2 (volume.restrict (Ioo 0 (2 * Real.pi)))

/-- The Frobenius half energy in the angular parameter of a vacuum loop. -/
def vacuumLoopEnergy {a : BulkCoefficients} {A : vacuum a} (γ : Path A A) : ℝ :=
  ∫ x in 0..(2 * Real.pi), (1 / 2 : ℝ) * ‖deriv (vacuumLoopTensor γ (2 * Real.pi)) x‖ ^ 2

theorem vacuumLoopEnergy_nonneg {a : BulkCoefficients} {A : vacuum a} (γ : Path A A) :
    0 ≤ vacuumLoopEnergy γ :=
  intervalIntegral.integral_nonneg_of_forall (by positivity) fun _ => by positivity

/-- Each light class has a loop attaining the sharp value `kappaStar a`. -/
theorem exists_vacuumLoop_light_competitor (a : BulkCoefficients) (v₀ : Sphere3)
    {g : QuaternionGroup 2} (hg : IsLightQuaternion g) :
    ∃ γ : Path (vacuumQuaternionProjection a v₀) (vacuumQuaternionProjection a v₀),
      vacuumFundamentalGroupEquiv a v₀
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = g ∧
      VacuumLoopH1 γ ∧ vacuumLoopEnergy γ = kappaStar a := by
  let e := quaternionWordReal g
  have hre : e.re = 0 := by
    rcases hg with rfl | rfl | rfl | rfl <;>
      simp only [e, quaternionWordReal_i, quaternionWordReal_negative_i,
        quaternionWordReal_j, quaternionWordReal_negative_j]
  have hE : ‖e‖ = 1 := norm_quaternionWordReal g
  obtain ⟨γ, hclass, hAC, hD, henergy⟩ :=
    quaternion_arc_loop a v₀ hre hE (1 / 4) g (quaternionArc_quarter_end e)
  refine ⟨γ, hclass, ⟨hAC, hD⟩, ?_⟩
  unfold vacuumLoopEnergy
  rw [henergy]
  rcases hg with rfl | rfl | rfl | rfl <;>
    (norm_num [e, quaternionWordReal_i, quaternionWordReal_negative_i,
      quaternionWordReal_j, quaternionWordReal_negative_j, kappaStar]; ring)

/-- The central class has a loop attaining the sharp value `4 * kappaStar a`. -/
theorem exists_vacuumLoop_antipodal_competitor (a : BulkCoefficients) (v₀ : Sphere3) :
    ∃ γ : Path (vacuumQuaternionProjection a v₀) (vacuumQuaternionProjection a v₀),
      vacuumFundamentalGroupEquiv a v₀
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = QuaternionGroup.a 2 ∧
      VacuumLoopH1 γ ∧ vacuumLoopEnergy γ = 4 * kappaStar a := by
  have hend : quaternionArc firstQuaternionUnit (1 / 2) (2 * Real.pi) =
      quaternionWordReal (QuaternionGroup.a 2) := by
    rw [quaternionArc_half_end, quaternionWordReal_negative_one]
  obtain ⟨γ, hclass, hAC, hD, henergy⟩ :=
    quaternion_arc_loop a v₀ (e := firstQuaternionUnit) rfl norm_firstQuaternionUnit
      (1 / 2) (QuaternionGroup.a 2) hend
  refine ⟨γ, hclass, ⟨hAC, hD⟩, ?_⟩
  unfold vacuumLoopEnergy
  rw [henergy]
  norm_num [firstQuaternionUnit, kappaStar]
  ring

/-- The two elements of the third class have loops with energy `4 * kappaStar a`. -/
theorem exists_vacuumLoop_third_class_competitor (a : BulkCoefficients) (v₀ : Sphere3)
    {g : QuaternionGroup 2} (hg : g = QuaternionGroup.xa 1 ∨ g = QuaternionGroup.xa 3) :
    ∃ γ : Path (vacuumQuaternionProjection a v₀) (vacuumQuaternionProjection a v₀),
      vacuumFundamentalGroupEquiv a v₀
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = g ∧
      VacuumLoopH1 γ ∧ vacuumLoopEnergy γ = 4 * kappaStar a := by
  let e := quaternionWordReal g
  have hre : e.re = 0 := by
    rcases hg with rfl | rfl <;> simp only [e, quaternionWordReal_negative_k, quaternionWordReal_k]
  have hE : ‖e‖ = 1 := norm_quaternionWordReal g
  obtain ⟨γ, hclass, hAC, hD, henergy⟩ :=
    quaternion_arc_loop a v₀ hre hE (1 / 4) g (quaternionArc_quarter_end e)
  refine ⟨γ, hclass, ⟨hAC, hD⟩, ?_⟩
  unfold vacuumLoopEnergy
  rw [henergy]
  rcases hg with rfl | rfl <;>
    (norm_num [e, quaternionWordReal_negative_k, quaternionWordReal_k, kappaStar]; ring)

/-- The attainable energies at a fixed base point and with a fixed quaternion word. -/
def vacuumClassEnergies (a : BulkCoefficients) (v : Sphere3) (g : QuaternionGroup 2) : Set ℝ :=
  {E | ∃ γ : Path (vacuumQuaternionProjection a v) (vacuumQuaternionProjection a v),
    vacuumFundamentalGroupEquiv a v (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = g ∧
    VacuumLoopH1 γ ∧ vacuumLoopEnergy γ = E}

theorem vacuumClassEnergies_isLeast_one (a : BulkCoefficients) (v : Sphere3) :
    IsLeast (vacuumClassEnergies a v 1) 0 := by
  have hend : quaternionArc firstQuaternionUnit 0 (2 * Real.pi) = quaternionWordReal 1 := by
    simp [quaternionArc]
  obtain ⟨γ, hclass, hAC, hD, henergy⟩ :=
    quaternion_arc_loop a v (e := firstQuaternionUnit) rfl norm_firstQuaternionUnit 0 1 hend
  refine ⟨⟨γ, hclass, ⟨hAC, hD⟩, ?_⟩, fun E hE => ?_⟩
  · unfold vacuumLoopEnergy
    rw [henergy]
    simp
  · obtain ⟨γ', _, _, hE'⟩ := hE
    rw [← hE']
    exact vacuumLoopEnergy_nonneg γ'

theorem vacuumClassEnergies_isLeast_light (a : BulkCoefficients) (v : Sphere3)
    {g : QuaternionGroup 2} (hg : IsLightQuaternion g) :
    IsLeast (vacuumClassEnergies a v g) (kappaStar a) := by
  refine ⟨exists_vacuumLoop_light_competitor a v hg, ?_⟩
  intro E hE
  obtain ⟨γ, hclass, hγ, henergy⟩ := hE
  rw [← henergy]
  exact vacuumLoop_energy_ge_light a v γ hγ.1 hγ.2 (hclass ▸ hg)

theorem vacuumClassEnergies_isLeast_antipodal (a : BulkCoefficients) (v : Sphere3) :
    IsLeast (vacuumClassEnergies a v (QuaternionGroup.a 2)) (4 * kappaStar a) := by
  refine ⟨exists_vacuumLoop_antipodal_competitor a v, ?_⟩
  intro E hE
  obtain ⟨γ, hclass, hγ, henergy⟩ := hE
  rw [← henergy]
  exact vacuumLoop_energy_ge_antipodal a v γ hγ.1 hγ.2 hclass

end Thesis

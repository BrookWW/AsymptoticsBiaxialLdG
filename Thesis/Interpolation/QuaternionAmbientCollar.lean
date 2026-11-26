module

public import Thesis.Definitions
public import StratificationTheory.Frozen.SphereSobolev
public import StratificationTheory.Frozen.SphereGradient
import StratificationTheory.Interpolation.ProjectedAnnularConnector
import StratificationTheory.Frozen.RadialTraceGluing
import StratificationTheory.Frozen.SphereGradientCharacterization
import StratificationTheory.Foundation.RadialSobolevPullback
import StratificationTheory.Foundation.RadialPiecewiseSobolevData
import StratificationTheory.Foundation.SphereAEClasses
import HarmonicMaps.Analysis.SmoothWeakGradient

/-! A bounded affine collar for the actual unit-sphere Sobolev data. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff

namespace Thesis

abbrev UnitBoundarySphere (n : ℕ) := sphere (0 : Domain n) 1

abbrev unitBoundarySurface (n : ℕ) : Measure (UnitBoundarySphere n) :=
  Measure.euclideanHausdorffMeasure (n - 1)

@[expose] def quaternionBoundaryEnergy {n : ℕ} (hn : 2 ≤ n)
    (v : UnitBoundarySphere n → Ambient 4) (hv : MemSphereW12 hn v) : ℝ :=
  ∫ θ : UnitBoundarySphere n, ∑ i : Fin n, ‖(sphereGradient hn v hv i) θ‖ ^ 2
    ∂unitBoundarySurface n

/-- The unhalved native tangential energy for Euclidean-valued sphere data. -/
@[expose] def ambientBoundaryEnergy {n q : ℕ} (hn : 2 ≤ n)
    (v : UnitBoundarySphere n → Ambient q) (hv : MemSphereW12 hn v) : ℝ :=
  ∫ θ : UnitBoundarySphere n, ∑ i : Fin n, ‖(sphereGradient hn v hv i) θ‖ ^ 2
    ∂unitBoundarySurface n

private theorem hasWeakGradient_const_ambient {n q : ℕ} (Ω : OpenDomain n) (c : Ambient q) :
    HasWeakGradient Ω (fun _ => c) (fun _ _ => 0) := by
  simpa only [coordinateDerivative, fderiv_fun_const, Pi.zero_apply, zero_apply] using
    (hasWeakGradient_of_contDiff Ω (f := fun _ => c) contDiff_const)

private theorem sphereGradient_const_ambient {n q : ℕ} (hn : 2 ≤ n) (c : Ambient q)
    (hc : MemSphereW12 hn (fun _ : UnitBoundarySphere n => c)) :
    sphereGradient hn (fun _ : UnitBoundarySphere n => c) hc = 0 := by
  let Ω : OpenDomain n := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hW : MemW12Loc Ω (fun _ => c) (fun _ _ => 0) := by
    refine ⟨hasWeakGradient_const_ambient Ω c, ?_, ?_⟩
    · intro K hK _
      letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict K) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
      exact memLp_const c
    · intro _ K _ _
      exact MemLp.zero
  symm
  apply (sphereGradient_characterization hn (fun _ => c) hc).2.1
  refine ⟨fun _ => c, fun _ _ => 0, hW, fun _ _ => rfl, ?_⟩
  intro ρ i
  change (fun θ : UnitBoundarySphere n => ρ.val • (0 : Ambient q)) =ᵐ[unitBoundarySurface n]
    fun θ => (0 : Lp (Ambient q) 2 (unitBoundarySurface n)) θ
  simp only [smul_zero]
  exact (Lp.coeFn_zero (Ambient q) 2 (unitBoundarySurface n)).symm

private theorem ae_ambient_affine_collar_norm {n q : ℕ} (hn : 2 ≤ n)
    {B : ℝ} {v : UnitBoundarySphere n → Ambient q} {c : Ambient q}
    (hV : ∀ᵐ θ ∂unitBoundarySurface n, ‖v θ‖ ≤ B) (hc : ‖c‖ ≤ B)
    {h : ℝ} (hh : 0 < h) (hr : 0 < 1 - h)
    {w : Domain n → Ambient q} (hCore : ∀ x : Domain n, ‖x‖ < 1 - h → w x = c)
    (hRaw : ∀ s ∈ Ioo (1 - h) 1, ∀ θ : UnitBoundarySphere n,
      w (s • θ.val) = c + ((s - (1 - h)) / h) • (v θ - c)) :
    ∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ‖w x‖ ≤ B := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let U := ({(0 : Domain n)}ᶜ : Set (Domain n))
  have hV' : ∀ᵐ θ ∂(volume : Measure (Domain n)).toSphere, ‖v θ‖ ≤ B := by
    rw [← euclideanHausdorffMeasure_unitSphere_eq_toSphere (by omega : 0 < n)]
    exact hV
  have hAng' : ∀ᵐ x ∂volume.restrict U,
      ∀ hx : x ∈ U, ‖v ((homeomorphUnitSphereProd (Domain n) ⟨x, hx⟩).1)‖ ≤ B := by
    apply (ae_restrict_iff_subtype (measurableSet_singleton (0 : Domain n)).compl).2
    filter_upwards [ae_polar_angle_of_ae_sphere hV'] with x hx
    exact fun _ => hx
  have hAng : ∀ᵐ x ∂volume,
      ∀ hx : x ∈ U, ‖v ((homeomorphUnitSphereProd (Domain n) ⟨x, hx⟩).1)‖ ≤ B := by
    simpa only [U, restrict_compl_singleton] using hAng'
  filter_upwards [hAng.filter_mono (ae_mono Measure.restrict_le_self),
    (ae_norm_sub_ne_radius (0 : Domain n) hr).filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_ball] with x hx hseam hBall
  rcases lt_or_gt_of_ne (by simpa only [sub_zero] using hseam : ‖x‖ ≠ 1 - h) with hCoreX | hAnn
  · rw [hCore _ hCoreX]
    exact hc
  · have hxU : x ∈ U := by
      intro hZero
      have hx0 : x = 0 := hZero
      rw [hx0, norm_zero] at hAnn
      linarith
    let xx : U := ⟨x, hxU⟩
    let p := homeomorphUnitSphereProd (Domain n) xx
    have hRad : p.2.val = ‖x‖ := homeomorphUnitSphereProd_apply_snd_coe (Domain n) xx
    have hDecomp : p.2.val • p.1.val = x := by
      rw [← homeomorphUnitSphereProd_symm_apply_coe, Homeomorph.symm_apply_apply]
    have hInside : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hBall
    have hp : p.2.val ∈ Ioo (1 - h) 1 := by rw [hRad]; exact ⟨hAnn, hInside⟩
    let t := (p.2.val - (1 - h)) / h
    have ht : 0 ≤ t ∧ t ≤ 1 := ⟨div_nonneg (sub_nonneg.mpr hp.1.le) hh.le,
      (div_le_one hh).2 (by rw [hRad]; linarith)⟩
    have hv : ‖v p.1‖ ≤ B := hx hxU
    calc
      ‖w x‖ = ‖(1 - t) • c + t • v p.1‖ := by
        rw [← hDecomp, hRaw _ hp p.1]
        change ‖c + t • (v p.1 - c)‖ = _
        rw [sub_smul, one_smul, smul_sub]
        congr 1
        abel
      _ ≤ ‖(1 - t) • c‖ + ‖t • v p.1‖ := norm_add_le _ _
      _ = (1 - t) * ‖c‖ + t * ‖v p.1‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht.2), Real.norm_of_nonneg ht.1]
      _ ≤ (1 - t) * B + t * B := add_le_add
        (mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr ht.2)) (mul_le_mul_of_nonneg_left hv ht.1)
      _ = B := by ring

/-- Join data in a fixed closed ball to a constant with a radial affine
collar of width `h`, glued to a constant core by its actual Sobolev trace. -/
theorem exists_ambient_affine_collar_of_sphere {n q : ℕ} (hn : 2 ≤ n)
    (v : UnitBoundarySphere n → Ambient q) (hv : MemSphereW12 hn v) {B : ℝ}
    (hV : ∀ᵐ θ ∂unitBoundarySurface n, ‖v θ‖ ≤ B) (c : Ambient q) (hc : ‖c‖ ≤ B)
    {h : ℝ} (hh : 0 < h) (hh₂ : h ≤ 1 / 2) :
    ∃ (w : Domain n → Ambient q) (Dw : Domain n → HarmonicMaps.Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 1) w Dw ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ‖w x‖ ≤ B) ∧
      (∀ r ∈ Ioo (1 - h) 1, ∀ θ : UnitBoundarySphere n,
        w (r • θ.val) = c + ((r - (1 - h)) / h) • (v θ - c)) ∧
      (∫ x in ball (0 : Domain n) 1, hsNormSq (Dw x)) ≤
        4 * (h / 2 * ambientBoundaryEnergy hn v hv +
          h⁻¹ * ∫ θ : UnitBoundarySphere n, ‖v θ - c‖ ^ 2 ∂unitBoundarySurface n) := by
  let σ := unitBoundarySurface n
  let r := 1 - h
  have hr : 0 < r := by dsimp only [r]; linarith
  have hr₁ : r < 1 := by dsimp only [r]; linarith
  have hr₂ : (1 / 2 : ℝ) ≤ r := by dsimp only [r]; linarith
  letI : IsFiniteMeasure σ := by
    dsimp only [σ, unitBoundarySurface]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere (by omega : 0 < n)]
    infer_instance
  let u : UnitBoundarySphere n → Ambient q := fun _ => c
  have hu : MemSphereW12 hn u := memSphereW12_smooth_slice hn
    (f := fun _ => c) contDiff_const 0 1
  have hF : ContDiff ℝ ∞ (id : Ambient q → Ambient q) := contDiff_id
  have hD : ∀ z : Ambient q, ‖fderiv ℝ (id : Ambient q → Ambient q) z‖ ≤ 1 := by
    intro z
    rw [fderiv_id]
    exact ContinuousLinearMap.norm_id_le
  have hab : -h < (0 : ℝ) := neg_lt_zero.2 hh
  have ha : (-1 : ℝ) < -h := by linarith
  obtain ⟨_, W, DW, hW, hRaw, hEnergy, _, _, _⟩ :=
    exists_affine_annular_postcomposition_trace_energy hn (a := -h) (b := 0) (s := 1)
      hab ha zero_lt_one u v hu hv id hF 1 hD 1 (ae_of_all _ fun _ => hD _)
  let A : OpenDomain n := ⟨{x : Domain n | r < ‖x‖ ∧ ‖x‖ < 1},
    isOpen_Ioo.preimage continuous_norm⟩
  have hWA : MemW12 A W DW := by
    simpa only [A, r, sub_eq_add_neg, add_zero, one_mul] using hW
  have hWR (s : ℝ) (hs : s ∈ Ioo r 1) (θ : UnitBoundarySphere n) :
      W (s • θ.val) = c + ((s - r) / h) • (v θ - c) := by
    have hs' : s - 1 ∈ Ioo (-h) (0 : ℝ) := by
      rcases hs with ⟨hs₁, hs₂⟩
      change -h < s - 1 ∧ s - 1 < 0
      dsimp only [r] at hs₁
      constructor <;> linarith
    have he := hRaw θ (s - 1) hs'
    have hRadius : 1 * (1 + (s - 1)) = s := by ring
    have hFraction : (s - 1 - -h) / (0 - -h) = (s - r) / h := by
      dsimp only [r]
      rw [zero_sub, neg_neg]
      congr 1
      ring
    rw [hRadius, hFraction, id_eq] at he
    rw [he]
    change (1 - (s - r) / h) • c + ((s - r) / h) • v θ =
      c + ((s - r) / h) • (v θ - c)
    rw [sub_smul, one_smul, smul_sub]
    abel
  let C : Domain n → Ambient q := fun _ => c
  let DC : Domain n → HarmonicMaps.Gradient n q := fun _ _ => 0
  letI : IsFiniteMeasure (volume.restrict (ballDomain (0 : Domain n) r).val) := by
    refine ⟨?_⟩
    change ((volume : Measure (Domain n)).restrict (ball 0 r)) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hC : MemW12 (ballDomain (0 : Domain n) r) C DC :=
    ⟨hasWeakGradient_const_ambient _ c, memLp_const c, fun _ => MemLp.zero⟩
  let hLc : MemLp u 2 σ := memLp_const c
  let Lc := hLc.toLp u
  let Lv := hv.1.toLp v
  let H : C(Icc (r / 2) r, Lp (Ambient q) 2 σ) := ContinuousMap.const _ Lc
  let K (b : ℝ) : C(Icc r b, Lp (Ambient q) 2 σ) :=
    ⟨fun s => Lc + ((s.val - r) / h) • (Lv - Lc), by fun_prop⟩
  have hH : ∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo (r / 2) r,
      ∃ hsLp : MemLp (fun θ : UnitBoundarySphere n => C (0 + s • θ.val)) 2 σ,
        H ⟨s, hs.1.le, hs.2.le⟩ = hsLp.toLp _ :=
    ae_of_all _ fun _ _ => ⟨hLc, rfl⟩
  have hK : ∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo r ((r + 1) / 2),
      ∃ hsLp : MemLp (fun θ : UnitBoundarySphere n => W (0 + s • θ.val)) 2 σ,
        K ((r + 1) / 2) ⟨s, hs.1.le, hs.2.le⟩ = hsLp.toLp _ := by
    refine ae_of_all _ fun s hs => ?_
    have hs₁ : s ∈ Ioo r 1 := ⟨hs.1, hs.2.trans (by linarith)⟩
    have hEq : (fun θ : UnitBoundarySphere n => W (0 + s • θ.val)) =
        u + ((s - r) / h) • (v - u) := by
      funext θ
      rw [zero_add, hWR s hs₁ θ]
      rfl
    let hLp : MemLp (u + ((s - r) / h) • (v - u)) 2 σ :=
      hLc.add ((hv.1.sub hLc).const_smul _)
    let hLp' := hLp.ae_eq (Eventually.of_forall (congrFun hEq.symm))
    refine ⟨hLp', ?_⟩
    change Lc + ((s - r) / h) • (Lv - Lc) = _
    have hSame := MemLp.toLp_congr hLp hLp'
      (Eventually.of_forall (congrFun hEq.symm))
    rw [← hSame]
    rw [MemLp.toLp_add hLc ((hv.1.sub hLc).const_smul _),
      MemLp.toLp_const_smul _ (hv.1.sub hLc), MemLp.toLp_sub hv.1 hLc]
  have hMatch : H ⟨r, by linarith, le_rfl⟩ = K ((r + 1) / 2) ⟨r, le_rfl, by linarith⟩ := by
    change Lc = Lc + ((r - r) / h) • (Lv - Lc)
    simp
  have hg := memW12_radial_trace_gluing hn (0 : Domain n) hr hr₁ C W DC DW hC
    (by simpa only [A, sub_zero] using hWA) H (K ((r + 1) / 2)) hH hK hMatch
  let w (x : Domain n) := if ‖x - 0‖ < r then C x else W x
  let D (x : Domain n) (i : Fin n) := if ‖x - 0‖ < r then DC x i else DW x i
  change MemW12 (ballDomain (0 : Domain n) 1) w D ∧ _ at hg
  have hRad (s : ℝ) (hs : 0 ≤ s) (θ : UnitBoundarySphere n) : ‖s • θ.val‖ = s := by
    have hunit : ‖θ.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
    rw [norm_smul, hunit, Real.norm_of_nonneg hs, mul_one]
  have hRawW (s : ℝ) (hs : s ∈ Ioo r 1) (θ : UnitBoundarySphere n) :
      w (s • θ.val) = c + ((s - r) / h) • (v θ - c) := by
    unfold w
    rw [sub_zero, hRad s (hr.trans hs.1).le, if_neg (not_lt_of_ge hs.1.le), hWR s hs θ]
  refine ⟨w, D, hg.1, ?_, hRawW, ?_⟩
  · apply ae_ambient_affine_collar_norm hn hV hc hh hr
    · intro x hx
      exact if_pos (by simpa only [sub_zero] using hx)
    · exact hRawW
  · have hGrad : sphereGradient hn u hu = 0 := sphereGradient_const_ambient hn c hu
    have hEConst : (∫ θ : UnitBoundarySphere n,
        ∑ i : Fin n, (‖(sphereGradient hn u hu i) θ‖ ^ 2 + ‖(sphereGradient hn v hv i) θ‖ ^ 2) ∂σ) =
        ambientBoundaryEnergy hn v hv := by
      unfold ambientBoundaryEnergy
      have hZ : ∀ᵐ θ ∂σ, (0 : Lp (Ambient q) 2 σ) θ = 0 := Lp.coeFn_zero _ _ _
      apply integral_congr_ae
      filter_upwards [hZ] with θ hθ
      simp only [hGrad, Pi.zero_apply, hθ, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add]
    have hE' : (∫ x in A.val, hsNormSq (DW x)) ≤
        (max r⁻¹ 1) ^ 2 * (h / 2 * ambientBoundaryEnergy hn v hv +
          h⁻¹ * ∫ θ : UnitBoundarySphere n, ‖v θ - c‖ ^ 2 ∂σ) := by
      rw [hEConst] at hEnergy
      simpa only [A, r, sub_eq_add_neg, zero_add, zero_sub, neg_neg, one_mul, add_zero,
        inv_one, one_pow, NNReal.coe_one, mul_one, u, σ] using hEnergy
    have hMax : max r⁻¹ 1 ≤ 2 := max_le (by rw [inv_le_comm₀ hr (by norm_num)]; simpa using hr₂)
      (by norm_num)
    have hB0 : 0 ≤ h / 2 * ambientBoundaryEnergy hn v hv + h⁻¹ *
        ∫ θ : UnitBoundarySphere n, ‖v θ - c‖ ^ 2 ∂σ := by
      have hGrad0 : 0 ≤ ambientBoundaryEnergy hn v hv :=
        by unfold ambientBoundaryEnergy; exact integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      exact add_nonneg (mul_nonneg (by positivity) hGrad0)
        (mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _))
    rw [hg.2]
    have hCore : (∫ x in ball (0 : Domain n) r, hsNormSq (DC x)) = 0 := by
      simp [DC, hsNormSq]
    rw [hCore, zero_add]
    simp only [sub_zero]
    change (∫ x in A.val, hsNormSq (DW x)) ≤ _
    exact hE'.trans (mul_le_mul_of_nonneg_right
      ((pow_le_pow_left₀ (le_trans zero_le_one (le_max_right _ _)) hMax 2).trans_eq (by norm_num)) hB0)

/-- The radius-one quaternion instance of the native affine collar. -/
theorem exists_quaternion_ambient_affine_collar {n : ℕ} (hn : 2 ≤ n)
    (v : UnitBoundarySphere n → Ambient 4) (hv : MemSphereW12 hn v)
    (hV : ∀ᵐ θ ∂unitBoundarySurface n, ‖v θ‖ ≤ 1) (c : Ambient 4) (hc : ‖c‖ ≤ 1)
    {h : ℝ} (hh : 0 < h) (hh₂ : h ≤ 1 / 2) :
    ∃ (w : Domain n → Ambient 4) (Dw : Domain n → HarmonicMaps.Gradient n 4),
      MemW12 (ballDomain (0 : Domain n) 1) w Dw ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ‖w x‖ ≤ 1) ∧
      (∀ r ∈ Ioo (1 - h) 1, ∀ θ : UnitBoundarySphere n,
        w (r • θ.val) = c + ((r - (1 - h)) / h) • (v θ - c)) ∧
      (∫ x in ball (0 : Domain n) 1, hsNormSq (Dw x)) ≤
        4 * (h / 2 * quaternionBoundaryEnergy hn v hv +
          h⁻¹ * ∫ θ : UnitBoundarySphere n, ‖v θ - c‖ ^ 2 ∂unitBoundarySurface n) :=
  exists_ambient_affine_collar_of_sphere hn v hv hV c hc hh hh₂

end Thesis

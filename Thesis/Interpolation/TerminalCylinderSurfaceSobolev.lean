module

public import Thesis.Interpolation.TerminalCylinderSurfaceGraph
import Thesis.Interpolation.NativeBallTraceEstimate
import StratificationTheory.Frozen.SphereRadialBallExtension
import HarmonicMaps.Analysis.SobolevAECongruence

/-! Sobolev transport and the uniform energy bounds for the literal terminal boundary. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ENNReal NNReal Topology

namespace Thesis.MeasureGeometry

private theorem terminalRoundShell_subset_ball :
    terminalRoundShell.val ⊆ ball (0 : Point) 2 :=
  fun _ hx => mem_ball_zero_iff.2 hx.2

private theorem terminalRoundShell_not_origin : (0 : Point) ∉ terminalRoundShell.val := by
  intro hx
  have h : 1 / 2 < ‖(0 : Point)‖ := hx.1
  norm_num at h

private theorem terminalSphere_memLp_of_radialGraph {q : ℕ} {b : UnitTensorSphere → Ambient q}
    {w : Point → Ambient q} (hw : MemLp w 2 (volume.restrict terminalRoundShell.val))
    (hRay : ∀ (ρ : PositiveRadius) (θ : UnitTensorSphere), ρ.val • θ.val ∈ terminalRoundShell.val →
      w (ρ.val • θ.val) = b θ) : MemLp b 2 tensorSphereMeasure := by
  let w₀ := terminalRoundShell.val.indicator w
  letI : IsFiniteMeasure (unitBoundarySurface 3) := by
    change IsFiniteMeasure (Measure.euclideanHausdorffMeasure (3-1) :
      Measure (sphere (0 : Domain 3) 1))
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 3)]
    infer_instance
  have h0 : MemLp w₀ 2 volume := memLp_zeroExtension terminalRoundShell.property.measurableSet hw
  have h0B := h0.mono_measure (Measure.restrict_le_self (s := ball (0 : Point) 2))
  have hProd := (memLp_native_ball_closed_radial_product (by decide : 0 < 3)
    (a := 1/2) (by norm_num : (0 : ℝ) < 1/2) h0B).1
  have hSlice : ∀ᵐ t : ℝ ∂volume.restrict (Icc (1/2) 2),
      MemLp (fun θ : UnitTensorSphere => w₀ (t • θ.val)) 2 tensorSphereMeasure := by
    filter_upwards [hProd.aestronglyMeasurable.prodMk_right,
      (hProd.integrable_norm_pow (by decide : 2 ≠ 0)).prod_left_ae] with t hm hi
    exact (memLp_two_iff_integrable_sq_norm hm).2 hi
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc] at hSlice
  have hVol : (volume : Measure ℝ) (Ioo (1/2) 2) ≠ 0 := by rw [Real.volume_Ioo]; norm_num
  obtain ⟨t, ht, htLp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hVol hSlice
  have ht₀ : 0 < t := (by norm_num : (0 : ℝ) < 1/2).trans ht.1
  apply htLp.ae_eq
  refine Eventually.of_forall fun θ => ?_
  have hy : t • θ.val ∈ terminalRoundShell.val := by
    change ‖t • θ.val‖ ∈ Ioo (1/2) 2
    rw [norm_smul, Real.norm_of_nonneg ht₀.le, mem_sphere_zero_iff_norm.1 θ.property, mul_one]
    exact ht
  change w₀ (t • θ.val) = b θ
  rw [show w₀ (t • θ.val) = w (t • θ.val) from indicator_of_mem hy _]
  exact hRay ⟨t, ht₀⟩ θ hy

private theorem eqAt_of_radial_values {q : ℕ} {A : Set Point} {b : UnitTensorSphere → Ambient q}
    {w v : Point → Ambient q}
    (hw : ∀ (ρ : PositiveRadius) (θ : UnitTensorSphere), ρ.val • θ.val ∈ A → w (ρ.val • θ.val) = b θ)
    (hv : ∀ (ρ : PositiveRadius) (θ : UnitTensorSphere), ρ.val • θ.val ∈ A → v (ρ.val • θ.val) = b θ)
    {x : Point} (hx : x ∈ A) (hx₀ : x ≠ 0) : w x = v x := by
  let ρ : PositiveRadius := ⟨‖x‖, norm_pos_iff.2 hx₀⟩
  let θ : UnitTensorSphere := ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hx₀)⟩
  have hEq : ρ.val • θ.val = x := NormedSpace.norm_smul_normalize x
  have h := (hw ρ θ (hEq.symm ▸ hx)).trans (hv ρ θ (hEq.symm ▸ hx)).symm
  rwa [hEq] at h

private theorem terminalRoundShell_norm_ae_ne (t : ℝ) : ∀ᵐ x : Point ∂volume, ‖x‖ ≠ t := by
  rw [ae_iff]
  simpa only [not_not, ← mem_sphere_zero_iff_norm, setOf_mem_eq] using
    (Measure.addHaar_sphere volume (0 : Point) t)

private theorem terminalSphereEnergy_le_radialGraph {q : ℕ} {b : UnitTensorSphere → Ambient q}
    (hb : MemSphereW12 (by decide : 2 ≤ 3) b)
    {w : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hw : MemW12 terminalRoundShell w D)
    (hRay : ∀ (ρ : PositiveRadius) (θ : UnitTensorSphere), ρ.val • θ.val ∈ terminalRoundShell.val →
      w (ρ.val • θ.val) = b θ) :
    ENNReal.ofReal (nativeTerminalSphereDirichlet b hb) ≤
      HarmonicMaps.dirichletEnergy D terminalRoundShell.val := by
  let A : Set Point := ball (0 : Point) (1/2)
  let B : Set Point := ball (0 : Point) 2
  let S : Set Point := terminalRoundShell.val
  let E := nativeTerminalSphereDirichlet b hb
  obtain ⟨u, Du, hu, huRay, _, huInt, huE, _⟩ :=
    exists_radial_ball_sobolev_extension (by decide : 3 ≤ 3) b hb (R := 2) (by norm_num)
  obtain ⟨v, Dv, hv, hvRay, _, _, hvE, _⟩ :=
    exists_radial_ball_sobolev_extension (by decide : 3 ≤ 3) b hb (R := 1/2) (by norm_num)
  have hAS : A ⊆ B := ball_subset_ball (by norm_num)
  have hS : S ⊆ B := terminalRoundShell_subset_ball
  have huA : HasWeakGradient (ballDomain (0 : Point) (1/2)) u Du := hu.1.mono hAS
  have hD₁ : Du =ᵐ[volume.restrict A] Dv := by
    apply huA.ae_eq_of_ae_eq_map hv.1
    filter_upwards [ae_restrict_mem (show MeasurableSet A from measurableSet_ball),
      ((volume : Measure Point).ae_ne 0).filter_mono (ae_mono Measure.restrict_le_self)] with x hx hx₀
    exact eqAt_of_radial_values (fun ρ θ _ => huRay ρ θ) (fun ρ θ _ => hvRay ρ θ) hx hx₀
  have huS : HasWeakGradient terminalRoundShell u Du := hu.1.mono hS
  have hD₂ : Du =ᵐ[volume.restrict S] D := by
    apply huS.ae_eq_of_ae_eq_map hw.1
    filter_upwards [ae_restrict_mem terminalRoundShell.property.measurableSet] with x hx
    have hx₀ : x ≠ 0 := fun h => terminalRoundShell_not_origin (h ▸ hx)
    exact eqAt_of_radial_values (fun ρ θ _ => huRay ρ θ) hRay hx hx₀
  have hUnion : (A ∪ S : Set Point) =ᵐ[(volume : Measure Point)] B := by
    filter_upwards [terminalRoundShell_norm_ae_ne (1/2)] with x hx
    apply propext
    change (x ∈ A ∨ x ∈ S) ↔ x ∈ B
    refine ⟨fun h => h.elim (fun hxA => hAS hxA) (fun hxS => hS hxS), ?_⟩
    intro h
    by_cases p : ‖x‖ < 1 / 2
    · exact Or.inl (mem_ball_zero_iff.2 p)
    · exact Or.inr ⟨lt_of_le_of_ne (le_of_not_gt p) (Ne.symm hx), mem_ball_zero_iff.1 h⟩
  have hDisj : Disjoint A S := by
    apply Set.disjoint_left.2
    intro x hx hxS
    exact (not_lt_of_ge (show 1/2 ≤ ‖x‖ from hxS.1.le)) (mem_ball_zero_iff.1 hx)
  have hAdd : (∫ x in B, hsNormSq (Du x)) =
      (∫ x in A, hsNormSq (Du x)) + ∫ x in S, hsNormSq (Du x) := by
    rw [← Measure.restrict_congr_set hUnion]
    exact setIntegral_union hDisj terminalRoundShell.property.measurableSet
      (huInt.mono_measure (Measure.restrict_mono_set volume hAS))
      (huInt.mono_measure (Measure.restrict_mono_set volume hS))
  have hThree : ((3 : ℕ) : ℝ) - 2 = 1 := by norm_num
  have hAeq : (∫ x in A, hsNormSq (Du x)) = (1/2 : ℝ) * E := by
    rw [integral_congr_ae (hD₁.mono fun _ h => congrArg hsNormSq h)]
    simpa only [Nat.reduceSub, pow_one, hThree, div_one, E, nativeTerminalSphereDirichlet, hsNormSq] using hvE
  have hBeq : (∫ x in B, hsNormSq (Du x)) = 2 * E := by
    simpa only [Nat.reduceSub, pow_one, hThree, div_one, E, nativeTerminalSphereDirichlet, hsNormSq] using huE
  have hSeq : (∫ x in S, hsNormSq (Du x)) = ∫ x in S, hsNormSq (D x) :=
    integral_congr_ae (hD₂.mono fun _ h => congrArg hsNormSq h)
  rw [hAeq, hBeq, hSeq] at hAdd
  have hNonneg : 0 ≤ E := integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [HarmonicMaps.dirichletEnergy_eq_ofReal_integral hw.integrable_hsNormSq]
  exact ENNReal.ofReal_le_ofReal (by linarith only [hAdd, hNonneg])

private theorem terminalCylinderBallChart_symm_on_unit_ray
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hLow : R/4 ≤ H) (hHigh : H ≤ R)
    (θ : UnitTensorSphere) :
    (terminalCylinderBallChart (B.orthonormal.norm_eq_one 2) c hR hLow hHigh).symm (R • θ.val) =
      c + (R / terminalFrameGauge B (R/H) θ.val) • θ.val := by
  let m := terminalFrameGauge B (R/H) θ.val
  have hθ : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.1 θ.property
  have hH := (div_pos hR (by norm_num : (0 : ℝ) < 4)).trans_le hLow
  have hk : 1 ≤ R/H := (one_le_div₀ hH).2 hHigh
  have hm : 0 < m := by
    have hTop : θ.val ∈ terminalRoundShell.val := by
      change ‖θ.val‖ ∈ Ioo (1/2) 2
      rw [hθ]
      norm_num
    rw [← terminalHalfShell_cover B hk] at hTop
    rcases hTop with h | h
    · exact (terminalHalfParameter_reconstruct B (by norm_num : |(1 : ℝ)| = 1) hR hH hk h).1
    · exact (terminalHalfParameter_reconstruct B (by norm_num : |(-1 : ℝ)| = 1) hR hH hk h).1
  rw [terminalCylinderBallChart_symm_apply, ballToCylinderCap, norm_smul, Real.norm_of_nonneg hR.le,
    hθ, mul_one, cylinderCapGauge_smul _ _ hR.le, ← terminalFrameGauge_eq, smul_smul]
  have h : R / (R * m) * R = R / m := by field_simp
  rw [h]

/-- The original charted cylinder boundary has the claimed sphere graph and
a Dirichlet bound independent of position, radius and aspect ratio. -/
theorem exists_terminalCylinderSphere_graph {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hLow : R/4 ≤ H) (hHigh : H ≤ R)
    (D : TerminalCylinderBoundaryData q R hR) :
    let F := terminalCylinderBallChart (B.orthonormal.norm_eq_one 2) c hR hLow hHigh
    let b (θ : UnitTensorSphere) := terminalCylinderSurfaceValue B c H D (F.symm (R • θ.val))
    ∃ hb : MemSphereW12 (by decide : 2 ≤ 3) b,
      ENNReal.ofReal (nativeTerminalSphereDirichlet b hb) ≤
        (2*(3*56^2*549250)*20001) * terminalCylinderSurfaceDirichlet H D := by
  intro F b
  let w (x : Point) := terminalCylinderSurfaceValue B c H D
    (c + (R / terminalFrameGauge B (R/H) x) • x)
  obtain ⟨G, hG, hEnergy⟩ := exists_terminalCylinder_radialGraph B c hR hLow hHigh D
  have hRay (ρ : PositiveRadius) (θ : UnitTensorSphere) (_ : ρ.val • θ.val ∈ terminalRoundShell.val) :
      w (ρ.val • θ.val) = b θ := by
    have hP := terminalCylinderBallChart_symm_on_unit_ray B c hR hLow hHigh θ
    unfold w b
    rw [hP, terminalFrameGauge_eq, cylinderCapGauge_smul _ _ ρ.property.le, ← terminalFrameGauge_eq, smul_smul]
    by_cases hm : terminalFrameGauge B (R/H) θ.val = 0
    · rw [hm, mul_zero, div_zero, zero_mul]
    · have h : R / (ρ.val * terminalFrameGauge B (R/H) θ.val) * ρ.val = R / terminalFrameGauge B (R/H) θ.val := by
        field_simp [ρ.property.ne', hm]
      rw [h]
  have hLp := terminalSphere_memLp_of_radialGraph hG.2.1 hRay
  have hContains : sphere (0 : Point) 1 ⊆ terminalRoundShell.val := by
    intro x hx
    have h := mem_sphere_zero_iff_norm.1 hx
    change ‖x‖ ∈ Ioo (1/2) 2
    rw [h]
    norm_num
  let hb : MemSphereW12 (by decide : 2 ≤ 3) b :=
    ⟨hLp, terminalRoundShell, hContains, terminalRoundShell_not_origin, w, G, hG, hRay⟩
  exact ⟨hb, (terminalSphereEnergy_le_radialGraph hb hG hRay).trans hEnergy⟩

end Thesis.MeasureGeometry

namespace Thesis

open MeasureGeometry

/-- Compatible weak disk and wall graphs transport to the literal native
sphere boundary data within uniform Dirichlet and value bounds. -/
theorem terminalCylinderSurfaceSobolev : External.TerminalCylinderSurfaceSobolev := by
  let C : ℝ := 2*(3*56^2*549250)*20001
  let K : ℝ := C + 9216
  have hC : 0 ≤ C := by positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro q B c R H hR hLow hHigh D F b
  obtain ⟨hb, hE⟩ := exists_terminalCylinderSphere_graph B c hR hLow hHigh D
  refine ⟨hb, hE.trans ?_, ?_⟩
  · have hCe : (2*(3*56^2*549250)*20001 : ℝ≥0∞) = ENNReal.ofReal C := by
      dsimp only [C]
      norm_num
    rw [hCe]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by norm_num))) _
  · intro φ _
    apply (terminalSphereValue_lintegral_le B c hR hLow hHigh D φ).trans
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_left hC) (sq_nonneg _)

end Thesis

end

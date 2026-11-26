module

public import Thesis.Interpolation.TerminalCylinderWallReflection
import Thesis.Interpolation.OpenOverlapGluing
import HarmonicMaps.Analysis.SobolevAECongruence

/-! The actual Sobolev graph of the terminal cylinder's homogeneous boundary extension. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace Thesis.MeasureGeometry

private theorem terminalWall_polar_columns_sq {q : ℕ} (A : HarmonicMaps.Gradient 2 q)
    {v : Plane} (hv : ‖v‖ = 1) :
    ‖∑ i : Fin 2, v i • A i‖ ^ 2 + ‖∑ i : Fin 2, planarQuarterTurn v i • A i‖ ^ 2 =
      hsNormSq A := by
  have hQ₀ : planarQuarterTurn v 0 = -(v 1) := by simp [planarQuarterTurn]
  have hQ₁ : planarQuarterTurn v 1 = v 0 := by simp [planarQuarterTurn]
  have h : v 0 ^ 2 + v 1 ^ 2 = 1 := by
    have hN := EuclideanSpace.real_norm_sq_eq v
    rw [hv, one_pow, Fin.sum_univ_two] at hN
    exact hN.symm
  rw [Fin.sum_univ_two, Fin.sum_univ_two, hQ₀, hQ₁]
  have hStep :
      ‖v 0 • A 0 + v 1 • A 1‖ ^ 2 + ‖(-v 1) • A 0 + v 0 • A 1‖ ^ 2 =
        (v 0 ^ 2 + v 1 ^ 2) * (‖A 0‖ ^ 2 + ‖A 1‖ ^ 2) := by
    rw [← real_inner_self_eq_norm_sq (v 0 • A 0 + v 1 • A 1),
      ← real_inner_self_eq_norm_sq ((-v 1) • A 0 + v 0 • A 1)]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [hStep, h, one_mul, hsNormSq, Fin.sum_univ_two]

/-- The physical wall energy dominates the plain annular graph energy. -/
theorem terminalWall_dirichletEnergy_le {q : ℕ} {R H : ℝ}
    (hR : 0 < R) (hLow : R / 4 ≤ H) (hHigh : H ≤ R)
    (D : Plane → HarmonicMaps.Gradient 2 q) :
    HarmonicMaps.dirichletEnergy D (terminalWallAnnulus R).val ≤
      16 * ∫⁻ y in (terminalWallAnnulus R).val, ENNReal.ofReal (terminalWallDirichletDensity R H D y) := by
  have hH := (div_pos hR (by norm_num : (0 : ℝ) < 4)).trans_le hLow
  rw [HarmonicMaps.dirichletEnergy, ← lintegral_const_mul' _ _ (by norm_num : (16 : ℝ≥0∞) ≠ ⊤)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (terminalWallAnnulus R).property.measurableSet] with y hy
  have hY : ‖y‖ ∈ Ioo R (2*R) := hy
  have hY₀ := hR.trans hY.1
  let θ := NormedSpace.normalize y
  have hθ : ‖θ‖ = 1 := NormedSpace.norm_normalize (norm_pos_iff.mp hY₀)
  let A := ‖∑ i : Fin 2, θ i • D y i‖ ^ 2
  let B := ‖∑ i : Fin 2, planarQuarterTurn θ i • D y i‖ ^ 2
  have hA : 0 ≤ A := sq_nonneg _
  have hB : 0 ≤ B := sq_nonneg _
  have hEq : A+B = hsNormSq (D y) := terminalWall_polar_columns_sq (D y) hθ
  have hK : 1/4 ≤ 2*H/‖y‖ := (le_div_iff₀ hY₀).2 (by linarith only [hY.2, hLow])
  have hL : 1/2 ≤ R/(2*H) := (le_div_iff₀ (by positivity)).2 (by linarith only [hHigh])
  have hM : 1 ≤ ‖y‖/R := (one_le_div₀ hR).2 hY.1.le
  rw [show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  rw [← hEq]
  change A+B ≤ 16 * ((2*H/‖y‖) * ((R/(2*H))^2 * A + (‖y‖/R)^2 * B))
  have hL₂ : 1 / 4 ≤ (R/(2*H))^2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) hL 2
    norm_num at h
    exact h
  have hM₂ : 1 / 4 ≤ (‖y‖/R)^2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hM 2
    exact (by norm_num : (1 / 4 : ℝ) ≤ 1).trans (by simpa only [one_pow] using h)
  have hFace := add_le_add (mul_le_mul_of_nonneg_right hL₂ hA) (mul_le_mul_of_nonneg_right hM₂ hB)
  have hFin := mul_le_mul hK hFace (by positivity) (by positivity)
  linarith only [hFin]

private theorem ae_planar_norm_ne_terminalRim (R : ℝ) : ∀ᵐ y : Plane ∂volume, ‖y‖ ≠ R := by
  rw [ae_iff]
  simpa only [not_not, ← mem_sphere_zero_iff_norm, setOf_mem_eq] using
    (Measure.addHaar_sphere volume (0 : Plane) R)

private theorem terminalDiskWall_memW12 {q : ℕ} {R : ℝ} (hR : 0 < R)
    (u v : Plane → Ambient q) (Du Dv : Plane → HarmonicMaps.Gradient 2 q)
    (hu : MemW12 (ballDomain (0 : Plane) R) u Du)
    (hv : MemW12 (terminalWallAnnulus R) v Dv)
    (P : C(Icc (R/2) R, Lp (Ambient q) 2 ((volume : Measure Plane).toSphere)))
    (T : C(Icc R (2*R), Lp (Ambient q) 2 ((volume : Measure Plane).toSphere)))
    (hP : RepresentsNativePlanarRadialTrace u P) (hT : RepresentsNativePlanarRadialTrace v T)
    (hRim : P ⟨R, half_le_self hR.le, le_rfl⟩ = T ⟨R, le_rfl, by linarith only [hR]⟩) :
    let f (y : Plane) := if ‖y‖ ≤ R then u y else v y
    let Df (y : Plane) (i : Fin 2) := if ‖y‖ < R then Du y i else Dv y i
    MemW12 (ballDomain (0 : Plane) (2*R)) f Df ∧
      HarmonicMaps.dirichletEnergy Df (ball (0 : Plane) (2*R)) =
        HarmonicMaps.dirichletEnergy Du (ball (0 : Plane) R) +
          HarmonicMaps.dirichletEnergy Dv (terminalWallAnnulus R).val := by
  intro f Df
  have hR₂ : R < 2*R := by linarith only [hR]
  obtain ⟨hw, _, hE⟩ := memW12_planar_core_annulus_glue_of_lt hR hR₂
    u v Du Dv hu hv P T hP hT hRim
  have hF : (fun y : Plane => if ‖y‖ < R then u y else v y) =ᵐ[volume.restrict (ball (0 : Plane) (2*R))] f := by
    filter_upwards [(ae_planar_norm_ne_terminalRim R).filter_mono (ae_mono Measure.restrict_le_self)] with y hy
    by_cases h : ‖y‖ < R
    · simp only [f, if_pos h, if_pos h.le]
    · simp only [f, if_neg h, if_neg (fun h' => hy (le_antisymm h' (le_of_not_gt h)))]
  exact ⟨hw.congr_ae hF EventuallyEq.rfl, hE⟩

private theorem terminalOrientedFace_value_lower {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hH : 0 < H) (D : TerminalCylinderBoundaryData q R hR)
    {y : Plane} (hy : y ∈ ball (0 : Plane) (2*R)) :
    terminalCylinderSurfaceValue B c H D (c + terminalOrientedFace B 1 R H y) =
      if ‖y‖ ≤ R then D.lower y else D.wall y := by
  unfold terminalOrientedFace
  split_ifs with h
  · rw [neg_one_mul, terminalCylinderSurfaceValue_lower]
  · rw [one_mul]
    exact terminalCylinderSurfaceValue_wall B c hH D ⟨lt_of_not_ge h, mem_ball_zero_iff.1 hy⟩

private theorem terminalOrientedFace_value_upper {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hH : 0 < H) (D : TerminalCylinderBoundaryData q R hR)
    {y : Plane} (hy : y ∈ ball (0 : Plane) (2*R)) :
    terminalCylinderSurfaceValue B c H D (c + terminalOrientedFace B (-1) R H y) =
      if ‖y‖ ≤ R then D.upper y else D.wall (terminalWallReflection R y) := by
  unfold terminalOrientedFace
  split_ifs with h
  · rw [neg_neg, one_mul, terminalCylinderSurfaceValue_upper B c hH]
  · have hyA : y ∈ (terminalWallAnnulus R).val := ⟨lt_of_not_ge h, mem_ball_zero_iff.1 hy⟩
    have hRef := terminalWallReflection_mapsTo hR hyA
    have hRefEq := terminalWallReflection_eq (R := R) (y := y)
      (Ioo_subset_Icc_self (show ‖y‖ ∈ Ioo R (2*R) from hyA))
    have hs : 0 < 3*R - ‖y‖ := by have hyN := mem_ball_zero_iff.1 hy; linarith only [hyN,hR]
    have hy₀ : y ≠ 0 := norm_pos_iff.1 (hR.trans (lt_of_not_ge h))
    have hG : terminalWallChart B c R H (terminalWallReflection R y) =
        c + axisChart B (R • NormedSpace.normalize y, (-1)*((2*H/R)*(‖y‖-R)-H)) := by
      rw [terminalWallChart, hRefEq, NormedSpace.normalize_smul_of_pos hs, norm_smul,
        NormedSpace.normalize_eq_self_of_norm_eq_one (NormedSpace.norm_normalize hy₀),
        Real.norm_of_nonneg hs.le, NormedSpace.norm_normalize hy₀, mul_one]
      have hZ : (2*H/R)*(3*R-‖y‖-R)-H = (-1)*((2*H/R)*(‖y‖-R)-H) := by
        field_simp
        ring
      rw [hZ]
    rw [← hG]
    exact terminalCylinderSurfaceValue_wall B c hH D hRef

private theorem terminalHalfParameter_memW12 {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) {s R H : ℝ}
    (hs : |s| = 1) (hR : 0 < R) (hLow : R/4 ≤ H) (hHigh : H ≤ R)
    {v : Plane → Ambient q} {D : Plane → HarmonicMaps.Gradient 2 q}
    (hv : MemW12 (ballDomain (0 : Plane) (2*R)) v D) :
    let P := terminalHalfParameter B s (R/H) R
    let U := terminalHalfShell B s (R/H)
    ∃ G : Point → HarmonicMaps.Gradient 3 q, MemW12 U (v ∘ P) G ∧
      HarmonicMaps.dirichletEnergy G U.val ≤
        (3*56^2*549250) * HarmonicMaps.dirichletEnergy D (ball (0 : Plane) (2*R)) := by
  intro P U
  let V := ballDomain (0 : Plane) (2*R)
  have hH := (div_pos hR (by norm_num : (0 : ℝ) < 4)).trans_le hLow
  have hk : 1 ≤ R/H := (one_le_div₀ hH).2 hHigh
  have hk₄ : R/H ≤ 4 := (div_le_iff₀ hH).2 (by linarith only [hLow])
  have hLip := terminalHalfParameter_lipschitz B hs (div_nonneg hR.le hH.le) hk₄ hR
  have hMap := map_terminalHalfParameter_volume_le B hs hR hLow hHigh
  have hInto : MapsTo P U.val V.val := fun _ hx => (terminalHalfParameter_reconstruct B hs hR hH hk hx).2.1
  let G (x : Point) (i : Fin 3) := ∑ j : Fin 2, (fderiv ℝ P x (EuclideanSpace.single i 1)) j • D (P x) j
  refine ⟨G, memW12_lipschitz_domain_pullback U V P hLip hInto ENNReal.ofReal_ne_top hMap hv, ?_⟩
  have hE := dirichletEnergy_lipschitz_domain_pullback_le U V P hLip hMap hv
  have hConst : ENNReal.ofReal (3 * ((Real.toNNReal (56*R) : ℝ≥0) : ℝ)^2) *
      ENNReal.ofReal (549250/R^2) = (3*56^2*549250 : ℝ≥0∞) := by
    rw [Real.coe_toNNReal _ (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    have h₁ : 3*(56*R)^2*(549250/R^2) = 3*56^2*549250 := by field_simp
    rw [h₁]
    norm_num
  change HarmonicMaps.dirichletEnergy G U.val ≤
    (ENNReal.ofReal (3 * ((Real.toNNReal (56*R) : ℝ≥0) : ℝ)^2) *
      ENNReal.ofReal (549250/R^2)) * HarmonicMaps.dirichletEnergy D (ball (0 : Plane) (2*R)) at hE
  rwa [hConst] at hE

private theorem dirichletEnergy_piecewise_cover_le {q : ℕ}
    {U V W : Set Point} (hU : MeasurableSet U) (hV : MeasurableSet V) (hCover : U ⊆ V ∪ W)
    (D G : Point → HarmonicMaps.Gradient 3 q) [DecidablePred (· ∈ V)] :
    HarmonicMaps.dirichletEnergy (fun x => if x ∈ V then D x else G x) U ≤
      HarmonicMaps.dirichletEnergy D V + HarmonicMaps.dirichletEnergy G W := by
  let f (x : Point) := ENNReal.ofReal (hsNormSq (if x ∈ V then D x else G x))
  change (∫⁻ x in U, f x) ≤ _
  rw [← lintegral_add_compl _ hV, Measure.restrict_restrict hV, Measure.restrict_restrict hV.compl]
  have hS : Vᶜ ∩ U ⊆ W := fun x hx => (hCover hx.2).resolve_left hx.1
  have hLeft : (∫⁻ x in V ∩ U, f x) ≤ HarmonicMaps.dirichletEnergy D V := by
    calc
      _ = ∫⁻ x in V ∩ U, ENNReal.ofReal (hsNormSq (D x)) :=
        setLIntegral_congr_fun (hV.inter hU) (fun x hx => by simp only [f, if_pos hx.1])
      _ ≤ _ := lintegral_mono' (Measure.restrict_mono_set _ inter_subset_left) (fun _ => le_rfl)
  have hRight : (∫⁻ x in Vᶜ ∩ U, f x) ≤ HarmonicMaps.dirichletEnergy G W := by
    calc
      _ = ∫⁻ x in Vᶜ ∩ U, ENNReal.ofReal (hsNormSq (G x)) :=
        setLIntegral_congr_fun (hV.compl.inter hU) (fun x hx => by simp only [f, if_neg hx.1])
      _ ≤ _ := lintegral_mono' (Measure.restrict_mono_set _ hS) (fun _ => le_rfl)
  exact add_le_add hLeft hRight

/-- The degree-zero boundary extension has the original weak graph in the round
annulus. Its energy is bounded by a uniform multiple of the three genuine faces. -/
theorem exists_terminalCylinder_radialGraph {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hLow : R/4 ≤ H) (hHigh : H ≤ R) (D : TerminalCylinderBoundaryData q R hR) :
    let w (x : Point) := terminalCylinderSurfaceValue B c H D
      (c + (R / terminalFrameGauge B (R/H) x) • x)
    ∃ G : Point → HarmonicMaps.Gradient 3 q, MemW12 terminalRoundShell w G ∧
      HarmonicMaps.dirichletEnergy G terminalRoundShell.val ≤ (2*(3*56^2*549250)*20001) *
        terminalCylinderSurfaceDirichlet H D := by
  classical
  intro w
  let f₁ (y : Plane) := if ‖y‖ ≤ R then D.lower y else D.wall y
  let f₂ (y : Plane) := if ‖y‖ ≤ R then D.upper y else D.wall (terminalWallReflection R y)
  let V₁ := terminalHalfShell B 1 (R/H)
  let V₂ := terminalHalfShell B (-1) (R/H)
  let P₁ := terminalHalfParameter B 1 (R/H) R
  let P₂ := terminalHalfParameter B (-1) (R/H) R
  have hH := (div_pos hR (by norm_num : (0 : ℝ) < 4)).trans_le hLow
  have hk : 1 ≤ R / H := (one_le_div₀ hH).2 hHigh
  obtain ⟨J, hJ, hJE⟩ := terminalWallReflection_memW12 hR D.wall_memW12
  obtain ⟨T, hT, hTR⟩ := terminalWallReflection_trace hR D.wallTrace D.wallTraceData
  let G₁ (y : Plane) (i : Fin 2) := if ‖y‖ < R then D.lowerDerivative y i else D.wallDerivative y i
  let G₂ (y : Plane) (i : Fin 2) := if ‖y‖ < R then D.upperDerivative y i else J y i
  obtain ⟨h₁, hE₁⟩ := terminalDiskWall_memW12 hR D.lower D.wall D.lowerDerivative D.wallDerivative
    D.lower_memW12 D.wall_memW12 D.lowerTrace D.wallTrace D.lowerTraceData D.wallTraceData D.lowerRim
  obtain ⟨h₂, hE₂⟩ := terminalDiskWall_memW12 hR D.upper (D.wall ∘ terminalWallReflection R)
    D.upperDerivative J D.upper_memW12 hJ D.upperTrace T D.upperTraceData hT (D.upperRim.trans hTR.symm)
  have hF₁ : MemW12 (ballDomain (0 : Plane) (2*R)) f₁ G₁ := h₁
  have hF₂ : MemW12 (ballDomain (0 : Plane) (2*R)) f₂ G₂ := h₂
  have hs₁ : |(1 : ℝ)| = 1 := by norm_num
  have hs₂ : |(-1 : ℝ)| = 1 := by norm_num
  obtain ⟨K₁, hK₁, hKE₁⟩ := terminalHalfParameter_memW12 B hs₁ hR hLow hHigh hF₁
  obtain ⟨K₂, hK₂, hKE₂⟩ := terminalHalfParameter_memW12 B hs₂ hR hLow hHigh hF₂
  have hW₁ : MemW12 V₁ w K₁ := hK₁.congr_ae
    ((ae_restrict_mem V₁.property.measurableSet).mono fun x hx => by
      have hRec := terminalHalfParameter_reconstruct B hs₁ hR hH hk hx
      have h := terminalOrientedFace_value_lower B c hR hH D hRec.2.1
      rw [hRec.2.2] at h
      exact h.symm) EventuallyEq.rfl
  have hW₂ : MemW12 V₂ w K₂ := hK₂.congr_ae
    ((ae_restrict_mem V₂.property.measurableSet).mono fun x hx => by
      have hRec := terminalHalfParameter_reconstruct B hs₂ hR hH hk hx
      have h := terminalOrientedFace_value_upper B c hR hH D hRec.2.1
      rw [hRec.2.2] at h
      exact h.symm) EventuallyEq.rfl
  have hCover := (terminalHalfShell_cover B hk).ge
  let G (x : Point) := if x ∈ V₁.val then K₁ x else K₂ x
  have hW : MemW12 terminalRoundShell w G := by
    have h := memW12_openOverlap_piecewise hW₁ hW₂ hCover (fun _ _ => rfl)
    simpa only [ite_self] using h
  refine ⟨G, hW, ?_⟩
  let A := terminalCylinderSurfaceDirichlet H D
  let C : ℝ≥0∞ := 3*56^2*549250
  have hWE := terminalWall_dirichletEnergy_le hR hLow hHigh D.wallDerivative
  have hL : HarmonicMaps.dirichletEnergy D.lowerDerivative (ball 0 R) ≤ A := by
    unfold A terminalCylinderSurfaceDirichlet
    exact (le_self_add (b := HarmonicMaps.dirichletEnergy D.upperDerivative (ball 0 R))).trans (le_self_add)
  have hU : HarmonicMaps.dirichletEnergy D.upperDerivative (ball 0 R) ≤ A := by
    unfold A terminalCylinderSurfaceDirichlet
    have h : HarmonicMaps.dirichletEnergy D.upperDerivative (ball 0 R) ≤
        HarmonicMaps.dirichletEnergy D.lowerDerivative (ball 0 R) +
          HarmonicMaps.dirichletEnergy D.upperDerivative (ball 0 R) := le_add_of_nonneg_left zero_le
    exact h.trans le_self_add
  have hEWall : HarmonicMaps.dirichletEnergy D.wallDerivative (terminalWallAnnulus R).val ≤ 16 * A := by
    apply hWE.trans
    unfold A terminalCylinderSurfaceDirichlet
    exact mul_le_mul_right (le_add_self) _
  have hJWall : HarmonicMaps.dirichletEnergy J (terminalWallAnnulus R).val ≤ 20000 * A := by
    apply hJE.trans
    have h := mul_le_mul_right hEWall (1250 : ℝ≥0∞)
    rwa [← mul_assoc, show (1250 : ℝ≥0∞) * 16 = 20000 by norm_num] at h
  have hTarget₁ : HarmonicMaps.dirichletEnergy G₁ (ball (0 : Plane) (2*R)) ≤ 20001*A := by
    change HarmonicMaps.dirichletEnergy G₁ (ball (0 : Plane) (2*R)) = _ at hE₁
    rw [hE₁, show (20001 : ℝ≥0∞) = 1+20000 by norm_num, add_mul, one_mul]
    exact add_le_add hL (hEWall.trans (mul_le_mul_left (by norm_num) _))
  have hTarget₂ : HarmonicMaps.dirichletEnergy G₂ (ball (0 : Plane) (2*R)) ≤ 20001*A := by
    change HarmonicMaps.dirichletEnergy G₂ (ball (0 : Plane) (2*R)) = _ at hE₂
    rw [hE₂, show (20001 : ℝ≥0∞) = 1+20000 by norm_num, add_mul, one_mul]
    exact add_le_add hU hJWall
  calc
    _ ≤ HarmonicMaps.dirichletEnergy K₁ V₁.val + HarmonicMaps.dirichletEnergy K₂ V₂.val :=
      dirichletEnergy_piecewise_cover_le terminalRoundShell.property.measurableSet
        V₁.property.measurableSet hCover K₁ K₂
    _ ≤ C * (20001 * A) + C * (20001 * A) :=
      add_le_add (hKE₁.trans (mul_le_mul_right hTarget₁ _)) (hKE₂.trans (mul_le_mul_right hTarget₂ _))
    _ = _ := by
      change C * (20001 * A) + C * (20001 * A) = (2 * C * 20001) * A
      ring

end Thesis.MeasureGeometry

end

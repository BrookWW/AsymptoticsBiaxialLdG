module

public import Thesis.Interpolation.CylinderRecoveryMiddle
public import Thesis.Interpolation.CylinderCapClassicalData
public import Thesis.MeasureGeometry.CylinderUpperLimit
import Thesis.MeasureGeometry.CylinderEndHeights

/-! The genuine cylinder competitor and its normalized comparison on the fixed band. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

private theorem closedCylinder_subset_regularBall (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) {r s lo hi : ℝ} (hs : 0 < s) (hrs : r < s) (hlo : -s ≤ lo) (hhi : hi ≤ s) :
    translatedClosedAxisCylinder c (B 2) r lo hi ⊆ ball c (2 * s) := by
  intro x hx
  have hx' : x - c ∈ closedAxisCylinder (B 2) r lo hi := hx
  exact closedCylinder_centered_height_subset_ball B c hs hrs
    (show x - c ∈ closedAxisCylinder (B 2) r (-s) s from
      ⟨hx'.1, hlo.trans hx'.2.1, hx'.2.2.trans hhi⟩)

private theorem horizontal_mem_closedCylinder (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) {r lo hi z : ℝ} (hz : z ∈ Icc lo hi) {y : Plane}
    (hy : y ∈ closedBall (0 : Plane) r) :
    c + axisChart B (y, z) ∈ translatedClosedAxisCylinder c (B 2) r lo hi := by
  change c + axisChart B (y, z) - c ∈ closedAxisCylinder (B 2) r lo hi
  rw [add_sub_cancel_left]
  simp only [closedAxisCylinder, mem_setOf_eq, cylinderTransverseRadius_axisChart, cylinderHeight_axisChart]
  exact ⟨mem_closedBall_zero_iff.1 hy, hz⟩

private theorem planarWeakEnergy_nonneg (a : BulkCoefficients) (ε : ℝ)
    (u : Plane → Ambient 5) (D : Plane → HarmonicMaps.Gradient 2 5) (r : ℝ) :
    0 ≤ planarWeakEnergy a ε u D r :=
  add_nonneg (mul_nonneg (by norm_num) (integral_nonneg fun _ => hsNormSq_nonneg _))
    (mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => bulkPotential_nonneg a _))

private theorem nativeVacuumCircleCost_range (a : BulkCoefficients) (p : C(NativeCircle, vacuum a)) :
    0 ≤ nativeVacuumCircleCost a p ∧ nativeVacuumCircleCost a p ≤ 2 * kappaStar a := by
  have h := nativeVacuumCircleCost_mem_three a p
  simp only [mem_insert_iff, mem_singleton_iff] at h
  rcases h with h | h | h <;> rw [h] <;> constructor <;> linarith only [kappaStar_pos a]

private theorem terminalCost_pair_le (a : BulkCoefficients) (ε : ElasticScale)
    {r : ℝ} {hr : 0 < r} (L U : TerminalCylinderBoundaryData 5 r hr)
    {u v w z A B C : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hz : 0 ≤ z) (hC : 0 ≤ C)
    (hL : terminalCylinderSurfacePenalizedEnergy a ε (r / 4) L ≤
      ENNReal.ofReal u + ENNReal.ofReal v + ENNReal.ofReal C)
    (hU : terminalCylinderSurfacePenalizedEnergy a ε (r / 4) U ≤
      ENNReal.ofReal w + ENNReal.ofReal z + ENNReal.ofReal C)
    (hEnd : u + z ≤ A) (hInner : v + w + 2 * C ≤ B) :
    terminalCylinderSurfacePenalizedEnergy a ε (r / 4) L +
      terminalCylinderSurfacePenalizedEnergy a ε (r / 4) U ≤ ENNReal.ofReal (A + B) := by
  calc
    _ ≤ (ENNReal.ofReal u + ENNReal.ofReal v + ENNReal.ofReal C) +
        (ENNReal.ofReal w + ENNReal.ofReal z + ENNReal.ofReal C) := add_le_add hL hU
    _ = ENNReal.ofReal ((u + v + C) + (w + z + C)) := by
      rw [← ENNReal.ofReal_add hu hv, ← ENNReal.ofReal_add hw hz,
        ← ENNReal.ofReal_add (add_nonneg hu hv) hC, ← ENNReal.ofReal_add (add_nonneg hw hz) hC,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith only [hEnd, hInner])

/-- For the same regular sequence, the upper recovery has a cap coefficient
uniform in the radius, half-height, position, and regular compact wall. -/
theorem exists_eventually_normalizedCylinder_upper_of_regularBand (a : BulkCoefficients)
    (hPolar : External.PeriodicAngularSobolev)
    (hSurf : External.TerminalCylinderSurfaceSobolev) (hTransport : External.AmbientBiLipschitzSobolevPullback3)
    (hChart : External.CylinderBoundaryChartTraceTransport) (hKernel : External.CylinderBoundaryTraceKernel)
    {Ω R : Set Point} (hΩ : IsOpen Ω) (hR : IsOpen R) (hRO : R ⊆ Ω)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (q : Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hMin : ∀ n, IsLocalEnergyMinimizer a (ε n) Ω (Q n) (ClassicalGradient (Q n)))
    (hF : ∀ n, energy a (ε n) Ω (Q n) (ClassicalGradient (Q n)) < ⊤)
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω) (hq : ContDiffOn ℝ ∞ q R) (hVac : MapsTo q R (vacuum a))
    {M : ℝ} (hRange : ∀ n x, x ∈ Ω → ‖Q n x‖ ≤ M)
    (hDensity : ∀ K : Set Point, IsCompact K → K ⊆ R → ∃ D > (0 : ℝ),
      ∀ n x, x ∈ K → energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ D)
    (hConv : ∀ K : Set Point, IsCompact K → K ⊆ R → TendstoUniformlyOn Q q atTop K)
    (ν : ℕ → Measure Point)
    (hν : ∀ n, ν n = normalizedEnergyMeasure a (ε n) Ω (Q n) (ClassicalGradient (Q n))) :
    ∀ cap : ℝ, 0 ≤ cap → ∃ C ≥ (0 : ℝ),
      ∀ (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {r s : ℝ}, 0 < r → 0 < s → r < s →
        closedBall c (2 * s) ⊆ Ω → ∀ K : Set Point, IsCompact K → K ⊆ R →
        (∀ z ∈ Icc (-s) s, ∀ θ : NativeCircle, c + axisChart B (r • θ.val, z) ∈ K) →
        ∀ p : C(NativeCircle, vacuum a),
          (∀ θ, (p θ).val = q (c + axisChart B (r • θ.val, 0))) →
          ∀ ξ > 0, ∀ᶠ n : ℕ in atTop,
            ∀ lo ∈ Ioo (-s) (-(s / 2)), ∀ hi ∈ Ioo (s / 2) s,
              planarSmoothEnergy a (ε n) (cylinderSliceMap B c (Q n) lo) r +
                planarSmoothEnergy a (ε n) (cylinderSliceMap B c (Q n) hi) r ≤
                  cap * Real.log (1 / (ε n : ℝ)) →
              ((ν n) (translatedAxisCylinder c (B 2) r lo hi)).toReal / (hi - lo) ≤
                nativeVacuumCircleCost a p + C * (r / (hi - lo)) + ξ := by
  obtain ⟨K₀, hK₀, hComp⟩ := exists_cylinderRecoveryCompetitor a hSurf hTransport hChart hKernel
  intro cap hcap
  let Ccap := K₀ * (cap + 4 * kappaStar a)
  have hCcap : 0 ≤ Ccap := mul_nonneg hK₀.le (by have := kappaStar_pos a; positivity)
  refine ⟨Ccap, hCcap, ?_⟩
  intro B c r s hr hs hrs hBall K hK hKR hLat p hp
  let e := nativeVacuumCircleCost a p
  obtain ⟨he, heκ⟩ := nativeVacuumCircleCost_range a p
  apply eventually_normalizedCylinder_upper_of_trace_matched_competitors a B c hr hs hrs hBall he hCcap
    ε Q hε hMin hF ν hν
  obtain ⟨D, hD, hDensityK⟩ := hDensity K hK hKR
  have hKO : K ⊆ Ω := hKR.trans hRO
  obtain ⟨C₀, C, hC₀, hC, V, _, hCV, hMiddle⟩ := exists_cylinderRecoveryMiddle_of_regular_band
    a hPolar hR hKR B c hr hs hD.le hLat ε hε hq (fun n => (hQ n).mono hRO)
    (hVac.mono_left hKR) (hConv K hK hKR) (fun n x hx => hRange n x (hKO hx)) hDensityK p hp
  obtain ⟨Cw, hCw, hWall⟩ := exists_uniform_terminalWall_energy a B c hr (by positivity : 0 < r / 4)
    hD.le hΩ hKO hLat ε hQ hDensityK
  let Ca := C * (volume (ball (0 : Plane) r)).toReal
  let Cv := C * (volume (cylinderRecoveryBand B c r s)).toReal
  let Cside := max Cv (2 * Ca + 2 * Cw)
  have hCa : 0 ≤ Ca := by dsimp only [Ca]; positivity
  have hCv : 0 ≤ Cv := by dsimp only [Cv]; positivity
  have hCs : 0 ≤ Cside := hCv.trans (le_max_left _ _)
  let A := 2 * s * C₀ + Cside + K₀ * r * (4 * kappaStar a * |Real.log (r / 2)| + 2 * C₀ + Cside)
  have hA : 0 ≤ A := by dsimp only [A]; have := kappaStar_pos a; positivity
  refine ⟨A, hA, ?_⟩
  filter_upwards [hMiddle, hε.eventually_lt_const (half_pos hr)] with n hn hScale lo hlo hi hhi hEnds
  obtain ⟨G⟩ := hn
  let l := lo + r / 2
  let u := hi - r / 2
  have hCut : l < u := by dsimp only [l, u]; linarith only [hlo.2, hhi.1, hrs]
  have hll : lo < l := by dsimp only [l]; linarith only [hr]
  have huh : u < hi := by dsimp only [u]; linarith only [hr]
  have hl₀ : -s ≤ l := hlo.1.le.trans hll.le
  have hu₀ : u ≤ s := huh.le.trans hhi.2.le
  have hl : l ∈ Icc (-s) s := ⟨hl₀, hCut.le.trans hu₀⟩
  have hu : u ∈ Icc (-s) s := ⟨hl₀.trans hCut.le, hu₀⟩
  have hlh : lo < hi := hll.trans (hCut.trans huh)
  let S := translatedAxisCylinder c (B 2) r lo hi
  let Sclosure := translatedClosedAxisCylinder c (B 2) r lo hi
  have hSO : Sclosure ⊆ Ω :=
    (closedCylinder_subset_regularBall B c hs hrs hlo.1.le hhi.2.le).trans (ball_subset_closedBall.trans hBall)
  have hcl : closure S ⊆ Sclosure :=
    closure_minimal (translatedAxisCylinder_subset_closed _ _ _ _ _)
      (isCompact_translatedClosedAxisCylinder (B.orthonormal.norm_eq_one 2) _ _ _).isClosed
  have hS : IsOpen S := isOpen_translatedAxisCylinder _ _ _ _ _
  have hSobRef := (hMin n).1 S hS
    ⟨(isCompact_translatedClosedAxisCylinder (B.orthonormal.norm_eq_one 2) r lo hi).of_isClosed_subset
      isClosed_closure hcl, hcl.trans hSO⟩
  have hRefCont := (hQ n).continuousOn.mono hSO
  let g₁ := frobeniusCoordinateEquiv ∘ cylinderSliceMap B c (Q n) lo
  let g₂ := frobeniusCoordinateEquiv ∘ cylinderSliceMap B c (Q n) hi
  have hClosed₁ : ∀ y ∈ closedBall (0 : Plane) r, c + axisChart B (y, lo) ∈ Ω :=
    fun y hy => hSO (horizontal_mem_closedCylinder B c ⟨le_rfl, hlh.le⟩ hy)
  have hClosed₂ : ∀ y ∈ closedBall (0 : Plane) r, c + axisChart B (y, hi) ∈ Ω :=
    fun y hy => hSO (horizontal_mem_closedCylinder B c ⟨hlh.le, le_rfl⟩ hy)
  obtain ⟨hG₁, hG₁C, hG₁E⟩ := cylinderSlice_nativeGraph B c a (ε n) hΩ (hQ n) r lo hClosed₁
  obtain ⟨hG₂, hG₂C, hG₂E⟩ := cylinderSlice_nativeGraph B c a (ε n) hΩ (hQ n) r hi hClosed₂
  let M' := max M (Real.sqrt 2 * vacuumRadius a)
  have hGR (z : ℝ) (hz : ∀ y ∈ closedBall (0 : Plane) r, c + axisChart B (y, z) ∈ Ω) :
      ∀ᵐ y ∂volume.restrict (ball (0 : Plane) r),
        ‖(frobeniusCoordinateEquiv ∘ cylinderSliceMap B c (Q n) z) y‖ ≤ M' := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_ball] with y hy
    exact (frobeniusCoordinateEquiv.norm_map _).le.trans
      ((hRange n _ (hz y (ball_subset_closedBall hy))).trans (le_max_left _ _))
  let W := cylinderSideRecovery a B c r 0 q (Q n)
  let v₁ := cylinderMiddleSlice B c r G.core W l
  let v₂ := cylinderMiddleSlice B c r G.core W u
  obtain ⟨D₁, hV₁, hV₁E⟩ := G.slice l hl
  obtain ⟨D₂, hV₂, hV₂E⟩ := G.slice u hu
  have hBand (a₀ b₀ : ℝ) (ha : -s ≤ a₀) (hb : b₀ ≤ s) :
      ∀ z ∈ Icc a₀ b₀, ∀ θ : NativeCircle,
        let x := c + axisChart B (r • θ.val, z)
        x ∈ Ω ∧ ‖Q n x‖ ≤ M' := by
    intro z hz θ
    have hx := hKO (hLat z ⟨ha.trans hz.1, hz.2.trans hb⟩ θ)
    exact ⟨hx, (hRange n _ hx).trans (le_max_left _ _)⟩
  obtain ⟨L, hLg, hLv, hLW, hLB, hLE⟩ := exists_terminalData_of_original_wall a (ε n) B c hr
    hll.le hΩ (hQ n) (hBand lo l hlo.1.le hl.2) g₁ v₁ (planarClassicalColumns g₁) D₁
    hG₁ hV₁ (hG₁C.mono (fun _ hy => mem_closedBall_zero_iff.2 hy.2))
    (G.slice_continuousOn_collar hr hCV hl) (hGR lo hClosed₁) (G.slice_range l hl)
    (fun _ => rfl) (G.slice_rim_eq_ref hr hl)
  obtain ⟨U, hUv, hUg, hUW, hUB, hUE⟩ := exists_terminalData_of_original_wall a (ε n) B c hr
    huh.le hΩ (hQ n) (hBand u hi hu.1 hhi.2.le) v₂ g₂ D₂ (planarClassicalColumns g₂)
    hV₂ hG₂ (G.slice_continuousOn_collar hr hCV hu)
    (hG₂C.mono (fun _ hy => mem_closedBall_zero_iff.2 hy.2)) (G.slice_range u hu) (hGR hi hClosed₂)
    (G.slice_rim_eq_ref hr hu) (fun _ => rfl)
  obtain ⟨hGV, hME⟩ := G.volume hl₀ hCut hu₀
  obtain ⟨P, T, hP, hT, hPT, hTT⟩ := G.traces hl₀ hCut hu₀
  have hBelow : (l - lo) / 2 = r / 4 := by dsimp only [l]; ring
  have hAbove : (hi - u) / 2 = r / 4 := by dsimp only [u]; ring
  have hMatch : CylinderTerminalRimMatches B c hr hCut L U (Q n) P T :=
    ⟨Eventually.of_forall (congrFun hLg), Eventually.of_forall (congrFun hUg),
      (hPT ⟨l, le_rfl, hCut.le⟩).trans (Eventually.of_forall (congrFun hLv.symm)),
      (hPT ⟨u, hCut.le, le_rfl⟩).trans (Eventually.of_forall (congrFun hUv.symm)),
      by simpa only [hBelow] using terminalSurface_wall_eq_original B c hr L hLW,
      hTT ⟨r, half_le_self hr.le, le_rfl⟩ rfl,
      by simpa only [hAbove] using terminalSurface_wall_eq_original B c hr U hUW⟩
  obtain ⟨w, Dw, _, hSame, hEnergy⟩ := hComp B c hr hCut (ε n) L U M' hLB hUB G.field (Q n)
    G.gradient (ClassicalGradient (Q n)) hGV hSobRef hRefCont P T hP hT hMatch
  have hWL := hWall n hlo.1.le hl.2 hBelow
  have hWU := hWall n hu.1 hhi.2.le hAbove
  rw [hBelow, hG₁E] at hLE
  rw [hAbove, hG₂E] at hUE
  let E₁ := planarSmoothEnergy a (ε n) (cylinderSliceMap B c (Q n) lo) r
  let E₂ := planarSmoothEnergy a (ε n) (cylinderSliceMap B c (Q n) hi) r
  let F₁ := planarWeakEnergy a (ε n) v₁ D₁ r
  let F₂ := planarWeakEnergy a (ε n) v₂ D₂ r
  let Pcore := e * Real.log ((r / 2) / (ε n : ℝ)) + C₀
  let H := hi - lo
  let Hmid := u - l
  have hPc : 0 ≤ Pcore := add_nonneg (mul_nonneg he (Real.log_nonneg
    ((one_le_div (ε n).2.1).2 hScale.le))) hC₀
  have hF₁ : 0 ≤ F₁ := planarWeakEnergy_nonneg _ _ _ _ _
  have hF₂ : 0 ≤ F₂ := planarWeakEnergy_nonneg _ _ _ _ _
  have hE₁ : 0 ≤ E₁ := integral_nonneg fun _ => planarSmoothEnergyDensity_nonneg _ _ _ _
  have hE₂ : 0 ≤ E₂ := integral_nonneg fun _ => planarSmoothEnergyDensity_nonneg _ _ _ _
  have hEndCap : 0 ≤ cap * Real.log (1 / (ε n : ℝ)) := mul_nonneg hcap (log_inv_scale_pos (ε n)).le
  have hCore := G.core_cost
  have hInner : F₁ + F₂ + 2 * Cw ≤ 2 * Pcore + Cside := by
    have hCs' : 2 * Ca + 2 * Cw ≤ Cside := le_max_right _ _
    change F₁ ≤ planarWeakEnergy a (ε n) G.core G.coreDerivative (r / 2) + Ca at hV₁E
    change F₂ ≤ planarWeakEnergy a (ε n) G.core G.coreDerivative (r / 2) + Ca at hV₂E
    change planarWeakEnergy a (ε n) G.core G.coreDerivative (r / 2) ≤ Pcore at hCore
    linarith only [hV₁E, hV₂E, hCore, hCs']
  have hCaps := terminalCost_pair_le a (ε n) L U hE₁ hF₁ hF₂ hE₂ hCw
    (hLE.le.trans (add_le_add le_rfl hWL)) (hUE.le.trans (add_le_add le_rfl hWU)) hEnds hInner
  let Cfeat := cap * Real.log (1 / (ε n : ℝ)) + (2 * Pcore + Cside)
  have hCfeat : 0 ≤ Cfeat := by dsimp only [Cfeat]; positivity
  have hHmid : 0 ≤ Hmid := sub_nonneg.2 hCut.le
  have hHmidH : Hmid ≤ H := by dsimp only [Hmid, H, l, u]; linarith only [hr]
  have hH : H ≤ 2 * s := by dsimp only [H]; linarith only [hlo.1, hhi.2]
  have hCombined : energy a (ε n) S w Dw ≤ ENNReal.ofReal (Hmid * Pcore + Cside + K₀ * r * Cfeat) := by
    calc
      _ ≤ (ENNReal.ofReal (Hmid * Pcore) + ENNReal.ofReal Cside) +
          ENNReal.ofReal (K₀ * r) * ENNReal.ofReal Cfeat := by
        apply hEnergy.trans
        exact add_le_add (hME.trans (add_le_add
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hCore hHmid))
          (ENNReal.ofReal_le_ofReal (le_max_left _ _)))) (mul_le_mul_right hCaps _)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hK₀.le hr.le),
          ← ENNReal.ofReal_add (mul_nonneg hHmid hPc) hCs, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hBudget := cylinderRecovery_energy_budget a (cap := cap) (e := e)
    hr (ε n).2.1 hScale.le hHmid hHmidH hH he heκ hK₀.le hC₀
    (E := Hmid * Pcore + Cside + K₀ * r * Cfeat) (Ecore := Hmid * Pcore)
    (Eside := Cside) (Ecaps := K₀ * r * Cfeat) le_rfl le_rfl le_rfl (by
      dsimp only [Cfeat, Pcore]
      apply le_of_eq
      ring)
  exact ⟨w, Dw, hSame, hCombined.trans (ENNReal.ofReal_le_ofReal hBudget)⟩

end Thesis.MeasureGeometry

module

public import Thesis.MeasureGeometry.CylinderDensityAssembly
public import Thesis.MeasureGeometry.LocalEdgeMeasure
public import Thesis.MeasureGeometry.MeridianWeightComparison
public import Thesis.MeasureGeometry.OrthogonalMeridianRadii
public import Thesis.MeasureGeometry.OrthogonalMeridians

/-! The splitting cost of the actual transverse meridian recovers the
weight of the same edge in the limiting energy measure. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

private theorem exists_radius_and_compact_edgeSide
    {Ω S Spt : Set Point} (hP : Spt.Countable)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (x : Point)
    {R s : ℝ} (hs : 0 < s) (h2s : 2*s < R)
    (hΩ : ball x R ⊆ Ω)
    (hGerm : ∀ y ∈ ball x R, y ∈ S ↔ axisChartTransverseCoordinates B (y-x) = 0) :
    ∀ ρ : ℝ, 0 < ρ → ∃ r ∈ Ioo 0 (min ρ s), ∃ T : Set Point,
      IsCompact T ∧ T ⊆ (Ω \ S) \ Spt ∧
      ∀ z ∈ Icc (-s) s, ∀ w : NativeCircle, x + axisChart B (r • w.val,z) ∈ T := by
  intro ρ hρ
  let f (y : Point) := cylinderTransverseRadius (B 2) (y-x)
  have hBad : (f '' Spt).Countable := hP.image f
  have hRadius : ∃ r ∈ Ioo (0 : ℝ) (min ρ s), r ∉ f '' Spt := by
    by_contra! h
    have hZero := hBad.measure_zero (volume : Measure ℝ)
    have hMass := (measure_mono (μ := (volume : Measure ℝ)) (show Ioo (0 : ℝ) (min ρ s) ⊆ f '' Spt from h)).trans_eq hZero
    rw [Real.volume_Ioo, sub_zero] at hMass
    exact (ENNReal.ofReal_pos.mpr (lt_min hρ hs)).not_ge hMass
  obtain ⟨r,hr,hSafe⟩ := hRadius
  have hrs := hr.2.trans_le (min_le_right ρ s)
  let F (p : ℝ × Plane) := x + axisChart B (r • p.2,p.1)
  let T := F '' (Icc (-s) s ×ˢ sphere (0 : Plane) 1)
  have hF : Continuous F := continuous_const.add ((continuous_axisChart B).comp
    ((continuous_snd.const_smul r).prodMk continuous_fst))
  have hT : IsCompact T := (isCompact_Icc.prod (isCompact_sphere _ _)).image hF
  have hTinside : T ⊆ (Ω \ S) \ Spt := by
    rintro _ ⟨p, hp, rfl⟩
    have hRad : ‖r • p.2‖ = r := by
      rw [norm_smul, Real.norm_of_nonneg hr.1.le, mem_sphere_zero_iff_norm.mp hp.2, mul_one]
    have hC : F p ∈ translatedClosedAxisCylinder x (B 2) r (-s) s := by
      change x + axisChart B (r • p.2,p.1) - x ∈ closedAxisCylinder (B 2) r (-s) s
      rw [add_sub_cancel_left]
      change cylinderTransverseRadius (B 2) (axisChart B (r • p.2,p.1)) ≤ r ∧
        -s ≤ cylinderHeight (B 2) (axisChart B (r • p.2,p.1)) ∧
        cylinderHeight (B 2) (axisChart B (r • p.2,p.1)) ≤ s
      rw [cylinderTransverseRadius_axisChart, cylinderHeight_axisChart, hRad]
      exact ⟨le_rfl,hp.1⟩
    have hB : F p ∈ ball x R := ball_subset_ball h2s.le
      (closedCylinder_centered_height_subset_ball B x hs hrs hC)
    have hAt : f (F p) = r := by
      change cylinderTransverseRadius (B 2) (x + axisChart B (r • p.2,p.1) - x) = r
      rw [add_sub_cancel_left, cylinderTransverseRadius_axisChart, hRad]
    refine ⟨⟨hΩ hB,?_⟩, fun h => hSafe ⟨F p,h,hAt⟩⟩
    intro h
    have hProj := (hGerm _ hB).mp h
    change axisChartTransverseCoordinates B (x + axisChart B (r • p.2,p.1) - x) = 0 at hProj
    rw [add_sub_cancel_left, axisChartTransverseCoordinates_axisChart] at hProj
    apply hr.1.ne'
    rw [← hRad, hProj, norm_zero]
  exact ⟨r,hr,T,hT,hTinside,fun z hz w => ⟨(z,w.val),⟨hz,w.property⟩,rfl⟩⟩

/-- A selected cylinder at an open edge and all its nearby cap heights
see the original regular side, the original normalized measures, and
one common meridian cost. -/
theorem orthogonal_meridian_cost_eq_local_weight_of_upper
    (hAvoid : External.RelativeAnnulusPointAvoidance)
    (hcoarea : External.PlanarScalarCoarea) (hAngular : External.PeriodicAngularSobolev)
    (a : BulkCoefficients) {Ω S Spt : Set Point} (hΩ : IsOpen Ω) (hS : IsClosed S)
    (hLoc : LocallyFiniteIn (Ω \ S) Spt) (hSpt : Spt ⊆ Ω \ S)
    {M : ℝ} (hM : 0 ≤ M) (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (Q₀ : Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω)
    (hEuler : ∀ n x, x ∈ Ω → (ε n : ℝ)^2 • (laplacian (Q n) x : S0).val = bulkGradient a (Q n x))
    (hBound : ∀ n x, x ∈ Ω → ‖Q n x‖ ≤ M)
    (hEnergy : ∀ n, energy a (ε n) Ω (Q n) (ClassicalGradient (Q n)) ≤
      ENNReal.ofReal (M * (Real.log (1 / (ε n : ℝ)) + 1)))
    (hQ₀ : ContinuousOn Q₀ ((Ω \ S) \ Spt)) (hVac : MapsTo Q₀ ((Ω \ S) \ Spt) (vacuum a))
    (hDensity : ∀ T : Set Point, IsCompact T → T ⊆ (Ω \ S) \ Spt → ∃ D : ℝ,
      ∀ n x, x ∈ T → energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ D)
    (hConv : ∀ T : Set Point, IsCompact T → T ⊆ (Ω \ S) \ Spt → TendstoUniformlyOn Q Q₀ atTop T)
    (ν : ℕ → FiniteMeasure Point) (μ : FiniteMeasure Point) (hWeak : Tendsto ν atTop (𝓝 μ))
    (hν : ∀ n, (ν n : Measure Point) = normalizedEnergyMeasure a (ε n) Ω (Q n) (ClassicalGradient (Q n)))
    (B : OrthonormalBasis (Fin 3) ℝ Point) (x : Point) {R θ : ℝ} (hR : 0 < R)
    (hθ : 0 ≤ θ) (hΩR : ball x R ⊆ Ω)
    (hGerm : ∀ y ∈ ball x R, y ∈ S ↔ axisChartTransverseCoordinates B (y-x) = 0)
    (hLocal : (μ : Measure Point).restrict (ball x R) = (ENNReal.ofReal θ • HausdorffOne.restrict
      ((fun y : Point => x+y) '' ((Submodule.span ℝ {B 2} : Submodule ℝ Point) : Set Point))).restrict
        (ball x R))
    (hUpper : ∀ cap : ℝ, 0 ≤ cap → ∃ C ≥ (0 : ℝ),
      ∀ {r s : ℝ}, 0 < r → 0 < s → r < s → closedBall x (2*s) ⊆ Ω →
        ∀ T : Set Point, IsCompact T → T ⊆ (Ω \ S) \ Spt →
          (∀ z ∈ Icc (-s) s, ∀ w : NativeCircle, x + axisChart B (r • w.val,z) ∈ T) →
          ∀ p : C(NativeCircle, vacuum a),
            (∀ w, (p w).val = Q₀ (x + axisChart B (r • w.val,0))) →
            ∀ ξ > 0, ∀ᶠ n : ℕ in atTop,
              ∀ lo ∈ Ioo (-s) (-(s/2)), ∀ hi ∈ Ioo (s/2) s,
                planarSmoothEnergy a (ε n) (cylinderSliceMap B x (Q n) lo) r +
                  planarSmoothEnergy a (ε n) (cylinderSliceMap B x (Q n) hi) r ≤
                    cap * Real.log (1 / (ε n : ℝ)) →
                ((ν n : Measure Point) (translatedAxisCylinder x (B 2) r lo hi)).toReal / (hi-lo) ≤
                  nativeVacuumCircleCost a p + C*(r/(hi-lo)) + ξ)
    {r₀ : ℝ} (hr₀ : r₀ ∈ Ioo 0 R) (b : C(NativeCircle, vacuum a))
    (hb : ∀ z, (b z).val = Q₀ (x + r₀ • axisChartPlane B z.val))
    (hbSafe : ∀ z : NativeCircle, x + r₀ • axisChartPlane B z.val ∉ Spt) :
    nativeVacuumCircleCost a b = θ := by
  let R' := R / 2
  let s := R / 8
  have hR' : 0 < R' := half_pos hR
  have hs : 0 < s := div_pos hR (by norm_num)
  have h2s : 2*s < R := by dsimp only [s]; linarith only [hR]
  have h2sR' : 2*s ≤ R' := by dsimp only [R',s]; linarith only [hR]
  have hR'R : R' < R := half_lt_self hR
  have hO : closedBall x R' ⊆ Ω := (closedBall_subset_ball hR'R).trans hΩR
  have hO' : closedBall x (2*s) ⊆ Ω := (closedBall_subset_closedBall h2sR').trans hO
  let cap := 16*M/R'
  have hcap : 0 ≤ cap := div_nonneg (mul_nonneg (by norm_num) hM) hR'.le
  obtain ⟨C,hC,hUC⟩ := hUpper cap hcap
  have hE : ‖B 2‖ = 1 := B.orthonormal.norm_eq_one 2
  symm
  apply edge_weight_eq_meridian_cost_of_comparisons hWeak x (B 2) hE hs hθ hC hLocal
  intro ρ hρ
  have hP := locallyFiniteIn_countable (hΩ.sdiff hS) hSpt hLoc
  obtain ⟨r,hr,T,hT,hTR,hSide⟩ := exists_radius_and_compact_edgeSide hP B x hs h2s hΩR hGerm ρ hρ
  have hrs := hr.2.trans_le (min_le_right ρ s)
  have hrR : r < R := hrs.trans (by linarith only [h2s,hs])
  have hCylR : translatedClosedAxisCylinder x (B 2) r (-(2*s)) (2*s) ⊆ ball x R := by
    intro y hy
    change y-x ∈ closedAxisCylinder (B 2) r (-(2*s)) (2*s) at hy
    have hBound := closedAxisCylinder_subset_closedBall hE r (-(2*s)) (2*s) hy
    rw [mem_closedBall, dist_zero_right, abs_neg, abs_of_nonneg (mul_nonneg (by norm_num) hs.le)] at hBound
    rw [mem_ball, dist_eq_norm]
    dsimp only [s] at hrs hBound
    linarith only [hrs,hBound,hR]
  refine ⟨r,⟨hr.1,hr.2.trans_le (min_le_left ρ s)⟩,hCylR,?_⟩
  have hTΩ := hTR.trans (sdiff_subset.trans sdiff_subset)
  have hCyl := (closedCylinder_centered_height_subset_ball B x hs hrs).trans (ball_subset_closedBall.trans hO')
  obtain ⟨D,hD⟩ := hDensity T hT hTR
  obtain ⟨p,hp,hLower⟩ := exists_eventually_normalizedCylinder_lower_of_regularSide hcoarea hAngular
    a hM B x hΩ hT hTΩ hr.1 (by linarith only [hs]) hCyl hSide (hQ₀.mono hTR)
    (hVac.mono_left hTR) hQ (hConv T hT hTR) ε hε hBound hD (fun n => ν n) hν
  have hp' (w : NativeCircle) : (p w).val = Q₀ (x + axisChart B (r • w.val,0)) := by
    simpa only [neg_add_cancel,zero_div] using hp w
  have hAxis (w : NativeCircle) : x + axisChart B (r • w.val,0) =
      x + r • axisChartPlane B w.val := by
    rw [← axisChartPlane_apply, map_smul]
  have hPSafe (w : NativeCircle) : x + r • axisChartPlane B w.val ∉ Spt := by
    rw [← hAxis]
    exact (hTR (hSide 0 ⟨by linarith only [hs],hs.le⟩ w)).2
  have hSame := nativeVacuumCircleCost_homotopic a (orthogonal_meridians_homotopic_of_local_axis
    hAvoid a hΩ hS hLoc hQ₀ hVac B x hΩR hGerm hr₀ ⟨hr.1,hrR⟩
    (fun w => ⟨hbSafe w,hPSafe w⟩) b p hb (fun w => (hp' w).trans (congrArg Q₀ (hAxis w))))
  intro ξ hξ
  filter_upwards [hLower ξ hξ, hUC hr.1 hs hrs hO' T hT hTR hSide p hp' ξ hξ,
    eventual_log_scale_ge_one hε] with n hL hU hLog
  obtain ⟨lo,hlo,hi,hhi,hCap⟩ := good_classical_endHeights_of_logarithmic_ball_bound
    a (ε n) B x hΩ (hQ n) (hEuler n) hM hs hrs h2sR' hO hLog (hEnergy n)
  have hH : s ≤ hi-lo := by linarith only [hlo.2,hhi.1]
  have hLH : lo < hi := by linarith only [hs,hH]
  have hErr : C*(r/(hi-lo)) ≤ C*(r/s) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hr.1.le hs hH) hC
  rw [hSame]
  refine ⟨lo,hlo,hi,hhi,hL lo hi hlo.1.le hLH hhi.2.le,?_⟩
  linarith only [hU lo hlo hi hhi hCap,hErr]

/-- On the actual finite segment network, the splitting cost of every
admissible transverse meridian is the original edge weight. -/
theorem meridian_boundary_cost_eq_edge_weight_of_regularCylinder_upper
    (hAvoid : External.RelativeAnnulusPointAvoidance)
    (hcoarea : External.PlanarScalarCoarea) (hAngular : External.PeriodicAngularSobolev)
    (a : BulkCoefficients) {Ω Spt : Set Point} (hΩ : IsOpen Ω)
    {μ : Measure Point} [IsFiniteMeasure μ] [μ.OuterRegular]
    (hμ : μ (closure Ω)ᶜ = 0)
    (hLoc : LocallyFiniteIn (Ω \ μ.support) Spt) (hSpt : Spt ⊆ Ω \ μ.support)
    {M : ℝ} (hM : 0 ≤ M) (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (Q₀ : Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω)
    (hEuler : ∀ n x, x ∈ Ω → (ε n : ℝ)^2 • (laplacian (Q n) x : S0).val = bulkGradient a (Q n x))
    (hBound : ∀ n x, x ∈ Ω → ‖Q n x‖ ≤ M)
    (hEnergy : ∀ n, energy a (ε n) Ω (Q n) (ClassicalGradient (Q n)) ≤
      ENNReal.ofReal (M * (Real.log (1 / (ε n : ℝ)) + 1)))
    (hQ₀ : ContinuousOn Q₀ ((Ω \ μ.support) \ Spt))
    (hVac : MapsTo Q₀ ((Ω \ μ.support) \ Spt) (vacuum a))
    (hDensity : ∀ T : Set Point, IsCompact T → T ⊆ (Ω \ μ.support) \ Spt → ∃ D > (0 : ℝ),
      ∀ n x, x ∈ T → energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ D)
    (hConv : ∀ T : Set Point, IsCompact T → T ⊆ (Ω \ μ.support) \ Spt →
      TendstoUniformlyOn Q Q₀ atTop T)
    (ν : ℕ → Measure Point) (hνfin : ∀ n, IsFiniteMeasure (ν n))
    (hν : ∀ n, ν n = normalizedEnergyMeasure a (ε n) Ω (Q n) (ClassicalGradient (Q n)))
    (hWeak : WeakStarOnClosure Ω ν μ)
    (hUpper : ∀ cap : ℝ, 0 ≤ cap → ∃ C ≥ (0 : ℝ),
      ∀ (B : OrthonormalBasis (Fin 3) ℝ Point) (x : Point) {r s : ℝ}, 0 < r → 0 < s → r < s →
        closedBall x (2*s) ⊆ Ω →
        ∀ T : Set Point, IsCompact T → T ⊆ (Ω \ μ.support) \ Spt →
          (∀ z ∈ Icc (-s) s, ∀ w : NativeCircle, x + axisChart B (r • w.val,z) ∈ T) →
          ∀ p : C(NativeCircle, vacuum a),
            (∀ w, (p w).val = Q₀ (x + axisChart B (r • w.val,0))) →
            ∀ ξ > 0, ∀ᶠ n : ℕ in atTop,
              ∀ lo ∈ Ioo (-s) (-(s/2)), ∀ hi ∈ Ioo (s/2) s,
                planarSmoothEnergy a (ε n) (cylinderSliceMap B x (Q n) lo) r +
                  planarSmoothEnergy a (ε n) (cylinderSliceMap B x (Q n) hi) r ≤
                    cap * Real.log (1 / (ε n : ℝ)) →
                (ν n (translatedAxisCylinder x (B 2) r lo hi)).toReal / (hi-lo) ≤
                  nativeVacuumCircleCost a p + C*(r/(hi-lo)) + ξ)
    {K U : Set Point} (hK : IsOpen K) (hKU : K ⊆ U) (hKΩ : K ⊆ Ω)
    {m : ℕ} {p q : Fin m → Point} {θ : Fin m → ℝ}
    (hn : ∀ i, p i ≠ q i) (hθ : ∀ i, 0 ≤ θ i)
    (hRep : μ.support ∩ closure U = ⋃ i, segment ℝ (p i) (q i))
    (hMeet : ∀ i j : Fin m, i ≠ j → ∀ z ∈ segment ℝ (p i) (q i) ∩ segment ℝ (p j) (q j),
      (z = p i ∨ z = q i) ∧ (z = p j ∨ z = q j))
    (hMass : μ.restrict (closure K) = ∑ j, ENNReal.ofReal (θ j) •
      HausdorffOne.restrict (segment ℝ (p j) (q j) ∩ closure K))
    (i : Fin m) (d : Plane → Point) (hd : IsSmoothDiskEmbedding d) (hDK : d '' Disk ⊆ K)
    (y : Plane) (hy : y ∈ ball (0 : Plane) 1) (hDmeet : d '' Disk ∩ μ.support = {d y})
    (hySeg : d y ∈ openSegment ℝ (p i) (q i))
    (hTrans : q i - p i ∉ LinearMap.range (fderiv ℝ d y).toLinearMap)
    (hDSafe : Disjoint (d '' sphere (0 : Plane) 1) Spt)
    (b : C(NativeCircle, vacuum a)) (hb : ∀ z, (b z).val = Q₀ (d z.val)) :
    θ i = nativeVacuumCircleCost a b := by
  let x := d y
  have hxK : x ∈ K := hDK ⟨y,ball_subset_closedBall hy,rfl⟩
  obtain ⟨R,hR,hRK,hGerm,hLocal⟩ :=
    exists_ball_localWeightedAxis_of_segmentNetwork hK hKU hRep hn hMeet hMass i hxK hySeg
  let e := segmentDirection (p i) (q i)
  have he : ‖e‖ = 1 := norm_segmentDirection (hn i)
  obtain ⟨B,hB⟩ := exists_axis_orthonormalBasis he
  have hGermB (z : Point) (hz : z ∈ ball x R) :
     z ∈ μ.support ↔ axisChartTransverseCoordinates B (z-x) = 0 := by
    rw [hGerm z hz, axisChartTransverseCoordinates_eq_zero_iff, hB]
    constructor
    · rintro ⟨t,ht,rfl⟩
      rwa [add_sub_cancel_left]
    · intro h
      exact ⟨z-x,h,by abel⟩
  have hTransB : B 2 ∉ LinearMap.range (fderiv ℝ d y).toLinearMap := by
    intro h
    have hL : 0 < ‖q i - p i‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hn i).symm)
    have hh := (LinearMap.range (fderiv ℝ d y).toLinearMap).smul_mem ‖q i-p i‖ h
    have hEq : ‖q i - p i‖ • B 2 = q i-p i := by
      rw [hB]
      change ‖q i-p i‖ • (‖q i-p i‖⁻¹ • (q i-p i)) = _
      rw [smul_smul,mul_inv_cancel₀ hL.ne',one_smul]
    exact hTrans (hEq ▸ hh)
  have hBΩ : ball x R ⊆ Ω := hRK.trans hKΩ
  obtain ⟨r,hr,b',hb',hSafe,_,hCost⟩ := transverse_disk_meridian_cost_eq_arbitrarily_small_orthogonal
    hAvoid a hΩ μ.isClosed_support hLoc hSpt hQ₀ hVac B hd (hDK.trans hKΩ) hy hDmeet
    hTransB hDSafe hR hBΩ hGermB b hb R hR
  let ν' (n : ℕ) : FiniteMeasure Point := ⟨ν n,hνfin n⟩
  let μ' : FiniteMeasure Point := ⟨μ,inferInstance⟩
  have hνS (n : ℕ) : (ν' n : Measure Point) (closure Ω)ᶜ = 0 := by
    change ν n (closure Ω)ᶜ = 0
    rw [hν n]
    exact normalizedEnergyMeasure_compl_closure a (ε n) Ω (Q n) (ClassicalGradient (Q n))
  have hW : Tendsto ν' atTop (𝓝 μ') := finiteMeasure_tendsto_of_weakStarOnClosure hνS hμ hWeak
  have hLocalB : (μ' : Measure Point).restrict (ball x R) = (ENNReal.ofReal (θ i) • HausdorffOne.restrict
      ((fun z : Point => x+z) '' ((Submodule.span ℝ {B 2} : Submodule ℝ Point) : Set Point))).restrict
        (ball x R) := by
    rw [hB]
    exact hLocal
  have hD (T : Set Point) (hT : IsCompact T) (hTR : T ⊆ (Ω \ μ.support) \ Spt) :
      ∃ D : ℝ, ∀ n x, x ∈ T → energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ D := by
    obtain ⟨D,_,hD⟩ := hDensity T hT hTR
    exact ⟨D,hD⟩
  have h := orthogonal_meridian_cost_eq_local_weight_of_upper hAvoid hcoarea hAngular a hΩ
    μ.isClosed_support hLoc hSpt hM ε Q Q₀ hε hQ hEuler hBound hEnergy hQ₀ hVac hD hConv ν' μ'
    hW hν B x hR (hθ i) hBΩ hGermB hLocalB
    (fun cap hCap => by
      obtain ⟨C,hC,hCmp⟩ := hUpper cap hCap
      exact ⟨C,hC,fun hr' hs' => hCmp B x hr' hs'⟩)
    hr b' hb' hSafe
  exact h.symm.trans hCost.symm

end Thesis.MeasureGeometry

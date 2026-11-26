module

public import Thesis.Interpolation.CylinderCentralRecovery
public import Thesis.Interpolation.PlanarPairReference
import Thesis.Variational.InteriorBulkSmall
import Thesis.Variational.BoundaryPoissonEstimate
import Thesis.Interpolation.SmoothRadialSphereGradient
import HolderToCK.Analysis.ClassicalEquation

/-! A fixed regular lateral band supplies the middle comparison for all selected end heights. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

local instance recoveryBandNorm : Norm (Point →L[ℝ] S0) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ) (E := Point) (F := S0)

/-- The closed collar used for the side and the two inner cap rims. -/
def cylinderRecoveryBand (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (r s : ℝ) : Set Point :=
  {x | r / 4 ≤ ‖(axisCoordinates B c x).1‖ ∧ ‖(axisCoordinates B c x).1‖ ≤ r ∧
    (axisCoordinates B c x).2 ∈ Icc (-s) s}

theorem isCompact_cylinderRecoveryBand (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (r s : ℝ) : IsCompact (cylinderRecoveryBand B c r s) := by
  let A := closedBall (0 : Plane) r \ ball (0 : Plane) (r / 4)
  have hA : IsCompact A := (isCompact_closedBall _ _).diff isOpen_ball
  have hEq : cylinderRecoveryBand B c r s = (fun p : Plane × ℝ => c + axisChart B p) '' (A ×ˢ Icc (-s) s) := by
    ext x
    constructor
    · intro hx
      exact ⟨axisCoordinates B c x, ⟨⟨mem_closedBall_zero_iff.2 hx.2.1,
        fun h => hx.1.not_gt (mem_ball_zero_iff.1 h)⟩, hx.2.2⟩, axisChart_axisCoordinates B c x⟩
    · rintro ⟨p, hp, rfl⟩
      change r / 4 ≤ ‖(axisCoordinates B c (c + axisChart B p)).1‖ ∧ _
      rcases p with ⟨y, z⟩
      rw [axisCoordinates_axisChart]
      exact ⟨le_of_not_gt (fun h => hp.1.2 (mem_ball_zero_iff.2 h)),
        mem_closedBall_zero_iff.1 hp.1.1, hp.2⟩
  rw [hEq]
  exact (hA.prod isCompact_Icc).image (continuous_const.add (continuous_axisChart B))

theorem axisChart_mem_cylinderRecoveryBand (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) {r s : ℝ} {y : Plane} {z : ℝ} (h₁ : r / 4 ≤ ‖y‖)
    (h₂ : ‖y‖ ≤ r) (hz : z ∈ Icc (-s) s) :
    c + axisChart B (y, z) ∈ cylinderRecoveryBand B c r s := by
  unfold cylinderRecoveryBand
  rw [mem_setOf_eq, axisCoordinates_axisChart]
  exact ⟨h₁, h₂, hz⟩

theorem cylinderMiddleSideDomain_subset_recoveryBand (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) {r s lo hi : ℝ} (hr : 0 < r) (hlo : -s ≤ lo) (hhi : hi ≤ s) :
    (cylinderMiddleSideDomain B c r lo hi).val ⊆ cylinderRecoveryBand B c r s := by
  intro x hx
  have hAxis := (mem_translatedAxisCylinder_iff_coordinates B c x r lo hi).1 hx.1
  have hρ : (7 / 16 : ℝ) * r < ‖(axisCoordinates B c x).1‖ := hx.2
  exact ⟨(show r / 4 ≤ (7 / 16 : ℝ) * r by linarith only [hr]).trans hρ.le,
    hAxis.1.le, hlo.trans hAxis.2.1.le, hAxis.2.2.le.trans hhi⟩

theorem fderiv_norm_le_sqrt_gradient (q : Point → S0) (x : Point) :
    ‖fderiv ℝ q x‖ ≤ Real.sqrt (gradientNormSq (ClassicalGradient q x)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro z
  calc
    _ = ‖gradientFromColumns (ClassicalGradient q x) z‖ :=
      congrArg (fun w : S0 => ‖w‖) (gradientFromColumns_classicalGradient q x z).symm
    _ ≤ _ := (norm_gradientFromColumns_le _ _).trans_eq (mul_comm _ _)

theorem exists_cylinderRecoverySide_of_regular_band (a : BulkCoefficients)
    {U K : Set Point} (hU : IsOpen U) (hKU : K ⊆ U)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {r s M D : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hD : 0 ≤ D)
    (hLat : ∀ z ∈ Icc (-s) s, ∀ θ : NativeCircle, c + axisChart B (r • θ.val, z) ∈ K)
    (ε : ℕ → ElasticScale) {q : Point → S0} {Q : ℕ → Point → S0}
    (hq : ContDiffOn ℝ ∞ q U) (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) U)
    (hVac : MapsTo q K (vacuum a)) (hConv : TendstoUniformlyOn Q q atTop K)
    (hRange : ∀ n x, x ∈ K → ‖Q n x‖ ≤ M)
    (hDensity : ∀ n x, x ∈ K → energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ D)
    (p : C(NativeCircle, vacuum a)) (hp : ∀ θ, (p θ).val = q (c + axisChart B (r • θ.val, 0))) :
    let Cₛ := cylinderRecoveryBand B c r s
    ∃ C ≥ (0 : ℝ), ∃ V : Set Point, IsOpen V ∧ Cₛ ⊆ V ∧
      ∀ᶠ n : ℕ in atTop,
        let w := cylinderSideRecovery a B c r 0 q (Q n)
        ContDiffOn ℝ ∞ w V ∧ ∀ x ∈ Cₛ,
          ‖w x‖ ≤ max M (Real.sqrt 2 * vacuumRadius a) ∧
          energyDensity a (ε n) (w x) (ClassicalGradient w x) ≤ C ∧
          (‖(axisCoordinates B c x).1‖ ≤ (5 / 8 : ℝ) * r →
            w x = (p (sphereRadialDirection nativeCircleLoopBase (axisCoordinates B c x).1)).val) ∧
          (‖(axisCoordinates B c x).1‖ = r → w x = Q n x) := by
  obtain ⟨δ, hδ, hRec⟩ := exists_uniform_cylinderSideRecovery_on_band a
  let P := vacuumTubularProjection a
  let η := min δ (P.radius / 3)
  have hη : 0 < η := lt_min hδ (div_pos P.radius_pos (by norm_num))
  have hClose := (Metric.tendstoUniformlyOn_iff.mp hConv) η hη
  let I := {n : ℕ // ∀ x ∈ K, dist (q x) (Q n x) < η}
  let Q' (n : I) := Q n.val
  let ε' (n : I) := ε n.val
  let A := cylinderRecoveryBand B c r s
  have hAxis : ∀ x ∈ A, (axisCoordinates B c x).1 ≠ 0 := fun x hx =>
    norm_pos_iff.1 ((by positivity : 0 < r / 4).trans_le hx.1)
  have hz₀ : (0 : ℝ) ∈ Icc (-s) s := ⟨by linarith only [hs], hs.le⟩
  have hData (n : I) (θ : NativeCircle) (z : ℝ) (hz : z ∈ Icc (-s) s) :
      let y := c + axisChart B (r • θ.val, z)
      (Q' n y ∈ vacuumTube a δ ∧ ‖Q' n y‖ ≤ M ∧ dist (P.extend (Q' n y)) (q y) < P.radius) ∧
        ‖fderiv ℝ (Q' n) y‖ ≤ Real.sqrt (2 * D) ∧
        (ε' n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q' n y) ≤ D := by
    let y := c + axisChart B (r • θ.val, z)
    have hy := hLat z hz θ
    have hqV := hVac hy
    have hNear : dist (Q' n y) (q y) < η := by rw [dist_comm]; exact n.property y hy
    have hInf := infDist_le_dist_of_mem (x := Q' n y) hqV
    have hP : Q' n y ∈ vacuumTube a P.radius :=
      hInf.trans_lt (hNear.trans_le ((min_le_right _ _).trans (by linarith only [P.radius_pos])))
    have hProj : dist (P.extend (Q' n y)) (q y) < P.radius := by
      rw [P.extend_eq ⟨Q' n y, hP⟩]
      have hT := dist_triangle (P.project ⟨Q' n y, hP⟩).val (Q' n y) (q y)
      rw [dist_comm _ (Q' n y)] at hT
      have hN := P.nearest ⟨Q' n y, hP⟩ ⟨q y, hqV⟩
      change dist (Q' n y) (P.project ⟨Q' n y, hP⟩).val ≤ dist (Q' n y) (q y) at hN
      have hηP : η ≤ P.radius / 3 := min_le_right _ _
      linarith only [hT, hN, hNear, hηP, P.radius_pos]
    have hDE := hDensity n.val y hy
    have hE₀ : 0 ≤ gradientNormSq (ClassicalGradient (Q' n) y) := by
      rw [gradientNormSq_eq_sum_norm_sq]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hF₀ : 0 ≤ (ε' n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q' n y) :=
      mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _)
    change (1 / 2 : ℝ) * gradientNormSq (ClassicalGradient (Q' n) y) +
      (ε' n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q' n y) ≤ D at hDE
    exact ⟨⟨hInf.trans_lt (hNear.trans_le (min_le_left _ _)), hRange n.val y hy, hProj⟩,
      (fderiv_norm_le_sqrt_gradient (Q' n) y).trans (Real.sqrt_le_sqrt (by linarith only [hDE, hF₀])),
      by linarith only [hDE, hE₀]⟩
  obtain ⟨V, C, hV, hAV, hC, hw, hW⟩ := hRec ε' B c hr hz₀ hU
    (isCompact_cylinderRecoveryBand B c r s) hq (fun n => hQ n.val) hAxis
    (fun x hx => hx.2.2) (fun θ z hz => ⟨hKU (hLat z hz θ), hVac (hLat z hz θ)⟩)
    (Real.sqrt_nonneg _) hD hData
  refine ⟨C, hC, V, hV, hAV, ?_⟩
  filter_upwards [hClose] with n hn
  let n' : I := ⟨n, hn⟩
  refine ⟨hw n', fun x hx => ?_⟩
  obtain ⟨hNorm, _, hE, hInner, hOut⟩ := hW n' x hx
  refine ⟨hNorm, hE, ?_, hOut⟩
  intro hρ
  rw [hInner hρ, hp]
  simp only [cylinderSidePoint, sphereRadialDirection, dif_pos (hAxis x hx)]

theorem memSphereW12_of_regular_cylinder_circle (a : BulkCoefficients)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (r z : ℝ) {U : Set Point}
    {q : Point → S0} (hq : ContDiffOn ℝ ∞ q U)
    (hSide : ∀ θ : NativeCircle, c + axisChart B (r • θ.val, z) ∈ U)
    (p : C(NativeCircle, vacuum a)) (hp : ∀ θ, (p θ).val = q (c + axisChart B (r • θ.val, z))) :
    MemSphereW12 (le_refl 2) (fun θ => frobeniusCoordinateEquiv (p θ).val) := by
  let G (y : Plane) : Point := c + axisChart B (r • NormedSpace.normalize y, z)
  let F := frobeniusCoordinateEquiv ∘ q ∘ G
  have hG : ContDiffOn ℝ ∞ G ({0}ᶜ : Set Plane) := by
    intro y hy
    have h0 : y ≠ 0 := hy
    have hN := (contDiffAt_norm ℝ (n := ∞) h0).inv (norm_ne_zero_iff.2 h0)
    have hn : ContDiffAt ℝ ∞ (fun y : Plane => r • NormedSpace.normalize y) y :=
      (hN.smul contDiffAt_id).const_smul r
    exact (contDiff_const.contDiffAt.add ((contDiff_axisChart B).contDiffAt.comp y
      (hn.prodMk contDiffAt_const))).contDiffWithinAt
  have hGU : MapsTo G ({0}ᶜ : Set Plane) U := by
    intro y hy
    let θ : NativeCircle := ⟨NormedSpace.normalize y, mem_sphere_zero_iff_norm.2
      (NormedSpace.norm_normalize (show y ≠ 0 from hy))⟩
    exact hSide θ
  have hF : ContDiffOn ℝ ∞ F ({0}ᶜ : Set Plane) :=
    frobeniusCoordinateEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn (hq.comp hG hGU)
  have hRay (ρ : ℝ) (hρ : 0 < ρ) (y : Plane) : F (ρ • y) = F y := by
    simp only [F, Function.comp_apply, G, NormedSpace.normalize_smul_of_pos hρ]
  obtain ⟨hMem, _⟩ := exists_memSphereW12_of_smooth_degreeZero (le_refl 2) hF hRay
  have he : (fun θ : NativeCircle => F θ.val) = fun θ => frobeniusCoordinateEquiv (p θ).val := by
    funext θ
    simp only [F, Function.comp_apply, G,
      NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.1 θ.property), hp]
  exact he ▸ hMem

end Thesis.MeasureGeometry

module

public import Thesis.Variational.BoundaryDefect
public import Thesis.Variational.SmoothWallGeometry
import Mathlib.Analysis.Calculus.DerivativeTest

/-! A classical comparison barrier in the actual physical boundary charts. -/

public section

open Filter Set Topology
open scoped BigOperators ContDiff Matrix.Norms.Frobenius RealInnerProductSpace

set_option autoImplicit false
noncomputable section

namespace Thesis

theorem laplacian_nonpos_of_isLocalMax
    {U : Set Point} (hU : IsOpen U) {f : Point → ℝ} {x : Point}
    (hf : ContDiffOn ℝ 2 f U) (hx : x ∈ U) (hMax : IsLocalMax f x) :
    laplacian f x ≤ 0 := by
  unfold laplacian
  apply Finset.sum_nonpos
  intro j _
  let γ (t : ℝ) := x + t • axis j
  let g := f ∘ γ
  have hγ0 : γ 0 = x := by simp only [γ, zero_smul, add_zero]
  have hγ (t : ℝ) : HasDerivAt γ (axis j) t := by
    simpa only [γ, id_eq, one_smul] using ((hasDerivAt_id t).smul_const (axis j)).const_add x
  have hT : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 x) := by
    rw [← hγ0]
    exact (hγ 0).continuousAt.tendsto
  have hLoc : IsLocalMax g 0 := by
    have hMax' : ∀ᶠ y in 𝓝 x, f y ≤ f x := hMax
    filter_upwards [hT hMax'] with t ht
    change f (γ t) ≤ f x at ht
    simpa only [g, Function.comp_apply, hγ0] using ht
  have hFirst : deriv g =ᶠ[𝓝 (0 : ℝ)] (fun t => coordDeriv j f (γ t)) := by
    filter_upwards [hT (hU.mem_nhds hx)] with t ht
    have hF := ((hf (γ t) ht).contDiffAt (hU.mem_nhds ht)).differentiableAt two_ne_zero
    exact (hF.hasFDerivAt.comp_hasDerivAt t (hγ t)).deriv
  have hSecond : deriv (deriv g) 0 = coordDeriv j (coordDeriv j f) x := by
    have hC := differentiableAt_coordDeriv_of_contDiffAt ((hf x hx).contDiffAt (hU.mem_nhds hx)) j
    have hC' : HasFDerivAt (coordDeriv j f) (fderiv ℝ (coordDeriv j f) x) (γ 0) := hγ0.symm ▸ hC.hasFDerivAt
    exact hFirst.deriv_eq.trans (hC'.comp_hasDerivAt 0 (hγ 0)).deriv
  by_contra h
  have hPos := lt_of_not_ge h
  have hfc : ContinuousAt f (γ 0) := by
    rw [hγ0]
    exact ((hf x hx).contDiffAt (hU.mem_nhds hx)).continuousAt
  have hMin := isLocalMin_of_deriv_deriv_pos (hSecond.symm ▸ hPos) hLoc.deriv_eq_zero
    (hfc.comp (hγ 0).continuousAt)
  have hEq : g =ᶠ[𝓝 (0 : ℝ)] (fun _ => g 0) := by
    filter_upwards [hLoc, hMin] with t ht₁ ht₂
    exact le_antisymm ht₁ ht₂
  have hD : deriv g =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [eventually_eventually_nhds.mpr hEq] with t ht
    exact (Filter.EventuallyEq.deriv_eq ht).trans (deriv_const _ _)
  have hz := hD.deriv_eq.trans (deriv_const _ _)
  exact hPos.ne' (hSecond.symm.trans hz)

/-- The classical Laplacian of squared distance in the three source
coordinates is six everywhere. -/
theorem laplacian_norm_sub_sq (c x : Point) :
    laplacian (fun y : Point => ‖y - c‖ ^ 2) x = 6 := by
  have hD (j : Fin 3) :
      coordDeriv j (fun y : Point => ‖y - c‖ ^ 2) =
        (fun y : Point => (2 : ℝ) * inner ℝ (axis j) (y - c)) := by
    funext y
    have h := ((hasFDerivAt_id y).sub_const c).norm_sq
    have hEval := DFunLike.congr_fun h.fderiv (axis j)
    simpa only [id_eq, coordDeriv, ContinuousLinearMap.comp_id, two_nsmul, add_apply, innerSL_apply_apply,
      real_inner_comm (axis j) (y - c), two_mul] using hEval
  have hD' (j : Fin 3) : coordDeriv j (fun y : Point => (2 : ℝ) * inner ℝ (axis j) (y - c)) x = 2 := by
    let L := innerSL ℝ (axis j)
    have h := (((L.hasFDerivAt (x := x)).sub_const (L c)).const_mul (2 : ℝ)).fderiv
    have hEq : (fun y : Point => (2 : ℝ) * (L y - L c)) =
        (fun y : Point => (2 : ℝ) * inner ℝ (axis j) (y - c)) := by
      funext y
      rw [← map_sub]
      rfl
    rw [hEq] at h
    have hEval := DFunLike.congr_fun h (axis j)
    have hNorm : ‖axis j‖ = 1 := by simp [axis]
    simpa only [coordDeriv, smul_apply, smul_eq_mul, L, innerSL_apply_apply, real_inner_self_eq_norm_sq,
      hNorm, one_pow, mul_one] using hEval
  rw [laplacian]
  simp only [hD, hD', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

private theorem coordDeriv_const_real (i : Fin 3) (c : ℝ) (x : Point) :
    coordDeriv i (fun _ : Point => c) x = 0 :=
  DFunLike.congr_fun (hasFDerivAt_const c x).fderiv (axis i)

/-- Classical comparison on a bounded cap follows by adding a strict
quadratic perturbation and applying the Laplacian test at a maximum. -/
theorem nonpos_of_laplacian_nonneg_on_ball_subset
    {U : Set Point} (hU : IsOpen U) {c : Point} {r : ℝ} (hSub : U ⊆ Metric.ball c r)
    {f : Point → ℝ} (hClosed : ContinuousOn f (closure U))
    (hDiff : ContDiffOn ℝ 2 f U) (hLap : ∀ y ∈ U, 0 ≤ laplacian f y)
    (hFront : ∀ y ∈ frontier U, f y ≤ 0) :
    ∀ y ∈ closure U, f y ≤ 0 := by
  intro y hy
  by_contra hNot
  have hPos := lt_of_not_ge hNot
  have hCl : closure U ⊆ Metric.closedBall c r :=
    closure_minimal (hSub.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall
  have hK : IsCompact (closure U) :=
    (isCompact_closedBall c r).of_isClosed_subset isClosed_closure hCl
  let η := f y / (2 * (r ^ 2 + 1))
  have hη : 0 < η := div_pos hPos (by positivity)
  let p (z : Point) := (r ^ 2 : ℝ) - ‖z - c‖ ^ 2
  let g (z : Point) := f z - η • p z
  have hNorm (z : Point) (hz : z ∈ closure U) : ‖z - c‖ ^ 2 ≤ r ^ 2 := by
    have hDist : ‖z - c‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hCl hz
    exact pow_le_pow_left₀ (norm_nonneg _) hDist 2
  have hp : ContDiff ℝ 2 p := contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)
  have hg : ContinuousOn g (closure U) := hClosed.sub (hp.continuous.continuousOn.const_smul η)
  have hgDiff : ContDiffOn ℝ 2 g U := hDiff.sub (hp.contDiffOn.const_smul η)
  have hgy : 0 < g y := by
    have hA : η * r ^ 2 ≤ f y / 2 := by
      dsimp only [η]
      have hDen : 0 < 2 * (r ^ 2 + 1) := by positivity
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hDen).mpr
      nlinarith only [hPos]
    have hB := mul_le_mul_of_nonneg_left (sub_le_self (r ^ 2) (sq_nonneg ‖y - c‖)) hη.le
    change 0 < f y - η * (r ^ 2 - ‖y - c‖ ^ 2)
    linarith only [hPos, hA, hB]
  obtain ⟨z, hz, hMax⟩ := hK.exists_isMaxOn ⟨y, hy⟩ hg
  have hgz : 0 < g z := hgy.trans_le (hMax hy)
  have hzU : z ∈ U := by
    by_contra hn
    have hzF : z ∈ frontier U := by rw [frontier, hU.interior_eq]; exact ⟨hz, hn⟩
    have hpz : 0 ≤ p z := sub_nonneg.mpr (hNorm z hz)
    exact (not_lt_of_ge (sub_nonpos_of_le (le_trans (hFront z hzF) (mul_nonneg hη.le hpz)))) hgz
  have hLocal : IsLocalMax g z := by
    filter_upwards [hU.mem_nhds hzU] with t ht
    exact hMax (subset_closure ht)
  have hLP : laplacian p z = -6 := by
    have hF : ContDiffOn ℝ 2 (fun y : Point => ‖y - c‖ ^ 2) U :=
      ((contDiff_id.sub contDiff_const).norm_sq ℝ).contDiffOn
    change laplacian (fun y : Point => (r ^ 2 : ℝ) - ‖y - c‖ ^ 2) z = _
    rw [laplacian_sub_of_contDiffOn hU contDiffOn_const hF hzU, laplacian_norm_sub_sq]
    have hC (i : Fin 3) : coordDeriv i (fun _ : Point => (r ^ 2 : ℝ)) = fun _ => 0 :=
      funext fun y => coordDeriv_const_real i (r ^ 2) y
    simp only [laplacian, hC, coordDeriv_const_real, Finset.sum_const_zero, zero_sub]
  have hLG : laplacian g z = laplacian f z + 6 * η := by
    change laplacian (fun y => f y - η • p y) z = _
    rw [laplacian_sub_of_contDiffOn hU hDiff (hp.contDiffOn.const_smul η) hzU,
      laplacian_const_smul hU hp.contDiffOn hzU, hLP]
    change laplacian f z - η * (-6) = _
    ring
  have hNeg := laplacian_nonpos_of_isLocalMax hU hgDiff hzU hLocal
  linarith only [hLG, hNeg, hLap z hzU, hη]

private theorem continuous_laplacian_of_smooth {f : Point → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) f) : Continuous (laplacian f) := by
  have hCoord {g : Point → ℝ} (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) g) (j : Fin 3) :
      ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (coordDeriv j g) :=
    (ContinuousLinearMap.apply ℝ ℝ (axis j)).contDiff.comp (hg.fderiv_right (by simp))
  unfold laplacian
  exact continuous_finsetSum Finset.univ fun j _ => (hCoord (hCoord hf j) j).continuous

private theorem one_le_gradient_sq_of_unit_direction
    {f : Point → ℝ} {y w : Point} (hw : ‖w‖ = 1) (hD : fderiv ℝ f y w = 1) :
    1 ≤ ∑ j, (coordDeriv j f y) ^ 2 := by
  let L := fderiv ℝ f y
  have hVec : (∑ j : Fin 3, w j • axis j) = w := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, axis] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
  have hLin : (∑ j : Fin 3, w j * coordDeriv j f y) = 1 := by
    have hEq := congrArg L hVec
    dsimp only at hEq
    rw [map_sum] at hEq
    simpa only [map_smul, smul_eq_mul, L, hD, coordDeriv] using hEq
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : Fin 3 => w j)
    (fun j => coordDeriv j f y)
  simpa only [hLin, ← EuclideanSpace.real_norm_sq_eq w, hw, one_pow, one_mul] using hCS

/-- Compactness of the physical wall gives one radius and one derivative
bound for the signed local barrier functions at all wall centers. -/
theorem IsSmoothDomain.exists_uniform_wall_barrier_charts
    {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ R L M : ℝ, 0 < R ∧ 0 ≤ L ∧ 0 ≤ M ∧
      ∀ a ∈ frontier U, ∀ r ∈ Ioo 0 R, ∃ b : Point → ℝ,
        ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) b ∧ b a = 0 ∧
        (∀ y ∈ frontier U ∩ Metric.closedBall a r, b y = 0) ∧
        (∀ y ∈ closure U ∩ Metric.closedBall a r, 0 ≤ b y ∧ b y ≤ L * r) ∧
        ∀ y ∈ Metric.closedBall a r, ‖fderiv ℝ b y‖ ≤ L ∧
          |laplacian b y| ≤ M ∧ 1 ≤ ∑ j, (coordDeriv j b y) ^ 2 := by
  classical
  let K := frontier U
  have hK : IsCompact K := hU.1.2.2.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hLocal (a : K) := exists_local_smooth_defining_function_and_unit_direction hU a.property
  choose ρ φ _ _ w hρ hφ _ hDef hw hDir _ _ _ using hLocal
  let b (a : K) (y : Point) := -φ a y
  have hb (a : K) : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (b a) := (hφ a).neg
  have hLocalL (a : K) := (isCompact_closedBall (a : Point) (ρ a)).exists_bound_of_continuousOn
    ((hb a).continuous_fderiv (by simp)).continuousOn
  have hLocalM (a : K) := (isCompact_closedBall (a : Point) (ρ a)).exists_bound_of_continuousOn
    (continuous_laplacian_of_smooth (hb a)).continuousOn
  choose L₀ hL₀ using hLocalL
  choose M₀ hM₀ using hLocalM
  let W (a : K) := Metric.ball (a : Point) (ρ a / 2)
  have hCover : K ⊆ ⋃ a : K, W a := fun a ha =>
    mem_iUnion.mpr ⟨⟨a, ha⟩, Metric.mem_ball_self (half_pos (hρ ⟨a, ha⟩))⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover W (fun _ => Metric.isOpen_ball) hCover
  have hSmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ a ∈ I, s < ρ a / 2 :=
    (eventually_all_finset I).mpr fun a _ => nhdsWithin_le_nhds (Iio_mem_nhds (half_pos (hρ a)))
  have hPos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  obtain ⟨R, hR, hSmallR⟩ := (hPos.and hSmall).exists
  let L := ∑ a ∈ I, max (L₀ a) 0
  let M := ∑ a ∈ I, max (M₀ a) 0
  have hL : 0 ≤ L := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => le_max_right _ _
  refine ⟨R, L, M, hR, hL, hM, ?_⟩
  intro a ha r hr
  obtain ⟨i, hi, haI⟩ := mem_iUnion₂.mp (hI ha)
  have hA : dist a (i : Point) < ρ i / 2 := haI
  have hNear : Metric.closedBall a r ⊆ Metric.ball (i : Point) (ρ i) := by
    intro y hy
    have hT := dist_triangle y a (i : Point)
    have hyD : dist y a ≤ r := hy
    exact Metric.mem_ball.mpr (by linarith only [hT, hyD, hA, hr.2, hSmallR i hi])
  have hNear' : Metric.closedBall a r ⊆ Metric.closedBall (i : Point) (ρ i) :=
    hNear.trans Metric.ball_subset_closedBall
  have hWall (y : Point) (hy : y ∈ frontier U ∩ Metric.closedBall a r) : b i y = 0 := by
    have h := localDefiningFunction_eq_zero_on_frontier hU.1.1 ((hφ i).continuous.continuousOn)
      (hDef i) hy.1 (hNear hy.2)
    simp only [b, h, neg_zero]
  have ha0 : b i a = 0 := hWall a ⟨ha, Metric.mem_closedBall_self hr.1.le⟩
  have hDb (y : Point) (hy : y ∈ Metric.closedBall a r) : ‖fderiv ℝ (b i) y‖ ≤ L :=
    ((hL₀ i y (hNear' hy)).trans (le_max_left _ _)).trans
      (Finset.single_le_sum (fun _ _ => le_max_right _ _) hi)
  refine ⟨b i, hb i, ha0, hWall, ?_, ?_⟩
  · intro y hy
    have hy0 : 0 ≤ b i y := by
      by_cases hyU : y ∈ U
      · have hyG : y ∈ U ∩ Metric.ball (i : Point) (ρ i) := ⟨hyU, hNear hy.2⟩
        rw [hDef i] at hyG
        exact neg_nonneg.mpr (show φ i y < 0 from hyG.1).le
      · have hyF : y ∈ frontier U := by rw [frontier, hU.1.1.interior_eq]; exact ⟨hy.1, hyU⟩
        rw [hWall y ⟨hyF, hy.2⟩]
    refine ⟨hy0, ?_⟩
    have hLip := (convex_closedBall a r).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hb i).differentiable (by simp) z) hDb (Metric.mem_closedBall_self hr.1.le) hy.2
    rw [ha0, sub_zero, Real.norm_eq_abs, abs_of_nonneg hy0] at hLip
    exact hLip.trans (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy.2) hL)
  · intro y hy
    have hLap : |laplacian (b i) y| ≤ M := by
      have h := hM₀ i y (hNear' hy)
      rw [Real.norm_eq_abs] at h
      exact (h.trans (le_max_left _ _)).trans (Finset.single_le_sum (fun _ _ => le_max_right _ _) hi)
    have hV : fderiv ℝ (b i) y (w i) = 1 := by
      have hD := ((hφ i).differentiable (by simp) y).hasFDerivAt.neg.fderiv
      have hd := DFunLike.congr_fun hD (w i)
      simpa only [b, Pi.neg_def, neg_apply, hDir i y, neg_neg] using! hd
    exact ⟨hDb y hy, hLap, one_le_gradient_sq_of_unit_direction (hw i) hV⟩

private theorem laplacian_scalar_sq {U : Set Point} (hU : IsOpen U) {b : Point → ℝ}
    (hb : ContDiffOn ℝ 2 b U) {x : Point} (hx : x ∈ U) :
    laplacian (fun y => b y ^ 2) x = 2 * b x * laplacian b x +
      2 * ∑ i, (coordDeriv i b x) ^ 2 := by
  have hB (y : Point) (hy : y ∈ U) := ((hb y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt two_ne_zero
  have hTerm (j : Fin 3) :
      coordDeriv j (coordDeriv j (fun y => b y ^ 2)) x =
        (2 * b x) * coordDeriv j (coordDeriv j b) x + 2 * (coordDeriv j b x) ^ 2 := by
    have hEq : coordDeriv j (fun y => b y ^ 2) =ᶠ[𝓝 x] (fun y => 2 * b y * coordDeriv j b y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      have h := ((hB y hy).hasFDerivAt.pow 2).fderiv
      have hv := DFunLike.congr_fun h (axis j)
      simpa only [coordDeriv, Nat.cast_ofNat, Nat.reduceSub, pow_one, smul_apply, smul_eq_mul, two_nsmul,
        ← two_mul] using hv
    have hDj := differentiableAt_coordDeriv_of_contDiffAt ((hb x hx).contDiffAt (hU.mem_nhds hx)) j
    have hp := (((hB x hx).hasFDerivAt.const_mul 2).mul hDj.hasFDerivAt).fderiv
    have hReplace :
        coordDeriv j (coordDeriv j (fun y => b y ^ 2)) x =
        coordDeriv j (fun y => 2 * b y * coordDeriv j b y) x :=
      DFunLike.congr_fun hEq.fderiv_eq (axis j)
    rw [hReplace]
    have h : coordDeriv j (fun y => 2 * b y * coordDeriv j b y) x =
        2 * b x * coordDeriv j (coordDeriv j b) x + coordDeriv j b x * (2 * coordDeriv j b x) := by
      simpa only [coordDeriv, Pi.mul_def, add_apply, smul_apply, smul_eq_mul] using!
        DFunLike.congr_fun hp (axis j)
    rw [h]
    ring
  simp only [laplacian, hTerm, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- A nonnegative scalar defect with a uniform amplitude and a bounded
Laplacian is controlled by a barrier at every physical-wall center. The
parameters and defining function are chosen before the scalar equation. -/
theorem IsSmoothDomain.exists_uniform_wall_barrier_bound
    {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ R L A : ℝ, 0 < R ∧ 0 ≤ L ∧ 0 < A ∧
      ∀ a ∈ frontier U, ∀ r ∈ Ioo 0 R, ∃ b : Point → ℝ,
        ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) b ∧ b a = 0 ∧ ‖fderiv ℝ b a‖ ≤ L ∧
        ∀ (d F : ℝ), 0 ≤ d → 0 ≤ F → ∀ w : Point → ℝ,
          let V := U ∩ Metric.ball a r
          ContinuousOn w (closure V) → ContDiffOn ℝ 2 w V →
          EqOn w (fun _ => 0) (frontier U ∩ Metric.ball a r) →
          (∀ x ∈ closure V, w x ≤ d) →
          (∀ x ∈ V, -laplacian w x ≤ F) →
          ∀ x ∈ closure V,
            w x ≤ (d / r ^ 2) * ‖x - a‖ ^ 2 + A * (d / r + r * F) * b x := by
  obtain ⟨R₀, L, M, hR₀, hL, hM, hCharts⟩ := hU.exists_uniform_wall_barrier_charts
  let A := 8 * L + 1
  have hA : 0 < A := by dsimp only [A]; linarith only [hL]
  let H := M * (A + 16 * L)
  have hH : 0 ≤ H := mul_nonneg hM (add_nonneg hA.le (mul_nonneg (by norm_num) hL))
  let R := min R₀ (1 / (1 + H))
  have hR : 0 < R := lt_min hR₀ (one_div_pos.mpr (by positivity))
  refine ⟨R, L, A, hR, hL, hA, ?_⟩
  intro a ha r hr
  have hr₀ : r < R₀ := hr.2.trans_le (min_le_left _ _)
  have hSmall : r * H ≤ 1 := by
    have h₁ : r * (1 + H) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 1 + H)).mp
      (hr.2.le.trans (min_le_right _ _))
    linarith only [h₁, hr.1]
  obtain ⟨b, hb, hba, hWall0, hB, hBd⟩ := hCharts a ha r ⟨hr.1, hr₀⟩
  refine ⟨b, hb, hba, (hBd a (Metric.mem_closedBall_self hr.1.le)).1, ?_⟩
  intro d F hd hF w
  let V := U ∩ Metric.ball a r
  change ContinuousOn w (closure V) → ContDiffOn ℝ 2 w V → _ → _ → _ → _
  intro hw hDw hTrace hSup hLap x hx
  have hV : IsOpen V := hU.1.1.inter Metric.isOpen_ball
  have hSub : V ⊆ Metric.ball a r := inter_subset_right
  have hClosure : closure V ⊆ closure U ∩ Metric.closedBall a r := by
    refine subset_inter (closure_mono inter_subset_left) ?_
    exact closure_minimal (hSub.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall
  let T := d / r ^ 2 + F
  let a₁ := A * r * T
  let a₂ := 8 * T
  have hT : 0 ≤ T := add_nonneg (div_nonneg hd (sq_nonneg _)) hF
  have ha₁ : 0 ≤ a₁ := mul_nonneg (mul_nonneg hA.le hr.1.le) hT
  have ha₂ : 0 ≤ a₂ := mul_nonneg (by norm_num) hT
  let χ (y : Point) := (d / r ^ 2) • (‖y - a‖ ^ 2) - (a₂ • (b y ^ 2) - a₁ • b y)
  have hχ : ContDiff ℝ 2 χ := by
    have hB₂ : ContDiff ℝ 2 b := hb.of_le (WithTop.coe_le_coe.mpr le_top)
    exact (((contDiff_id.sub contDiff_const).norm_sq ℝ).const_smul (d / r ^ 2)).sub
      ((hB₂.pow 2).const_smul a₂ |>.sub (hB₂.const_smul a₁))
  have hb2 : ContDiffOn ℝ 2 b V := (hb.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hχLower (y : Point) (hy : y ∈ closure V) : (d / r ^ 2) * ‖y - a‖ ^ 2 ≤ χ y := by
    have hyB := hB y (hClosure hy)
    have hC : 0 ≤ A * r - 8 * b y := by
      dsimp only [A]
      linarith only [hyB.2, hr.1]
    have hh := mul_nonneg (mul_nonneg hT hyB.1) hC
    change (d / r ^ 2) * ‖y - a‖ ^ 2 ≤
      (d / r ^ 2) * ‖y - a‖ ^ 2 - (8 * T * b y ^ 2 - A * r * T * b y)
    linarith only [hh]
  have hχF (y : Point) (hy : y ∈ frontier V) : w y ≤ χ y := by
    rcases frontier_slice_subset hU.1.1 a hr.1 hy with (hS | hW) | hSeam
    · have hh := hχLower y (frontier_subset_closure hy)
      have hRnorm : ‖y - a‖ = r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hS.2
      rw [hRnorm, div_mul_cancel₀ _ (sq_pos_of_pos hr.1).ne'] at hh
      exact (hSup y (frontier_subset_closure hy)).trans hh
    · rw [hTrace hW]
      exact (mul_nonneg (div_nonneg hd (sq_nonneg _)) (sq_nonneg _)).trans
        (hχLower y (frontier_subset_closure hy))
    · have hh := hχLower y (frontier_subset_closure hy)
      have hRnorm : ‖y - a‖ = r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hSeam.2
      rw [hRnorm, div_mul_cancel₀ _ (sq_pos_of_pos hr.1).ne'] at hh
      exact (hSup y (frontier_subset_closure hy)).trans hh
  have hχLap (y : Point) (hy : y ∈ V) : F ≤ -laplacian χ y := by
    have hNormC : ContDiffOn ℝ 2 (fun z : Point => ‖z - a‖ ^ 2) V :=
      ((contDiff_id.sub contDiff_const).norm_sq ℝ).contDiffOn
    have hEq : laplacian χ y = (d / r ^ 2) * 6 -
        (a₂ * (2 * b y * laplacian b y + 2 * ∑ j, (coordDeriv j b y) ^ 2) - a₁ * laplacian b y) := by
      change laplacian (fun z => (d / r ^ 2) • ‖z - a‖ ^ 2 - (a₂ • b z ^ 2 - a₁ • b z)) y = _
      rw [laplacian_sub_of_contDiffOn hV (hNormC.const_smul _) ((hb2.pow 2).const_smul a₂ |>.sub
        (hb2.const_smul a₁)) hy, laplacian_sub_of_contDiffOn hV ((hb2.pow 2).const_smul a₂)
        (hb2.const_smul a₁) hy, laplacian_const_smul hV hNormC hy,
        laplacian_const_smul hV (hb2.pow 2) hy, laplacian_const_smul hV hb2 hy,
        laplacian_norm_sub_sq, laplacian_scalar_sq hV hb2 hy, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    have hCb := hClosure (subset_closure hy)
    have hyB := hB y hCb
    have hyD := hBd y hCb.2
    have hMin := (neg_le_neg hyD.2.1).trans (neg_abs_le (laplacian b y))
    have hT₁ := mul_le_mul_of_nonneg_left (le_abs_self (laplacian b y) |>.trans hyD.2.1) ha₁
    have hT₂ := mul_le_mul_of_nonneg_left hMin
      (mul_nonneg (mul_nonneg ha₂ (by norm_num : (0 : ℝ) ≤ 2)) hyB.1)
    have hT₃ := mul_le_mul_of_nonneg_left hyB.2
      (mul_nonneg (mul_nonneg ha₂ (by norm_num : (0 : ℝ) ≤ 2)) hM)
    have hT₄ := mul_le_mul_of_nonneg_left hyD.2.2 (mul_nonneg ha₂ (by norm_num : (0 : ℝ) ≤ 2))
    have hErr := mul_le_mul_of_nonneg_right hSmall hT
    have hfT : F ≤ T := le_add_of_nonneg_left (div_nonneg hd (sq_nonneg _))
    have hdT : d / r ^ 2 ≤ T := le_add_of_nonneg_right hF
    dsimp only [a₁, a₂, H] at hEq hT₁ hT₂ hT₃ hT₄ hErr
    linarith only [hEq, hT₁, hT₂, hT₃, hT₄, hErr, hfT, hdT, hT]
  have hCmp := nonpos_of_laplacian_nonneg_on_ball_subset hV hSub (hw.sub hχ.continuous.continuousOn)
    (hDw.sub hχ.contDiffOn) (f := fun y => w y - χ y) (fun y hy => by
      rw [laplacian_sub_of_contDiffOn hV hDw hχ.contDiffOn hy]
      linarith only [hχLap y hy, hLap y hy])
    (fun y hy => sub_nonpos.mpr (hχF y hy)) x hx
  have hχUp : χ x ≤ (d / r ^ 2) * ‖x - a‖ ^ 2 + A * (d / r + r * F) * b x := by
    have hRate : A * r * T = A * (d / r + r * F) := by
      dsimp only [T]
      field_simp [hr.1.ne']
    have hDrop : 0 ≤ a₂ * b x ^ 2 := mul_nonneg ha₂ (sq_nonneg _)
    change (d / r ^ 2) * ‖x - a‖ ^ 2 - (a₂ * b x ^ 2 - (A * r * T) * b x) ≤ _
    rw [hRate]
    linarith only [hDrop]
  exact (sub_nonpos.mp hCmp).trans hχUp

/-- A uniform bound for the true normal derivative follows by comparing
each smooth regularization with the same physical-wall barrier and then
taking the right-hand derivative along the inward normal. -/
theorem IsSmoothDomain.exists_wall_normalDerivative_bound_for_regularized_defect
    {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧
      ∀ a ∈ frontier U, ∀ r ∈ Ioo 0 R, ∀ ν : Point, HasRegularOutwardNormalAt U a ν →
        ∀ (d F : ℝ), 0 ≤ d → 0 ≤ F → ∀ (Z : Point → S0) (DZ : Point →L[ℝ] S0),
          let V := U ∩ Metric.ball a r
          ContinuousOn Z (closure V) → ContDiffOn ℝ 2 Z V →
          HasFDerivWithinAt Z DZ (closure U) a →
          EqOn Z (fun _ => 0) (frontier U ∩ Metric.ball a r) →
          (∀ x ∈ closure V, ‖Z x‖ ≤ d) →
          (∀ η : ℝ, 0 < η → ∀ x ∈ V, -laplacian (regularizedFrobeniusNorm η ∘ Z) x ≤ F) →
          ‖DZ ν‖ ≤ C * (d / r + r * F) := by
  obtain ⟨R, L, A, hR, hL, hA, hBarrier⟩ := hU.exists_uniform_wall_barrier_bound
  refine ⟨R, A * L + 1, hR, add_pos_of_nonneg_of_pos (mul_nonneg hA.le hL) zero_lt_one, ?_⟩
  intro a ha r hr ν hNormal d F hd hF Z DZ
  let V := U ∩ Metric.ball a r
  change ContinuousOn Z (closure V) → ContDiffOn ℝ 2 Z V → _ → _ → _ → _ → _
  intro hZ hZ₂ hDZ hTrace hSup hLap
  obtain ⟨b, hb, hba, hDb, hComp⟩ := hBarrier a ha r hr
  let K := d / r + r * F
  have hK : 0 ≤ K := add_nonneg (div_nonneg hd hr.1.le) (mul_nonneg hr.1.le hF)
  have haZ : Z a = 0 := hTrace ⟨ha, Metric.mem_ball_self hr.1⟩
  have hValue (y : Point) (hy : y ∈ closure V) :
      ‖Z y‖ ≤ (d / r ^ 2) * ‖y - a‖ ^ 2 + A * K * b y := by
    apply le_of_forall_pos_le_add
    intro η hη
    let W := regularizedFrobeniusNorm η ∘ Z
    have hW := contDiff_regularizedFrobeniusNorm hη
    have hWc : ContinuousOn W (closure V) := hW.continuous.comp_continuousOn hZ
    have hWd : ContDiffOn ℝ 2 W V := (hW.of_le (WithTop.coe_le_coe.mpr le_top)).comp_contDiffOn hZ₂
    have hWt : EqOn W (fun _ => 0) (frontier U ∩ Metric.ball a r) := fun x hx => by
      change regularizedFrobeniusNorm η (Z x) = 0
      rw [hTrace hx, regularizedFrobeniusNorm_zero hη.le]
    have hWup : ∀ x ∈ closure V, W x ≤ d := fun x hx =>
      ((regularizedFrobeniusNorm_nonneg_le hη.le (Z x)).2.1).trans (hSup x hx)
    have hA' := hComp d F hd hF W hWc hWd hWt hWup (hLap η hη) y hy
    exact ((regularizedFrobeniusNorm_nonneg_le hη.le (Z y)).2.2).trans
      (add_le_add hA' le_rfl)
  let v := -ν
  let γ (t : ℝ) := a + t • v
  have hv : ‖v‖ = 1 := by rw [show v = -ν from rfl, norm_neg, hNormal.2.1]
  have hγ0 : γ 0 = a := by simp only [γ, zero_smul, add_zero]
  have hγ : HasDerivAt γ v 0 := by
    simpa only [γ, id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add a
  have hN : inner ℝ ν v < 0 := by
    change inner ℝ ν (-ν) < 0
    rw [inner_neg_right, real_inner_self_eq_norm_sq, hNormal.2.1, one_pow]
    norm_num
  have hγU : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ U :=
    (hNormal.eventually_mem_iff_signedRay hN.ne).mono fun t ht => ht.mpr hN
  have hγB : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ Metric.ball a r := by
    apply hγ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [hγ0]
    exact Metric.ball_mem_nhds a hr.1
  let S := (γ ⁻¹' closure U) ∩ Ioi (0 : ℝ)
  have hS : 𝓝[S] (0 : ℝ) = 𝓝[>] (0 : ℝ) :=
    nhdsWithin_inter_of_mem (hγU.mono fun _ ht => subset_closure ht)
  have hMaps : MapsTo γ S (closure U) := fun _ ht => ht.1
  have hZray := hDZ.comp_hasDerivWithinAt_of_eq 0 hγ.hasDerivWithinAt hMaps hγ0.symm
  have hZray' : Tendsto (fun t : ℝ => t⁻¹ • Z (γ t)) (𝓝[>] (0 : ℝ)) (𝓝 (DZ v)) := by
    have hs₀ : (0 : ℝ) ∉ S := fun h => (lt_irrefl (0 : ℝ)) (show (0 : ℝ) < 0 from h.2)
    have h := (hasDerivWithinAt_iff_tendsto_slope' hs₀).mp hZray
    rw [hS] at h
    have hEq : slope (Z ∘ γ) 0 = fun t : ℝ => t⁻¹ • Z (γ t) := by
      funext t
      simp only [slope_def_module, sub_zero, Function.comp_apply, hγ0, haZ]
    rwa [hEq] at h
  have hBder : HasDerivAt (b ∘ γ) (fderiv ℝ b a v) 0 := by
    have hD : HasFDerivAt b (fderiv ℝ b a) (γ 0) := hγ0.symm ▸ (hb.differentiable (by simp) a).hasFDerivAt
    exact hD.comp_hasDerivAt 0 hγ
  have hBlim : Tendsto (fun t : ℝ => b (γ t) / t) (𝓝[>] (0 : ℝ)) (𝓝 (fderiv ℝ b a v)) := by
    simpa only [Function.comp_apply, zero_add, hγ0, hba, sub_zero, smul_eq_mul, div_eq_inv_mul] using
      hBder.tendsto_slope_zero_right
  have hLimR : Tendsto (fun t : ℝ => (d / r ^ 2) * t + (A * K) * (b (γ t) / t))
      (𝓝[>] (0 : ℝ)) (𝓝 (A * K * (fderiv ℝ b a v))) := by
    have hT : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero, zero_add] using (tendsto_const_nhds.mul hT).add (tendsto_const_nhds.mul hBlim)
  have hSlope : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖t⁻¹ • Z (γ t)‖ ≤ (d / r ^ 2) * t + (A * K) * (b (γ t) / t) := by
    have hT : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    filter_upwards [hγU, hγB, hT] with t htU htB ht
    have hVal := hValue (γ t) (subset_closure ⟨htU, htB⟩)
    have hdγ : ‖γ t - a‖ = t := by
      change ‖a + t • v - a‖ = t
      rw [add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_of_nonneg ht.le]
    rw [hdγ] at hVal
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
    refine (mul_le_mul_of_nonneg_left hVal (inv_nonneg.mpr ht.le)).trans_eq ?_
    field_simp [ht.ne']
  have hSlope' := le_of_tendsto_of_tendsto hZray'.norm hLimR hSlope
  have hbL : fderiv ℝ b a v ≤ L := by
    have hD := (fderiv ℝ b a).le_opNorm v
    rw [hv, mul_one, Real.norm_eq_abs] at hD
    exact (le_abs_self _).trans (hD.trans hDb)
  have hEq : ‖DZ v‖ = ‖DZ ν‖ := by
    change ‖DZ (-ν)‖ = ‖DZ ν‖
    rw [map_neg, norm_neg]
  rw [hEq] at hSlope'
  calc
    _ ≤ A * K * (fderiv ℝ b a v) := hSlope'
    _ ≤ A * K * L := mul_le_mul_of_nonneg_left hbL (mul_nonneg hA.le hK)
    _ = (A * L) * K := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hK

end Thesis

end

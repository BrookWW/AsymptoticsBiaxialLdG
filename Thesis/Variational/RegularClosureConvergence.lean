module

public import Thesis.Variational.BoundaryHolderAnalysis
public import Thesis.Variational.BoundaryScaledDefect
import Thesis.Variational.FirstCorrectionEquations
import Thesis.Variational.BoundarySubsolution
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.ContinuousMap.Compact

/-! Cutoffs supported off the singular set and the physical-boundary limit. -/

public section

open Filter Set Topology
open scoped BigOperators ContDiff ENNReal Manifold Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem coordDeriv_smul_field {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → ℝ} {u : Point → E} {x : Point}
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) (j : Fin 3) :
    coordDeriv j (fun y => f y • u y) x = f x • coordDeriv j u x + coordDeriv j f x • u x := by
  exact DFunLike.congr_fun (hf.hasFDerivAt.smul hu.hasFDerivAt).fderiv (axis j)

private theorem laplacian_smul_field {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set Point} (hU : IsOpen U) {f : Point → ℝ} {u : Point → E}
    (hf : ContDiffOn ℝ 2 f U) (hu : ContDiffOn ℝ 2 u U) {x : Point} (hx : x ∈ U) :
    laplacian (fun y => f y • u y) x = f x • laplacian u x + laplacian f x • u x +
      (2 : ℝ) • ∑ j, coordDeriv j f x • coordDeriv j u x := by
  have hf₂ := (hf x hx).contDiffAt (hU.mem_nhds hx)
  have hu₂ := (hu x hx).contDiffAt (hU.mem_nhds hx)
  have h (j : Fin 3) : coordDeriv j (coordDeriv j (fun y => f y • u y)) x =
      f x • coordDeriv j (coordDeriv j u) x + coordDeriv j (coordDeriv j f) x • u x +
        (2 : ℝ) • (coordDeriv j f x • coordDeriv j u x) := by
    have hEq : coordDeriv j (fun y => f y • u y) =ᶠ[𝓝 x]
        fun y => f y • coordDeriv j u y + coordDeriv j f y • u y := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact coordDeriv_smul_field
        (((hf y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt two_ne_zero)
        (((hu y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt two_ne_zero) j
    have hg := (hf₂.differentiableAt two_ne_zero).hasFDerivAt.smul
      (differentiableAt_coordDeriv_of_contDiffAt hu₂ j).hasFDerivAt
    have hh := (differentiableAt_coordDeriv_of_contDiffAt hf₂ j).hasFDerivAt.smul
      (hu₂.differentiableAt two_ne_zero).hasFDerivAt
    have hD := DFunLike.congr_fun ((hg.add hh).congr_of_eventuallyEq hEq).fderiv (axis j)
    change coordDeriv j (coordDeriv j (fun y => f y • u y)) x =
      (f x • coordDeriv j (coordDeriv j u) x + coordDeriv j f x • coordDeriv j u x) +
        (coordDeriv j f x • coordDeriv j u x + coordDeriv j (coordDeriv j f) x • u x) at hD
    rw [hD, two_smul ℝ]
    abel
  simp only [laplacian, h, Finset.smul_sum, Finset.sum_smul, ← Finset.sum_add_distrib]

private theorem exists_value_gradient_laplacian_bound_of_smooth_ambient_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set Point} (hU : IsSmoothDomain U) {b : Point → E}
    (hb : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) b) :
    ∃ M G F : ℝ, 0 ≤ M ∧ 0 ≤ G ∧ 0 ≤ F ∧
      (∀ x ∈ U, ‖b x‖ ≤ M) ∧
      (∀ x ∈ U, ∀ j : Fin 3, ‖coordDeriv j b x‖ ≤ G) ∧
      (∀ x ∈ U, ‖laplacian b x‖ ≤ F) := by
  obtain ⟨M, F, hM, hF, hBM, hBF⟩ := exists_value_laplacian_bound_of_contDiffOn_closure hU
    (hb.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  obtain ⟨A, hA⟩ := hU.1.2.2.isCompact_closure.exists_bound_of_continuousOn
    (hb.continuous_fderiv (by simp)).continuousOn
  refine ⟨M, max A 0, F, hM, le_max_right _ _, hF, hBM, ?_, hBF⟩
  intro x hx j
  have hAxis : ‖axis j‖ = 1 := by simp [axis]
  change ‖fderiv ℝ b x (axis j)‖ ≤ _
  exact (ContinuousLinearMap.le_opNorm (fderiv ℝ b x) (axis j)).trans
    (by rw [hAxis, mul_one]; exact (hA x (subset_closure hx)).trans (le_max_left _ _))

private theorem sqrt_gradientSq_bounds_column (D : Gradient) {M : ℝ} (h : gradientNormSq D ≤ M)
    (j : Fin 3) : ‖D j‖ ≤ Real.sqrt M := by
  apply Real.le_sqrt_of_sq_le
  rw [gradientNormSq_eq_sum_norm_sq] at h
  exact (Finset.single_le_sum (f := fun i : Fin 3 => ‖D i‖^2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)).trans h

private theorem cutoff_value_laplacian_uniform_bound
    {U S : Set Point} (hU : IsSmoothDomain U) {χ : Point → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) χ) (hχRange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hχSupp : Disjoint (tsupport χ) S)
    {B : Point → S0} (hB : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) B)
    {Q : ℕ → Point → S0} (hQ : ∀ n, ContDiffOn ℝ 2 (Q n) (closure U))
    {M : ℝ} (hM : 0 ≤ M) (hRange : ∀ n, ∀ x ∈ U, ‖Q n x‖ ≤ M)
    (hRegular : ∀ K : Set Point, IsCompact K → K ⊆ closure U \ S →
      ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ n in atTop, ∀ x ∈ U ∩ K,
        ‖laplacian (Q n) x‖ + gradientNormSq (ClassicalGradient (Q n) x) ≤ L) :
    let v (n : ℕ) (x : Point) := χ x • (Q n x - B x)
    ∃ A F : ℝ, 0 ≤ A ∧ 0 ≤ F ∧
      ∀ᶠ n in atTop, (∀ x ∈ U, ‖v n x‖ ≤ A) ∧ ∀ x ∈ U, ‖laplacian (v n) x‖ ≤ F := by
  let K := closure U ∩ tsupport χ
  have hK : IsCompact K := hU.1.2.2.isCompact_closure.inter_right (isClosed_tsupport χ)
  have hKw : K ⊆ closure U \ S := fun x hx => ⟨hx.1, fun hs => Set.disjoint_left.mp hχSupp hx.2 hs⟩
  obtain ⟨L, hL, hLocal⟩ := hRegular K hK hKw
  obtain ⟨MB, GB, FB, hMB, hGB, hFB, hValB, hGradB, hLapB⟩ :=
    exists_value_gradient_laplacian_bound_of_smooth_ambient_field hU hB
  obtain ⟨_, Gχ, Fχ, _, hGχ, hFχ, _, hGradχ, hLapχ⟩ :=
    exists_value_gradient_laplacian_bound_of_smooth_ambient_field hU hχ
  let A := M + MB
  let F := (L + FB) + Fχ*A + 2*(3*(Gχ*(Real.sqrt L + GB)))
  have hA : 0 ≤ A := add_nonneg hM hMB
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  refine ⟨A, F, hA, hF, ?_⟩
  filter_upwards [hLocal] with n hn
  let u (x : Point) := Q n x - B x
  let v (x : Point) := χ x • u x
  have hu₂ : ContDiffOn ℝ 2 u U :=
    (((hQ n).mono subset_closure).sub ((hB.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn))
  have hχ₂ : ContDiffOn ℝ 2 χ U :=
    (hχ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hu (x : Point) (hx : x ∈ U) : ‖u x‖ ≤ A :=
    (norm_sub_le _ _).trans (add_le_add (hRange n x hx) (hValB x hx))
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · change ‖χ x • u x‖ ≤ A
    rw [norm_smul, Real.norm_of_nonneg (hχRange x).1]
    exact (mul_le_mul_of_nonneg_right (hχRange x).2 (norm_nonneg _)).trans (by 
      rw [one_mul]
      exact hu x hx)
  · change ‖laplacian v x‖ ≤ F
    by_cases hSupport : x ∈ tsupport χ
    · have hCap := hn x ⟨hx, subset_closure hx, hSupport⟩
      have hSum : 0 ≤ gradientNormSq (ClassicalGradient (Q n) x) := by
        rw [gradientNormSq_eq_sum_norm_sq]
        exact Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hGradL : gradientNormSq (ClassicalGradient (Q n) x) ≤ L :=
        (le_add_of_nonneg_left (norm_nonneg _)).trans hCap
      have huLap : ‖laplacian u x‖ ≤ L + FB := by
        rw [laplacian_sub_of_contDiffOn hU.1.1 ((hQ n).mono subset_closure)
          ((hB.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn) hx]
        exact (norm_sub_le _ _).trans (add_le_add ((le_add_of_nonneg_right hSum).trans hCap) (hLapB x hx))
      have huGrad (j : Fin 3) : ‖coordDeriv j u x‖ ≤ Real.sqrt L + GB := by
        have hQ₁ := (((hQ n).mono subset_closure x hx).contDiffAt (hU.1.1.mem_nhds hx)).differentiableAt two_ne_zero
        have hB₁ := hB.differentiable (by simp) x
        have hD := DFunLike.congr_fun (hQ₁.hasFDerivAt.sub hB₁.hasFDerivAt).fderiv (axis j)
        change coordDeriv j u x = coordDeriv j (Q n) x - coordDeriv j B x at hD
        rw [hD]
        exact (norm_sub_le _ _).trans
          (add_le_add (sqrt_gradientSq_bounds_column _ hGradL j) (hGradB x hx j))
      rw [laplacian_smul_field hU.1.1 hχ₂ hu₂ hx]
      have h1 : ‖χ x • laplacian u x‖ ≤ L + FB := by
        rw [norm_smul, Real.norm_of_nonneg (hχRange x).1]
        exact (mul_le_mul_of_nonneg_right (hχRange x).2 (norm_nonneg _)).trans (by 
          rw [one_mul]
          exact huLap)
      have h2 : ‖laplacian χ x • u x‖ ≤ Fχ * A := by
        rw [norm_smul]
        exact mul_le_mul (hLapχ x hx) (hu x hx) (norm_nonneg _) hFχ
      have h3 : ‖(2 : ℝ) • ∑ j, coordDeriv j χ x • coordDeriv j u x‖ ≤
          2 * (3 * (Gχ * (Real.sqrt L + GB))) := by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        refine (norm_sum_le _ _).trans ?_
        calc
          _ ≤ ∑ _j : Fin 3, Gχ * (Real.sqrt L + GB) := Finset.sum_le_sum fun j _ => by
            rw [norm_smul]
            exact mul_le_mul (hGradχ x hx j) (huGrad j) (norm_nonneg _) hGχ
          _ = _ := by simp
      exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)
    · have hχz : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hSupport
      have hvz : v =ᶠ[𝓝 x] (fun _ => (0 : S0)) := hχz.mono fun y hy => by
        change χ y = 0 at hy
        simp [v, hy]
      rw [laplacian_eq_of_eventuallyEq hvz]
      have hDz (j : Fin 3) : coordDeriv j (fun _ : Point => (0 : S0)) = fun _ => 0 := by
        funext y
        simp [coordDeriv]
      simpa only [laplacian, hDz, Finset.sum_const_zero, norm_zero] using hF

private theorem regular_closure_eventuallyEq_closure {U S : Set Point} (hS : IsClosed S)
    {x : Point} (hx : x ∉ S) : closure U \ S =ᶠ[𝓝 x] closure U := by
  filter_upwards [hS.isOpen_compl.mem_nhds (show x ∈ Sᶜ from hx)] with y hy
  exact propext ⟨And.left, fun h => ⟨h, hy⟩⟩

private theorem cutoff_contDiffOn_closure {U S : Set Point} (hS : IsClosed S)
    {χ : Point → ℝ} (hχ : ContDiff ℝ 2 χ) (hzero : ∀ x ∈ S, χ =ᶠ[𝓝 x] 0)
    {q B : Point → S0} (hq : ContDiffOn ℝ 2 q (closure U \ S)) (hB : ContDiff ℝ 2 B) :
    ContDiffOn ℝ 2 (fun x => χ x • (q x - B x)) (closure U) := by
  intro x hx
  by_cases hSx : x ∈ S
  · have hEq : (fun x => χ x • (q x - B x)) =ᶠ[𝓝 x] (fun _ => (0 : S0)) :=
      (hzero x hSx).mono fun y hy => by
        change χ y = 0 at hy
        simp [hy]
    exact contDiffWithinAt_const.congr_of_eventuallyEq (hEq.filter_mono nhdsWithin_le_nhds) hEq.eq_of_nhds
  · have hq' : ContDiffWithinAt ℝ 2 q (closure U) x :=
      (hq x ⟨hx, hSx⟩).congr_set (regular_closure_eventuallyEq_closure hS hSx)
    exact hχ.contDiffAt.contDiffWithinAt.smul (hq'.sub hB.contDiffAt.contDiffWithinAt)

private theorem cutoff_gradientWithin_eq_sub {U S : Set Point} (hU : IsSmoothDomain U)
    (hS : IsClosed S) {χ : Point → ℝ} {q B : Point → S0}
    (hq : ContDiffOn ℝ 1 q (closure U \ S)) (hB : ContDiff ℝ 1 B)
    {x : Point} (hx : x ∈ closure U \ S) (hχ : χ =ᶠ[𝓝 x] (fun _ => 1))
    (j : Fin 3) :
    fderivWithin ℝ (fun y => χ y • (q y - B y)) (closure U) x (axis j) =
      fderivWithin ℝ q (closure U \ S) x (axis j) - coordDeriv j B x := by
  have hSet := regular_closure_eventuallyEq_closure (U := U) hS hx.2
  have hEq : (fun y => χ y • (q y - B y)) =ᶠ[𝓝 x] (fun y => q y - B y) :=
    hχ.mono fun y hy => by
      change χ y = 1 at hy
      simp [hy]
  have hqu : DifferentiableWithinAt ℝ q (closure U) x :=
    ((hq x hx).congr_set hSet).differentiableWithinAt one_ne_zero
  have hBu := hB.differentiable one_ne_zero x
  have hD :=
    (hqu.hasFDerivWithinAt.sub hBu.hasFDerivAt.hasFDerivWithinAt).fderivWithin (hU.uniqueDiffOn_closure x hx.1)
  change fderivWithin ℝ (fun y => q y - B y) (closure U) x =
    fderivWithin ℝ q (closure U) x - fderiv ℝ B x at hD
  have hL := hEq.fderivWithin_eq_of_nhds (𝕜 := ℝ) (s := closure U)
  rw [hL, hD]
  have hSetD := fderivWithin_congr_set (𝕜 := ℝ) (f := q) hSet
  exact congrArg (fun L : Point →L[ℝ] S0 => L (axis j) - coordDeriv j B x) hSetD.symm

private theorem holderSeminorm_congr_eqOn
    {E : Type*} [NormedAddCommGroup E] {α : ℝ} {K : Set Point} {f g : Point → E}
    (h : EqOn f g K) : holderSeminorm α K f = holderSeminorm α K g := by
  unfold holderSeminorm
  exact iSup_congr fun x => iSup_congr fun y => by rw [h x.property, h y.property]

theorem holderSeminorm_add_le
    {E : Type*} [NormedAddCommGroup E] (α : ℝ) (K : Set Point) (f g : Point → E) :
    holderSeminorm α K (f + g) ≤ holderSeminorm α K f + holderSeminorm α K g := by
  refine iSup_le fun x => iSup_le fun y => ?_
  let d := dist (x : Point) (y : Point) ^ α
  have hd : 0 ≤ d := Real.rpow_nonneg dist_nonneg _
  have h₁ : ‖(f + g) x - (f + g) y‖ ≤ ‖f x - f y‖ + ‖g x - g y‖ := by
    rw [show (f + g) x - (f + g) y = (f x - f y) + (g x - g y) by simp only [Pi.add_apply]; abel]
    exact norm_add_le _ _
  calc
    _ ≤ ENNReal.ofReal ((‖f x - f y‖ + ‖g x - g y‖) / d) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right h₁ hd)
    _ = ENNReal.ofReal (‖f x - f y‖ / d) + ENNReal.ofReal (‖g x - g y‖ / d) := by
      rw [add_div, ENNReal.ofReal_add (div_nonneg (norm_nonneg _) hd) (div_nonneg (norm_nonneg _) hd)]
    _ ≤ _ := add_le_add
      (le_iSup₂ (f := fun x' y' : K =>
        ENNReal.ofReal (‖f x' - f y'‖ / (dist (x' : Point) (y' : Point) ^ α))) x y)
      (le_iSup₂ (f := fun x' y' : K =>
        ENNReal.ofReal (‖g x' - g y'‖ / (dist (x' : Point) (y' : Point) ^ α))) x y)

private theorem holderSeminorm_classicalGradient_lt_top
    {B : Point → S0} (hB : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) B)
    {α : ℝ} (hα : 0 < α) (hα₁ : α < 1) {K : Set Point} (hK : IsCompact K) :
    holderSeminorm α K (ClassicalGradient B) < ⊤ := by
  letI : NormedAddCommGroup (Point →L[ℝ] S0) :=
    ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)
  letI : NormedSpace ℝ (Point →L[ℝ] S0) :=
    ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)
  have hG : ContDiff ℝ 1 (ClassicalGradient B) := by
    apply contDiff_pi.mpr
    intro j
    have hB₂ : ContDiff ℝ 2 B := hB.of_le (WithTop.coe_le_coe.mpr le_top)
    have hd : ContDiff ℝ 1 (fderiv ℝ B) := hB₂.fderiv_right (by norm_num)
    exact (ContinuousLinearMap.apply ℝ S0 (axis j)).contDiff.comp hd
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Point)
  obtain ⟨L, hL⟩ := hG.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall (0 : Point) R) (isCompact_closedBall _ _)
  apply holderSeminorm_lt_top_of_higherHolder hK hα hα₁ L.coe_nonneg
  intro x hx y hy
  have h := hL.dist_le_mul x (hR hx) y (hR hy)
  rw [dist_eq_norm (ClassicalGradient B x) (ClassicalGradient B y)] at h
  simpa only [Real.rpow_one] using h

private theorem cutoff_pointwise_convergence
    {U S : Set Point} (hU : IsOpen U) (hS : IsClosed S)
    {χ : Point → ℝ} (hχ : ContDiff ℝ 1 χ) (hzero : ∀ x ∈ S, χ =ᶠ[𝓝 x] 0)
    {B : Point → S0} (hB : ContDiff ℝ 1 B)
    {Q : ℕ → Point → S0} {q : Point → S0}
    (hInt : ConvergesCjLoc 2 (U \ S) Q q) :
    let v (n : ℕ) (x : Point) := χ x • (Q n x - B x)
    let w (x : Point) := χ x • (q x - B x)
    ∀ x ∈ U, Tendsto (fun n => v n x) atTop (𝓝 (w x)) ∧
      Tendsto (fun n => ClassicalGradient (v n) x) atTop (𝓝 (ClassicalGradient w x)) := by
  intro v w x hx
  by_cases hSx : x ∈ S
  · have hZ (f : Point → S0) : (fun y => χ y • (f y - B y)) =ᶠ[𝓝 x] (fun _ => (0 : S0)) :=
      (hzero x hSx).mono fun _ hy => by change χ _ = 0 at hy; simp [hy]
    have hG (f : Point → S0) : ClassicalGradient (fun y => χ y • (f y - B y)) x = 0 := by
      funext j
      have hF := (hZ f).fderiv_eq (𝕜 := ℝ)
      change (fderiv ℝ (fun y => χ y • (f y - B y)) x) (axis j) = 0
      rw [hF]
      simp
    have hVal (n : ℕ) : v n x = w x := ((hZ (Q n)).eq_of_nhds).trans (hZ q).eq_of_nhds.symm
    have hGrad (n : ℕ) : ClassicalGradient (v n) x = ClassicalGradient w x :=
      (hG (Q n)).trans (hG q).symm
    exact ⟨tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hVal n).symm),
      tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hGrad n).symm)⟩
  · let V := U \ S
    have hV : IsOpen V := hU.sdiff hS
    have hxV : x ∈ V := ⟨hx, hSx⟩
    have hQpoint := hInt.tendsto_at_of_two hxV
    have hD := hInt.tendsto_classicalGradient_at_of_two hxV
    have hχD := hχ.differentiable one_ne_zero x
    have hBD := hB.differentiable one_ne_zero x
    have hQdiff (n : ℕ) : DifferentiableAt ℝ (Q n) x :=
      (((hInt.1 n) x hxV).contDiffAt (hV.mem_nhds hxV)).differentiableAt two_ne_zero
    have hqdiff : DifferentiableAt ℝ q x :=
      ((hInt.2.1 x hxV).contDiffAt (hV.mem_nhds hxV)).differentiableAt two_ne_zero
    have hG (f : Point → S0) (hf : DifferentiableAt ℝ f x) (j : Fin 3) :
        coordDeriv j (fun y => χ y • (f y - B y)) x =
          χ x • (coordDeriv j f x - coordDeriv j B x) + coordDeriv j χ x • (f x - B x) := by
      have hProd := coordDeriv_smul_field hχD (hf.sub hBD) j
      change coordDeriv j (fun y => χ y • (f y - B y)) x =
        χ x • coordDeriv j (fun y => f y - B y) x + coordDeriv j χ x • (f x - B x) at hProd
      have h' := DFunLike.congr_fun (hf.hasFDerivAt.sub hBD.hasFDerivAt).fderiv (axis j)
      change coordDeriv j (fun y => f y - B y) x = coordDeriv j f x - coordDeriv j B x at h'
      rwa [h'] at hProd
    refine ⟨(hQpoint.sub_const (B x)).const_smul (χ x), ?_⟩
    apply tendsto_pi_nhds.mpr
    intro j
    have hDc := tendsto_pi_nhds.mp hD j
    have hFirst := (hDc.sub_const (coordDeriv j B x)).const_smul (χ x)
    have hSecond := (hQpoint.sub_const (B x)).const_smul (coordDeriv j χ x)
    have hLim := hFirst.add hSecond
    have hqEq : ClassicalGradient w x j =
        χ x • (ClassicalGradient q x j - coordDeriv j B x) + coordDeriv j χ x • (q x - B x) :=
      hG q hqdiff j
    rw [← hqEq] at hLim
    exact hLim.congr' (Eventually.of_forall fun n => (hG (Q n) (hQdiff n) j).symm)

/-- The regular closed-domain convergence follows from the actual fixed
trace, compact regular Poisson bounds, and the interior \(C^2\) convergence. -/
theorem convergesC1HolderLoc_of_compact_regular_Poisson_bounds
    (hPoisson : External.GlobalDirichletPoissonGradientHolder)
    {U S : Set Point} (hU : IsSmoothDomain U) (hS : IsClosed S)
    {B : Point → S0} (hB : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) B)
    {Q : ℕ → Point → S0} {q : Point → S0}
    (hQ : ∀ n, ContDiffOn ℝ 2 (Q n) (closure U))
    (hq : ContDiffOn ℝ 2 q (closure U \ S))
    (hTrace : ∀ n, EqOn (Q n) B (frontier U))
    {M : ℝ} (hM : 0 ≤ M) (hRange : ∀ n, ∀ x ∈ U, ‖Q n x‖ ≤ M)
    (hInt : ConvergesCjLoc 2 (U \ S) Q q)
    (hRegular : ∀ K : Set Point, IsCompact K → K ⊆ closure U \ S →
      ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ n in atTop, ∀ x ∈ U ∩ K,
        ‖laplacian (Q n) x‖ + gradientNormSq (ClassicalGradient (Q n) x) ≤ L)
    {α : ℝ} (hα : 0 < α) (hα₁ : α < 1) :
    ConvergesC1HolderLoc α U S Q q := by
  let W := closure U \ S
  let D (f : Point → S0) (x : Point) (j : Fin 3) := fderivWithin ℝ f W x (axis j)
  let E (f : Point → S0) (x : Point) (j : Fin 3) := fderivWithin ℝ f (closure U) x (axis j)
  have hB₂ : ContDiff ℝ 2 B := hB.of_le (WithTop.coe_le_coe.mpr le_top)
  have hB₁ : ContDiff ℝ 1 B := hB₂.of_le (by norm_num)
  have hQ₁ (n : ℕ) : ContDiffOn ℝ 1 (Q n) W := ((hQ n).of_le (by norm_num)).mono Set.sdiff_subset
  have hq₁ : ContDiffOn ℝ 1 q W := hq.of_le (by norm_num)
  refine ⟨hQ₁, hq₁, ?_⟩
  intro K hK hKw
  have hDisj : Disjoint S K := Set.disjoint_left.mpr fun x hxS hxK => (hKw hxK).2 hxS
  obtain ⟨χ₀, hχ₀, hχ₁, hχRange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed
      (𝓘(ℝ, Point)) (n := (⊤ : ℕ∞)) hS hK.isClosed hDisj
  let χ : Point → ℝ := χ₀
  have hχ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) χ := χ₀.contMDiff.contDiff
  have hχ₂ : ContDiff ℝ 2 χ := hχ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hχ₁' : ContDiff ℝ 1 χ := hχ₂.of_le (by norm_num)
  have hZero (x : Point) (hx : x ∈ S) : χ =ᶠ[𝓝 x] (0 : Point → ℝ) :=
    hχ₀.filter_mono (nhds_le_nhdsSet hx)
  have hOne (x : Point) (hx : x ∈ K) : χ =ᶠ[𝓝 x] (fun _ => 1) :=
    hχ₁.filter_mono (nhds_le_nhdsSet hx)
  have hSupp : Disjoint (tsupport χ) S := Set.disjoint_left.mpr fun x hx hxS =>
    (notMem_tsupport_iff_eventuallyEq.mpr (hZero x hxS)) hx
  let v (n : ℕ) (x : Point) := χ x • (Q n x - B x)
  let w (x : Point) := χ x • (q x - B x)
  have hv (n : ℕ) : ContDiffOn ℝ 2 (v n) (closure U) :=
    hχ₂.contDiffOn.smul ((hQ n).sub hB₂.contDiffOn)
  have hw : ContDiffOn ℝ 2 w (closure U) := cutoff_contDiffOn_closure hS hχ₂ hZero hq hB₂
  have hWall (n : ℕ) : EqOn (v n) (fun _ => 0) (frontier U) := by
    intro x hx
    simp only [v, hTrace n hx, sub_self, smul_zero]
  obtain ⟨A, F, hA, hF, hBounds⟩ :=
    cutoff_value_laplacian_uniform_bound hU hχ hχRange hSupp hB hQ hM hRange hRegular
  have hPoint := cutoff_pointwise_convergence hU.1.1 hS hχ₁' hZero hB₁ hInt
  have hCl := convergesC1HolderClosure_of_zero_trace_Poisson hPoisson hU v w hv (hw.of_le (by norm_num))
    hWall hPoint hA hF hBounds hα hα₁
  simp only [ConvergesC1HolderLoc, Set.sdiff_empty] at hCl
  have hKcl : K ⊆ closure U := hKw.trans Set.sdiff_subset
  obtain ⟨hVfinite, hWfinite, hV, hE, hHolder⟩ := hCl.2.2 K hK hKcl
  have hVeq (f : Point → S0) (x : Point) (hx : x ∈ K) : χ x • (f x - B x) = f x - B x := by
    rw [show χ x = 1 from (hOne x hx).eq_of_nhds, one_smul]
  have hEeq (f : Point → S0) (hf : ContDiffOn ℝ 1 f W) (x : Point) (hx : x ∈ K) :
      E (fun y => χ y • (f y - B y)) x = D f x - ClassicalGradient B x :=
    funext (cutoff_gradientWithin_eq_sub hU hS hf hB₁ (hKw hx) (hOne x hx))
  have hShift (f : Point → S0) (hf : ContDiffOn ℝ 1 f W) :
      EqOn (D f) (E (fun y => χ y • (f y - B y)) + ClassicalGradient B) K := by
    intro x hx
    change D f x = E (fun y => χ y • (f y - B y)) x + ClassicalGradient B x
    rw [hEeq f hf x hx, sub_add_cancel]
  have hBase := holderSeminorm_classicalGradient_lt_top hB hα hα₁ hK
  have hQfinite (n : ℕ) : holderSeminorm α K (D (Q n)) < ⊤ :=
    (holderSeminorm_congr_eqOn (hShift (Q n) (hQ₁ n))).le.trans_lt
      ((holderSeminorm_add_le α K (E (v n)) (ClassicalGradient B)).trans_lt
        (ENNReal.add_lt_top.2 ⟨hVfinite n, hBase⟩))
  have hqfinite : holderSeminorm α K (D q) < ⊤ :=
    (holderSeminorm_congr_eqOn (hShift q hq₁)).le.trans_lt
      ((holderSeminorm_add_le α K (E w) (ClassicalGradient B)).trans_lt
        (ENNReal.add_lt_top.2 ⟨hWfinite, hBase⟩))
  refine ⟨hQfinite, hqfinite, ?_, ?_, ?_⟩
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hV ε hε] with n hn x hx
    have heq : dist (w x) (v n x) = dist (q x) (Q n x) := by
      change dist (χ x • (q x - B x)) (χ x • (Q n x - B x)) = _
      rw [hVeq q x hx, hVeq (Q n) x hx, dist_sub_right]
    exact heq ▸ hn x hx
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hE ε hε] with n hn x hx
    have heq : dist (E w x) (E (v n) x) = dist (D q x) (D (Q n) x) := by
      change dist (E (fun y => χ y • (q y - B y)) x) (E (fun y => χ y • (Q n y - B y)) x) = _
      rw [hEeq q hq₁ x hx, hEeq (Q n) (hQ₁ n) x hx, dist_sub_right]
    exact heq ▸ hn x hx
  · exact hHolder.congr' (Eventually.of_forall fun n => holderSeminorm_congr_eqOn (fun x hx => by
      change E (fun y => χ y • (Q n y - B y)) x - E (fun y => χ y • (q y - B y)) x =
        D (Q n) x - D q x
      rw [hEeq (Q n) (hQ₁ n) x hx, hEeq q hq₁ x hx]
      abel))

private theorem eventually_iteratedFDeriv_bound_on_compact
    {V K : Set Point} (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    {Q : ℕ → Point → S0} {q : Point → S0} (h : ConvergesCjLoc 2 V Q q)
    (k : ℕ) (hk : k ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (Q n) x‖ ≤ C := by
  have hc : ContinuousOn (iteratedFDeriv ℝ k q) V :=
    ContinuousOn.continuousOn_iteratedFDeriv h.2.1 hV (by exact_mod_cast hk)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hc.mono hKV)
  refine ⟨max B 0 + 1, add_nonneg (le_max_right _ _) zero_le_one, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (h.2.2 k hk K hK hKV) 1 zero_lt_one] with n hn x hx
  have hD := dist_triangle (iteratedFDeriv ℝ k (Q n) x) (iteratedFDeriv ℝ k q x) 0
  rw [dist_zero_right, dist_zero_right, dist_comm] at hD
  exact hD.trans (by
    have hScale := hn x hx
    have hRange := (hB x hx).trans (le_max_left B 0)
    linarith only [hScale, hRange])

private theorem eventually_gradient_laplacian_bound_on_interior_compact
    {V K : Set Point} (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    {Q : ℕ → Point → S0} {q : Point → S0} (h : ConvergesCjLoc 2 V Q q) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ n in atTop, ∀ x ∈ K,
      ‖laplacian (Q n) x‖ + gradientNormSq (ClassicalGradient (Q n) x) ≤ L := by
  obtain ⟨A, hA, hFirst⟩ := eventually_iteratedFDeriv_bound_on_compact hV hK hKV h 1 (by decide)
  obtain ⟨B, hB, hSecond⟩ := eventually_iteratedFDeriv_bound_on_compact hV hK hKV h 2 le_rfl
  refine ⟨3 * B + 3 * A^2, by positivity, ?_⟩
  filter_upwards [hFirst, hSecond] with n hn₁ hn₂ x hx
  have hAxis (j : Fin 3) : ‖axis j‖ = 1 := by simp [axis]
  have hg (j : Fin 3) : ‖coordDeriv j (Q n) x‖ ≤ A := by
    have hG := (iteratedFDeriv ℝ 1 (Q n) x).le_opNorm (fun _ => axis j)
    simp only [iteratedFDeriv_one_apply, hAxis, Finset.prod_const_one, mul_one] at hG
    exact hG.trans (hn₁ x hx)
  have hL (j : Fin 3) : ‖coordDeriv j (coordDeriv j (Q n)) x‖ ≤ B := by
    have hReg := (h.1 n x (hKV hx)).contDiffAt (hV.mem_nhds (hKV hx))
    rw [coordDeriv_twice_eq_iteratedFDeriv_two hReg j]
    have hG := (iteratedFDeriv ℝ 2 (Q n) x).le_opNorm (fun _ => axis j)
    simpa only [hAxis, Finset.prod_const_one, mul_one] using hG.trans (by
      simp only [hAxis, Finset.prod_const_one, mul_one]
      exact hn₂ x hx)
  have hd : ‖laplacian (Q n) x‖ ≤ 3 * B :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hL j)).trans_eq (by simp))
  have hGrad : gradientNormSq (ClassicalGradient (Q n) x) ≤ 3 * A^2 := by
    rw [gradientNormSq_eq_sum_norm_sq]
    exact (Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hg j) 2)).trans_eq (by simp)
  exact add_le_add hd hGrad

theorem eventually_gradient_laplacian_bound_on_regular_compact
    {U S : Set Point} (hU : IsOpen U) (hS : IsClosed S)
    {Q : ℕ → Point → S0} {q : Point → S0} (hInt : ConvergesCjLoc 2 (U \ S) Q q)
    (hWall : ∀ c ∈ frontier U, ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ᶠ n in atTop, ∀ x ∈ U ∩ Metric.ball c r,
        ‖laplacian (Q n) x‖ + gradientNormSq (ClassicalGradient (Q n) x) ≤ L)
    (K : Set Point) (hK : IsCompact K) (hKW : K ⊆ closure U \ S) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ n in atTop, ∀ x ∈ U ∩ K,
      ‖laplacian (Q n) x‖ + gradientNormSq (ClassicalGradient (Q n) x) ≤ L := by
  classical
  have hV : IsOpen (U \ S) := hU.sdiff hS
  have hLocal (c : K) : ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ᶠ n in atTop, ∀ x ∈ U ∩ Metric.ball (c : Point) r,
        ‖laplacian (Q n) x‖ + gradientNormSq (ClassicalGradient (Q n) x) ≤ L := by
    have hc := hKW c.property
    by_cases hcU : (c : Point) ∈ U
    · obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds ⟨hcU, hc.2⟩)
      have hCl : Metric.closedBall (c : Point) (r / 2) ⊆ U \ S :=
        (Metric.closedBall_subset_ball (half_lt_self hr)).trans hBall
      obtain ⟨L, hL, hEst⟩ := eventually_gradient_laplacian_bound_on_interior_compact hV
        (isCompact_closedBall _ _) hCl hInt
      exact ⟨r / 2, L, half_pos hr, hL,
        hEst.mono fun n hn x hx => hn x (Metric.ball_subset_closedBall hx.2)⟩
    · exact hWall c (by rw [frontier, hU.interior_eq]; exact ⟨hc.1, hcU⟩)
  choose r L hr hL hEst using hLocal
  let V (c : K) := Metric.ball (c : Point) (r c)
  have hCover : K ⊆ ⋃ c : K, V c := fun c hc =>
    mem_iUnion.2 ⟨⟨c, hc⟩, Metric.mem_ball_self (hr ⟨c, hc⟩)⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover V (fun _ => Metric.isOpen_ball) hCover
  refine ⟨∑ c ∈ I, L c, Finset.sum_nonneg fun c _ => hL c, ?_⟩
  filter_upwards [(Filter.eventually_all_finset I).2 fun c _ => hEst c] with n hn x hx
  obtain ⟨c, hc, hcV⟩ := mem_iUnion₂.1 (hI hx.2)
  exact (hn c hc x ⟨hx.1, hcV⟩).trans (Finset.single_le_sum (fun c _ => hL c) hc)

theorem contDiffOn_regular_closure_of_interior_and_wall
    {U S V : Set Point} (hU : IsOpen U) (hS : IsClosed S) (hV : IsOpen V)
    (hWall : frontier U ⊆ V) {q : Point → S0}
    (hInt : ContDiffOn ℝ 2 q (U \ S)) (hCollar : ContDiffOn ℝ 2 q (closure U ∩ V)) :
    ContDiffOn ℝ 2 q (closure U \ S) := by
  intro x hx
  by_cases hxU : x ∈ U
  · exact ((hInt x ⟨hxU, hx.2⟩).contDiffAt ((hU.sdiff hS).mem_nhds ⟨hxU, hx.2⟩)).contDiffWithinAt
  · have hxWall : x ∈ frontier U := by rw [frontier, hU.interior_eq]; exact ⟨hx.1, hxU⟩
    have hxV := hWall hxWall
    have hClose : closure U ∈ 𝓝[closure U \ S] x :=
      Filter.mem_of_superset self_mem_nhdsWithin (by intro y hy; exact hy.1)
    have hNear : closure U ∩ V ∈ 𝓝[closure U \ S] x :=
      Filter.inter_mem hClose (mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV))
    exact (hCollar x ⟨hx.1, hxV⟩).mono_of_mem_nhdsWithin hNear

/-- The regular \(C^{1,\alpha}\) convergence uses the fixed physical trace,
the collar energy cap and the interior convergence of the same representatives. -/
theorem convergesC1HolderLoc_of_regular_wall_energy_cap
    (hPoisson : External.GlobalDirichletPoissonGradientHolder)
    (a : BulkCoefficients) {U S : Set Point} (hU : IsSmoothDomain U) (hS : IsClosed S)
    {B : Point → S0} (hB : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) B)
    (hBV : MapsTo B (frontier U) (vacuum a))
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (q : Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hQ : ∀ n, ContDiffOn ℝ 2 (Q n) (closure U))
    (hq : ContDiffOn ℝ 2 q (closure U \ S))
    (hTrace : ∀ n, EqOn (Q n) B (frontier U))
    (hEq : ∀ n, ∀ x ∈ U, (ε n : ℝ)^2 • (↑(laplacian (Q n) x) : Tensor) = bulkGradient a (Q n x))
    {M : ℝ} (hM : 0 ≤ M) (hRange : ∀ n, ∀ x ∈ U, ‖Q n x‖ ≤ M)
    (hInt : ConvergesCjLoc 2 (U \ S) Q q)
    (hEnergy : ∀ c ∈ frontier U, ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ᶠ n in atTop, ∀ x ∈ U ∩ Metric.ball c r,
        energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ L)
    {α : ℝ} (hα : 0 < α) (hα₁ : α < 1) :
    ConvergesC1HolderLoc α U S Q q := by
  have hWall (n : ℕ) : MapsTo (Q n) (frontier U) (vacuum a) := fun x hx => (hTrace n hx).symm ▸ hBV hx
  have hCap (c : Point) (hc : c ∈ frontier U) : ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ᶠ n in atTop, ∀ x ∈ U ∩ Metric.ball c r,
        ‖laplacian (Q n) x‖ + gradientNormSq (ClassicalGradient (Q n) x) ≤ L := by
    obtain ⟨r, L, hr, hL, hEn⟩ := hEnergy c hc
    obtain ⟨C, hC, hP⟩ := exists_eventual_gradient_laplacian_bound_on_smaller_wall_neighborhood
      a hU.1.1 hr hL ε Q hε hQ hWall hEq hEn
    exact ⟨r / 2, C, half_pos hr, hC, hP⟩
  exact convergesC1HolderLoc_of_compact_regular_Poisson_bounds hPoisson hU hS hB hQ hq
    hTrace hM hRange hInt (eventually_gradient_laplacian_bound_on_regular_compact hU.1.1 hS hInt hCap) hα hα₁

end Thesis

end

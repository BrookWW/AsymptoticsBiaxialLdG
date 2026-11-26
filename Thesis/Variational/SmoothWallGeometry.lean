module

public import Thesis.Variational.BoundaryNormalEnergy
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! Tangent directions and outward normals for smooth epigraph walls. -/

public section

open Filter Set Topology
open scoped ContDiff NNReal RealInnerProductSpace

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem eventually_pos_right_of_hasDerivAt {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (h0 : f 0 = 0) (hp : 0 < d) : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < f t := by
  have h := hd.tendsto_slope_zero_right
  simp only [zero_add, h0, sub_zero, smul_eq_mul] at h
  filter_upwards [h (Ioi_mem_nhds hp), self_mem_nhdsWithin] with t hdt ht
  exact pos_of_mul_pos_right hdt (inv_nonneg.mpr (le_of_lt ht))

private theorem eventually_neg_right_of_hasDerivAt {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (h0 : f 0 = 0) (hp : d < 0) : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < 0 := by
  have h := eventually_pos_right_of_hasDerivAt hd.neg
    (show (-f) 0 = 0 from by simp only [Pi.neg_apply, h0, neg_zero]) (neg_pos.mpr hp)
  exact h.mono fun _ ht => neg_pos.mp ht

/-- The sign of the derivative of a local defining function determines the
side of the wall reached by a transverse ray. -/
theorem HasRegularOutwardNormalAt.eventually_mem_iff_signedRay
    {U : Set Point} {a n : Point} (h : HasRegularOutwardNormalAt U a n)
    {v : Point} (hv : inner ℝ n v ≠ 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), a + t • v ∈ U ↔ inner ℝ n v < 0 := by
  obtain ⟨_, _, r, φ, s, hr, _, hφ0, hs, hd, hDef⟩ := h
  let X (t : ℝ) := a + t • v
  let f := φ ∘ X
  have hX : HasDerivAt X v 0 := by
    simpa only [X, id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add a
  have hX0 : X 0 = a := by simp only [X, zero_smul, add_zero]
  have hD : HasDerivAt f (s * inner ℝ n v) 0 := by
    have hda : HasFDerivAt φ (s • innerSL ℝ n) (X 0) := hX0.symm ▸ hd
    simpa only [f, smul_apply, smul_eq_mul, innerSL_apply_apply] using hda.comp_hasDerivAt 0 hX
  have hf0 : f 0 = 0 := by simp only [f, Function.comp_apply, hX0, hφ0]
  have hBall : ∀ᶠ t in 𝓝[>] (0 : ℝ), X t ∈ Metric.ball a r :=
    ((hX.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) :
      Tendsto X (𝓝[>] (0 : ℝ)) (𝓝 (X 0)))
        (hX0.symm ▸ Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have hMem : ∀ᶠ t in 𝓝[>] (0 : ℝ), X t ∈ U ↔ f t < 0 := hBall.mono fun t ht => by
    have he : X t ∈ U ∩ Metric.ball a r ↔ X t ∈ {y | φ y < 0} ∩ Metric.ball a r := by rw [hDef]
    simpa only [f, Function.comp_apply, mem_inter_iff, mem_setOf_eq, ht, and_true] using he
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · filter_upwards [hMem, eventually_neg_right_of_hasDerivAt hD hf0 (mul_neg_of_pos_of_neg hs hneg)]
      with t ht htneg
    exact ⟨fun _ => hneg, fun _ => ht.mpr htneg⟩
  · filter_upwards [hMem, eventually_pos_right_of_hasDerivAt hD hf0 (mul_pos hs hpos)] with t ht htpos
    exact ⟨fun h => (lt_asymm (ht.mp h) htpos).elim, fun hn => (lt_asymm hn hpos).elim⟩

/-- The regular outward normal is unique, including where two local
defining functions overlap. -/
theorem HasRegularOutwardNormalAt.unique {U : Set Point} {x n₁ n₂ : Point}
    (h₁ : HasRegularOutwardNormalAt U x n₁) (h₂ : HasRegularOutwardNormalAt U x n₂) : n₁ = n₂ := by
  by_contra hn
  have hPos : 0 < ‖n₁ - n₂‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hn))
  rw [norm_sub_sq_real, h₁.2.1, h₂.2.1, one_pow] at hPos
  have hInner : inner ℝ n₁ n₂ < 1 := by linarith only [hPos]
  let v := n₂ - n₁
  have hneg : inner ℝ n₁ v < 0 := by
    rw [show v = n₂ - n₁ by rfl, inner_sub_right, real_inner_self_eq_norm_sq, h₁.2.1, one_pow]
    exact sub_neg.mpr hInner
  have hpos : 0 < inner ℝ n₂ v := by
    rw [show v = n₂ - n₁ by rfl, inner_sub_right, real_inner_self_eq_norm_sq, h₂.2.1, one_pow,
      real_inner_comm n₁ n₂]
    exact sub_pos.mpr hInner
  have hFalse : ∀ᶠ t in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [h₁.eventually_mem_iff_signedRay hneg.ne, h₂.eventually_mem_iff_signedRay hpos.ne']
      with t ht₁ ht₂
    exact (lt_asymm (ht₂.mp (ht₁.mpr hneg)) hpos)
  exact hFalse.exists.elim fun _ h => h

/-- The open inward half-space lies in the tangent cone. This proves
unique differentiability within the domain at its regular wall points. -/
theorem HasRegularOutwardNormalAt.uniqueDiffWithinAt {U : Set Point} {x n : Point}
    (h : HasRegularOutwardNormalAt U x n) : UniqueDiffWithinAt ℝ U x := by
  let V : Set Point := {v | inner ℝ n v < 0}
  have hV : IsOpen V := isOpen_lt (continuous_const.inner continuous_id) continuous_const
  have hn : -n ∈ V := by
    change inner ℝ n (-n) < 0
    rw [inner_neg_right, real_inner_self_eq_norm_sq, h.2.1, one_pow]
    norm_num
  have hSub : V ⊆ tangentConeAt ℝ U x := by
    intro v hv
    have hneg : inner ℝ n v < 0 := hv
    apply mem_tangentConeAt_of_add_smul_mem (tendsto_id'.mpr (nhdsGT_le_nhdsNE (0 : ℝ)))
    exact (h.eventually_mem_iff_signedRay hneg.ne).mono fun _ ht => ht.mpr hneg
  let W := Submodule.span ℝ (tangentConeAt ℝ U x)
  have hn' : -n ∈ interior V := hV.interior_eq.symm ▸ hn
  have hIn : -n ∈ interior (W : Set Point) :=
    interior_mono (hSub.trans Submodule.subset_span) hn'
  have hTop : W = ⊤ := W.eq_top_of_nonempty_interior' ⟨-n, hIn⟩
  change Submodule.span ℝ (tangentConeAt ℝ U x) = ⊤ at hTop
  simp [uniqueDiffWithinAt_iff, hTop, frontier_subset_closure h.1]

/-- The closure of the frozen smooth epigraph domain is a set of unique
differentiability, including at the physical wall. -/
theorem IsSmoothDomain.uniqueDiffOn_closure {U : Set Point} (hU : IsSmoothDomain U) :
    UniqueDiffOn ℝ (closure U) := by
  intro x hx
  by_cases hu : x ∈ U
  · exact (uniqueDiffWithinAt_of_mem_nhds (mem_of_superset (hU.1.1.mem_nhds hu) subset_closure))
  · have hFr : x ∈ frontier U := by rw [frontier, hU.1.1.interior_eq]; exact ⟨hx, hu⟩
    obtain ⟨r, n, hr, _, hNormal⟩ := exists_local_smooth_outward_normal_field hU hFr
    exact (hNormal x ⟨hFr, Metric.mem_ball_self hr⟩).uniqueDiffWithinAt.closure

theorem localDefiningFunction_eq_zero_on_frontier
    {U : Set Point} (hU : IsOpen U) {a : Point} {r : ℝ} {φ : Point → ℝ}
    (hφ : ContinuousOn φ (Metric.ball a r))
    (hDef : U ∩ Metric.ball a r = {y | φ y < 0} ∩ Metric.ball a r)
    {y : Point} (hy : y ∈ frontier U) (hr : y ∈ Metric.ball a r) : φ y = 0 := by
  have hX : y ∈ closure (U ∩ Metric.ball a r) := Metric.isOpen_ball.closure_inter ⟨hy.1, hr⟩
  have hCY : ContinuousAt φ y := (hφ y hr).continuousAt (Metric.isOpen_ball.mem_nhds hr)
  have hC : φ y ∈ closure (φ '' (U ∩ Metric.ball a r)) := hCY.continuousWithinAt.mem_closure_image hX
  have hSub : φ '' (U ∩ Metric.ball a r) ⊆ Iic (0 : ℝ) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hDef] at hz
    exact (show φ z < 0 from hz.1).le
  apply le_antisymm (closure_minimal hSub isClosed_Iic hC)
  refine le_of_not_gt fun hn => ?_
  have hYU : y ∈ U ∩ Metric.ball a r := hDef.symm ▸ ⟨hn, hr⟩
  exact hy.2 (hU.interior_eq.symm ▸ hYU.1)

/-- A differentiable wall curve has velocity perpendicular to the
regular outward normal. -/
theorem HasRegularOutwardNormalAt.inner_velocity_eq_zero
    {U : Set Point} (hU : IsOpen U) {a n : Point} (h : HasRegularOutwardNormalAt U a n)
    {γ : ℝ → Point} {v : Point} (hγ : HasDerivAt γ v 0) (hγ0 : γ 0 = a)
    (hWall : ∀ᶠ t in 𝓝 0, γ t ∈ frontier U) : inner ℝ n v = 0 := by
  obtain ⟨_, _, r, φ, s, hr, hφ, _, hs, hD, hDef⟩ := h
  have hD' : HasFDerivAt φ (s • innerSL ℝ n) (γ 0) := hγ0.symm ▸ hD
  have hC : HasDerivAt (φ ∘ γ) (s * inner ℝ n v) 0 := by
    simpa only [smul_apply, smul_eq_mul, innerSL_apply_apply] using hD'.comp_hasDerivAt 0 hγ
  have hNear : ∀ᶠ t in 𝓝 0, γ t ∈ Metric.ball a r :=
    hγ.continuousAt.tendsto (hγ0.symm ▸ Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have hZero : (φ ∘ γ) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
    filter_upwards [hWall, hNear] with t ht ht'
    exact localDefiningFunction_eq_zero_on_frontier hU hφ.continuousOn hDef ht ht'
  exact (mul_eq_zero.mp (hC.unique ((hasDerivAt_const 0 (0 : ℝ)).congr_of_eventuallyEq hZero))).resolve_left hs.ne'

private theorem exists_boundary_parametrization_with_projection
    {U : Set Point} (hU : IsSmoothDomain U) {a : Point} (ha : a ∈ frontier U) :
    ∃ (r : ℝ) (Γ : Plane → Point) (L : Point →L[ℝ] Plane) (w : Point),
      0 < r ∧ ContDiff ℝ ∞ Γ ∧ Γ 0 = a ∧
      (∀ y ∈ Metric.ball a r, y ∈ frontier U ↔ y ∈ range Γ) ∧
      (∀ p, L (Γ p - a) = p) ∧
      (∀ z, L z = 0 → ∃ k : ℝ, z = k • w) := by
  obtain ⟨r, A, g, hr, hg, hg0, hChart⟩ := hU.2 a ha
  let E : Point ≃L[ℝ] Plane × EuclideanSpace ℝ (Fin 1) :=
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let P : Point →L[ℝ] Plane := (ContinuousLinearMap.fst ℝ Plane (EuclideanSpace ℝ (Fin 1))).comp
    E.toContinuousLinearMap
  let L : Point →L[ℝ] Plane := P.comp A.toContinuousLinearEquiv.toContinuousLinearMap
  have hP (z : Point) : P z = WithLp.toLp 2 ![z 0, z 1] := by
    ext i
    fin_cases i <;> rfl
  let e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
  have hVert : E (axis 2) = (0, e) := by
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · ext i
      fin_cases i
      rfl
  let Γ (p : Plane) := a + A.symm (E.symm (p, 0) + g p • axis 2)
  have hΓ : ContDiff ℝ ∞ Γ := by
    exact contDiff_const.add (A.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp
      ((E.symm.toContinuousLinearMap.contDiff.comp (contDiff_id.prodMk contDiff_const)).add
        (hg.smul contDiff_const)))
  have hΓ0 : Γ 0 = a := by simp only [Γ, hg0, zero_smul, add_zero, Prod.mk_zero_zero, map_zero]
  have hChart' : U ∩ Metric.ball a r = {y | g (P (A (y - a))) < (A (y - a)) 2} ∩ Metric.ball a r := by
    simpa only [hP] using hChart
  have hCoord (p : Plane) : E (A (Γ p - a)) = (p, g p • e) := by
    have hArg : Γ p - a = A.symm (E.symm (p, 0) + g p • axis 2) := by dsimp only [Γ]; abel
    rw [hArg, A.apply_symm_apply, map_add, E.apply_symm_apply, map_smul, hVert]
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add]
  have hHor (p : Plane) : L (Γ p - a) = p := congrArg Prod.fst (hCoord p)
  have hHeight (p : Plane) : (A (Γ p - a)) 2 = g p := by
    change (E (A (Γ p - a))).2 0 = g p
    rw [hCoord]
    simp only [PiLp.smul_apply, e, PiLp.single_apply, if_true, smul_eq_mul, mul_one]
  let w := A.symm (axis 2)
  have hWall (p : Plane) (hp : Γ p ∈ Metric.ball a r) : Γ p ∈ frontier U := by
    rw [frontier, hU.1.1.interior_eq]
    refine ⟨?_, ?_⟩
    · let R (t : ℝ) := Γ p + t • w
      have hRC : Continuous R := continuous_const.add (continuous_id.smul continuous_const)
      have hR0 : R 0 = Γ p := by simp only [R, zero_smul, add_zero]
      have hT : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 (Γ p)) := by
        rw [← hR0]
        exact hRC.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      apply mem_closure_of_tendsto hT
      filter_upwards [hT (Metric.isOpen_ball.mem_nhds hp), self_mem_nhdsWithin] with t hBall ht
      have hTrans : A (R t - a) = A (Γ p - a) + t • axis 2 := by
        simp only [R, w, map_sub, map_add, map_smul, A.apply_symm_apply]
        abel
      have hHt : (A (R t - a)) 2 = g p + t := by
        rw [hTrans, PiLp.add_apply, PiLp.smul_apply, hHeight]
        simp only [axis, PiLp.single_apply, if_true, smul_eq_mul, mul_one]
      have hPt : P (A (R t - a)) = p := by
        change (E (A (R t - a))).1 = p
        rw [hTrans, map_add, map_smul, hCoord, hVert]
        simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
      have hRight : R t ∈ {y | g (P (A (y - a))) < (A (y - a)) 2} ∩ Metric.ball a r := by
        refine ⟨?_, hBall⟩
        change g (P (A (R t - a))) < (A (R t - a)) 2
        rw [hPt, hHt]
        exact lt_add_of_pos_right _ ht
      exact (show R t ∈ U ∩ Metric.ball a r from hChart'.symm ▸ hRight).1
    · intro h
      have hL : Γ p ∈ U ∩ Metric.ball a r := ⟨h, hp⟩
      rw [hChart'] at hL
      have h' : g (L (Γ p - a)) < (A (Γ p - a)) 2 := hL.1
      rw [hHor, hHeight] at h'
      exact (lt_irrefl _ h')
  refine ⟨r, Γ, L, w, hr, hΓ, hΓ0, ?_, hHor, ?_⟩
  · intro y hy
    refine ⟨?_, ?_⟩
    · intro hyWall
      let p := L (y - a)
      let φ (z : Point) := g (P (A (z - a))) - (A (z - a)) 2
      have hA : Continuous (fun z : Point => A (z - a)) :=
        A.continuous.comp (continuous_id.sub continuous_const)
      have hφ : Continuous φ := (hg.continuous.comp (P.continuous.comp hA)).sub
        ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp hA)
      have hDef : U ∩ Metric.ball a r = {z | φ z < 0} ∩ Metric.ball a r := by
        simpa only [φ, sub_neg] using hChart'
      have hZero : φ y = 0 := localDefiningFunction_eq_zero_on_frontier hU.1.1
        hφ.continuousOn hDef hyWall hy
      have hY : (A (y - a)) 2 = g p := (sub_eq_zero.mp hZero).symm
      refine ⟨p, ?_⟩
      have hEq : E (A (Γ p - a)) = E (A (y - a)) := by
        rw [hCoord]
        apply Prod.ext
        · rfl
        · ext i
          fin_cases i
          change (g p • e) 0 = (A (y - a)) 2
          simp only [PiLp.smul_apply, e, PiLp.single_apply, if_true, smul_eq_mul, mul_one, hY]
      simpa only [sub_add_cancel] using congrArg (· + a) (A.injective (E.injective hEq))
    · rintro ⟨p, rfl⟩
      exact hWall p hy
  · intro z hz
    have hE : (E (A z)).1 = 0 := hz
    have h0 : (A z) 0 = 0 := congrArg (fun p : Plane => p 0) hE
    have h1 : (A z) 1 = 0 := congrArg (fun p : Plane => p 1) hE
    let k := (A z) 2
    refine ⟨k, A.injective ?_⟩
    change A z = A (k • w)
    simp only [map_smul, w, A.apply_symm_apply]
    ext i
    fin_cases i <;> simp [axis, h0, h1, k]

/-- The portion of the actual frontier in a sufficiently small ball
is exactly the image of a smooth planar parametrization in that ball. -/
theorem IsSmoothDomain.exists_boundary_parametrization
    {U : Set Point} (hU : IsSmoothDomain U) {a : Point} (ha : a ∈ frontier U) :
    ∃ (r : ℝ) (Γ : Plane → Point), 0 < r ∧ ContDiff ℝ ∞ Γ ∧ Γ 0 = a ∧
      ∀ y ∈ Metric.ball a r, y ∈ frontier U ↔ y ∈ range Γ := by
  obtain ⟨r, Γ, _, _, hr, hΓ, hΓ0, hImage, _, _⟩ :=
    exists_boundary_parametrization_with_projection hU ha
  exact ⟨r, Γ, hr, hΓ, hΓ0, hImage⟩

/-- A smooth epigraph wall realizes every vector perpendicular to its
regular outward normal as a velocity of a local smooth wall curve. -/
theorem IsSmoothDomain.exists_boundary_curve_of_inner_eq_zero
    {U : Set Point} (hU : IsSmoothDomain U) {a n v : Point} (hn : HasRegularOutwardNormalAt U a n)
    (hv : inner ℝ v n = 0) :
    ∃ γ : ℝ → Point, γ 0 = a ∧ HasDerivAt γ v 0 ∧ ∀ᶠ t in 𝓝 0, γ t ∈ frontier U := by
  obtain ⟨r, Γ, L, w, hr, hΓ, hΓ0, hImage, hHor, hKer⟩ :=
    exists_boundary_parametrization_with_projection hU hn.1
  have hNear : ∀ᶠ p in 𝓝 (0 : Plane), Γ p ∈ frontier U := by
    have hT : Tendsto Γ (𝓝 (0 : Plane)) (𝓝 a) := by
      rw [← hΓ0]
      exact hΓ.continuous.continuousAt.tendsto
    have hB : ∀ᶠ p in 𝓝 (0 : Plane), Γ p ∈ Metric.ball a r :=
      hT (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
    exact hB.mono fun p hp => (hImage (Γ p) hp).mpr ⟨p, rfl⟩
  let J := fderiv ℝ Γ 0
  have hdΓ : HasFDerivAt Γ J 0 := (hΓ.differentiable (by simp) 0).hasFDerivAt
  have hJ : L.comp J = ContinuousLinearMap.id ℝ Plane := by
    have hDL : HasFDerivAt (fun p => L (Γ p - a)) (L.comp J) 0 :=
      L.hasFDerivAt.comp 0 (hdΓ.sub_const a)
    have hId := hDL.congr_of_eventuallyEq (Eventually.of_forall fun p => (hHor p).symm)
    exact hId.unique (hasFDerivAt_id (0 : Plane))
  have hJw (p : Plane) : L (J p) = p := DFunLike.congr_fun hJ p
  have hCurves (p : Plane) : HasDerivAt (fun t : ℝ => Γ (t • p)) (J p) 0 ∧
      ∀ᶠ t : ℝ in 𝓝 0, Γ (t • p) ∈ frontier U := by
    let γ (t : ℝ) := t • p
    have hdP : HasDerivAt γ p 0 := by
      simpa only [γ, id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const p
    have hdΓ' : HasFDerivAt Γ J (γ 0) := by simpa only [γ, zero_smul] using hdΓ
    have hT : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 (0 : Plane)) := by
      simpa only [γ, zero_smul] using hdP.continuousAt.tendsto
    have hD : HasDerivAt (Γ ∘ γ) (J p) 0 := hdΓ'.comp_hasDerivAt 0 hdP
    exact ⟨hD, hT hNear⟩
  have hOrth (p : Plane) : inner ℝ n (J p) = 0 :=
    hn.inner_velocity_eq_zero hU.1.1 (hCurves p).1 (by simpa only [zero_smul] using hΓ0) (hCurves p).2
  have hResidual (z : Point) : ∃ k : ℝ, z - J (L z) = k • w :=
    hKer _ (by simp only [map_sub, hJw, sub_self])
  have hNW : inner ℝ n w ≠ 0 := by
    intro hW
    obtain ⟨k, hk⟩ := hResidual n
    have h := congrArg (inner ℝ n) hk
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hn.2.1, one_pow, hOrth, sub_zero,
      real_inner_smul_right, hW, mul_zero] at h
    exact one_ne_zero h
  obtain ⟨k, hk⟩ := hResidual v
  have hK := congrArg (inner ℝ n) hk
  rw [inner_sub_right, real_inner_comm v n, hv, hOrth, sub_zero, real_inner_smul_right] at hK
  have hk0 : k = 0 := (mul_eq_zero.mp hK.symm).resolve_right hNW
  rw [hk0, zero_smul] at hk
  have hV : v = J (L v) := sub_eq_zero.mp hk
  refine ⟨fun t => Γ (t • L v), ?_, ?_, (hCurves (L v)).2⟩
  · simpa only [zero_smul] using hΓ0
  · have hD := (hCurves (L v)).1
    rw [← hV] at hD
    exact hD

/-- The outward normal of a smooth bounded epigraph wall has a global
smooth extension. Finite subordinate bumps agree on the wall where they
overlap, because the regular outward normal is unique. -/
theorem IsSmoothDomain.exists_smooth_outward_normal_extension
    {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ X : Point → Point, ContDiff ℝ ∞ X ∧ ∀ y ∈ frontier U, HasRegularOutwardNormalAt U y (X y) := by
  classical
  let K := frontier U
  have hK : IsCompact K := hU.1.2.2.isCompact_closure.of_isClosed_subset
    isClosed_frontier frontier_subset_closure
  have hLocal (a : K) := exists_local_smooth_outward_normal_field hU a.property
  choose r n hr hn hN using hLocal
  let V (i : K) := Metric.ball (i : Point) (r i / 2)
  have hV (i : K) : IsOpen (V i) := Metric.isOpen_ball
  have hCover : K ⊆ ⋃ i : K, V i := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (half_pos (hr ⟨y, hy⟩))⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover V hV hCover
  let χ (i : K) : ContDiffBump (i : Point) := ⟨r i / 2, r i, half_pos (hr i), half_lt_self (hr i)⟩
  let S (y : Point) := ∑ i ∈ I, χ i y
  let W (y : Point) := ∑ i ∈ I, χ i y • n i y
  have hS : ContDiff ℝ ∞ S := ContDiff.sum fun i _ => (χ i).contDiff
  have hW : ContDiff ℝ ∞ W := ContDiff.sum fun i _ => (χ i).contDiff.smul (hn i)
  let d (y : Point) := S y + (1 - Real.smoothTransition (S y))
  have hd : ContDiff ℝ ∞ d := hS.add (contDiff_const.sub (Real.smoothTransition.contDiff.comp hS))
  have hPos (y : Point) : 0 < d y := by
    have hs : 0 ≤ S y := Finset.sum_nonneg fun i _ => (χ i).nonneg
    rcases hs.eq_or_lt with hz | hp
    · change 0 < S y + (1 - Real.smoothTransition (S y))
      rw [← hz, Real.smoothTransition.zero, sub_zero, zero_add]
      exact zero_lt_one
    · exact add_pos_of_pos_of_nonneg hp (sub_nonneg.mpr (Real.smoothTransition.le_one (S y)))
  let X (y : Point) := (d y)⁻¹ • W y
  have hXS : ContDiff ℝ ∞ X := (hd.inv fun y => (hPos y).ne').smul hW
  refine ⟨X, hXS, ?_⟩
  intro y hy
  obtain ⟨i, hi, hBall⟩ := mem_iUnion₂.mp (hI hy)
  have hOne : χ i y = 1 := (χ i).one_of_mem_closedBall (Metric.ball_subset_closedBall hBall)
  have hSOne : 1 ≤ S y := by
    rw [← hOne]
    exact Finset.single_le_sum (f := fun j => χ j y) (fun j _ => (χ j).nonneg) hi
  let z : K := ⟨y, hy⟩
  let N := n z y
  have hNy : HasRegularOutwardNormalAt U y N := hN z y ⟨hy, Metric.mem_ball_self (hr z)⟩
  have hEq (j : K) : χ j y • n j y = χ j y • N := by
    by_cases hj : χ j y = 0
    · simp only [hj, zero_smul]
    · have hM : y ∈ Metric.ball (j : Point) (r j) := by
        change y ∈ Metric.ball (j : Point) (χ j).rOut
        rw [← (χ j).support_eq]
        exact hj
      rw [(hN j y ⟨hy, hM⟩).unique hNy]
  have hW' : W y = S y • N := by
    change (∑ i ∈ I, χ i y • n i y) = (∑ i ∈ I, χ i y) • N
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl (fun j _ => hEq j)
  have hd' : d y = S y := by simp only [d, Real.smoothTransition.one_of_one_le hSOne, sub_self, add_zero]
  have hX' : X y = N := by
    change (d y)⁻¹ • W y = N
    rw [hd', hW', smul_smul, inv_mul_cancel₀ ((zero_lt_one.trans_le hSOne).ne'), one_smul]
  exact hX'.symm ▸ hNy

/-- The frozen smooth epigraph charts give the locally Lipschitz charts
needed for Gauss–Green. -/
theorem IsSmoothDomain.hasLocallyLipschitzBoundary {U : Set Point} (hU : IsSmoothDomain U) :
    HasLocallyLipschitzBoundary U := by
  intro x hx
  obtain ⟨r, A, g, hr, hg, hg0, hChart⟩ := hU.2 x hx
  have hd := hg.differentiable (by simp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Plane) r).exists_bound_of_continuousOn
    (hg.continuous_fderiv (by simp)).continuousOn
  let L : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  refine ⟨r, A, g, L, hr, ?_, hg0, hChart⟩
  apply (convex_ball (0 : Plane) r).lipschitzOnWith_of_nnnorm_fderiv_le (fun p _ => hd p)
  intro p hp
  change ‖fderiv ℝ g p‖₊ ≤ L
  exact_mod_cast (hM p (Metric.ball_subset_closedBall hp)).trans (le_max_left M 0)

end Thesis

end

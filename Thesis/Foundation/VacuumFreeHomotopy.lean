module

public import Thesis.Foundation.VacuumFundamentalGroup
public import Thesis.Interpolation.CircleTraceDescent

/-! Free homotopy of vacuum-valued maps on the Euclidean unit circle. -/

@[expose] public section

noncomputable section

open HarmonicMaps Metric Set StratificationTheory Topology

namespace Thesis

/-- The Euclidean circle used for the native surface trace. -/
abbrev NativeCircle := sphere (0 : Domain 2) 1

/-- The common endpoint of the angular interval. -/
def nativeCircleLoopBase : NativeCircle := circleNativeParam (-Real.pi)

/-- The angular parameter on the unit interval. -/
def nativeCircleLoopParam : C(unitInterval, NativeCircle) :=
  ⟨fun t => circleNativeParam (2 * Real.pi * t.val - Real.pi),
    continuous_circleNativeParam.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)⟩

theorem nativeCircleLoopParam_apply (t : unitInterval) :
    nativeCircleLoopParam t = circleNativeParam (2 * Real.pi * t.val - Real.pi) := rfl

theorem nativeCircleLoopParam_zero : nativeCircleLoopParam 0 = nativeCircleLoopBase := by
  rw [nativeCircleLoopParam_apply, show (0 : unitInterval).val = 0 from rfl, mul_zero, zero_sub]
  rfl

theorem nativeCircleLoopParam_one : nativeCircleLoopParam 1 = nativeCircleLoopBase := by
  rw [nativeCircleLoopParam_apply, show (1 : unitInterval).val = 1 from rfl, mul_one,
    show 2 * Real.pi - Real.pi = Real.pi by ring, ← circleNativeParam_neg_pi]
  rfl

theorem nativeCircleLoopParam_surjective : Function.Surjective nativeCircleLoopParam := by
  intro x
  obtain ⟨t, ht⟩ := circleNativeParam_closed_surjective x
  have hπ : 0 < 2 * Real.pi := by positivity
  let s : unitInterval := ⟨(t.val + Real.pi) / (2 * Real.pi),
    div_nonneg (by linarith [t.property.1]) hπ.le,
    (div_le_one hπ).2 (by linarith [t.property.2])⟩
  refine ⟨s, ?_⟩
  rw [nativeCircleLoopParam_apply]
  have harg : 2 * Real.pi * s.val - Real.pi = t.val := by
    change (2 * Real.pi) * ((t.val + Real.pi) / (2 * Real.pi)) - Real.pi = t.val
    field_simp
    exact add_sub_cancel_right _ _
  rwa [harg]

/-- A circle map as a based loop, traversed in the increasing angular direction. -/
def nativeCircleLoop {X : Type*} [TopologicalSpace X] (f : C(NativeCircle, X)) :
    Path (f nativeCircleLoopBase) (f nativeCircleLoopBase) where
  toContinuousMap := f.comp nativeCircleLoopParam
  source' := congrArg f nativeCircleLoopParam_zero
  target' := congrArg f nativeCircleLoopParam_one

theorem nativeCircleLoop_apply {X : Type*} [TopologicalSpace X] (f : C(NativeCircle, X))
    (t : unitInterval) :
    nativeCircleLoop f t = f (circleNativeParam (2 * Real.pi * t.val - Real.pi)) := rfl

private def nativeCircleAngular (t : unitInterval) : AngularInterval :=
  ⟨2 * Real.pi * t.val - Real.pi, by
    constructor
    · linarith [mul_nonneg Real.two_pi_pos.le t.property.1]
    · linarith [mul_le_mul_of_nonneg_left t.property.2 Real.two_pi_pos.le]⟩

private def angularUnitParameter (t : AngularInterval) : unitInterval :=
  ⟨(t.val + Real.pi) / (2 * Real.pi),
    div_nonneg (by linarith [t.property.1]) Real.two_pi_pos.le,
    (div_le_one Real.two_pi_pos).2 (by linarith [t.property.2])⟩

private theorem angularUnitParameter_left :
    angularUnitParameter ⟨-Real.pi, le_rfl, by linarith [Real.pi_pos]⟩ = 0 := by
  apply Subtype.ext
  change (-Real.pi + Real.pi) / (2 * Real.pi) = 0
  simp

private theorem angularUnitParameter_right :
    angularUnitParameter ⟨Real.pi, by linarith [Real.pi_pos], le_rfl⟩ = 1 := by
  apply Subtype.ext
  change (Real.pi + Real.pi) / (2 * Real.pi) = 1
  rw [← two_mul, div_self Real.two_pi_pos.ne']

private theorem angularUnitParameter_nativeCircleAngular (t : unitInterval) :
    angularUnitParameter (nativeCircleAngular t) = t := by
  apply Subtype.ext
  change (2 * Real.pi * t.val - Real.pi + Real.pi) / (2 * Real.pi) = t.val
  rw [sub_add_cancel, mul_div_cancel_left₀ _ Real.two_pi_pos.ne']

private theorem exists_nativeCircle_square_descent {X : Type*} [TopologicalSpace X]
    (F : C(unitInterval × unitInterval, X)) (hp : ∀ s, F (s, 0) = F (s, 1)) :
    ∃ H : C(unitInterval × NativeCircle, X),
      ∀ (s t : unitInterval), H (s, nativeCircleLoopParam t) = F (s, t) := by
  have hu : Continuous angularUnitParameter :=
    Continuous.subtype_mk ((continuous_subtype_val.add continuous_const).div_const _) _
  have hfibre (s t u : unitInterval) (heq : nativeCircleLoopParam t = nativeCircleLoopParam u) :
      F (s, t) = F (s, u) := by
    let U : C(AngularInterval, X) :=
      ⟨fun r => F (s, angularUnitParameter r), F.continuous.comp (continuous_const.prodMk hu)⟩
    have hEnd : U ⟨-Real.pi, le_rfl, by linarith [Real.pi_pos]⟩ =
        U ⟨Real.pi, by linarith [Real.pi_pos], le_rfl⟩ := by
      change F (s, angularUnitParameter _) = F (s, angularUnitParameter _)
      simpa only [angularUnitParameter_left, angularUnitParameter_right] using hp s
    obtain ⟨V, hV⟩ := exists_circleTrace_descent U hEnd
    have hV' (z : unitInterval) : V (nativeCircleLoopParam z) = F (s, z) := by
      have h := hV (nativeCircleAngular z)
      change V (nativeCircleLoopParam z) = F (s, angularUnitParameter (nativeCircleAngular z)) at h
      rwa [angularUnitParameter_nativeCircleAngular] at h
    rw [← hV' t, ← hV' u, heq]
  let p : unitInterval × unitInterval → unitInterval × NativeCircle :=
    fun x => (x.1, nativeCircleLoopParam x.2)
  have hpcts : Continuous p := continuous_fst.prodMk (nativeCircleLoopParam.continuous.comp continuous_snd)
  have hpSurj : Function.Surjective p := by
    rintro ⟨s, x⟩
    obtain ⟨t, ht⟩ := nativeCircleLoopParam_surjective x
    exact ⟨(s, t), Prod.ext rfl ht⟩
  have hpQuot : IsQuotientMap p := hpcts.isClosedMap.isQuotientMap hpcts hpSurj
  let H (x : unitInterval × NativeCircle) : X :=
    F (x.1, Classical.choose (nativeCircleLoopParam_surjective x.2))
  have hH (s t : unitInterval) : H (s, nativeCircleLoopParam t) = F (s, t) :=
    hfibre s _ t (Classical.choose_spec (nativeCircleLoopParam_surjective (nativeCircleLoopParam t)))
  have hHcts : Continuous H := hpQuot.continuous_iff.2 (by
    rw [show H ∘ p = F from funext fun x => hH x.1 x.2]
    exact F.continuous)
  exact ⟨⟨H, hHcts⟩, hH⟩

/-- Every continuous based loop descends to a map on the native circle with the same parametrization. -/
theorem exists_nativeCircleLoop_descent {X : Type*} [TopologicalSpace X] {A : X} (γ : Path A A) :
    ∃ (f : C(NativeCircle, X)) (hf : A = f nativeCircleLoopBase),
      (nativeCircleLoop f).cast hf hf = γ := by
  let F : C(unitInterval × unitInterval, X) := ⟨fun z => γ z.2, γ.continuous.comp continuous_snd⟩
  have hper (s : unitInterval) : F (s, 0) = F (s, 1) := γ.source.trans γ.target.symm
  obtain ⟨H, hH⟩ := exists_nativeCircle_square_descent F hper
  let f : C(NativeCircle, X) :=
    H.comp ((ContinuousMap.const NativeCircle (0 : unitInterval)).prodMk (ContinuousMap.id NativeCircle))
  have hf : A = f nativeCircleLoopBase := γ.source.symm.trans ((hH 0 0).symm.trans
    (congrArg (fun y => H (0, y)) nativeCircleLoopParam_zero))
  exact ⟨f, hf, Path.ext (funext (hH 0))⟩

/-- A continuous square with matching vertical sides descends to a free homotopy of circle maps. -/
theorem nativeCircle_homotopic_of_periodic_square {X : Type*} [TopologicalSpace X]
    {f g : C(NativeCircle, X)} (F : C(unitInterval × unitInterval, X))
    (h₀ : ∀ t, F (0, t) = nativeCircleLoop f t) (h₁ : ∀ t, F (1, t) = nativeCircleLoop g t)
    (hp : ∀ s, F (s, 0) = F (s, 1)) : f.Homotopic g := by
  obtain ⟨H, hH⟩ := exists_nativeCircle_square_descent F hp
  refine ⟨⟨H, ?_, ?_⟩⟩
  · intro x
    obtain ⟨t, rfl⟩ := nativeCircleLoopParam_surjective x
    exact (hH 0 t).trans (h₀ t)
  · intro x
    obtain ⟨t, rfl⟩ := nativeCircleLoopParam_surjective x
    exact (hH 1 t).trans (h₁ t)

/-- The native circle loop based at the projection of a chosen point in the fiber. -/
def nativeVacuumLoopPath (a : BulkCoefficients) (f : C(NativeCircle, vacuum a)) (v : Sphere3)
    (hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase) :
    Path (vacuumQuaternionProjection a v) (vacuumQuaternionProjection a v) :=
  (nativeCircleLoop f).cast hv hv

/-- The quaternion word of the native circle loop with a specified starting lift. -/
def nativeVacuumLoopWord (a : BulkCoefficients) (f : C(NativeCircle, vacuum a)) (v : Sphere3)
    (hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase) : QuaternionGroup 2 :=
  vacuumFundamentalGroupEquiv a v
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (nativeVacuumLoopPath a f v hv)))

private theorem nativeVacuumLoop_lift_end (a : BulkCoefficients) (f : C(NativeCircle, vacuum a))
    (v : Sphere3) (hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase)
    (Γ : C(unitInterval, Sphere3)) (hΓ₀ : Γ 0 = v)
    (hΓ : ∀ s, vacuumQuaternionProjection a (Γ s) = nativeCircleLoop f s) :
    Γ 1 = (nativeVacuumLoopWord a f v hv)⁻¹ • v := by
  obtain ⟨Γ', hΓ'₀, hΓ', hΓ'₁⟩ := vacuumLoop_exists_lift a v (nativeVacuumLoopPath a f v hv)
  have hEq : (fun s => Γ' s) = Γ :=
    (vacuumQuaternionProjection_isCoveringMap a).eq_of_comp_eq
      Γ'.continuous Γ.continuous (funext fun s => (hΓ' s).trans (hΓ s).symm) 0
        (hΓ'₀.trans hΓ₀.symm)
  rw [show Γ 1 = Γ' 1 from (congrFun hEq 1).symm]
  apply Subtype.ext
  apply Quaternion.linearIsometryEquivTuple.symm.injective
  rw [quaternionTuple_symm_smul, inv_inv]
  exact hΓ'₁

private theorem exists_nativeVacuumLoop_lift (a : BulkCoefficients) (f : C(NativeCircle, vacuum a))
    (v : Sphere3) (hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase) :
    ∃ Γ : C(unitInterval, Sphere3), Γ 0 = v ∧
      (∀ t, vacuumQuaternionProjection a (Γ t) = nativeCircleLoop f t) ∧
      Γ 1 = (nativeVacuumLoopWord a f v hv)⁻¹ • v := by
  obtain ⟨Γ, hΓ₀, hΓ, _⟩ := vacuumLoop_exists_lift a v (nativeVacuumLoopPath a f v hv)
  exact ⟨Γ, hΓ₀, hΓ, nativeVacuumLoop_lift_end a f v hv Γ hΓ₀ hΓ⟩

/-- Changing the starting lift acts by conjugation on the quaternion word. -/
theorem nativeVacuumLoopWord_smul (a : BulkCoefficients) (f : C(NativeCircle, vacuum a))
    (v : Sphere3) (hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase)
    (k : QuaternionGroup 2) :
    nativeVacuumLoopWord a f (k • v) ((vacuumQuaternionProjection_smul a k v).trans hv) =
      k * nativeVacuumLoopWord a f v hv * k⁻¹ := by
  let g := nativeVacuumLoopWord a f v hv
  obtain ⟨Γ, hΓ₀, hΓ, hΓ₁⟩ := exists_nativeVacuumLoop_lift a f v hv
  let Γ' : C(unitInterval, Sphere3) :=
    ⟨fun t => k • Γ t, (continuous_const_smul k).comp Γ.continuous⟩
  have hΓ'₀ : Γ' 0 = k • v := congrArg (fun z : Sphere3 => k • z) hΓ₀
  have hΓ' (t : unitInterval) : vacuumQuaternionProjection a (Γ' t) = nativeCircleLoop f t :=
    (vacuumQuaternionProjection_smul a k (Γ t)).trans (hΓ t)
  have hEnd := nativeVacuumLoop_lift_end a f (k • v)
    ((vacuumQuaternionProjection_smul a k v).trans hv) Γ' hΓ'₀ hΓ'
  apply inv_injective
  apply IsCancelSMul.right_cancel' _ _ (k • v)
  rw [← hEnd]
  change k • Γ 1 = (k * g * k⁻¹)⁻¹ • (k • v)
  rw [show Γ 1 = g⁻¹ • v from hΓ₁]
  simp only [mul_inv_rev, inv_inv, mul_smul, inv_smul_smul]

/-- The word's conjugacy class is independent of the chosen point over the circle base. -/
theorem nativeVacuumLoopWord_isConj_of_lifts (a : BulkCoefficients) (f : C(NativeCircle, vacuum a))
    (v w : Sphere3) (hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase)
    (hw : vacuumQuaternionProjection a w = f nativeCircleLoopBase) :
    IsConj (nativeVacuumLoopWord a f v hv) (nativeVacuumLoopWord a f w hw) := by
  obtain ⟨k, hk⟩ := (vacuumQuaternionProjection_eq_iff_orbit a).1 (hw.trans hv.symm)
  subst w
  exact isConj_iff.mpr ⟨k, (nativeVacuumLoopWord_smul a f v hv k).symm⟩

private theorem nativeVacuumLoopWord_isConj_of_homotopy (a : BulkCoefficients)
    {f₀ f₁ : C(NativeCircle, vacuum a)} (H : f₀.Homotopy f₁) (v₀ v₁ : Sphere3)
    (hv₀ : vacuumQuaternionProjection a v₀ = f₀ nativeCircleLoopBase)
    (hv₁ : vacuumQuaternionProjection a v₁ = f₁ nativeCircleLoopBase) :
    IsConj (nativeVacuumLoopWord a f₀ v₀ hv₀) (nativeVacuumLoopWord a f₁ v₁ hv₁) := by
  let g₀ := nativeVacuumLoopWord a f₀ v₀ hv₀
  obtain ⟨Γ₀, hΓ₀zero, hΓ₀, hΓ₀one⟩ := exists_nativeVacuumLoop_lift a f₀ v₀ hv₀
  let F : C(unitInterval × unitInterval, vacuum a) :=
    H.toContinuousMap.comp ⟨fun p => (p.1, nativeCircleLoopParam p.2),
      continuous_fst.prodMk (nativeCircleLoopParam.continuous.comp continuous_snd)⟩
  have hF₀ (t : unitInterval) : F (0, t) = vacuumQuaternionProjection a (Γ₀ t) :=
    (H.map_zero_left _).trans (hΓ₀ t).symm
  have hF₁ (t : unitInterval) : F (1, t) = nativeCircleLoop f₁ t := H.map_one_left _
  have hb (s : unitInterval) : F (s, 1) = F (s, 0) := by
    change H (s, nativeCircleLoopParam 1) = H (s, nativeCircleLoopParam 0)
    rw [nativeCircleLoopParam_zero, nativeCircleLoopParam_one]
  let cov := vacuumQuaternionProjection_isCoveringMap a
  let L := cov.liftHomotopy F Γ₀ hF₀
  have hL (s t : unitInterval) : vacuumQuaternionProjection a (L (s, t)) = F (s, t) :=
    congrFun (cov.liftHomotopy_lifts F Γ₀ hF₀) (s, t)
  have hL₀ (t : unitInterval) : L (0, t) = Γ₀ t :=
    cov.liftHomotopy_zero F Γ₀ hF₀ t
  have hDE : (fun s => L (s, 1)) = fun s => g₀⁻¹ • L (s, 0) := by
    refine cov.eq_of_comp_eq ?_ ?_ ?_ (0 : unitInterval) ?_
    · exact L.continuous.comp (continuous_id.prodMk continuous_const)
    · exact (continuous_const_smul g₀⁻¹).comp (L.continuous.comp (continuous_id.prodMk continuous_const))
    · funext s
      change vacuumQuaternionProjection a (L (s, 1)) = vacuumQuaternionProjection a (g₀⁻¹ • L (s, 0))
      rw [hL, vacuumQuaternionProjection_smul, hL, hb]
    · rw [hL₀, hL₀, hΓ₀zero]
      exact hΓ₀one
  let w := L (1, 0)
  have hw : vacuumQuaternionProjection a w = f₁ nativeCircleLoopBase :=
    (hL 1 0).trans ((hF₁ 0).trans (nativeCircleLoop f₁).source)
  let Γ₁ : C(unitInterval, Sphere3) :=
    ⟨fun t => L (1, t), L.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hΓ₁ (t : unitInterval) : vacuumQuaternionProjection a (Γ₁ t) = nativeCircleLoop f₁ t :=
    (hL 1 t).trans (hF₁ t)
  have hWord : nativeVacuumLoopWord a f₁ w hw = g₀ := by
    apply inv_injective
    apply IsCancelSMul.right_cancel' _ _ w
    rw [← nativeVacuumLoop_lift_end a f₁ w hw Γ₁ rfl hΓ₁]
    exact congrFun hDE 1
  rw [show nativeVacuumLoopWord a f₀ v₀ hv₀ = nativeVacuumLoopWord a f₁ w hw from hWord.symm]
  exact nativeVacuumLoopWord_isConj_of_lifts a f₁ w v₁ hw hv₁

private def tailParameter : C(unitInterval × unitInterval, unitInterval) := by
  let f (p : unitInterval × unitInterval) := p.1.val + (1 - p.1.val) * p.2.val
  have hf (p : unitInterval × unitInterval) : f p ∈ unitInterval := by
    have hs : 0 ≤ 1 - p.1.val := sub_nonneg.mpr p.1.property.2
    refine ⟨add_nonneg p.1.property.1 (mul_nonneg hs p.2.property.1), ?_⟩
    change p.1.val + (1 - p.1.val) * p.2.val ≤ 1
    linarith [mul_le_mul_of_nonneg_left p.2.property.2 hs]
  have hfcts : Continuous f := by dsimp only [f]; fun_prop
  exact ⟨fun p => ⟨f p, hf p⟩, hfcts.subtype_mk hf⟩

private def pathTail {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    (s : unitInterval) : Path (p s) y :=
  { toContinuousMap := ⟨fun t => p (tailParameter (s, t)),
      p.continuous.comp (tailParameter.continuous.comp (continuous_const.prodMk continuous_id))⟩
    source' := by
      change p (tailParameter (s, 0)) = p s
      congr 1
      apply Subtype.ext
      change s.val + (1 - s.val) * 0 = s.val
      ring
    target' := by
      change p (tailParameter (s, 1)) = y
      have hp : tailParameter (s, 1) = 1 := by
        apply Subtype.ext
        change s.val + (1 - s.val) * 1 = 1
        ring
      rw [hp, p.target] }

private theorem pathTail_zero {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    (t : unitInterval) : pathTail p 0 t = p t := by
  change p (tailParameter (0, t)) = p t
  congr 1
  apply Subtype.ext
  change 0 + (1 - 0) * t.val = t.val
  ring

private theorem pathTail_one {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    (t : unitInterval) : pathTail p 1 t = y := by
  have h : tailParameter (1, t) = 1 := by
    apply Subtype.ext
    change 1 + (1 - 1) * t.val = 1
    ring
  change p (tailParameter (1, t)) = y
  rw [h, p.target]

private def periodicPath {X : Type*} [TopologicalSpace X] (f : C(unitInterval, X)) : Prop :=
  f 0 = f 1

private def periodic_of_path_homotopy {X : Type*} [TopologicalSpace X] {x : X}
    {p q : Path x x} (H : p.Homotopy q) :
    p.toContinuousMap.HomotopyWith q.toContinuousMap periodicPath where
  toHomotopy := H.toHomotopy
  prop' := fun s => (Path.Homotopy.source H s).trans (Path.Homotopy.target H s).symm

private theorem path_conjugation_periodic_homotopy {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) (q : Path y y) :
    Nonempty ((p.trans (q.trans p.symm)).toContinuousMap.HomotopyWith q.toContinuousMap periodicPath) := by
  let Γ (s : unitInterval) : Path (p s) (p s) :=
    (pathTail p s).trans (q.trans (pathTail p s).symm)
  have hp : Continuous (fun z : unitInterval × unitInterval => pathTail p z.1 z.2) :=
    p.continuous.comp tailParameter.continuous
  have hq : Continuous (fun z : unitInterval × unitInterval => q z.2) :=
    q.continuous.comp continuous_snd
  have hΓ : Continuous (fun z : unitInterval × unitInterval => Γ z.1 z.2) :=
    Path.trans_continuous_family (pathTail p) hp _
      (Path.trans_continuous_family (fun _ : unitInterval => q) hq _
        (Path.symm_continuous_family (pathTail p) hp))
  let q' := (Path.refl y).trans (q.trans (Path.refl y))
  have h₀ : (pathTail p 0).cast p.source.symm rfl = p := by
    ext t
    exact pathTail_zero p t
  have h₁ : (pathTail p 1).cast p.target.symm rfl = Path.refl y := by
    ext t
    exact pathTail_one p t
  let H : (p.trans (q.trans p.symm)).toContinuousMap.HomotopyWith q'.toContinuousMap periodicPath :=
    { toHomotopy :=
        { toContinuousMap := ⟨fun z => Γ z.1 z.2, hΓ⟩
          map_zero_left := fun t => by
            change Γ 0 t = (p.trans (q.trans p.symm)) t
            have he : (Γ 0).cast p.source.symm p.source.symm = p.trans (q.trans p.symm) := by
              simp only [Γ, Path.cast_trans, Path.cast_symm, Path.cast_rfl_rfl, h₀]
            exact congrArg (fun l : Path x x => l t) he
          map_one_left := fun t => by
            change Γ 1 t = q' t
            have he : (Γ 1).cast p.target.symm p.target.symm = q' := by
              simp only [Γ, Path.cast_trans, Path.cast_symm, Path.cast_rfl_rfl, h₁, Path.refl_symm, q']
            exact congrArg (fun l : Path y y => l t) he }
      prop' := fun s => (Γ s).source.trans (Γ s).target.symm }
  have hlast : q'.Homotopic q :=
    (Path.Homotopic.refl_trans (q.trans (Path.refl y))).trans (Path.Homotopic.trans_refl q)
  obtain ⟨J⟩ := hlast
  exact ⟨H.trans (periodic_of_path_homotopy J)⟩

/-- A based path conjugation induces a free homotopy on the actual
native circle. -/
theorem nativeCircle_homotopic_of_path_conjugation {X : Type*} [TopologicalSpace X]
    {f g : C(NativeCircle, X)} (p : Path (f nativeCircleLoopBase) (g nativeCircleLoopBase))
    (h : (nativeCircleLoop f).Homotopic (p.trans ((nativeCircleLoop g).trans p.symm))) :
    f.Homotopic g := by
  obtain ⟨H⟩ := h
  obtain ⟨J⟩ := path_conjugation_periodic_homotopy p (nativeCircleLoop g)
  let K := (periodic_of_path_homotopy H).trans J
  exact nativeCircle_homotopic_of_periodic_square K.toHomotopy.toContinuousMap
    K.map_zero_left K.map_one_left K.prop'

/-- A based homotopy of the canonical circle paths gives a homotopy of
the original continuous circle maps. -/
theorem nativeCircle_homotopic_of_based_path_homotopy {X : Type*} [TopologicalSpace X]
    {f g : C(NativeCircle, X)} {x : X}
    (hf : x = f nativeCircleLoopBase) (hg : x = g nativeCircleLoopBase)
    (h : ((nativeCircleLoop f).cast hf hf).Homotopic ((nativeCircleLoop g).cast hg hg)) :
    f.Homotopic g := by
  obtain ⟨H⟩ := h
  let K := periodic_of_path_homotopy H
  exact nativeCircle_homotopic_of_periodic_square K.toHomotopy.toContinuousMap
    K.map_zero_left K.map_one_left K.prop'

private theorem nativeVacuumLoop_homotopic_of_eq_word (a : BulkCoefficients)
    {f₀ f₁ : C(NativeCircle, vacuum a)} (v₀ v₁ : Sphere3)
    (hv₀ : vacuumQuaternionProjection a v₀ = f₀ nativeCircleLoopBase)
    (hv₁ : vacuumQuaternionProjection a v₁ = f₁ nativeCircleLoopBase)
    (hw : nativeVacuumLoopWord a f₀ v₀ hv₀ = nativeVacuumLoopWord a f₁ v₁ hv₁) :
    f₀.Homotopic f₁ := by
  letI : SimplyConnectedSpace Sphere3 := simplyConnectedSpace_sphere3
  let g := nativeVacuumLoopWord a f₀ v₀ hv₀
  obtain ⟨Γ₀, hΓ₀zero, hΓ₀, hΓ₀one⟩ := exists_nativeVacuumLoop_lift a f₀ v₀ hv₀
  obtain ⟨Γ₁, hΓ₁zero, hΓ₁, hΓ₁one⟩ := exists_nativeVacuumLoop_lift a f₁ v₁ hv₁
  let p₀ : Path v₀ (g⁻¹ • v₀) := ⟨Γ₀, hΓ₀zero, hΓ₀one⟩
  let p₁ : Path v₁ (g⁻¹ • v₁) := ⟨Γ₁, hΓ₁zero, by
    change Γ₁ 1 = (nativeVacuumLoopWord a f₀ v₀ hv₀)⁻¹ • v₁
    rwa [hw]⟩
  let δ : Path v₀ v₁ := PathConnectedSpace.somePath v₀ v₁
  let Δ : Path (g⁻¹ • v₀) (g⁻¹ • v₁) := δ.map (continuous_const_smul g⁻¹)
  let aux := δ.trans (p₁.trans Δ.symm)
  obtain ⟨Hs⟩ := SimplyConnectedSpace.paths_homotopic p₀ aux
  let π : C(Sphere3, vacuum a) := ⟨vacuumQuaternionProjection a, continuous_vacuumQuaternionProjection a⟩
  let β : Path (π v₀) (π v₁) := δ.map π.continuous
  let r := nativeVacuumLoopPath a f₁ v₁ hv₁
  let m := β.trans (r.trans β.symm)
  have he₀ : π v₀ = π (g⁻¹ • v₀) := (vacuumQuaternionProjection_smul a g⁻¹ v₀).symm
  have he₁ : π v₁ = π (g⁻¹ • v₁) := (vacuumQuaternionProjection_smul a g⁻¹ v₁).symm
  have hmap₁ : (p₁.map π.continuous).cast rfl he₁ = r := by
    apply Path.ext
    funext t
    exact hΓ₁ t
  have hmapΔ : (Δ.map π.continuous).cast he₀ he₁ = β := by
    apply Path.ext
    funext t
    exact vacuumQuaternionProjection_smul a g⁻¹ (δ t)
  have haux : (aux.map π.continuous).cast rfl he₀ = m := by
    simp only [aux, Path.map_trans]
    rw [Path.cast_trans _ _ rfl rfl he₀, Path.cast_rfl_rfl, Path.cast_trans _ _ rfl he₁ he₀,
      ← Path.map_symm, Path.cast_symm, hmap₁, hmapΔ]
  let F : (nativeCircleLoop f₀).toContinuousMap.HomotopyWith m.toContinuousMap periodicPath :=
    { toHomotopy :=
        { toContinuousMap := π.comp Hs.toHomotopy.toContinuousMap
          map_zero_left := fun t => (congrArg π (Hs.toHomotopy.map_zero_left t)).trans (hΓ₀ t)
          map_one_left := fun t => (congrArg π (Hs.toHomotopy.map_one_left t)).trans
            (congrArg (fun p : Path (π v₀) (π v₀) => p t) haux) }
      prop' := fun s => by
        change π (Hs (s, 0)) = π (Hs (s, 1))
        rw [Path.Homotopy.source, Path.Homotopy.target]
        exact he₀ }
  obtain ⟨J⟩ := path_conjugation_periodic_homotopy β r
  let K := F.trans J
  exact nativeCircle_homotopic_of_periodic_square K.toHomotopy.toContinuousMap
    K.map_zero_left K.map_one_left K.prop'

/-- Free homotopy on the actual Euclidean circle is conjugacy of the based quaternion words. -/
theorem nativeVacuum_homotopic_iff_isConj (a : BulkCoefficients)
    (f₀ f₁ : C(NativeCircle, vacuum a)) (v₀ v₁ : Sphere3)
    (hv₀ : vacuumQuaternionProjection a v₀ = f₀ nativeCircleLoopBase)
    (hv₁ : vacuumQuaternionProjection a v₁ = f₁ nativeCircleLoopBase) :
    f₀.Homotopic f₁ ↔ IsConj (nativeVacuumLoopWord a f₀ v₀ hv₀) (nativeVacuumLoopWord a f₁ v₁ hv₁) := by
  constructor
  · rintro ⟨H⟩
    exact nativeVacuumLoopWord_isConj_of_homotopy a H v₀ v₁ hv₀ hv₁
  · intro h
    obtain ⟨k, hk⟩ := isConj_iff.mp h
    let w := k⁻¹ • v₁
    have hw : vacuumQuaternionProjection a w = f₁ nativeCircleLoopBase :=
      (vacuumQuaternionProjection_smul a k⁻¹ v₁).trans hv₁
    have hword : nativeVacuumLoopWord a f₁ w hw = nativeVacuumLoopWord a f₀ v₀ hv₀ := by
      calc
        _ = k⁻¹ * nativeVacuumLoopWord a f₁ v₁ hv₁ * (k⁻¹)⁻¹ :=
          nativeVacuumLoopWord_smul a f₁ v₁ hv₁ k⁻¹
        _ = _ := by rw [← hk]; group
    exact nativeVacuumLoop_homotopic_of_eq_word a v₀ w hv₀ hw hword.symm

/-- Every quaternion word is realized by a map on the native circle with the chosen base lift. -/
theorem exists_nativeVacuumLoopWord (a : BulkCoefficients) (v : Sphere3) (g : QuaternionGroup 2) :
    ∃ (f : C(NativeCircle, vacuum a))
      (hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase),
      nativeVacuumLoopWord a f v hv = g := by
  letI : SimplyConnectedSpace Sphere3 := simplyConnectedSpace_sphere3
  let Γ : Path v (g⁻¹ • v) := PathConnectedSpace.somePath v (g⁻¹ • v)
  let F : C(unitInterval × unitInterval, vacuum a) :=
    ⟨fun z => vacuumQuaternionProjection a (Γ z.2),
      (continuous_vacuumQuaternionProjection a).comp (Γ.continuous.comp continuous_snd)⟩
  have hper (s : unitInterval) : F (s, 0) = F (s, 1) := by
    change vacuumQuaternionProjection a (Γ 0) = vacuumQuaternionProjection a (Γ 1)
    rw [Γ.source, Γ.target, vacuumQuaternionProjection_smul]
  obtain ⟨H, hH⟩ := exists_nativeCircle_square_descent F hper
  let f : C(NativeCircle, vacuum a) :=
    H.comp ((ContinuousMap.const NativeCircle (0 : unitInterval)).prodMk (ContinuousMap.id NativeCircle))
  have hProj (t : unitInterval) : vacuumQuaternionProjection a (Γ t) = nativeCircleLoop f t :=
    (hH 0 t).symm
  have hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase := by
    rw [← nativeCircleLoopParam_zero]
    exact (congrArg (vacuumQuaternionProjection a) Γ.source).symm.trans (hProj 0)
  refine ⟨f, hv, ?_⟩
  have hEnd := nativeVacuumLoop_lift_end a f v hv Γ.toContinuousMap Γ.source hProj
  apply inv_injective
  apply IsCancelSMul.right_cancel' _ _ v
  exact hEnd.symm.trans Γ.target

theorem nativeVacuumLoopWord_const (a : BulkCoefficients) (v : Sphere3) (A : vacuum a)
    (hv : vacuumQuaternionProjection a v = A) :
    nativeVacuumLoopWord a (ContinuousMap.const NativeCircle A) v hv = 1 := by
  let Γ := ContinuousMap.const unitInterval v
  have hProj (t : unitInterval) : vacuumQuaternionProjection a (Γ t) =
      nativeCircleLoop (ContinuousMap.const NativeCircle A) t := hv
  have hEnd := nativeVacuumLoop_lift_end a (ContinuousMap.const NativeCircle A) v hv Γ rfl hProj
  change v = (nativeVacuumLoopWord a (ContinuousMap.const NativeCircle A) v hv)⁻¹ • v at hEnd
  apply inv_injective
  apply IsCancelSMul.right_cancel' _ _ v
  simpa only [inv_one, one_smul] using hEnd.symm

/-- Null homotopy at the native circle base is the identity-word condition. -/
theorem nativeVacuum_homotopic_const_iff (a : BulkCoefficients) (f : C(NativeCircle, vacuum a))
    (v : Sphere3) (hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase) :
    f.Homotopic (ContinuousMap.const NativeCircle (f nativeCircleLoopBase)) ↔
      nativeVacuumLoopWord a f v hv = 1 := by
  rw [nativeVacuum_homotopic_iff_isConj a f (ContinuousMap.const NativeCircle (f nativeCircleLoopBase)) v v hv hv,
    nativeVacuumLoopWord_const, isConj_one_left]

end Thesis

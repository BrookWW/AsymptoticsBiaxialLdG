module

public import Thesis.Variational.FlatWallWeakHessianCutoff
import Thesis.Upstream.TangentialWeakPartialGluing

/-! Reflection of the flat strong equation with the actual weak Hessian columns. -/

public section

noncomputable section

open Filter Function HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Topology

namespace Thesis

private theorem flatReflectionSign_mul_self (i : Fin 3) : flatReflectionSign i*flatReflectionSign i=1 := by
  by_cases hi : i=2 <;> simp [flatReflectionSign,hi]

private theorem flatReflectionSign_abs (i : Fin 3) : |flatReflectionSign i|=1 := by
  by_cases hi : i=2 <;> simp [flatReflectionSign,hi]

private theorem flatReflectionSign_pair_mul_self (i j : Fin 3) :
    (flatReflectionSign i*flatReflectionSign j)*(flatReflectionSign i*flatReflectionSign j)=1 := by
  calc
    _ = (flatReflectionSign i*flatReflectionSign i)*(flatReflectionSign j*flatReflectionSign j) := by ring
    _ = _ := by rw [flatReflectionSign_mul_self,flatReflectionSign_mul_self,one_mul]

private theorem reflected_mem_upper_iff_lower (x : Point) :
    normalReflection x ∈ upperCoordinateHalfSpace.val ↔ x ∈ negativeWallHalf := by
  change 0 < normalReflection x 2 ↔ x 2 < 0
  rw [normalReflection_height,neg_pos]

private theorem hasCompactSupport_indicator_subset {E : Type*} [Zero E]
    {f : Point → E} (hf : HasCompactSupport f) (S : Set Point) : HasCompactSupport (S.indicator f) := by
  apply hf.mono
  intro x hx
  by_contra h
  have hz := Function.notMem_support.mp h
  exact hx (by by_cases hxS : x ∈ S <;> simp [hxS,hz])

/-- The forcing changes sign with the odd field. -/
@[expose] def oddFlatWeakForcing {q : ℕ} (f : Point → Ambient q) (x : Point) : Ambient q :=
  upperCoordinateHalfSpace.val.indicator f x-upperCoordinateHalfSpace.val.indicator f (normalReflection x)

/-- A coefficient of the Hessian changes sign for each reflected normal index. -/
@[expose] def reflectedFlatWeakHessianCoefficient (a : Fin 3 → Fin 3 → Point → ℝ)
    (i j : Fin 3) (x : Point) : ℝ :=
  upperCoordinateHalfSpace.val.indicator (a i j) x+
    flatReflectionSign i*flatReflectionSign j*upperCoordinateHalfSpace.val.indicator (a i j) (normalReflection x)

theorem oddFlatWeakForcing_memLp {q : ℕ} {f : Point → Ambient q} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict upperCoordinateHalfSpace.val)) : MemLp (oddFlatWeakForcing f) p volume := by
  have hI := (memLp_indicator_iff_restrict upperCoordinateHalfSpace.property.measurableSet).2 hf
  exact hI.sub (hI.comp_measurePreserving normalReflection.measurePreserving)

theorem oddFlatWeakForcing_hasCompactSupport {q : ℕ} {f : Point → Ambient q}
    (hf : HasCompactSupport f) : HasCompactSupport (oddFlatWeakForcing f) := by
  have hI := hasCompactSupport_indicator_subset hf upperCoordinateHalfSpace.val
  exact hI.sub (hI.comp_homeomorph normalReflection.toHomeomorph)

theorem reflectedFlatWeakHessianCoefficient_measurable {a : Fin 3 → Fin 3 → Point → ℝ}
    (i j : Fin 3) (h : AEStronglyMeasurable (a i j) (volume.restrict upperCoordinateHalfSpace.val)) :
    AEStronglyMeasurable (reflectedFlatWeakHessianCoefficient a i j) (volume : Measure Point) := by
  have hI := (aestronglyMeasurable_indicator_iff upperCoordinateHalfSpace.property.measurableSet).2 h
  exact hI.add ((hI.comp_quasiMeasurePreserving normalReflection.measurePreserving.quasiMeasurePreserving).const_mul _)

theorem reflectedFlatWeakHessianCoefficient_hasCompactSupport {a : Fin 3 → Fin 3 → Point → ℝ}
    (i j : Fin 3) (h : HasCompactSupport (a i j)) : HasCompactSupport (reflectedFlatWeakHessianCoefficient a i j) := by
  have hI := hasCompactSupport_indicator_subset h upperCoordinateHalfSpace.val
  exact hI.add (hI.comp_homeomorph normalReflection.toHomeomorph).mul_left

theorem oddFlatWeakForcing_eq_upper {q : ℕ} (f : Point → Ambient q) {x : Point}
    (hx : x ∈ upperCoordinateHalfSpace.val) : oddFlatWeakForcing f x = f x := by
  have hR : normalReflection x ∉ upperCoordinateHalfSpace.val :=
    fun h => lt_asymm (show 0 < x 2 from hx) ((reflected_mem_upper_iff_lower x).1 h)
  simp only [oddFlatWeakForcing,indicator_of_mem hx,indicator_of_notMem hR,sub_zero]

theorem oddFlatWeakForcing_eq_lower {q : ℕ} (f : Point → Ambient q) {x : Point}
    (hx : x ∈ negativeWallHalf) : oddFlatWeakForcing f x = -f (normalReflection x) := by
  have hxN : x ∉ upperCoordinateHalfSpace.val := fun h => lt_asymm (show x 2 < 0 from hx) h
  have hR := (reflected_mem_upper_iff_lower x).2 hx
  simp only [oddFlatWeakForcing,indicator_of_mem hR,indicator_of_notMem hxN,zero_sub]

theorem reflectedFlatWeakHessianCoefficient_eq_upper (a : Fin 3 → Fin 3 → Point → ℝ)
    (i j : Fin 3) {x : Point} (hx : x ∈ upperCoordinateHalfSpace.val) :
    reflectedFlatWeakHessianCoefficient a i j x = a i j x := by
  have hR : normalReflection x ∉ upperCoordinateHalfSpace.val :=
    fun h => lt_asymm (show 0 < x 2 from hx) ((reflected_mem_upper_iff_lower x).1 h)
  simp only [reflectedFlatWeakHessianCoefficient,indicator_of_mem hx,indicator_of_notMem hR,mul_zero,add_zero]

theorem reflectedFlatWeakHessianCoefficient_eq_lower (a : Fin 3 → Fin 3 → Point → ℝ)
    (i j : Fin 3) {x : Point} (hx : x ∈ negativeWallHalf) :
    reflectedFlatWeakHessianCoefficient a i j x =
      flatReflectionSign i*flatReflectionSign j*a i j (normalReflection x) := by
  have hxN : x ∉ upperCoordinateHalfSpace.val := fun h => lt_asymm (show x 2 < 0 from hx) h
  have hR := (reflected_mem_upper_iff_lower x).2 hx
  simp only [reflectedFlatWeakHessianCoefficient,indicator_of_mem hR,indicator_of_notMem hxN,zero_add]

/-- The whole-space coefficients retain the original smallness threshold. -/
theorem abs_reflectedFlatWeakHessianCoefficient_le {a : Fin 3 → Fin 3 → Point → ℝ}
    {δ : ℝ} (hδ : 0 ≤ δ) (hA : ∀ i j x, x ∈ upperCoordinateHalfSpace.val → |a i j x| ≤ δ)
    (i j : Fin 3) (x : Point) : |reflectedFlatWeakHessianCoefficient a i j x| ≤ δ := by
  rcases lt_trichotomy (x 2) (0:ℝ) with h|h|h
  · rw [reflectedFlatWeakHessianCoefficient_eq_lower a i j (show x ∈ negativeWallHalf from h),abs_mul,abs_mul,
      flatReflectionSign_abs,flatReflectionSign_abs,one_mul,one_mul]
    exact hA i j (normalReflection x) ((reflected_mem_upper_iff_lower x).2 h)
  · have hN : x ∉ upperCoordinateHalfSpace.val := fun hx => h.not_gt hx
    have hR : normalReflection x ∉ upperCoordinateHalfSpace.val := fun hx =>
      h.not_lt ((reflected_mem_upper_iff_lower x).1 hx)
    simpa only [reflectedFlatWeakHessianCoefficient,indicator_of_notMem hN,indicator_of_notMem hR,
      mul_zero,add_zero,abs_zero] using hδ
  · rw [reflectedFlatWeakHessianCoefficient_eq_upper a i j (show x ∈ upperCoordinateHalfSpace.val from h)]
    exact hA i j x h

/-- The strong nondivergence equation reflects as an almost-everywhere whole-space identity. -/
theorem oddFlatWallWeakHessian_reflect_equation {q : ℕ}
    {J : Point → Fin 3 → HarmonicMaps.Gradient 3 q} {f : Point → Ambient q}
    {a : Fin 3 → Fin 3 → Point → ℝ}
    (hEq : (fun x => ∑ i : Fin 3, J x i i) =ᵐ[volume.restrict upperCoordinateHalfSpace.val]
      fun x => f x+∑ i : Fin 3, ∑ j : Fin 3, a i j x • J x i j) :
    (fun x => ∑ i : Fin 3, oddFlatWallWeakHessian J x i i) =ᵐ[(volume : Measure Point)]
      fun x => oddFlatWeakForcing f x+
        ∑ i : Fin 3, ∑ j : Fin 3, reflectedFlatWeakHessianCoefficient a i j x • oddFlatWallWeakHessian J x i j := by
  have hS := upperCoordinateHalfSpace.property.measurableSet
  have hPos := (ae_restrict_iff' hS).1 hEq
  have hNeg := normalReflection.measurePreserving.quasiMeasurePreserving.ae hPos
  have hN : ∀ᵐ x ∂(volume : Measure Point), x 2 ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff] using normal_plane_volume_zero
  filter_upwards [hPos,hNeg,hN] with x hxP hxN hx₀
  rcases lt_or_gt_of_ne hx₀ with hx|hx
  · have hxL : x ∈ negativeWallHalf := hx
    have hR : normalReflection x ∈ upperCoordinateHalfSpace.val := (reflected_mem_upper_iff_lower x).2 hxL
    change (∑ i : Fin 3, oddFlatWallWeakHessian J x i i) = oddFlatWeakForcing f x+
      ∑ i : Fin 3, ∑ j : Fin 3, reflectedFlatWeakHessianCoefficient a i j x • oddFlatWallWeakHessian J x i j
    have hLeft : (∑ i : Fin 3, oddFlatWallWeakHessian J x i i) = -(∑ i : Fin 3, J (normalReflection x) i i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [oddFlatWallWeakHessian_eq_lower J hxL,flatReflectionSign_mul_self,neg_one_smul]
    have hRight : (∑ i : Fin 3, ∑ j : Fin 3, reflectedFlatWeakHessianCoefficient a i j x •
        oddFlatWallWeakHessian J x i j) = -(∑ i : Fin 3, ∑ j : Fin 3, a i j (normalReflection x) •
          J (normalReflection x) i j) := by
      simp only [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [reflectedFlatWeakHessianCoefficient_eq_lower a i j hxL,oddFlatWallWeakHessian_eq_lower J hxL,
        smul_smul,← neg_smul]
      congr 2
      calc
        _ = -(((flatReflectionSign i*flatReflectionSign j)*(flatReflectionSign i*flatReflectionSign j))*
            a i j (normalReflection x)) := by ring
        _ = _ := by rw [flatReflectionSign_pair_mul_self,one_mul]
    rw [hLeft,hRight,oddFlatWeakForcing_eq_lower f hxL,← neg_add]
    exact congrArg Neg.neg (hxN hR)
  · have hxU : x ∈ upperCoordinateHalfSpace.val := hx
    change (∑ i : Fin 3, oddFlatWallWeakHessian J x i i) = oddFlatWeakForcing f x+
      ∑ i : Fin 3, ∑ j : Fin 3, reflectedFlatWeakHessianCoefficient a i j x • oddFlatWallWeakHessian J x i j
    simp only [oddFlatWallWeakHessian_eq_upper J hxU,oddFlatWeakForcing_eq_upper f hxU,
      reflectedFlatWeakHessianCoefficient_eq_upper a _ _ hxU]
    exact hxP hxU

/-- The odd forcing has the odd reflection of its actual tangential partial. -/
theorem oddFlatWeakForcing_weakTangentialPartial {q : ℕ} {f : Point → Ambient q}
    {D : Point → HarmonicMaps.Gradient 3 q} (hf : MemW12 upperCoordinateHalfSpace f D)
    {i : Fin 3} (hi : i ≠ 2) :
    IsWeakAmbientCoordinatePartial univ i (oddFlatWeakForcing f) (oddFlatWeakForcing (fun x => D x i)) := by
  let S := upperCoordinateHalfSpace
  let N : OpenDomain 3 := ⟨negativeWallHalf,isOpen_negativeWallHalf⟩
  have hfL : MemLp (oddFlatWeakForcing f) 2 (volume : Measure Point) := oddFlatWeakForcing_memLp hf.2.1
  have hDL : MemLp (oddFlatWeakForcing (fun x => D x i)) 2 (volume : Measure Point) :=
    oddFlatWeakForcing_memLp (hf.2.2 i)
  apply IsWeakAmbientCoordinatePartial.of_flat_open_sides hfL hDL hi
  · have hW : IsWeakAmbientCoordinatePartial S.val i f (fun x => D x i) := hf.1.2.2 i
    exact hW.congr_ae
      ((ae_restrict_mem S.property.measurableSet).mono fun _ hx => (oddFlatWeakForcing_eq_upper f hx).symm)
      ((ae_restrict_mem S.property.measurableSet).mono fun _ hx => (oddFlatWeakForcing_eq_upper (fun x => D x i) hx).symm)
  · have he : (⟨normalReflection ⁻¹' S.val,S.property.preimage normalReflection.continuous⟩ : OpenDomain 3) = N :=
      Subtype.ext (Set.ext fun x => reflected_mem_upper_iff_lower x)
    have h := memW12_normalReflection_preimage hf
    rw [he] at h
    have hW : IsWeakAmbientCoordinatePartial N.val i (f ∘ normalReflection) (fun x => D (normalReflection x) i) := by
      intro φ hφ hc hS
      simpa only [flatReflectionSign_tangential hi,one_smul] using h.1.2.2 i φ hφ hc hS
    exact hW.neg.congr_ae
      ((ae_restrict_mem N.property.measurableSet).mono fun _ hx => (oddFlatWeakForcing_eq_lower f hx).symm)
      ((ae_restrict_mem N.property.measurableSet).mono fun _ hx => (oddFlatWeakForcing_eq_lower (fun x => D x i) hx).symm)

/-- Reflection preserves a tangential Lipschitz bound on each coefficient,
including values represented on the null wall. -/
theorem abs_ambientDifferenceQuotient_reflectedFlatWeakHessianCoefficient_le
    {a : Fin 3 → Fin 3 → Point → ℝ} (i j : Fin 3) {k : Fin 3} (hk : k ≠ 2)
    {K : ℝ≥0} (hA : LipschitzOnWith K (a i j) upperCoordinateHalfSpace.val)
    (x : Point) (s : ℝ) : |ambientDifferenceQuotient k s (reflectedFlatWeakHessianCoefficient a i j) x| ≤ K := by
  let z := x+s • axis k
  have hz : z 2 = x 2 := by
    change x 2+s*(axis k) 2=x 2
    rw [show (axis k) 2=0 by simp [axis,Ne.symm hk],mul_zero,add_zero]
  have hDist : dist z x = |s| := by
    dsimp only [z]
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,show ‖axis k‖=1 by simp [axis],mul_one]
  let b := reflectedFlatWeakHessianCoefficient a i j
  have hDiff : |b z-b x| ≤ (K:ℝ)*|s| := by
    rcases lt_trichotomy (x 2) (0:ℝ) with hx | hx | hx
    · have hxn : x ∈ negativeWallHalf := hx
      have hzn : z ∈ negativeWallHalf := by change z 2 < 0; rwa [hz]
      have hX := (reflected_mem_upper_iff_lower x).2 hxn
      have hZ := (reflected_mem_upper_iff_lower z).2 hzn
      have hH := hA.dist_le_mul (normalReflection z) hZ (normalReflection x) hX
      rw [normalReflection.isometry.dist_eq, hDist,Real.dist_eq] at hH
      dsimp only [b]
      rw [reflectedFlatWeakHessianCoefficient_eq_lower a i j hzn,reflectedFlatWeakHessianCoefficient_eq_lower a i j hxn,
        ← mul_sub,abs_mul,abs_mul,flatReflectionSign_abs,flatReflectionSign_abs,one_mul,one_mul]
      exact hH
    · have hwall (y : Point) (hy : y 2 = 0) : b y=0 := by
        have hN : y ∉ upperCoordinateHalfSpace.val := fun h => hy.not_gt h
        have hR : normalReflection y ∉ upperCoordinateHalfSpace.val :=
          fun h => hy.not_lt ((reflected_mem_upper_iff_lower y).1 h)
        simp only [b,reflectedFlatWeakHessianCoefficient,indicator_of_notMem hN,indicator_of_notMem hR,mul_zero,add_zero]
      rw [hwall z (hz.trans hx),hwall x hx,sub_zero,abs_zero]
      positivity
    · have hxU : x ∈ upperCoordinateHalfSpace.val := hx
      have hzU : z ∈ upperCoordinateHalfSpace.val := by change 0 < z 2; rwa [hz]
      have hh := hA.dist_le_mul z hzU x hxU
      rw [hDist,Real.dist_eq] at hh
      dsimp only [b]
      rw [reflectedFlatWeakHessianCoefficient_eq_upper a i j hzU,reflectedFlatWeakHessianCoefficient_eq_upper a i j hxU]
      exact hh
  change |s⁻¹*(b z-b x)| ≤ (K:ℝ)
  rw [abs_mul,abs_inv]
  by_cases hs : s=0
  · simp [hs]
  refine (mul_le_mul_of_nonneg_left hDiff (inv_nonneg.mpr (abs_nonneg s))).trans_eq ?_
  rw [mul_comm (K:ℝ),← mul_assoc,inv_mul_cancel₀ (abs_ne_zero.mpr hs),one_mul]

end Thesis

end

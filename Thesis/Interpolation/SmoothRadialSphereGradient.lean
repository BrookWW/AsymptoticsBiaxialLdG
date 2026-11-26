module

public import StratificationTheory.Frozen.SphereGradientCharacterization
import StratificationTheory.Foundation.AngularL2Membership
import HolderToCK.Analysis.ClassicalWeakGradient
import HarmonicMaps.SobolevRestriction

/-! The native tangential gradient of a smooth degree-zero radial field. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff

namespace Thesis

theorem fderiv_degreeZero_smul_eq {n q : ℕ} {f : Domain n → Ambient q}
    (hF : ContDiffOn ℝ ∞ f ({0}ᶜ : Set (Domain n)))
    (hRay : ∀ r : ℝ, 0 < r → ∀ x : Domain n, f (r • x) = f x)
    {x : Domain n} (hx : x ≠ 0) (r : ℝ) (hr : 0 < r) (v : Domain n) :
    r • fderiv ℝ f (r • x) v = fderiv ℝ f x v := by
  let A : Domain n →L[ℝ] Domain n := r • ContinuousLinearMap.id ℝ _
  have hAp (y : Domain n) : A y = r • y := rfl
  have hOuter : DifferentiableAt ℝ f (A x) :=
    ((hF (A x) (by rw [hAp]; exact smul_ne_zero hr.ne' hx)).contDiffAt
      (isOpen_compl_singleton.mem_nhds (by rw [hAp]; exact smul_ne_zero hr.ne' hx))).differentiableAt (by simp)
  have hComp := hOuter.hasFDerivAt.comp x A.hasFDerivAt
  have hEq : (f ∘ A) = f := funext fun y => hRay r hr y
  rw [hEq] at hComp
  have hD := congrArg (fun L : Domain n →L[ℝ] Ambient q => L v) hComp.fderiv
  change fderiv ℝ f x v = fderiv ℝ f (A x) (A v) at hD
  rw [hAp x, hAp v, map_smul] at hD
  exact hD.symm

/-- Smooth degree-zero data on the punctured space restrict to the native
unit sphere with the original derivative columns at unit radius. -/
theorem exists_memSphereW12_of_smooth_degreeZero {n q : ℕ} (hn : 2 ≤ n)
    {f : Domain n → Ambient q} (hF : ContDiffOn ℝ ∞ f ({0}ᶜ : Set (Domain n)))
    (hRay : ∀ r : ℝ, 0 < r → ∀ x : Domain n, f (r • x) = f x) :
    ∃ hu : MemSphereW12 hn (fun θ : sphere (0 : Domain n) 1 => f θ.val),
      ∀ i : Fin n,
        (fun θ : sphere (0 : Domain n) 1 =>
          (sphereGradient hn (fun θ : sphere (0 : Domain n) 1 => f θ.val) hu i) θ) =ᵐ[
            Measure.euclideanHausdorffMeasure (n - 1)]
          fun θ => fderiv ℝ f θ.val (EuclideanSpace.single i 1) := by
  let U : OpenDomain n := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let W : OpenDomain n := ⟨{x : Domain n | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2},
    isOpen_Ioo.preimage continuous_norm⟩
  let K := closedBall (0 : Domain n) 2 \ ball 0 (1 / 2)
  let D : Domain n → HarmonicMaps.Gradient n q := fun x i => fderiv ℝ f x (EuclideanSpace.single i 1)
  have hK : IsCompact K := (isCompact_closedBall _ _).diff isOpen_ball
  have hKW : W.val ⊆ K := by
    intro x hx
    refine ⟨?_, ?_⟩
    · simpa only [mem_closedBall, dist_zero_right] using hx.2.le
    · simpa only [mem_ball, dist_zero_right, not_lt] using hx.1.le
  have hKU : K ⊆ U.val := fun x hx h => hx.2 (by
    rw [show x = 0 from h]
    exact mem_ball_self (by norm_num))
  have hS : sphere (0 : Domain n) 1 ⊆ W.val := by
    intro x hx
    have h := mem_sphere_zero_iff_norm.mp hx
    change (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2
    rw [h]
    norm_num
  have hLoc : MemW12Loc U f D := HolderToCK.memW12Loc_of_contDiffOn_one U (hF.of_le (by simp))
  have hW : MemW12 W f D := by
    refine ⟨(hLoc.mono (hKW.trans hKU)).1, ?_, ?_⟩
    · exact (hLoc.2.1 K hK hKU).mono_measure (Measure.restrict_mono_set _ hKW)
    · intro i
      exact (hLoc.2.2 i K hK hKU).mono_measure (Measure.restrict_mono_set _ hKW)
  let σ : Measure (sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere (by omega : 0 < n)]
    infer_instance
  letI : CompactSpace (sphere (0 : Domain n) 1) := isCompact_iff_compactSpace.1 (isCompact_sphere _ _)
  have hLpRestrict {g : Domain n → Ambient q} (hg : ContinuousOn g U.val) :
      MemLp (fun θ : sphere (0 : Domain n) 1 => g θ.val) 2 σ := by
    have hc : Continuous (fun θ : sphere (0 : Domain n) 1 => g θ.val) :=
      (hg.mono (hS.trans (hKW.trans hKU))).restrict
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    exact MemLp.of_bound hc.aestronglyMeasurable B (ae_of_all _ fun θ => hB θ (mem_univ _))
  let u : sphere (0 : Domain n) 1 → Ambient q := fun θ => f θ.val
  have hU : MemSphereW12 hn u := ⟨hLpRestrict hF.continuousOn, W, hS,
    fun h => (hKU (hKW h)) rfl, f, D, hW, fun r θ _ => hRay r.val r.property θ.val⟩
  have hLp (i : Fin n) : MemLp (fun θ : sphere (0 : Domain n) 1 => D θ.val i) 2 σ :=
    hLpRestrict ((hF.continuousOn_fderiv_of_isOpen U.property (by simp)).clm_apply continuousOn_const)
  let G (i : Fin n) : Lp (Ambient q) 2 σ := (hLp i).toLp (fun θ => D θ.val i)
  have hG : G = sphereGradient hn u hU := by
    apply (sphereGradient_characterization hn u hU).2.1 G
    refine ⟨f, D, hLoc, fun r θ => hRay r.val r.property θ.val, fun r i => ?_⟩
    filter_upwards [(hLp i).coeFn_toLp] with θ hθ
    have hNe : θ.val ≠ 0 := by
      have h := mem_sphere_zero_iff_norm.mp θ.property
      intro h0
      rw [h0, norm_zero] at h
      exact zero_ne_one h
    change r.val • D (r.val • θ.val) i = G i θ
    rw [hθ]
    exact fderiv_degreeZero_smul_eq hF hRay hNe r.val r.property _
  refine ⟨hU, fun i => ?_⟩
  rw [← hG]
  exact (hLp i).coeFn_toLp

end Thesis

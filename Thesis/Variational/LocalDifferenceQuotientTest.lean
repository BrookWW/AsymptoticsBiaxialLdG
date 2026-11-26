module

public import Thesis.Variational.DirichletDifferenceQuotientEstimate
import Thesis.Interpolation.ConvexZeroTrace

/-! Actual zero-boundary tangential tests in a ball or a flattened half-ball. -/

public section

noncomputable section

open Function HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace Thesis

theorem norm_smul_euclideanAxis_eq_abs {n : ℕ} (i : Fin n) (h : ℝ) :
    ‖h • (EuclideanSpace.single i (1 : ℝ) : Domain n)‖ = |h| := by
  simp only [norm_smul,Real.norm_eq_abs,PiLp.norm_single,norm_one,mul_one]

theorem mem_ball_add_scaled_axis {n : ℕ} {a x : Domain n} {R : ℝ}
    (hx : x ∈ closedBall a (R/2)) (i : Fin n) {h : ℝ} (hh : |h| < R/2) :
    x+h • EuclideanSpace.single i 1 ∈ ball a R := by
  apply mem_ball.mpr
  rw [dist_eq_norm,show x+h • EuclideanSpace.single i 1-a =
    (x-a)+h • EuclideanSpace.single i 1 by abel]
  have h0 : ‖x-a‖ ≤ R/2 := by simpa only [mem_closedBall,dist_eq_norm] using hx
  exact (norm_add_le _ _).trans_lt (by rw [norm_smul_euclideanAxis_eq_abs]; linarith only [h0,hh])

/-- The test obtained by taking the backward difference of the localized
forward difference has the intrinsic zero trace on the actual ball part.
For a half-ball only the directions preserving the flat side are used. -/
theorem zeroBoundary_differenceQuotient_test_in_ball_part {n q : ℕ}
    {a : Domain n} {R : ℝ} (hR : 0 < R) (S : OpenDomain n)
    (hConvex : Convex ℝ S.val) (hn : (ball a R ∩ S.val).Nonempty)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχSupp : tsupport χ ⊆ closedBall a (R/2))
    {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hu : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) u D)
    (hZero : ∀ x ∈ ball a R, x ∉ S.val → u x = 0 ∧ D x = 0)
    (i : Fin n) (h : ℝ) (hh : |h| < R/2)
    (hStay : ∀ x : Domain n, ∀ t : ℝ, x+t • EuclideanSpace.single i 1 ∈ S.val ↔ x ∈ S.val) :
    let V : OpenDomain n := ⟨ball a R ∩ S.val,isOpen_ball.inter S.property⟩
    let w := ambientDifferenceQuotient i (-h) (differenceQuotientTestValue χ i h u)
    let G (x : Domain n) (j : Fin n) :=
      ambientDifferenceQuotient i (-h) (fun y => differenceQuotientTestColumns χ i h u D y j) x
    HasZeroBoundaryValues V w G ∧ (∀ x ∉ V.val, w x = 0 ∧ G x = 0) := by
  intro V w G
  let u₁ := differenceQuotientTestValue χ i h u
  let D₁ := differenceQuotientTestColumns χ i h u D
  have hOffχ (x : Domain n) (hx : χ x = 0) : u₁ x = 0 ∧ D₁ x = 0 := by
    refine ⟨?_,funext fun j => ?_⟩
    · simp only [u₁,differenceQuotientTestValue,hx,zero_pow (by decide : 2 ≠ 0),zero_smul]
    · simp only [D₁,differenceQuotientTestColumns,hx,mul_zero,zero_mul,zero_pow (by decide : 2 ≠ 0),
        zero_smul,add_zero,Pi.zero_apply]
  have hOffClosed (x : Domain n) (hx : x ∉ closedBall a (R/2)) : u₁ x = 0 ∧ D₁ x = 0 :=
    hOffχ x (image_eq_zero_of_notMem_tsupport (fun h => hx (hχSupp h)))
  have hOffS (x : Domain n) (hx : x ∉ S.val) : u₁ x = 0 ∧ D₁ x = 0 := by
    by_cases hIn : x ∈ closedBall a (R/2)
    · have hX := hZero x (closedBall_subset_ball (half_lt_self hR) hIn) hx
      have hShift := hZero (x+h • EuclideanSpace.single i 1) (mem_ball_add_scaled_axis hIn i hh)
        (fun hx' => hx ((hStay x h).mp hx'))
      refine ⟨?_,funext fun j => ?_⟩
      · simp only [u₁,differenceQuotientTestValue,ambientDifferenceQuotient,hX.1,hShift.1,
          sub_self,smul_zero]
      · simp only [D₁,differenceQuotientTestColumns,ambientDifferenceQuotient,hX.1,hShift.1,
          hX.2,hShift.2,Pi.zero_apply,sub_self,smul_zero,add_zero]
    · exact hOffClosed x hIn
  have hOff (x : Domain n) (hx : x ∉ V.val) : w x = 0 ∧ G x = 0 := by
    have hx' : x ∉ ball a R ∨ x ∉ S.val := by
      by_cases hIn : x ∈ ball a R
      · exact Or.inr (fun hS => hx ⟨hIn,hS⟩)
      · exact Or.inl hIn
    have hx₁ : u₁ x = 0 ∧ D₁ x = 0 := hx'.elim
      (fun h => hOffClosed x (fun hk => h (closedBall_subset_ball (half_lt_self hR) hk))) (hOffS x)
    have hx₂ : u₁ (x + (-h) • EuclideanSpace.single i 1) = 0 ∧
        D₁ (x + (-h) • EuclideanSpace.single i 1) = 0 := by
      rcases hx' with hOut | hS
      · apply hOffClosed
        intro hy
        have hrev : x+(-h) • EuclideanSpace.single i 1+h • EuclideanSpace.single i 1 = x := by
          rw [neg_smul,add_assoc,neg_add_cancel,add_zero]
        exact hOut (hrev ▸ mem_ball_add_scaled_axis hy i hh)
      · exact hOffS _ (fun he => hS ((hStay x (-h)).mp he))
    refine ⟨?_,funext fun j => ?_⟩
    · simp only [w,ambientDifferenceQuotient,show differenceQuotientTestValue χ i h u = u₁ from rfl,
        hx₁.1,hx₂.1,sub_self,smul_zero]
    · simp only [G,ambientDifferenceQuotient,show differenceQuotientTestColumns χ i h u D = D₁ from rfl,
        hx₁.2,hx₂.2,Pi.zero_apply,sub_self,smul_zero]
  have hWide : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) w G :=
    memW12_differenceQuotient_univ (memW12_differenceQuotientTest hχ hcχ hu i h) i (-h)
  have hμ : (volume : Measure (Domain n)).restrict V.val ≤ volume.restrict (univ : Set (Domain n)) :=
    Measure.restrict_mono_set _ (subset_univ _)
  have hCut : MemW12 V w G :=
    ⟨hWide.1.mono (subset_univ _),hWide.2.1.mono_measure hμ,fun j => (hWide.2.2 j).mono_measure hμ⟩
  have hValue : V.val.indicator w = w := indicator_eq_self.mpr
    (fun x hx => of_not_not fun h => hx (hOff x h).1)
  have hGrad : V.val.indicator G = G := indicator_eq_self.mpr
    (fun x hx => of_not_not fun h => hx (hOff x h).2)
  have hZ : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) (V.val.indicator w) (V.val.indicator G) := by
    rw [hValue,hGrad]
    exact hWide
  have hK : IsCompact (closure V.val) :=
    (isBounded_ball.subset (show V.val ⊆ ball a R from inter_subset_left)).isCompact_closure
  obtain ⟨z,hz⟩ := hn
  exact ⟨hasZeroBoundaryValues_of_convex_zeroExtension V ((convex_ball a R).inter hConvex)
    hK hz hCut hZ,hOff⟩

end Thesis

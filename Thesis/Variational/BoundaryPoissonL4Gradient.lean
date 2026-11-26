module

public import Thesis.External.BoundaryPoisson
import Thesis.Variational.BoundaryL4CapValue
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! The native local scalar (L^4) gradient estimate on the actual smooth wall. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace Thesis

private theorem eLpNorm_toReal_mono_measure_of_mem {X E : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] {μ ν : Measure X}
    {p : ℝ≥0∞} {f : X → E} (hf : MemLp f p ν) (hμν : μ ≤ ν) :
    (eLpNorm f p μ).toReal ≤ (eLpNorm f p ν).toReal :=
  ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure _ hμν)

/-- An interior point has an inscribed ball reaching a nearest point of the wall. -/
theorem exists_interior_ball_nearest_wall
    {U : Set Point} (hU : IsOpen U) (hNC : (Uᶜ : Set Point).Nonempty) {x : Point}
    (hx : x ∈ U) :
    ∃ p ∈ frontier U, 0 < dist x p ∧ ball x (dist x p) ⊆ U := by
  have hd₀ : 0 < infDist x Uᶜ :=
    (hU.isClosed_compl.notMem_iff_infDist_pos hNC).1 (fun h => h hx)
  obtain ⟨p,hp,hd⟩ := hU.isClosed_compl.exists_infDist_eq_dist hNC x
  rw [hd] at hd₀
  have hBall : ball x (dist x p) ⊆ U := hd ▸ ball_infDist_compl_subset
  have hpC : p ∈ closure U := by
    have h1 : p ∈ closedBall x (dist x p) := by rw [mem_closedBall,dist_comm]
    rw [← closure_ball _ hd₀.ne'] at h1
    exact closure_mono hBall h1
  have hpF : p ∈ frontier U := by rw [frontier,hU.interior_eq]; exact ⟨hpC,hp⟩
  exact ⟨p,hpF,hd₀,hBall⟩

/-- The zero-trace scalar boundary gradient estimate at exponent four,
including the within derivative at every point of the actual closed inner cap. -/
theorem zeroTraceBoundaryPoissonL4GradientEstimate : External.ZeroTraceBoundaryPoissonL4GradientEstimate := by
  intro U hU
  obtain ⟨R,A,CB,hR,hA,hCB,hWall⟩ := hU.exists_localBoundaryL4_value_bound
  obtain ⟨CI,hCI,hInter⟩ := exists_scalar_interiorPoissonL4_gradient_bounds
  let t := (32*A)⁻¹
  have ht : 0 < t := inv_pos.mpr (by positivity)
  have ht₁ : t ≤ 1 := by
    dsimp only [t]
    exact inv_le_one_of_one_le₀ (by linarith only [hA])
  let M := (32 : ℝ) ^ (3/2 : ℝ)
  have hM : 0 ≤ M := Real.rpow_nonneg (by norm_num) _
  let Λ := CI*(4*CB+M+2)
  let C := Λ*(t^(-3/2:ℝ)+t^(1/4:ℝ))
  have hΛ : 0 < Λ := by dsimp only [Λ]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨R,C,hR,hC,?_⟩
  intro c hc r hr u f E K hu hTrace hLap hDu hf
  have hr₀ : 0 < r := hr.1
  let W := U∩ball c (r/2)
  let s := t*r
  have hs : 0 < s := mul_pos ht hr.1
  have hsr : s ≤ r := mul_le_of_le_one_left hr.1.le ht₁
  have hsA : A*s = r/32 := by
    dsimp only [s,t]
    field_simp
  let F := (eLpNorm f 4 (volume.restrict E)).toReal
  let G := (eLpNorm (fderiv ℝ u) 2 (volume.restrict E)).toReal
  let J := s^(-3/2:ℝ)*G+s^(1/4:ℝ)*F
  let B := r^(-3/2:ℝ)*G+r^(1/4:ℝ)*F
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hJb : J ≤ (t^(-3/2:ℝ)+t^(1/4:ℝ))*B := by
    dsimp only [J,s,B]
    rw [Real.mul_rpow ht.le hr.1.le,Real.mul_rpow ht.le hr.1.le]
    have h₁ := mul_nonneg (Real.rpow_nonneg ht.le (-3/2:ℝ))
      (mul_nonneg (Real.rpow_nonneg hr.1.le (1/4:ℝ)) hF)
    have h₂ := mul_nonneg (Real.rpow_nonneg ht.le (1/4:ℝ))
      (mul_nonneg (Real.rpow_nonneg hr.1.le (-3/2:ℝ)) hG)
    nlinarith only [h₁,h₂]
  have hcN : c ∉ U := fun h => disjoint_left.1 ((disjoint_frontier_iff_isOpen).2 hU.1.1) hc h
  have hOn (x : Point) (hx : x ∈ W) : ‖fderiv ℝ u x‖ ≤ Λ*J := by
    obtain ⟨p,hp,hd,hBall⟩ := exists_interior_ball_nearest_wall hU.1.1 ⟨c,hcN⟩ hx.1
    let d := dist x p
    change 0 < d at hd
    by_cases hNear : d < s/16
    · have hpCap : ball p (A*s) ⊆ ball c r := by
        intro y hy
        have hpc := dist_triangle p x c
        rw [dist_comm p x] at hpc
        have hyd := mem_ball.1 hy
        rw [hsA] at hyd
        exact mem_ball.2 (by linarith only [dist_triangle y p c, hpc, hyd,hNear,hsr,mem_ball.1 hx.2,hr.1])
      let E₁ := U∩ball p (A*s)
      let K₁ := closure U∩ball p (A*s)
      have hEE : E₁ ⊆ E := inter_subset_inter_right _ hpCap
      have hKK : K₁ ⊆ K := inter_subset_inter_right _ hpCap
      have hμ : volume.restrict E₁ ≤ volume.restrict E := Measure.restrict_mono_set volume hEE
      have hLocal := hWall p hp s ⟨hs,hsr.trans_lt hr.2⟩ u f (hu.mono hKK)
        (hTrace.mono (inter_subset_inter_right _ hpCap))
        (fun x hx => hLap x (hEE hx)) (hDu.mono_measure hμ) (hf.mono_measure hμ)
      have hLocalJ :
          s^(-3/2:ℝ)*(eLpNorm (fderiv ℝ u) 2 (volume.restrict E₁)).toReal +
          s^(1/4:ℝ)*(eLpNorm f 4 (volume.restrict E₁)).toReal ≤ J :=
        add_le_add (mul_le_mul_of_nonneg_left (eLpNorm_toReal_mono_measure_of_mem hDu hμ)
          (Real.rpow_nonneg hs.le _))
          (mul_le_mul_of_nonneg_left (eLpNorm_toReal_mono_measure_of_mem hf hμ)
            (Real.rpow_nonneg hs.le _))
      let ρ := d/2
      have hρ : 0 < ρ := half_pos hd
      have hρs : ρ ≤ s := by dsimp only [ρ]; linarith only [hNear,hs]
      have hUρ : ball x ρ ⊆ U := (ball_subset_ball (half_le_self hd.le)).trans hBall
      have hBρ : ball x ρ ⊆ ball c r := by
        intro y hy
        have hxy : dist y x < d/2 := mem_ball.1 hy
        exact mem_ball.2 (by
          linarith only [dist_triangle y x c,hxy,mem_ball.1 hx.2,hNear,hsr,hr₀])
      have hρE : ball x ρ ⊆ E := fun _ hy => ⟨hUρ hy,hBρ hy⟩
      have hρK : ball x ρ ⊆ K := fun _ hy => ⟨subset_closure (hUρ hy),hBρ hy⟩
      have hμρ : volume.restrict (ball x ρ) ≤ volume.restrict E := Measure.restrict_mono_set volume hρE
      have hUval (y : Point) (hy : y ∈ ball x ρ) : ‖u y‖ ≤ 2*CB*d*J := by
        have hDy : dist y p ≤ 2*d := by
          have h := dist_triangle y x p
          dsimp only [ρ,d] at *
          linarith only [h,mem_ball.1 hy,hd]
        have hCy : y ∈ ball p (s/4) := mem_ball.2 (hDy.trans_lt (by linarith only [hNear,hs]))
        have h := hLocal y ⟨subset_closure (hUρ hy),hCy⟩
        rw [Real.norm_eq_abs]
        exact (h.trans (mul_le_mul_of_nonneg_left hLocalJ (mul_nonneg hCB.le dist_nonneg))).trans
          ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDy hCB.le) hJ).trans_eq (by ring))
      have hInterv := (hInter x hρ u f (hu.mono hρK) (fun y hy => hLap y (hρE hy))
        (hf.mono_measure hμρ) (hDu.mono_measure hμρ)).2
      have hEst := hInterv (2*CB*d*J) (by positivity) hUval
      have hρpow : ρ^(1/4:ℝ) ≤ s^(1/4:ℝ) := Real.rpow_le_rpow hρ.le hρs (by norm_num)
      have hΦ := mul_le_mul hρpow (eLpNorm_toReal_mono_measure_of_mem hf hμρ)
        ENNReal.toReal_nonneg (Real.rpow_nonneg hs.le _)
      have hN : s^(1/4:ℝ)*F ≤ J :=
        le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hs.le _) hG)
      have hS : ρ⁻¹*(2*CB*d*J) = 4*CB*J := by
        dsimp only [ρ]
        field_simp
        ring
      rw [hS] at hEst
      have h' := hEst.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hΦ.trans hN)) hCI.le)
      dsimp only [Λ]
      nlinarith only [h',mul_nonneg (mul_nonneg hCI.le hM) hJ,mul_nonneg hCI.le hJ]
    · let ρ := s/32
      have hρ : 0 < ρ := by dsimp only [ρ]; positivity
      have hρd : ρ ≤ d := by dsimp only [ρ]; linarith only [le_of_not_gt hNear,hs]
      have hUρ : ball x ρ ⊆ U := (ball_subset_ball hρd).trans hBall
      have hBρ : ball x ρ ⊆ ball c r := by
        intro y hy
        have hxy : dist y x < s/32 := mem_ball.1 hy
        exact mem_ball.2 (by
          linarith only [dist_triangle y x c,hxy,mem_ball.1 hx.2,hsr,hr₀])
      have hρE : ball x ρ ⊆ E := fun _ hy => ⟨hUρ hy,hBρ hy⟩
      have hρK : ball x ρ ⊆ K := fun _ hy => ⟨subset_closure (hUρ hy),hBρ hy⟩
      have hμρ : volume.restrict (ball x ρ) ≤ volume.restrict E := Measure.restrict_mono_set volume hρE
      have hEst := (hInter x hρ u f (hu.mono hρK) (fun y hy => hLap y (hρE hy))
        (hf.mono_measure hμρ) (hDu.mono_measure hμρ)).1
      have hS : ρ^(-3/2:ℝ) = M * s^(-3/2:ℝ) := by
        dsimp only [ρ,M]
        have hPow : (32:ℝ)^(-3/2:ℝ) = ((32:ℝ)^(3/2:ℝ))⁻¹ := by
          rw [show (-3/2:ℝ) = -(3/2) by ring, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 32)]
        rw [Real.div_rpow hs.le (by norm_num), hPow, div_inv_eq_mul,mul_comm]
      have hρpow : ρ^(1/4:ℝ) ≤ s^(1/4:ℝ) :=
        Real.rpow_le_rpow hρ.le (by dsimp only [ρ]; linarith only [hs]) (by norm_num)
      have hΦ := mul_le_mul hρpow (eLpNorm_toReal_mono_measure_of_mem hf hμρ)
        ENNReal.toReal_nonneg (Real.rpow_nonneg hs.le _)
      rw [hS] at hEst
      have h' : ‖fderiv ℝ u x‖ ≤ CI * (M*s^(-3/2:ℝ)*G+s^(1/4:ℝ)*F) :=
        hEst.trans (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (eLpNorm_toReal_mono_measure_of_mem hDu hμρ)
          (mul_nonneg hM (Real.rpow_nonneg hs.le _))) hΦ) hCI.le)
      have hJG : s^(-3/2:ℝ)*G ≤ J :=
        le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hs.le _) hF)
      have hJF : s^(1/4:ℝ)*F ≤ J :=
        le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hs.le _) hG)
      have hBound : M*s^(-3/2:ℝ)*G+s^(1/4:ℝ)*F ≤ (4*CB+M+2)*J := by
        calc
          _ = M*(s^(-3/2:ℝ)*G)+s^(1/4:ℝ)*F := by ring
          _ ≤ M*J+J := add_le_add (mul_le_mul_of_nonneg_left hJG hM) hJF
          _ = (M+1)*J := by ring
          _ ≤ (4*CB+M+2)*J := mul_le_mul_of_nonneg_right (by linarith only [hCB]) hJ
      exact h'.trans ((mul_le_mul_of_nonneg_left hBound hCI.le).trans_eq (by dsimp only [Λ]; ring))
  have hW : IsOpen W := hU.1.1.inter isOpen_ball
  have hWK : W ⊆ K := fun _ hx => ⟨subset_closure hx.1,ball_subset_ball (by linarith only [hr.1]) hx.2⟩
  have hWC : closure W ⊆ K := fun x hx => ⟨closure_mono inter_subset_left hx,
    closedBall_subset_ball (by linarith only [hr.1])
      (closure_minimal (inter_subset_right.trans ball_subset_closedBall) isClosed_closedBall hx)⟩
  have hK : UniqueDiffOn ℝ K := by
    intro x hx
    exact (uniqueDiffWithinAt_inter (isOpen_ball.mem_nhds hx.2)).2 (hU.uniqueDiffOn_closure x hx.1)
  have hCont : ContinuousOn (fun x => ‖fderivWithin ℝ u K x‖) (closure W) :=
    ((hu.continuousOn_fderivWithin hK (by norm_num)).norm).mono hWC
  have hInside (x : Point) (hx : x ∈ W) : ‖fderivWithin ℝ u K x‖ ≤ C*B := by
    have hNear : K ∈ 𝓝 x := mem_of_superset (hW.mem_nhds hx) hWK
    rw [fderivWithin_of_mem_nhds hNear]
    exact (hOn x hx).trans ((mul_le_mul_of_nonneg_left hJb hΛ.le).trans_eq (by dsimp only [C]; ring))
  intro x hx
  exact le_on_closure hInside hCont continuousOn_const (isOpen_ball.closure_inter hx)

end Thesis

end

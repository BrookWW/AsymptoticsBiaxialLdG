module

public import Thesis.Definitions
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Connected.LocallyPathConnected
import Thesis.Foundation.ShortSpherePath
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Null homotopies on Euclidean unit spheres of dimension at least two. -/

public section

noncomputable section

open Metric MeasureTheory Set Topology unitInterval

namespace Thesis

private def meshTime (n : ℕ) (i : Fin (n + 2)) : I :=
  ⟨(i.val : ℝ) / ((n : ℝ) + 1), div_nonneg (Nat.cast_nonneg _) (by positivity),
    (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr (by
      exact_mod_cast Nat.le_of_lt_succ i.isLt)⟩

private theorem meshTime_zero (n : ℕ) : meshTime n 0 = 0 := by
  apply Subtype.ext
  simp [meshTime]

private theorem meshTime_last (n : ℕ) : meshTime n (Fin.last (n + 1)) = 1 := by
  apply Subtype.ext
  change ((n + 1 : ℕ) : ℝ) / ((n : ℝ) + 1) = 1
  rw [Nat.cast_succ, div_self (by positivity)]

private theorem meshTime_step (n : ℕ) (i : Fin (n + 1)) :
    (meshTime n i.succ : ℝ) - (meshTime n i.castSucc : ℝ) = 1 / ((n : ℝ) + 1) := by
  change ((i.val + 1 : ℕ) : ℝ) / ((n : ℝ) + 1) - (i.val : ℝ) / ((n : ℝ) + 1) = _
  rw [Nat.cast_succ, add_div, add_sub_cancel_left]

private theorem concat_range_subset {X : Type*} [TopologicalSpace X] {S : Set X}
    {n : ℕ} (x : Fin (n + 1) → X) (q : (i : Fin n) → Path (x i.castSucc) (x i.succ))
    (hx : x 0 ∈ S) (hq : ∀ i, range (q i) ⊆ S) : range (Path.concat x q) ⊆ S := by
  induction n with
  | zero =>
    intro z hz
    rw [Path.concat_zero] at hz
    obtain ⟨t, rfl⟩ := hz
    exact hx
  | succ n ih =>
    let y : Fin (n + 1) → X := x ∘ Fin.castSucc
    let q' (i : Fin n) : Path (y i.castSucc) (y i.succ) := q i.castSucc
    have hEq : Path.concat x q = (Path.concat y q').trans (q (Fin.last n)) := Path.concat_succ x q
    have hr := Path.trans_range (Path.concat y q') (q (Fin.last n))
    calc
      _ = range ((Path.concat y q').trans (q (Fin.last n))) :=
        congrArg (fun p : Path (x 0) (x (Fin.last (n + 1))) => range p) hEq
      _ = _ := hr
      _ ⊆ _ := union_subset (ih y q' hx (fun i => hq i.castSucc)) (hq _)

private theorem endpoint_span_ne_top {n : ℕ} (hn : 3 ≤ n) (x y : EuclideanSpace ℝ (Fin n)) :
    Submodule.span ℝ ({x, y} : Set (EuclideanSpace ℝ (Fin n))) ≠ ⊤ := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let S : Finset E := {x, y}
  have hS : (↑S : Set E) = {x, y} := by simp [S]
  have hSpan : Module.finrank ℝ (Submodule.span ℝ ({x, y} : Set E)) ≤ S.card := by
    have h := finrank_span_finset_le_card (R := ℝ) S
    change Module.finrank ℝ (Submodule.span ℝ (↑S : Set E)) ≤ S.card at h
    rwa [hS] at h
  have hCard : S.card ≤ 2 := (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton])
  intro htop
  have hRank : Module.finrank ℝ E = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    rw [finrank_euclideanSpace, Fintype.card_fin]
  rw [htop, finrank_top, hRank] at hSpan
  omega

/-- Any path on a Euclidean unit sphere of dimension at least two is homotopic relative to its
endpoints to a finite concatenation of paths lying in two-dimensional
endpoint spans. In particular the replacement omits a point of the sphere. -/
theorem exists_unitSphere_path_homotopic_avoiding_pole {n : ℕ} (hdim : 3 ≤ n)
    {x y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1} (p : Path x y) :
    ∃ q : Path x y, p.Homotopic q ∧
      ∃ z : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, z ∉ range q := by
  let E := EuclideanSpace ℝ (Fin n)
  have hp := CompactSpace.uniformContinuous_of_continuous p.continuous
  obtain ⟨δ, hδ, hClose⟩ := Metric.uniformContinuous_iff.1 hp (1 / 2) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  let t := meshTime n
  let γ (i : Fin (n + 1)) := p.subpath (t i.castSucc) (t i.succ)
  let planes (i : Fin (n + 1)) : Submodule ℝ E :=
    Submodule.span ℝ {(p (t i.castSucc)).val, (p (t i.succ)).val}
  have hSmall (i : Fin (n + 1)) (s : I) : ‖(γ i s).val - (p (t i.castSucc)).val‖ ≤ 1 / 2 := by
    have hStep := meshTime_step n i
    have hMono : t i.castSucc ≤ t i.succ := by
      change (meshTime n i.castSucc : ℝ) ≤ (meshTime n i.succ : ℝ)
      apply sub_nonneg.mp
      rw [hStep]
      positivity
    have hIn : γ i s ∈ range (p.subpath (t i.castSucc) (t i.succ)) := mem_range_self s
    rw [p.range_subpath_of_le _ _ hMono] at hIn
    obtain ⟨v, hv, he⟩ := hIn
    have hDist : dist v (t i.castSucc) < δ := by
      have hl : (t i.castSucc : ℝ) ≤ (v : ℝ) := hv.1
      have hr : (v : ℝ) ≤ (t i.succ : ℝ) := hv.2
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hl)]
      calc
        _ ≤ (t i.succ : ℝ) - (t i.castSucc : ℝ) := sub_le_sub_right hr _
        _ = 1 / ((n : ℝ) + 1) := hStep
        _ < δ := hn
    have hh := hClose hDist
    rw [he, Subtype.dist_eq, dist_eq_norm] at hh
    exact hh.le
  have hReplace (i : Fin (n + 1)) : ∃ q : Path (p (t i.castSucc)) (p (t i.succ)),
      (γ i).Homotopic q ∧ ∀ s, (q s).val ∈ planes i :=
    exists_path_homotopic_secant_in_span (γ i) (hSmall i)
  choose sections hSections hPlane using hReplace
  let q₀ := Path.concat (p ∘ t) sections
  have hHom : (p.subpath (t 0) (t (Fin.last (n + 1)))).Homotopic q₀ :=
    (Path.Homotopic.concat_subpath p t).symm.trans
      (Path.Homotopic.concat_hcomp (p ∘ t) γ sections hSections)
  have hx : x = p (t 0) := by rw [show t 0 = 0 from meshTime_zero n, p.source]
  have hy : y = p (t (Fin.last (n + 1))) := by
    rw [show t (Fin.last (n + 1)) = 1 from meshTime_last n, p.target]
  let q := q₀.cast hx hy
  have hpEq : (p.subpath (t 0) (t (Fin.last (n + 1)))).cast hx hy = p := by
    refine DFunLike.ext _ _ fun s => ?_
    change p (Icc.convexComb (meshTime n 0) (meshTime n (Fin.last (n + 1))) s) = p s
    apply congrArg p
    rw [meshTime_zero, meshTime_last]
    apply Subtype.ext
    change (1 - (s : ℝ)) * 0 + (s : ℝ) * 1 = (s : ℝ)
    rw [mul_zero, mul_one, zero_add]
  have hq : p.Homotopic q := by
    rw [← hpEq]
    exact hHom.pathCast hx hy
  let U : Set E := ⋃ i, (planes i : Set E)
  have hp₀ : (p (t 0)).val ∈ U := mem_iUnion.2 ⟨0, Submodule.subset_span (Or.inl rfl)⟩
  have hRange : ∀ s : I, (q s).val ∈ U := by
    have hR := concat_range_subset (p ∘ t) sections (S := Subtype.val ⁻¹' U) hp₀
      (fun i _ ⟨v, hv⟩ => hv ▸ mem_iUnion.2 ⟨i, hPlane i v⟩)
    intro s
    exact hR (mem_range_self s)
  have hZero : volume U = 0 := measure_iUnion_null fun i =>
    Measure.addHaar_submodule _ _ (endpoint_span_ne_top hdim _ _)
  have hOutside : ∃ z : E, z ∉ U := by
    by_contra! hn'
    have hU : U = univ := eq_univ_of_forall hn'
    rw [hU, Measure.measure_univ_eq_zero] at hZero
    exact NeZero.ne (volume : Measure E) hZero
  obtain ⟨z, hz⟩ := hOutside
  have hz₀ : z ≠ 0 := by
    intro h
    exact hz (h.symm ▸ mem_iUnion.2 ⟨0, (planes 0).zero_mem⟩)
  let z₀ : sphere (0 : E) 1 := ⟨NormedSpace.normalize z, by
    rw [mem_sphere, dist_zero_right, NormedSpace.norm_normalize hz₀]⟩
  have hz₀U : z₀.val ∉ U := by
    intro hU
    obtain ⟨i, hi⟩ := mem_iUnion.1 hU
    apply hz
    apply mem_iUnion.2
    refine ⟨i, ?_⟩
    have h := (planes i).smul_mem ‖z‖ hi
    exact NormedSpace.norm_smul_normalize z ▸ h
  exact ⟨q, hq, z₀, fun ⟨s, hs⟩ => hz₀U (hs ▸ hRange s)⟩

theorem exists_sphere3_path_homotopic_avoiding_pole {x y : Sphere3} (p : Path x y) :
    ∃ q : Path x y, p.Homotopic q ∧ ∃ z : Sphere3, z ∉ range q :=
  exists_unitSphere_path_homotopic_avoiding_pole (by decide : 3 ≤ 4) p

private theorem unitSphere_loop_homotopic_refl_of_avoids_pole {d : ℕ}
    {x z : sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1} (q : Path x x)
    (hz : z ∉ range q) : q.Homotopic (Path.refl x) := by
  let E := EuclideanSpace ℝ (Fin (d + 1))
  letI : Fact (Module.finrank ℝ E = d + 1) := ⟨by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = d + 1
    rw [finrank_euclideanSpace, Fintype.card_fin]⟩
  let e := stereographic' d z
  have hIn (t : I) : q t ∈ e.source := by
    rw [show e.source = {z}ᶜ from stereographic'_source z]
    intro h
    exact hz ⟨t, h⟩
  let x₀ : e.source := ⟨x, q.source ▸ hIn 0⟩
  let Q : Path x₀ x₀ :=
    { toFun := fun t => ⟨q t, hIn t⟩
      continuous_toFun := q.continuous.subtype_mk hIn
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  have he : e.target = univ := stereographic'_target z
  let C : e.source ≃ₜ EuclideanSpace ℝ (Fin d) := e.toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr he).trans (Homeomorph.Set.univ _))
  letI : SimplyConnectedSpace e.source := C.toHomotopyEquiv.simplyConnectedSpace
  let incl : C(e.source, sphere (0 : E) 1) := ⟨Subtype.val, continuous_subtype_val⟩
  have h := (SimplyConnectedSpace.paths_homotopic Q (Path.refl x₀)).map incl
  have hq : Q.map incl.continuous = q := DFunLike.ext _ _ fun _ => rfl
  have h₀ : (Path.refl x₀).map incl.continuous = Path.refl x := DFunLike.ext _ _ fun _ => rfl
  exact hq ▸ h₀ ▸ h

/-- A Euclidean unit sphere of dimension at least two is simply connected. -/
theorem simplyConnectedSpace_unitSphere {d : ℕ} (hd : 2 ≤ d) :
    SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  constructor
  · apply isPathConnected_iff_pathConnectedSpace.mp
    have hRank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (d + 1))) := by
      rw [← Module.finrank_eq_rank]
      rw [finrank_euclideanSpace, Fintype.card_fin]
      exact_mod_cast (show 1 < d + 1 by omega)
    exact isPathConnected_sphere hRank 0 zero_le_one
  · intro x p
    obtain ⟨q, hp, z, hz⟩ := exists_unitSphere_path_homotopic_avoiding_pole (by omega) p
    exact hp.trans (unitSphere_loop_homotopic_refl_of_avoids_pole q hz)

theorem simplyConnectedSpace_sphere3 : SimplyConnectedSpace Sphere3 :=
  simplyConnectedSpace_unitSphere (by decide : 2 ≤ 3)

/-- Stereographic charts give a basis of path-connected neighborhoods. -/
theorem locallyPathConnectedSpace_unitSphere (d : ℕ) :
    LocallyPathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) := by
  let E := EuclideanSpace ℝ (Fin (d + 1))
  let S := sphere (0 : E) 1
  letI : Fact (Module.finrank ℝ E = d + 1) := ⟨by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = d + 1
    rw [finrank_euclideanSpace, Fintype.card_fin]⟩
  refine ⟨fun x => ?_⟩
  have hx : ‖x.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using x.property
  let z : S := ⟨-x.val, by simpa only [S, mem_sphere, dist_zero_right, norm_neg] using hx⟩
  have hNe : x ≠ z := by
    intro h
    have hSame : x.val = -x.val := congrArg Subtype.val h
    have hZero : x.val = 0 := by
      ext i
      have hi := congrArg (fun v : E => v i) hSame
      change x.val i = -(x.val i) at hi
      change x.val i = 0
      linarith
    rw [hZero, norm_zero] at hx
    exact zero_ne_one hx
  let e := stereographic' d z
  have hxE : x ∈ e.source := by rw [stereographic'_source]; exact hNe
  let x₀ : e.source := ⟨x, hxE⟩
  let C : e.source ≃ₜ EuclideanSpace ℝ (Fin d) := e.toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr (stereographic'_target z)).trans (Homeomorph.Set.univ _))
  letI : LocallyPathConnectedSpace e.source := C.isOpenEmbedding.locallyPathConnectedSpace
  rw [Filter.hasBasis_self]
  intro A hA
  have hSub : Subtype.val ⁻¹' A ∈ 𝓝 x₀ := continuous_subtype_val.continuousAt.preimage_mem_nhds hA
  obtain ⟨V, ⟨hVopen, hxV, hVp⟩, hV⟩ := (isOpen_isPathConnected_basis x₀).mem_iff.1 hSub
  refine ⟨Subtype.val '' V, ?_, hVp.image continuous_subtype_val, ?_⟩
  · exact (e.open_source.isOpenEmbedding_subtypeVal.isOpenMap _ hVopen).mem_nhds ⟨x₀, hxV, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hV hv

end Thesis

module

public import Thesis.MeasureGeometry.PuncturedSphereRetraction
import Mathlib.Geometry.Manifold.Instances.Sphere

/-! The ordered peripheral word under cap retraction and stereographic coordinates. -/

@[expose] public section

noncomputable section

open Metric Set
open scoped Topology

namespace Thesis.MeasureGeometry

/-- The same peripheral loops, each traversed once, admit an ordered
null product after transporting their basepoints along paths. -/
def HasOrderedPeripheralWord {X : Type*} [TopologicalSpace X] {q : ℕ}
    (γ : Fin q → C(NativeCircle,X)) : Prop :=
  ∃ (order : Equiv.Perm (Fin q)) (rev : Fin q → Bool) (base : X)
    (c : ∀ i : Fin q, Path base (γ (order i) nativeCircleLoopBase)),
    traversalPathClassProduct
      (fun i => (c i).trans ((orientedCirclePath (γ (order i)) (rev i)).trans (c i).symm)) = 1

theorem traversalPathClassProduct_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {q : ℕ}
    (f : C(X,Y)) {x : X} (p : Fin q → Path x x) :
    FundamentalGroup.map f x (traversalPathClassProduct p) =
      traversalPathClassProduct (fun i => (p i).map f.continuous) := by
  rw [traversalPathClassProduct,traversalPathClassProduct,map_list_prod,List.map_reverse,List.map_ofFn]
  rfl

private theorem map_orientedCirclePath {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) (γ : C(NativeCircle,X)) (rev : Bool) :
    (orientedCirclePath γ rev).map f.continuous = orientedCirclePath (f.comp γ) rev := by
  cases rev <;> apply Path.ext <;> funext t <;> rfl

theorem HasOrderedPeripheralWord.map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {q : ℕ}
    {γ : Fin q → C(NativeCircle,X)} (h : HasOrderedPeripheralWord γ) (f : C(X,Y)) :
    HasOrderedPeripheralWord (fun i => f.comp (γ i)) := by
  obtain ⟨order,rev,x,c,hc⟩ := h
  let p (i : Fin q) : Path x x :=
    (c i).trans ((orientedCirclePath (γ (order i)) (rev i)).trans (c i).symm)
  let c' (i : Fin q) : Path (f x) ((f.comp (γ (order i))) nativeCircleLoopBase) :=
    (c i).map f.continuous
  refine ⟨order,rev,f x,c',?_⟩
  have hP := congrArg (FundamentalGroup.map f x) hc
  change FundamentalGroup.map f x (traversalPathClassProduct p) = FundamentalGroup.map f x 1 at hP
  rw [traversalPathClassProduct_map,map_one] at hP
  have hEq (i : Fin q) : (p i).map f.continuous =
      (c' i).trans ((orientedCirclePath (f.comp (γ (order i))) (rev i)).trans (c' i).symm) := by
    simp only [p,c',Path.map_trans,← Path.map_symm,map_orientedCirclePath]
    rfl
  simpa only [hEq] using hP

/-- The relation for the actual peripheral loops is equivalent to the
same relation after retaining only the cap centers as punctures. -/
theorem hasOrderedPeripheralWord_iff_centerSphere
    {c : Point} {R : ℝ} (hR : 0 < R) {q : ℕ} (d : Fin q → Plane → Point)
    (hd : ∀ i, IsSmoothDiskEmbedding (d i)) (hs : ∀ i, MapsTo (d i) Disk (sphere c R))
    (hDisj : Pairwise (fun i j => Disjoint (d i '' Disk) (d j '' Disk)))
    (γ : Fin q → C(NativeCircle,puncturedCapSphere c R d)) :
    HasOrderedPeripheralWord γ ↔
      HasOrderedPeripheralWord (fun i => (puncturedCapSphere_inclusion c R d).comp (γ i)) := by
  constructor
  · exact fun h => h.map _
  · intro h
    obtain ⟨F,hF⟩ := exists_puncturedSphere_retraction hR d hd hs hDisj
    have h' := h.map F
    have hEq : (fun i => F.comp ((puncturedCapSphere_inclusion c R d).comp (γ i))) = γ := by
      funext i
      apply ContinuousMap.ext
      intro z
      exact hF (γ i z)
    exact hEq ▸ h'

/-- Translate and rescale a positive-radius sphere to the unit sphere. -/
def positiveSphereNormalize (c : Point) (R : ℝ) (hR : 0 < R) :
    sphere c R ≃ₜ sphere (0 : Point) 1 := by
  let f (x : Point) := R⁻¹ • (x-c)
  let g (y : Point) := c+R•y
  have hf (x : sphere c R) : f x.val ∈ sphere (0 : Point) 1 := by
    have hNorm : ‖x.val-c‖ = R := by simpa only [mem_sphere,dist_eq_norm] using x.property
    change R⁻¹ • (x.val-c) ∈ sphere (0 : Point) 1
    rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR.le),hNorm,
      inv_mul_cancel₀ hR.ne']
  have hg (x : sphere (0 : Point) 1) : g x.val ∈ sphere c R := by
    change c+R•x.val ∈ sphere c R
    rw [mem_sphere,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hR.le,
      mem_sphere_zero_iff_norm.mp x.property,mul_one]
  have hfC : Continuous f := (continuous_id.sub continuous_const).const_smul R⁻¹
  have hgC : Continuous g := continuous_const.add (continuous_id.const_smul R)
  exact
    { toFun := fun x => ⟨f x.val,hf x⟩
      invFun := fun x => ⟨g x.val,hg x⟩
      left_inv := fun x => Subtype.ext (by dsimp only [f,g]; rw [smul_smul,mul_inv_cancel₀ hR.ne',one_smul]; abel)
      right_inv := fun x => Subtype.ext (by dsimp only [f,g]; rw [add_sub_cancel_left,smul_smul,inv_mul_cancel₀ hR.ne',one_smul])
      continuous_toFun := (hfC.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (hgC.comp continuous_subtype_val).subtype_mk _ }

/-- Stereographic coordinates on an actual positive-radius sphere with
the specified pole removed. -/
def puncturedSphere_stereographic {c p : Point} {R : ℝ} (hR : 0 < R) (hp : p ∈ sphere c R) :
    ↥(sphere c R \ ({p} : Set Point)) ≃ₜ Plane := by
  let e := positiveSphereNormalize c R hR
  let p₀ : sphere c R := ⟨p,hp⟩
  let pole := e p₀
  letI : Fact (Module.finrank ℝ Point = 2+1) := ⟨finrank_euclideanSpace_fin⟩
  let z := stereographic' 2 pole
  have hSource : z.source = {pole}ᶜ := stereographic'_source pole
  let X := sphere c R \ ({p} : Set Point)
  let F (x : X) : sphere (0 : Point) 1 := e ⟨x.val,x.property.1⟩
  have hF (x : X) : F x ∈ z.source := by
    rw [hSource,mem_compl_iff,mem_singleton_iff]
    exact fun h => x.property.2 (mem_singleton_iff.mpr (congrArg Subtype.val (e.injective h)))
  let G (x : z.source) : sphere c R := e.symm x.val
  have hG (x : z.source) : (G x).val ∈ sphere c R \ {p} := by
    refine ⟨(G x).property,?_⟩
    intro h
    have he : G x = p₀ := Subtype.ext (mem_singleton_iff.mp h)
    have hx : x.val ≠ pole := by simpa only [hSource,mem_compl_iff,mem_singleton_iff] using x.property
    exact hx ((e.apply_symm_apply x.val).symm.trans (congrArg e he))
  have hFc : Continuous F := e.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hGc : Continuous G := e.symm.continuous.comp continuous_subtype_val
  let A : X ≃ₜ z.source :=
    { toFun := fun x => ⟨F x,hF x⟩
      invFun := fun x => ⟨(G x).val,hG x⟩
      left_inv := fun x => Subtype.ext
        (congrArg (fun z : sphere c R => z.val) (e.symm_apply_apply ⟨x.val,x.property.1⟩))
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val)
      continuous_toFun := hFc.subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp hGc).subtype_mk _ }
  exact A.trans (z.toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr (stereographic'_target pole)).trans (Homeomorph.Set.univ _)))

end Thesis.MeasureGeometry

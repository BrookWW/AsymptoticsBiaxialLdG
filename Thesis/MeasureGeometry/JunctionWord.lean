module

public import Thesis.MeasureGeometry.MeridianTrace
public import Thesis.Foundation.QuaternionWord
public import Thesis.MeasureGeometry.CylinderLateralClass

/-! The ordered punctured-sphere word and the parity of the actual incident weights. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace Thesis

/-- Keep or reverse the traversal of an actual based boundary circle. -/
def orientedCirclePath {X : Type*} [TopologicalSpace X] (f : C(NativeCircle, X))
    (reverse : Bool) : Path (f nativeCircleLoopBase) (f nativeCircleLoopBase) :=
  if reverse then (nativeCircleLoop f).symm else nativeCircleLoop f

theorem quaternionSplittingWeight_inv (g : QuaternionGroup 2) :
    quaternionSplittingWeight g⁻¹ = quaternionSplittingWeight g := by
  cases g with
  | a i => fin_cases i <;> decide
  | xa i => fin_cases i <;> decide

theorem exists_oriented_vacuumCircle (a : BulkCoefficients) (f : C(NativeCircle, vacuum a))
    (rev : Bool) : ∃ f' : C(NativeCircle, vacuum a),
    f' nativeCircleLoopBase = f nativeCircleLoopBase ∧
      (∀ t, f' (nativeCircleLoopParam t) = orientedCirclePath f rev t) ∧
      nativeVacuumCircleCost a f' = nativeVacuumCircleCost a f := by
  cases rev with
  | false => exact ⟨f, rfl, fun _ => rfl, rfl⟩
  | true =>
    obtain ⟨f', hB', hF⟩ := exists_nativeCircleLoop_descent (nativeCircleLoop f).symm
    have hB : f' nativeCircleLoopBase = f nativeCircleLoopBase := hB'.symm
    have hEval (t : unitInterval) : f' (nativeCircleLoopParam t) = (nativeCircleLoop f).symm t :=
      congrArg (fun q : Path (f nativeCircleLoopBase) (f nativeCircleLoopBase) => q t) hF
    obtain ⟨v, hv⟩ := vacuumQuaternionProjection_surjective a (f nativeCircleLoopBase)
    let hv' := hv.trans hB.symm
    have hP : nativeVacuumLoopPath a f' v hv' = (nativeVacuumLoopPath a f v hv).symm := by
      apply Path.ext
      funext t
      exact hEval t
    have hInv : nativeVacuumLoopWord a f' v hv' = (nativeVacuumLoopWord a f v hv)⁻¹ := by
      unfold nativeVacuumLoopWord
      rw [hP, ← map_inv]
      rfl
    refine ⟨f', hB, fun t => hEval t, ?_⟩
    rw [nativeVacuumCircleCost_eq a f' v hv', nativeVacuumCircleCost_eq a f v hv, hInv,
      vacuumSplittingCost_eq, vacuumSplittingCost_eq, quaternionSplittingWeight_inv]

/-- At one fixed starting lift, the based peripheral factor has the same
splitting cost as the original free circle, independent of the orientation. -/
theorem nativeVacuumCircleCost_eq_conjugated_oriented_path
    (a : BulkCoefficients) (f : C(NativeCircle, vacuum a)) (v : Sphere3)
    (p : Path (vacuumQuaternionProjection a v) (f nativeCircleLoopBase)) (rev : Bool) :
    nativeVacuumCircleCost a f = kappaStar a *
      (quaternionSplittingWeight (vacuumFundamentalGroupEquiv a v (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (p.trans ((orientedCirclePath f rev).trans p.symm))))) : ℝ) := by
  let q := p.trans ((orientedCirclePath f rev).trans p.symm)
  obtain ⟨g, hv, hg⟩ := exists_nativeCircleLoop_descent q
  have hvWord : nativeVacuumLoopWord a g v hv =
      vacuumFundamentalGroupEquiv a v (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) := by
    rw [nativeVacuumLoopWord, nativeVacuumLoopPath, hg]
  obtain ⟨f', hf', hEval, hCost⟩ := exists_oriented_vacuumCircle a f rev
  let p' : Path (g nativeCircleLoopBase) (f' nativeCircleLoopBase) := p.cast hv.symm hf'
  have hPath : nativeCircleLoop g = p'.trans ((nativeCircleLoop f').trans p'.symm) := by
    apply Path.ext
    funext t
    have hQ : (nativeCircleLoop f').cast hf'.symm hf'.symm = orientedCirclePath f rev := by
      apply Path.ext
      funext s
      exact hEval s
    have hP : (p'.trans ((nativeCircleLoop f').trans p'.symm)).cast hv hv = q := by
      rw [Path.cast_trans _ _ hv hf'.symm hv,
        Path.cast_trans _ _ hf'.symm hf'.symm hv, hQ]
      have hc₀ : p'.cast hv hf'.symm = p := Path.ext rfl
      have hc₁ : p'.symm.cast hf'.symm hv = p.symm := Path.ext rfl
      rw [hc₀, hc₁]
    exact (congrArg (fun p : Path (vacuumQuaternionProjection a v) (vacuumQuaternionProjection a v) => p t) hg).trans (congrArg (fun p : Path (vacuumQuaternionProjection a v) (vacuumQuaternionProjection a v) => p t)
      hP.symm)
  have hHom := nativeCircle_homotopic_of_path_conjugation p' (hPath ▸ Path.Homotopic.refl _)
  rw [← hCost, ← nativeVacuumCircleCost_homotopic a hHom, nativeVacuumCircleCost_eq a g v hv,
    vacuumSplittingCost_eq, hvWord]

/-- Fundamental-group multiplication in Mathlib is reverse concatenation.
Taking the product of the reversed list reads the boundary in its actual
traversal order. -/
def traversalPathClassProduct {X : Type*} [TopologicalSpace X] {q : ℕ} {x : X}
    (p : Fin q → Path x x) : FundamentalGroup X x :=
  (List.ofFn (fun j => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p j)))).reverse.prod

/-- The punctured sphere is the actual metric sphere with the relative
interiors of the given embedded caps removed. -/
def puncturedCapSphere (x : Point) (r : ℝ) {q : ℕ} (d : Fin q → Plane → Point) : Set Point :=
  sphere x r \ ⋃ j, d j '' ball (0 : Plane) 1

/-- Standard cutting-arc relation on the actual sphere with smooth disks
removed. The relation is in its own fundamental group, before any target
map or identification with quaternions. -/
def External.PuncturedSphereWord : Prop :=
  ∀ (x : Point) {r : ℝ}, 0 < r → ∀ {q : ℕ}, 0 < q →
    ∀ (d : Fin q → Plane → Point), (∀ j, IsSmoothDiskEmbedding (d j)) →
      (∀ j, MapsTo (d j) Disk (sphere x r)) →
      Pairwise (fun i j => Disjoint (d i '' Disk) (d j '' Disk)) →
      let F := puncturedCapSphere x r d
      ∀ (γ : Fin q → C(NativeCircle, F)),
        (∀ j z, (γ j z).val = d j z.val) →
        ∃ (order : Equiv.Perm (Fin q)) (rev : Fin q → Bool) (base : F)
          (c : ∀ i : Fin q, Path base (γ (order i) nativeCircleLoopBase)),
          traversalPathClassProduct
            (fun i => (c i).trans ((orientedCirclePath (γ (order i)) (rev i)).trans (c i).symm)) = 1

private theorem prod_map_inv_eq_reverse_inv {G : Type*} [Group G] (l : List G) :
    (l.map Inv.inv).prod = (l.reverse.prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons g l ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.reverse_cons, List.prod_append,
      List.prod_nil, mul_one, mul_inv_rev]

/-- Map the same ordered cut relation into the vacuum and identify the
actual free classes of all peripheral factors. -/
theorem exists_ordered_quaternion_caps_word
    (hCut : External.PuncturedSphereWord) (a : BulkCoefficients)
    (x : Point) {r : ℝ} (hr : 0 < r) {q : ℕ} (hq : 0 < q)
    (d : Fin q → Plane → Point) (hd : ∀ j, IsSmoothDiskEmbedding (d j))
    (hs : ∀ j, MapsTo (d j) Disk (sphere x r))
    (hDisj : Pairwise (fun i j => Disjoint (d i '' Disk) (d j '' Disk)))
    (Q : C(puncturedCapSphere x r d, vacuum a)) :
    ∃ (order : Equiv.Perm (Fin q)) (γ : Fin q → C(NativeCircle, puncturedCapSphere x r d))
      (g : Fin q → QuaternionGroup 2),
      (∀ j z, (γ j z).val = d j z.val) ∧
      (List.ofFn g).prod = 1 ∧
      (∀ i, nativeVacuumCircleCost a (Q.comp (γ (order i))) =
        kappaStar a * (quaternionSplittingWeight (g i) : ℝ)) := by
  let F := puncturedCapSphere x r d
  have hBoundary (j : Fin q) (z : NativeCircle) : d j z.val ∈ F := by
    have hz : z.val ∈ Disk := sphere_subset_closedBall z.property
    refine ⟨hs j hz, ?_⟩
    intro h
    obtain ⟨i, y, hy, he⟩ := mem_iUnion.mp h
    by_cases hij : i = j
    · subst i
      have hEq := (hd j).2.1 (ball_subset_closedBall hy) hz he
      have hn : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
      rw [hEq, mem_ball, dist_zero_right, hn] at hy
      exact (lt_irrefl (1 : ℝ)) hy
    · exact (disjoint_left.mp (hDisj hij)) ⟨y, ball_subset_closedBall hy, he⟩ ⟨z.val, hz, rfl⟩
  let γ (j : Fin q) : C(NativeCircle, F) :=
    ⟨fun z => ⟨d j z.val, hBoundary j z⟩,
      ((hd j).1.continuousOn.comp_continuous continuous_subtype_val (fun z => sphere_subset_closedBall z.property))

        |>.subtype_mk _⟩
  have hγ (j : Fin q) (z : NativeCircle) : (γ j z).val = d j z.val := rfl
  obtain ⟨order, rev, base, c, hWord⟩ := hCut x hr hq d hd hs hDisj γ hγ
  obtain ⟨v, hv⟩ := vacuumQuaternionProjection_surjective a (Q base)
  let p (i : Fin q) : Path base base :=
    (c i).trans ((orientedCirclePath (γ (order i)) (rev i)).trans (c i).symm)
  let φ := (vacuumFundamentalGroupEquiv a v).toMonoidHom.comp (FundamentalGroup.mapOfEq Q hv.symm)
  let g (i : Fin q) := (φ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p i))))⁻¹
  refine ⟨order, γ, g, hγ, ?_, ?_⟩
  · let L := List.ofFn (fun i => φ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p i))))
    have h := congrArg φ hWord
    change φ (traversalPathClassProduct p) = φ 1 at h
    rw [traversalPathClassProduct, map_list_prod, List.map_reverse, List.map_ofFn, map_one] at h
    change L.reverse.prod = 1 at h
    have hG : List.ofFn g = L.map Inv.inv := by rw [List.map_ofFn]; rfl
    rw [hG, prod_map_inv_eq_reverse_inv, h, inv_one]
  · intro i
    let f := Q.comp (γ (order i))
    let c₀ := ((c i).map Q.continuous).cast hv rfl
    have hCost := nativeVacuumCircleCost_eq_conjugated_oriented_path a f v c₀ (rev i)
    have hMap : ((p i).map Q.continuous).cast hv hv =
        c₀.trans ((orientedCirclePath f (rev i)).trans c₀.symm) := by
      simp only [p, Path.map_trans, Path.cast_trans _ _ hv rfl hv, Path.cast_trans _ _ rfl rfl hv,
        Path.cast_rfl_rfl, c₀]
      rw [← Path.map_symm, ← Path.cast_symm]
      congr 1
      congr 1
      cases rev i <;> simp [orientedCirclePath, f, nativeCircleLoop] <;>
        apply Path.ext <;> funext t <;> rfl
    have hElem : φ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p i))) =
        vacuumFundamentalGroupEquiv a v (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (c₀.trans ((orientedCirclePath f (rev i)).trans c₀.symm)))) := by
      dsimp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [FundamentalGroup.mapOfEq_apply]
      change vacuumFundamentalGroupEquiv a v (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (((p i).map Q.continuous).cast hv hv))) = _
      rw [hMap]
    dsimp only [g]
    rw [quaternionSplittingWeight_inv, hElem]
    exact hCost

/-- The ordered cap word gives even parity of the light incident weights.
The comparisons to cap boundary energies are for the same original limit. -/
theorem even_light_weights_of_actual_junction_caps
    (hCut : External.PuncturedSphereWord) (a : BulkCoefficients)
    (x : Point) {r : ℝ} (hr : 0 < r) {q : ℕ} (hq : 0 < q)
    (d : Fin q → Plane → Point) (hd : ∀ j, IsSmoothDiskEmbedding (d j))
    (hs : ∀ j, MapsTo (d j) Disk (sphere x r))
    (hDisj : Pairwise (fun i j => Disjoint (d i '' Disk) (d j '' Disk)))
    (Q₀ : Point → S0) (Q : C(puncturedCapSphere x r d, vacuum a))
    (hQ : ∀ y, (Q y).val = Q₀ y.val)
    (θ : Fin q → ℝ) (hθ : ∀ j, 0 < θ j)
    (hWeight : ∀ j (b : C(NativeCircle, vacuum a)),
      (∀ z, (b z).val = Q₀ (d j z.val)) → θ j = nativeVacuumCircleCost a b) :
    Even ((Finset.univ.filter fun j => θ j = kappaStar a).card) := by
  classical
  obtain ⟨order, γ, g, hΓ, hProd, hCost⟩ :=
    exists_ordered_quaternion_caps_word hCut a x hr hq d hd hs hDisj Q
  let τ (i : Fin q) := θ (order i)
  have hτ (i : Fin q) : τ i = kappaStar a * (quaternionSplittingWeight (g i) : ℝ) := by
    refine (hWeight (order i) (Q.comp (γ (order i))) ?_).trans (hCost i)
    intro z
    change (Q (γ (order i) z)).val = _
    rw [hQ, hΓ]
  have hLight (i : Fin q) : τ i = kappaStar a ↔ IsLightQuaternion (g i) := by
    have hne : g i ≠ 1 := by
      intro h
      have hPos : 0 < τ i := hθ (order i)
      rw [hτ, h, quaternionSplittingWeight] at hPos
      simp at hPos
    rw [hτ, quaternionSplittingWeight, if_neg hne]
    by_cases h : IsLightQuaternion (g i)
    · simp [h]
    · simp only [h, if_false, Nat.cast_ofNat, iff_false]
      exact ne_of_gt (by linarith only [kappaStar_pos a])
  have hEven := even_light_weights_of_ordered_quaternion_product g τ hLight hProd
  have hCard : (Finset.univ.filter fun j => τ j = kappaStar a).card =
      (Finset.univ.filter fun j => θ j = kappaStar a).card := by
    apply Finset.card_bij (fun i _ => order i)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · intro i hi j hj he
      exact order.injective he
    · intro i hi
      refine ⟨order.symm i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, order.apply_symm_apply i⟩
      change θ (order (order.symm i)) = kappaStar a
      rw [order.apply_symm_apply]
      exact (Finset.mem_filter.mp hi).2
  rwa [hCard] at hEven

end Thesis

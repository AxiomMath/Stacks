module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal
public import StacksFrontier.Topology.Simplicial.AugmentationDescent
public import StacksFrontier.Topology.Simplicial.ProperHypercoveringDescent
public import StacksFrontier.Topology.Sheaves.Functors.Pushforward.ProperPushforward

/-!
# Points of a proper hypercovering

Let `U` be a simplicial object of the category `LC` of Hausdorff, locally quasi-compact spaces
and `a : U ⟶ X` an augmentation which is a proper hypercovering: `U_0 → X`, the canonical map
`U_1 → U_0 ×_X U_0` and the matching maps `U_{n+1} → (cosk_n sk_n U)_{n+1}` are proper and
surjective. This file reads off the point-set consequences of the first three conditions which
the descent of sheaves along `a` uses: two points of `U_0` with the same image in `X` are the
vertices of a `1`-simplex, the vertex map `U_1 → U_0 × U_0` is closed, and three `1`-simplices
bounding a triangle are the edges of a `2`-simplex.

## Main results

* `Stacks.Topology.Simplicial.ProperHypercovering.descentConditions`: a proper hypercovering
  satisfies `Stacks.Topology.Simplicial.Augmentation.DescentConditions`.

## References

* [Stacks Project, Tag 0DAG](https://stacks.math.columbia.edu/tag/0DAG)
* [Stacks Project, Tag 0DER](https://stacks.math.columbia.edu/tag/0DER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TopologicalSpace
open CategoryTheory.SimplicialObject.Truncated
  (hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits)

universe u

namespace Stacks.Topology.Simplicial.ProperHypercovering

open Stacks.Topology Stacks.Topology.Simplicial.Augmentation

variable {Y : SimplicialObject LocallyQuasiCompactHausdorff.{u}}
  {X : LocallyQuasiCompactHausdorff.{u}}
  {a : Y ⟶ (SimplicialObject.const LocallyQuasiCompactHausdorff).obj X}

/-- The fibre product of a morphism of `LC` with itself, presented as the subspace of the
product cut out by the equation `f p = f q`. -/
noncomputable def pullbackSelfHomeo {A B : LocallyQuasiCompactHausdorff.{u}} (f : A ⟶ B) :
    (pullback f f).obj ≃ₜ {p : A.obj × A.obj // (f : A.obj → B.obj) p.1 = f p.2} :=
  TopCat.homeoOfIso (((IsPullback.of_hasPullback f f).map
    locallyQuasiCompactHausdorffToTop).isoPullback ≪≫ TopCat.pullbackIsoProdSubtype _ _)

/-- The presentation of the fibre product records the two projections. -/
theorem pullbackSelfHomeo_apply {A B : LocallyQuasiCompactHausdorff.{u}} (f : A ⟶ B)
    (z : (pullback f f).obj) :
    (pullbackSelfHomeo f z).1 = ((pullback.fst f f : _ → _) z, (pullback.snd f f : _ → _) z) := by
  let hc := (IsPullback.of_hasPullback f f).map locallyQuasiCompactHausdorffToTop
  change ((TopCat.pullbackIsoProdSubtype _ _).hom (hc.isoPullback.hom z)).1 = _
  rw [TopCat.pullbackIsoProdSubtype_hom_apply]
  have h1 := ConcreteCategory.congr_hom hc.isoPullback_hom_fst z
  have h2 := ConcreteCategory.congr_hom hc.isoPullback_hom_snd z
  rw [ConcreteCategory.comp_apply] at h1 h2
  exact Prod.ext h1 h2

variable (hyp : MorphismProperty.IsHypercovering properSurjective ⟨Y, X, a⟩)
include hyp

/-- The canonical map `U_1 → U_0 ×_X U_0` of a proper hypercovering, in Mathlib's sense of
proper. -/
theorem isProperMap_firstMatchingArrow :
    _root_.IsProperMap ((SimplicialObject.Augmented.firstMatchingArrow ⟨Y, X, a⟩).hom :
      _ → _) :=
  isProperMap_of_isProperMap
    (ConcreteCategory.hom (SimplicialObject.Augmented.firstMatchingArrow ⟨Y, X, a⟩).hom).continuous
    hyp.map_one.1

/-- The augmentation in degree zero of a proper hypercovering, in Mathlib's sense of proper. -/
theorem isProperMap_app_zero : _root_.IsProperMap (a.app (op ⦋0⦌) : _ → _) :=
  isProperMap_of_isProperMap (ConcreteCategory.hom (a.app (op ⦋0⦌))).continuous hyp.map_zero.1

omit hyp in
/-- The face `δ j` of a `1`-simplex is its vertex `1 - j`. -/
private theorem map_δ_eq_vertex (e : (U Y).obj (op ⦋1⦌)) (j : Fin 2) :
    (Y.map (SimplexCategory.δ j).op : _ → _) e = vertex (U Y) (1 - j) e := by
  fin_cases j
  · change (Y.map (SimplexCategory.δ 0).op : _ → _) e = (Y.map _ : _ → _) e
    rw [SimplexCategory.δ_zero_eq_const]
    rfl
  · change (Y.map (SimplexCategory.δ 1).op : _ → _) e = (Y.map _ : _ → _) e
    rw [SimplexCategory.δ_one_eq_const]
    rfl

omit hyp in
/-- The canonical map `U_1 → U_0 ×_X U_0`, read through the presentation of the fibre product as
a subspace of `U_0 × U_0`, is the pair of vertex maps. -/
theorem pullbackSelfHomeo_firstMatchingArrow (w : (Y.obj (op ⦋1⦌)).obj) :
    (pullbackSelfHomeo (a.app (op ⦋0⦌))
      ((SimplicialObject.Augmented.firstMatchingArrow ⟨Y, X, a⟩).hom w)).1 =
      (vertex (U Y) 0 w, vertex (U Y) 1 w) := by
  rw [pullbackSelfHomeo_apply]
  have h1 := ConcreteCategory.congr_hom
    (SimplicialObject.Augmented.firstMatchingArrow_hom_fst ⟨Y, X, a⟩) w
  have h2 := ConcreteCategory.congr_hom
    (SimplicialObject.Augmented.firstMatchingArrow_hom_snd ⟨Y, X, a⟩) w
  rw [ConcreteCategory.comp_apply] at h1 h2
  exact Prod.ext (h1.trans (map_δ_eq_vertex w 1)) (h2.trans (map_δ_eq_vertex w 0))

/-- The pair of vertex maps `U_1 → U_0 × U_0` of a proper hypercovering is closed. -/
theorem isClosedMap_vertices :
    IsClosedMap (fun w : (U Y).obj (op ⦋1⦌) => (vertex (U Y) 0 w, vertex (U Y) 1 w)) := by
  have hP : IsClosed {p : (Y.obj (op ⦋0⦌)).obj × (Y.obj (op ⦋0⦌)).obj |
      (a.app (op ⦋0⦌) : _ → _) p.1 = (a.app (op ⦋0⦌) : _ → _) p.2} :=
    isClosed_eq ((ConcreteCategory.hom (a.app (op ⦋0⦌))).continuous.comp continuous_fst)
      ((ConcreteCategory.hom (a.app (op ⦋0⦌))).continuous.comp continuous_snd)
  have e : (fun w : (U Y).obj (op ⦋1⦌) => (vertex (U Y) 0 w, vertex (U Y) 1 w)) =
      Subtype.val ∘ pullbackSelfHomeo (a.app (op ⦋0⦌)) ∘
        ((SimplicialObject.Augmented.firstMatchingArrow ⟨Y, X, a⟩).hom : _ → _) := by
    funext w
    exact (pullbackSelfHomeo_firstMatchingArrow w).symm
  rw [e]
  exact hP.isClosedMap_subtype_val.comp ((pullbackSelfHomeo _).isClosedMap.comp
    (isProperMap_firstMatchingArrow hyp).isClosedMap)

/-- Two points of `U_0` with the same image in `X` are the vertices of a `1`-simplex. -/
theorem exists_edge (p q : (U Y).obj (op ⦋0⦌))
    (h : (a.app (op ⦋0⦌) : _ → _) p = (a.app (op ⦋0⦌) : _ → _) q) :
    ∃ w, vertex (U Y) 0 w = p ∧ vertex (U Y) 1 w = q := by
  obtain ⟨w, hw⟩ := hyp.map_one.2 ((pullbackSelfHomeo (a.app (op ⦋0⦌))).symm ⟨(p, q), h⟩)
  have e := pullbackSelfHomeo_firstMatchingArrow (Y := Y) (X := X) (a := a) w
  rw [hw, Homeomorph.apply_symm_apply] at e
  exact ⟨w, (Prod.ext_iff.1 e).1.symm, (Prod.ext_iff.1 e).2.symm⟩

/-- The augmentation in degree one of a proper hypercovering is closed. -/
theorem isClosedMap_app_one : IsClosedMap ((topologicalAugmentation Y X a).app (op ⦋1⦌)) := by
  intro C hC
  let Q : (U Y).obj (op ⦋1⦌) → X.obj × X.obj := Prod.map (a.app (op ⦋0⦌) : _ → _)
    (a.app (op ⦋0⦌) : _ → _) ∘ fun w => (vertex (U Y) 0 w, vertex (U Y) 1 w)
  have hQ : IsClosedMap Q := ((isProperMap_app_zero hyp).prodMap
    (isProperMap_app_zero hyp)).isClosedMap.comp (isClosedMap_vertices hyp)
  have hv : ∀ (i : Fin 2) (w : (U Y).obj (op ⦋1⦌)),
      (a.app (op ⦋0⦌) : _ → _) (vertex (U Y) i w) =
        (topologicalAugmentation Y X a).app (op ⦋1⦌) w :=
    fun i w => app_zero_vertex (a := topologicalAugmentation Y X a) i w
  have e : (topologicalAugmentation Y X a).app (op ⦋1⦌) '' C = (fun x => (x, x)) ⁻¹' (Q '' C) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, Prod.ext (hv 0 w) (hv 1 w)⟩
    · rintro ⟨w, hw, hQw⟩
      exact ⟨w, hw, (hv 0 w).symm.trans (Prod.ext_iff.1 hQw).1⟩
  rw [e]
  exact (hQ C hC).preimage (continuous_id.prodMk continuous_id)

omit hyp in
/-- The point of `LC`. -/
private abbrev point : LocallyQuasiCompactHausdorff.{u} :=
  LocallyQuasiCompactHausdorff.of PUnit.{u + 1} inferInstance

omit hyp in
/-- The morphism from the point of `LC` picking out a point. -/
private abbrev pointMap (B : LocallyQuasiCompactHausdorff.{u}) (b : B.obj) : point ⟶ B :=
  ObjectProperty.homMk (TopCat.ofHom (ContinuousMap.const _ b))

omit hyp in
/-- The face `δ 2 : ⦋1⦌ ⟶ ⦋2⦌` is the edge from `0` to `1`. -/
private theorem δ_two_eq_mkOfLe :
    SimplexCategory.δ (n := 1) 2 = SimplexCategory.mkOfLe 0 1 (by decide) := by
  ext x : 3
  fin_cases x <;> rfl

omit hyp in
/-- The face `δ 1 : ⦋1⦌ ⟶ ⦋2⦌` is the edge from `0` to `2`. -/
private theorem δ_one_eq_mkOfLe :
    SimplexCategory.δ (n := 1) 1 = SimplexCategory.mkOfLe 0 2 (by decide) := by
  ext x : 3
  fin_cases x <;> rfl

omit hyp in
/-- The face `δ 0 : ⦋1⦌ ⟶ ⦋2⦌` is the edge from `1` to `2`. -/
private theorem δ_zero_eq_mkOfLe :
    SimplexCategory.δ (n := 1) 0 = SimplexCategory.mkOfLe 1 2 (by decide) := by
  ext x : 3
  fin_cases x <;> rfl

omit hyp in
/-- The unit of `coskAdj 1` in degree `2`, followed by a leg of the limit cone of the right Kan
extension, is the corresponding structure map. -/
private theorem coskAdj_unit_app_comp_coneAt_π_app {C : Type*} [Category C]
    [∀ F : SimplicialObject.Truncated C 1,
      (SimplexCategory.Truncated.inclusion 1).op.HasPointwiseRightKanExtension F]
    (Z : SimplicialObject C)
    (f : StructuredArrow (op ⦋2⦌) (SimplexCategory.Truncated.inclusion 1).op) :
    ((SimplicialObject.coskAdj 1).unit.app Z).app (op ⦋2⦌) ≫
      ((Functor.RightExtension.mk _ ((SimplexCategory.Truncated.inclusion 1).op.ranCounit.app
        ((SimplicialObject.truncation 1).obj Z))).coneAt (op ⦋2⦌)).π.app f = Z.map f.hom := by
  have k₁ := ((SimplicialObject.coskAdj 1).unit.app Z).naturality f.hom
  have k₂ := (SimplexCategory.Truncated.inclusion 1).op.ranCounit_app_app_ranAdjunction_unit_app_app
    (H := C) Z f.right
  have k₃ := congrArg (fun g => g ≫ ((SimplexCategory.Truncated.inclusion 1).op.ranCounit.app
    ((SimplicialObject.truncation 1).obj Z)).app f.right) k₁
  exact ((Category.assoc _ _ _).symm.trans k₃.symm).trans ((Category.assoc _ _ _).trans
    ((congrArg (fun g => Z.map f.hom ≫ g) k₂).trans (Category.comp_id _)))

/-- A compatible triple of edges over a point of `X` is the triple of faces of a `2`-simplex. -/
private theorem exists_map_δ_eq_of_compatible (x : X.obj)
    (f : Fin 3 → (Over.mk (pointMap X x) ⟶ ((SimplicialObject.truncation 1).obj
      (SimplicialObject.Augmented.over
        (⟨Y, X, a⟩ : SimplicialObject.Augmented LocallyQuasiCompactHausdorff.{u}))).obj
      (op ⟨⦋1⦌, le_rfl⟩)))
    (hf : ∀ i j : Fin 2, i ≤ j →
      f i.castSucc ≫ ((SimplicialObject.truncation 1).obj (SimplicialObject.Augmented.over
        (⟨Y, X, a⟩ : SimplicialObject.Augmented LocallyQuasiCompactHausdorff.{u}))).map
          (SimplexCategory.Truncated.δ 1 j (Nat.le_succ 0) le_rfl).op =
        f j.succ ≫ ((SimplicialObject.truncation 1).obj (SimplicialObject.Augmented.over
          (⟨Y, X, a⟩ : SimplicialObject.Augmented LocallyQuasiCompactHausdorff.{u}))).map
          (SimplexCategory.Truncated.δ 1 i (Nat.le_succ 0) le_rfl).op) :
    ∃ σ : (U Y).obj (op ⦋2⦌), ∀ i : Fin 3, (Y.map (SimplexCategory.δ i).op : _ → _) σ =
      ((f i).left : point.obj → _) PUnit.unit := by
  let A : SimplicialObject.Augmented LocallyQuasiCompactHausdorff.{u} := ⟨Y, X, a⟩
  let : HasFiniteLimits (Over A.right) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : ∀ F : SimplicialObject.Truncated (Over A.right) 1,
      (SimplexCategory.Truncated.inclusion 1).op.HasPointwiseRightKanExtension F := fun F =>
    (hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits
        (C := Over A.right)).2 (fun _ ↦ inferInstance) (0 + 1) (by omega) F
  let L := (SimplexCategory.Truncated.inclusion 1).op
  let Ut := (SimplicialObject.truncation 1).obj (SimplicialObject.Augmented.over A)
  let T : Over A.right := Over.mk (pointMap X x)
  obtain ⟨π, hπ, -⟩ := (SimplicialObject.Truncated.existsUnique_cone_app_δ_eq_iff Ut T f).2 hf
  let hlim := L.isPointwiseRightKanExtensionRanCounit Ut (op ⦋2⦌)
  let η := ((SimplicialObject.coskAdj 1).unit.app (SimplicialObject.Augmented.over A)).app
    (op ⦋2⦌)
  have hsurj : Function.Surjective (ConcreteCategory.hom ((Over.forget A.right).map η)) :=
    (hyp.matching 1 le_rfl).2
  obtain ⟨σ, hσ⟩ := hsurj (((hlim.lift ⟨T, π⟩).left : point.obj → _) PUnit.unit)
  refine ⟨σ, fun i => ?_⟩
  let g := StructuredArrow.mk (Y := op (⟨⦋1⦌, le_rfl⟩ : SimplexCategory.Truncated 1))
    (T := L) (SimplexCategory.δ i).op
  have e₁ := congrArg (fun k => (k.left : _ → _) σ)
    (coskAdj_unit_app_comp_coneAt_π_app (SimplicialObject.Augmented.over A) g)
  have e₂ := congrArg (fun k => (k.left : point.obj → _) PUnit.unit) (hlim.fac ⟨T, π⟩ g)
  have e₃ := congrArg (fun k => (k.left : point.obj → _) PUnit.unit) (hπ i)
  simp only [Over.comp_left, ConcreteCategory.comp_apply] at e₁ e₂
  refine e₁.symm.trans ?_
  change _ = ((f i).left : point.obj → _) PUnit.unit
  rw [← e₃, ← e₂]
  exact congrArg _ hσ

/-- **Triangles in a proper hypercovering.** Three `1`-simplices of `U` bounding a triangle are
the edges of a `2`-simplex. This is surjectivity of the matching map
`U_2 → (cosk_1 sk_1 U)_2`, read on points through the limit description of the coskeleton. -/
theorem exists_triangle (e₀₁ e₀₂ e₁₂ : (U Y).obj (op ⦋1⦌))
    (h₁ : vertex (U Y) 0 e₀₁ = vertex (U Y) 0 e₀₂) (h₂ : vertex (U Y) 1 e₀₁ = vertex (U Y) 0 e₁₂)
    (h₃ : vertex (U Y) 1 e₀₂ = vertex (U Y) 1 e₁₂) :
    ∃ σ : (U Y).obj (op ⦋2⦌), (U Y).map (SimplexCategory.mkOfLe 0 1 (by decide)).op σ = e₀₁ ∧
      (U Y).map (SimplexCategory.mkOfLe 0 2 (by decide)).op σ = e₀₂ ∧
      (U Y).map (SimplexCategory.mkOfLe 1 2 (by decide)).op σ = e₁₂ := by
  let A : SimplicialObject.Augmented LocallyQuasiCompactHausdorff.{u} := ⟨Y, X, a⟩
  let Ut := (SimplicialObject.truncation 1).obj (SimplicialObject.Augmented.over A)
  let x := (topologicalAugmentation Y X a).app (op ⦋1⦌) e₀₁
  have hx₀₂ : (topologicalAugmentation Y X a).app (op ⦋1⦌) e₀₂ = x :=
    (app_zero_vertex 0 e₀₂).symm.trans ((congrArg _ h₁.symm).trans (app_zero_vertex 0 e₀₁))
  have hx₁₂ : (topologicalAugmentation Y X a).app (op ⦋1⦌) e₁₂ = x :=
    (app_zero_vertex 1 e₁₂).symm.trans ((congrArg _ h₃.symm).trans
      ((app_zero_vertex 1 e₀₂).trans hx₀₂))
  let T : Over A.right := Over.mk (pointMap X x)
  let fe : ∀ e : (U Y).obj (op ⦋1⦌), (topologicalAugmentation Y X a).app (op ⦋1⦌) e = x →
      (T ⟶ Ut.obj (op ⟨⦋1⦌, le_rfl⟩)) := fun e he =>
    Over.homMk (pointMap _ e) (by
      apply ObjectProperty.hom_ext
      ext p
      exact he)
  let f : Fin 3 → (T ⟶ Ut.obj (op ⟨⦋1⦌, le_rfl⟩)) :=
    ![fe e₁₂ hx₁₂, fe e₀₂ hx₀₂, fe e₀₁ rfl]
  obtain ⟨σ, key⟩ := exists_map_δ_eq_of_compatible hyp x f (by
    intro i j hij
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    ext p
    fin_cases i <;> fin_cases j
    · exact (map_δ_eq_vertex e₁₂ 0).trans (h₃.symm.trans (map_δ_eq_vertex e₀₂ 0).symm)
    · exact (map_δ_eq_vertex e₁₂ 1).trans (h₂.symm.trans (map_δ_eq_vertex e₀₁ 0).symm)
    · exact absurd hij (by decide)
    · exact (map_δ_eq_vertex e₀₂ 1).trans (h₁.symm.trans (map_δ_eq_vertex e₀₁ 1).symm))
  refine ⟨σ, ?_, ?_, ?_⟩ <;> change (Y.map _ : _ → _) σ = _
  · rw [← δ_two_eq_mkOfLe]
    exact key 2
  · rw [← δ_one_eq_mkOfLe]
    exact key 1
  · rw [← δ_zero_eq_mkOfLe]
    exact key 0

/-- **A proper hypercovering satisfies the point-set conditions of descent.** -/
theorem descentConditions :
    DescentConditions (U Y) (locallyQuasiCompactHausdorffToTop.obj X)
      (topologicalAugmentation Y X a) where
  surjective₀ := hyp.map_zero.2
  isClosedMap₀ := (isProperMap_app_zero hyp).isClosedMap
  isCompact_fiber₀ _ := (isProperMap_app_zero hyp).isCompact_preimage isCompact_singleton
  t2Space₀ := inferInstanceAs (T2Space (Y.obj (op ⦋0⦌)).obj)
  isClosedMap₁ := isClosedMap_app_one hyp
  isClosedMap_vertices := isClosedMap_vertices hyp
  exists_edge := exists_edge hyp
  exists_triangle := exists_triangle hyp

end Stacks.Topology.Simplicial.ProperHypercovering

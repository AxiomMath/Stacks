module

public import StacksFrontier.CategoryTheory.FiberedInSetoids.Defs
public import StacksFrontier.CategoryTheory.Sites.Stack.FiberedInSets
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport

/-!
# A category fibred in setoids is a stack in setoids exactly when its presheaf is a sheaf

Let `(𝒞, J)` be a site, let `𝒳` be a category fibred in setoids over `𝒞` and let `𝒴` be a category
fibred in sets over `𝒞` which is equivalent to `𝒳` as a category over `𝒞`. Then `𝒳` is a stack in
setoids if and only if `𝒴` is a stack in sets, that is, if and only if the presheaf of objects
`U ↦ Ob(𝒴_U)` of `𝒴` is a sheaf. Its value at `U` is the set `Ob(𝒳_U)/≅` of isomorphism classes of
the fibre of `𝒳` over `U`.

## Main definitions

* `CategoryTheory.BasedCategory.Equivalence.fiberQuotientEquiv`: the identification of `Ob(𝒴_U)`
  with the set `Ob(𝒳_U)/≅` of isomorphism classes of the fibre of `𝒳` over `U`.

## Main results

* `CategoryTheory.BasedCategory.isStackInSetoids_iff_isStackInSets_of_equivalence`: `𝒳` is a stack
  in setoids if and only if `𝒴` is a stack in sets.
* `CategoryTheory.BasedCategory.isStackInSetoids_iff_isSheaf_objPresheaf_of_equivalence`: `𝒳` is a
  stack in setoids if and only if the presheaf of objects of `𝒴` is a sheaf.
-/

@[expose] public section

namespace CategoryTheory

open Opposite

universe v₁ v₂ u₁ u₂

namespace BasedCategory.Equivalence

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒞}
  (e : BasedCategory.Equivalence 𝒳 𝒴)

/-! ### The fibres of `𝒴` are the isomorphism classes of the fibres of `𝒳` -/

section Fibres

variable [∀ V : 𝒞, IsDiscrete (𝒴.p.Fiber V)] {U : 𝒞}

/-- Every object of a fibre of `𝒴` is the image of an object of the corresponding fibre of `𝒳`. -/
lemma fiberMap_surjective : Function.Surjective (e.fiberMap (U := U)) := by
  intro y
  have h := e.isHomLift_counitInv y.1
  rw [y.2] at h
  exact ⟨e.symm.fiberMap y,
    (obj_ext_of_isDiscrete (⟨e.counitInv y.1, h⟩ : y ⟶ e.fiberMap (e.symm.fiberMap y))).symm⟩

/-- Two objects of a fibre of `𝒳` have the same image in the fibre of `𝒴` exactly when they are
isomorphic. -/
lemma fiberMap_eq_iff (hgpd : ∀ V : 𝒞, IsGroupoid (𝒳.p.Fiber V)) (x y : 𝒳.p.Fiber U) :
    e.fiberMap x = e.fiberMap y ↔ IsIsomorphic x y := by
  refine ⟨fun h ↦ ?_, fun ⟨φ⟩ ↦ obj_ext_of_isDiscrete ((e.fiberMapFunctor U).map φ.hom)⟩
  set φ : x.1 ⟶ y.1 :=
    e.fullyFaithfulFunctor.preimage (Functor.Fiber.fiberInclusion.map (eqToHom h))
  have hφ : e.functor.map φ = Functor.Fiber.fiberInclusion.map (eqToHom h) :=
    e.fullyFaithfulFunctor.map_preimage _
  have : 𝒴.p.IsHomLift (𝟙 U) (e.functor.map φ) := by rw [hφ]; exact (eqToHom h).2
  have : IsGroupoid (𝒳.p.Fiber U) := hgpd U
  have m : x ⟶ y := ⟨φ, BasedFunctor.isHomLift_map e.functor (𝟙 U) φ⟩
  have := IsGroupoid.all_isIso m
  exact ⟨asIso m⟩

/-- For an equivalence over `𝒞` onto a category fibred in sets, the fibre of `𝒴` over `U` is the
set `Ob(𝒳_U)/≅` of isomorphism classes of the fibre of `𝒳` over `U` (Categories, Stacks 0045
(1)(b)). -/
noncomputable def fiberQuotientEquiv (hgpd : ∀ V : 𝒞, IsGroupoid (𝒳.p.Fiber V)) (U : 𝒞) :
    _root_.Quotient (isIsomorphicSetoid (𝒳.p.Fiber U)) ≃ 𝒴.p.Fiber U :=
  Equiv.ofBijective (_root_.Quotient.lift e.fiberMap fun _ _ h ↦ (e.fiberMap_eq_iff hgpd _ _).2 h)
    ⟨fun q q' h ↦ by
      induction q using _root_.Quotient.ind with
      | _ x =>
        induction q' using _root_.Quotient.ind with
        | _ y => exact _root_.Quotient.sound ((e.fiberMap_eq_iff hgpd x y).1 h),
     fun y ↦ by
      obtain ⟨x, hx⟩ := e.fiberMap_surjective y
      exact ⟨⟦x⟧, hx⟩⟩

/-- `CategoryTheory.BasedCategory.Equivalence.fiberQuotientEquiv` sends the class of `x` to the
image of `x` under the map on fibres induced by `e`. -/
@[simp]
lemma fiberQuotientEquiv_mk (hgpd : ∀ V : 𝒞, IsGroupoid (𝒳.p.Fiber V)) (U : 𝒞)
    (x : 𝒳.p.Fiber U) : e.fiberQuotientEquiv hgpd U ⟦x⟧ = e.fiberMap x := rfl

end Fibres

/-! ### Stacks in setoids and stacks in sets -/

/-- If `𝒳` is a stack in setoids and `𝒴` is fibred in sets, then `𝒴` is a stack in sets. -/
lemma isStackInSets_of_isStackInSetoids' (e : BasedCategory.Equivalence 𝒳 𝒴)
    [𝒴.p.IsFiberedInSets] {J : GrothendieckTopology 𝒞}
    (h : 𝒳.p.IsStackInSetoids J) : 𝒴.p.IsStackInSets J where
  isStack := e.isStack J h.isStack
  fiber_isDiscrete _ := inferInstance

/-- If `𝒴` is a stack in sets and `𝒳` is fibred in setoids, then `𝒳` is a stack in setoids. -/
lemma isStackInSetoids_of_isStackInSets' (e : BasedCategory.Equivalence 𝒳 𝒴)
    [𝒳.p.IsFiberedInSetoids] {J : GrothendieckTopology 𝒞}
    (h : 𝒴.p.IsStackInSets J) : 𝒳.p.IsStackInSetoids J where
  isStack := e.symm.isStack J h.isStack
  fiber_isGroupoid U := Functor.IsFiberedInSetoids.fiber_isGroupoid 𝒳.p U
  fiber_isThin U := Functor.IsFiberedInSetoids.fiber_isThin U

end BasedCategory.Equivalence

/-- Let `(𝒞, J)` be a site, let `𝒳` be a category fibred in setoids over `𝒞`, and let `𝒴` be a
category fibred in sets equivalent to `𝒳` as a category over `𝒞`. Then `𝒳` is a stack in setoids if
and only if `𝒴` is a stack in sets. -/
@[stacks 0432]
theorem BasedCategory.isStackInSetoids_iff_isStackInSets_of_equivalence
    {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒞}
    (e : BasedCategory.Equivalence 𝒳 𝒴) [𝒳.p.IsFiberedInSetoids] [𝒴.p.IsFiberedInSets]
    (J : GrothendieckTopology 𝒞) :
    𝒳.p.IsStackInSetoids J ↔ 𝒴.p.IsStackInSets J :=
  ⟨BasedCategory.Equivalence.isStackInSets_of_isStackInSetoids' e,
    BasedCategory.Equivalence.isStackInSetoids_of_isStackInSets' e⟩

/-- Let `(𝒞, J)` be a site, let `𝒳` be a category fibred in setoids over `𝒞`, and let `𝒴` be a
category fibred in sets equivalent to `𝒳` as a category over `𝒞`. Then `𝒳` is a stack in setoids if
and only if the presheaf of objects `U ↦ Ob(𝒴_U)` of `𝒴` is a sheaf. Its value at `U` is identified
with the set `Ob(𝒳_U)/≅` of isomorphism classes of the fibre of `𝒳` over `U` by
`CategoryTheory.BasedCategory.Equivalence.fiberQuotientEquiv`. -/
@[stacks 0432 "the \"in other words\" sentence: iff the presheaf `U ↦ Ob(𝒮_U)/≅` is a sheaf"]
theorem BasedCategory.isStackInSetoids_iff_isSheaf_objPresheaf_of_equivalence
    {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒞}
    (e : BasedCategory.Equivalence 𝒳 𝒴) [𝒳.p.IsFiberedInSetoids] [𝒴.p.IsFiberedInSets]
    (J : GrothendieckTopology 𝒞) :
    𝒳.p.IsStackInSetoids J ↔ Presheaf.IsSheaf J (Functor.objPresheaf 𝒴.p) :=
  (BasedCategory.isStackInSetoids_iff_isStackInSets_of_equivalence e J).trans
    (Functor.isStackInSets_iff_isSheaf_objPresheaf 𝒴.p J)

end CategoryTheory

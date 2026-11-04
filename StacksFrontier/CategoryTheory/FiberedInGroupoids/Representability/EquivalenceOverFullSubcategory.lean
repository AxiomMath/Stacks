module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp

/-!
# Restricting an equivalence over a base to a full subcategory

Let `e : EquivalenceOver p q` be an equivalence in the 2-category of categories over `C`, with
`p : D₁ ⥤ C` and `q : D₂ ⥤ C`, and let `Q` be a property of the objects of `D₁` closed under
isomorphisms. Pulling `Q` back along the backward functor of `e` gives a property
`Q.inverseImage e.inv.functor` of the objects of `D₂`, and the two full subcategories so selected
are again equivalent over `C`: that is
`StacksRepresentableCFG.EquivalenceOver.fullSubcategory`.

Both 1-morphisms are *strictly* over `C`, which is the point of stating this for
`EquivalenceOver` rather than for `CategoryTheory.Equivalence`: each is the restriction of one of
the two functors of `e`, and `CategoryTheory.ObjectProperty.lift` followed by
`CategoryTheory.ObjectProperty.ι` is that functor on the nose, so the strict commutation of the
restriction is the strict commutation of `e`. The unit and counit are those of `e` read on the
full subcategories; their components are the components of those of `e`, hence vertical, which is
the coherence condition `EquivalenceOver` asks for.

## Main definitions

* `StacksRepresentableCFG.EquivalenceOver.fullSubcategoryHom` and
  `StacksRepresentableCFG.EquivalenceOver.fullSubcategoryInv`: the two restricted
  1-morphisms over `C`.
* `StacksRepresentableCFG.EquivalenceOver.fullSubcategory`: the restricted
  equivalence over `C`.

## Main results

* `StacksRepresentableCFG.isHomLift_fullSubcategory`: a morphism of a full
  subcategory lies over a morphism of the base exactly when the morphism of the ambient category
  it is does.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace StacksRepresentableCFG

universe v₀ u₀ v₁ u₁ v₂ u₂

/-- **A morphism of a full subcategory lies over a morphism of the base exactly when the morphism
of the ambient category it is does.** The structure functor of the full subcategory is the
inclusion followed by the structure functor, and the inclusion forgets the membership proof, so
the two sides have the same factorisation; they are nevertheless different instances of
`CategoryTheory.Functor.IsHomLift`, whose ambient category is an index. -/
theorem isHomLift_fullSubcategory {D : Type u₁} [Category.{v₁} D] {E : Type u₀}
    [Category.{v₀} E] (r : D ⥤ E) {P : ObjectProperty D} {X Y : P.FullSubcategory} {R S : E}
    (f : R ⟶ S) (φ : X ⟶ Y) (h : r.IsHomLift f φ.hom) : (P.ι ⋙ r).IsHomLift f φ := by
  have := h
  exact IsHomLift.of_fac' (P.ι ⋙ r) f φ (IsHomLift.domain_eq r f φ.hom)
    (IsHomLift.codomain_eq r f φ.hom) (IsHomLift.fac' r f φ.hom)

variable {C : Type u₀} [Category.{v₀} C] {D₁ : Type u₁} [Category.{v₁} D₁]
  {D₂ : Type u₂} [Category.{v₂} D₂] {p : D₁ ⥤ C} {q : D₂ ⥤ C}
  (e : StacksRepresentableCFG.EquivalenceOver p q) (Q : ObjectProperty D₁)

/-- **The forward 1-morphism of the restricted equivalence**: the backward functor of `e`,
restricted to the full subcategory cut out by the pullback of `Q`. -/
def EquivalenceOver.fullSubcategoryHom :
    MorphismOver ((Q.inverseImage e.inv.functor).ι ⋙ q) (Q.ι ⋙ p) where
  functor := Q.lift ((Q.inverseImage e.inv.functor).ι ⋙ e.inv.functor) fun X => X.2
  w := by
    change (Q.inverseImage e.inv.functor).ι ⋙ e.inv.functor ⋙ p = _
    rw [e.inv.w]

variable [Q.IsClosedUnderIsomorphisms]

/-- **The backward 1-morphism of the restricted equivalence**: the forward functor of `e`,
restricted to the full subcategory cut out by `Q`. Its image lands in the pullback of `Q` because
the unit of `e` identifies an object with its round trip and `Q` is closed under
isomorphisms. -/
def EquivalenceOver.fullSubcategoryInv :
    MorphismOver (Q.ι ⋙ p) ((Q.inverseImage e.inv.functor).ι ⋙ q) where
  functor := (Q.inverseImage e.inv.functor).lift (Q.ι ⋙ e.hom.functor) fun Y =>
    Q.prop_of_iso (e.unitIso.app Y.obj) Y.2
  w := by
    change Q.ι ⋙ e.hom.functor ⋙ q = _
    rw [e.hom.w]

/-- **An equivalence over `C` restricts to the full subcategories cut out by a property of the
objects and by its pullback.** Let `e : EquivalenceOver p q` and let `Q` be a property of the
objects of the source closed under isomorphisms. Then the full subcategory of `Q` and the full
subcategory of the pullback of `Q` along the backward functor of `e` are equivalent over `C`, by
the restrictions of the two functors of `e`.

This is `CategoryTheory.Equivalence.congrFullSubcategory` in the 2-category of categories over
`C`: the restrictions commute strictly with the structure functors, and the unit and counit have
the components of those of `e`, which are vertical. -/
def EquivalenceOver.fullSubcategory :
    StacksRepresentableCFG.EquivalenceOver
      ((Q.inverseImage e.inv.functor).ι ⋙ q) (Q.ι ⋙ p) where
  hom := e.fullSubcategoryHom Q
  inv := e.fullSubcategoryInv Q
  unitIso := NatIso.ofComponents
    (fun X => ObjectProperty.isoMk _ (e.counitIso.app X.obj).symm)
    (fun {_ _} f => ObjectProperty.hom_ext _ (e.counitIso.inv.naturality f.hom))
  counitIso := NatIso.ofComponents
    (fun Y => ObjectProperty.isoMk _ (e.unitIso.app Y.obj).symm)
    (fun {_ _} f => ObjectProperty.hom_ext _ (e.unitIso.inv.naturality f.hom))
  unit_over := whiskerRight_eq_eqToHom _ _ _ fun x =>
    isHomLift_fullSubcategory q _ _ (e.isHomLift_counitIso_inv_app x.obj)
  counit_over := by
    refine whiskerRight_eq_eqToHom _ _ _ fun x => ?_
    have hx : p.obj ((e.hom.functor ⋙ e.inv.functor).obj x.obj) = p.obj x.obj := by
      change ((e.hom.functor ⋙ e.inv.functor) ⋙ p).obj x.obj = _
      simp only [Functor.assoc, e.inv.w, e.hom.w]
    exact isHomLift_fullSubcategory p _ _
      ((congrArg (fun U => p.IsHomLift (𝟙 U) (e.unitIso.inv.app x.obj)) hx).mpr
        (e.isHomLift_unitIso_inv_app x.obj))

end StacksRepresentableCFG

end

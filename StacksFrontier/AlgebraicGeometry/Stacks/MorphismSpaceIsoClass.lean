module

public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceSections
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsMap
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoClassSection

/-!
# The induced morphism of representing presheaves, on isomorphism classes (Stacks 04SW)

Let `𝒳` and `𝒴` be categories fibred in groupoids over the big fppf site of `S`, represented by
presheaves `F` and `G` through chosen equivalences over the site. The bijection of Stacks 04SW
(`AlgebraicGeometry.Stack.morphismSpaceEquiv`) turns a 1-morphism `Φ : 𝒳 ⟶ 𝒴` over the site into
a morphism `F ⟶ G` of presheaves; Stacks 04SC turns it into a morphism
`\overline{𝒳} ⟶ \overline{𝒴}` of the presheaves of isomorphism classes
(`CategoryTheory.Functor.isoClassMap`). This file says the two agree under the identification of
`\overline{𝒳}` with `F` and of `\overline{𝒴}` with `G` by naming sections
(`CategoryTheory.PresheafOfCategories.isoClassSection`).

It also records the criterion that identifies the induced morphism with a given one: it is enough
to compute it on every section named by an object.

## Main results

* `AlgebraicGeometry.Stack.morphismSpaceEquiv_app_isoClassSection`: **Stacks 04SW**, the induced
  morphism of representing presheaves is the morphism of Stacks 04SC on isomorphism classes.
* `AlgebraicGeometry.Stack.morphismSpaceEquiv_eq_of_sectionOfObj`: a morphism of presheaves
  agreeing with the 1-morphism on every named section *is* the induced morphism.
* `AlgebraicGeometry.Stack.morphismSpaceEquiv_eq_of_comp_eq`: the same criterion with the
  agreement replaced by a commuting square of functors of categories of elements.

## Implementation notes

The first two are immediate from
`AlgebraicGeometry.Stack.morphismSpaceEquiv_app_sectionOfObj` and
`AlgebraicGeometry.Stack.natTrans_eq_of_forall_sectionOfObj`: the first because the fibre functor
of `Φ` over `W` applies `Φ` to the underlying object, so the two sides name the section of `G`
belonging to `Φ z` for the same `z`; the second because every section is named by an object. The
third combines the second with
`CategoryTheory.PresheafOfCategories.natTrans_app_sectionOfObj_of_comp_eq`, and is the usable
form: the commuting square it asks for is typically an identity of functors, with no transport
along an equality of objects to carry.

## References

* [Stacks Project, Tag 04SC](https://stacks.math.columbia.edu/tag/04SC)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, w} (BigFppfOver B S hS))
variable (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (eX : StacksRepresentableCFG.EquivalenceOver
    𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
  (eY : StacksRepresentableCFG.EquivalenceOver
    𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)

/-- **Stacks 04SW on isomorphism classes.** Under the identification of the presheaf of
isomorphism classes of `𝒳` with `F` and of `𝒴` with `G` by naming sections, the morphism
`F ⟶ G` induced by a 1-morphism `Φ` over the site is the morphism of presheaves of isomorphism
classes that Stacks 04SC attaches to `Φ`. -/
theorem morphismSpaceEquiv_app_isoClassSection
    (Φ : {H : 𝒳.val.obj ⥤ 𝒴.val.obj // H ⋙ 𝒴.val.p = 𝒳.val.p})
    (W : BigFppfOver B S hS)
    (c : _root_.Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber W))) :
    letI : 𝒳.val.p.IsFibered := 𝒳.property.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.property.isFibered
    (morphismSpaceEquiv B S hS 𝒳 𝒴 F G eX eY (Quotient.mk _ Φ)).app (op W)
        (PresheafOfCategories.isoClassSection eX W c) =
      PresheafOfCategories.isoClassSection eY W
        ((Functor.isoClassMap (p := 𝒳.val.p) (q := 𝒴.val.p)
          (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒴.property Φ.2)).app (op W) c) := by
  let : 𝒳.val.p.IsFibered := 𝒳.property.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.property.isFibered
  induction c using _root_.Quotient.ind with
  | _ x => exact morphismSpaceEquiv_app_sectionOfObj B S hS 𝒳 𝒴 F G eX eY Φ x.1 x.2

/-- A morphism `m : F ⟶ G` of the representing presheaves which carries the section named by
every object `z` of `𝒳` to the section named by `Φ z` is the morphism induced by `Φ`. -/
theorem morphismSpaceEquiv_eq_of_sectionOfObj
    (Φ : {H : 𝒳.val.obj ⥤ 𝒴.val.obj // H ⋙ 𝒴.val.p = 𝒳.val.p}) (m : F ⟶ G)
    (h : ∀ (z : 𝒳.val.obj) (W : BigFppfOver B S hS) (hz : 𝒳.val.p.obj z = W),
      m.app (op W) (PresheafOfCategories.sectionOfObj eX z hz) =
        PresheafOfCategories.sectionOfObj eY (Φ.1.obj z)
          ((Functor.congr_obj Φ.2 z).trans hz)) :
    morphismSpaceEquiv B S hS 𝒳 𝒴 F G eX eY (Quotient.mk _ Φ) = m := by
  refine natTrans_eq_of_forall_sectionOfObj B S hS 𝒳 F G eX _ m (fun z W hz => ?_)
  rw [morphismSpaceEquiv_app_sectionOfObj]
  exact (h z W hz).symm

/-- A morphism `m : F ⟶ G` of the representing presheaves whose induced functor of categories of
elements makes the square with `Φ` and the two chosen equivalences commute on the nose is the
morphism induced by `Φ`. This is the form the criterion is applied in: the commuting square is
usually an identity of functors. -/
theorem morphismSpaceEquiv_eq_of_comp_eq
    (Φ : {H : 𝒳.val.obj ⥤ 𝒴.val.obj // H ⋙ 𝒴.val.p = 𝒳.val.p}) (m : F ⟶ G)
    (h : eX.hom.functor ⋙ PresheafOfCategories.elementsMap m = Φ.1 ⋙ eY.hom.functor) :
    morphismSpaceEquiv B S hS 𝒳 𝒴 F G eX eY (Quotient.mk _ Φ) = m :=
  morphismSpaceEquiv_eq_of_sectionOfObj B S hS 𝒳 𝒴 F G eX eY Φ m
    (fun z _ hz =>
      PresheafOfCategories.natTrans_app_sectionOfObj_of_comp_eq m eX eY Φ.1 h z hz _)

end AlgebraicGeometry.Stack

end

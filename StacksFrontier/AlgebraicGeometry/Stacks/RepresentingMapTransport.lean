module

public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial

/-!
# Transporting the morphism of representing presheaves along an isomorphism (Stacks 04SW)

A category fibred in groupoids over the big fppf site of `S` which is equivalent, over the site,
to the category of elements of a presheaf `F` is equally equivalent to the category of elements of
any presheaf isomorphic to `F`: compose the equivalence with
`CategoryTheory.PresheafOfCategories.equivalenceOverOfIso`. This module records what that
replacement does to the morphism of representing presheaves which a 1-morphism induces through
**Stacks 04SW**: it precomposes it with the isomorphism.

That is the computation a consumer needs whenever the presheaf it wants to represent a stack by is
not the one representability happened to hand it — for instance when a 2-fibre product of
represented stacks is to be represented by the Yoneda image of a fibre product in the site, rather
than by the algebraic space that **Stacks 0300** produces.

## Main results

* `CategoryTheory.PresheafOfCategories.sectionOfObj_trans_equivalenceOverOfIso`: the section named
  through the transported equivalence is the image of the section named through the original one.
* `AlgebraicGeometry.Stack.representingMap_trans_equivalenceOverOfIso`: the morphism of
  representing presheaves induced through the transported equivalence, precomposed with the
  isomorphism, is the one induced through the original equivalence.

## Implementation notes

Both halves of the section computation are `rfl`, but not the composite: naming a section through a
composite of equivalences over the site is naming it through the second after applying the first
(`CategoryTheory.PresheafOfCategories.sectionOfObj_trans`), and the base object of the image of
`z` is the base of `z` only through the compatibility `e.hom.w` of the first equivalence with the
two structure functors, which is not an identity. So the two steps are taken separately, with the
equality of base objects substituted away in the first.

The conclusion is stated as `representingMap … eF … = i.hom ≫ representingMap … (eF.trans …) …`
rather than with `i.inv` on the other side, because that is the orientation
`AlgebraicGeometry.Stack.morphismSpaceEquiv_eq_of_sectionOfObj` proves directly.

## References

* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.PresheafOfCategories

universe v₁ v₂ u₁ u₂ a

variable {C : Type u₁} [Category.{v₁} C] {F F' : Cᵒᵖ ⥤ Type a}
  {𝒮 : Type u₂} [Category.{v₂} 𝒮] {p : 𝒮 ⥤ C}

/-- **Naming a section through the equivalence attached to an isomorphism of presheaves.** The
section of `F'` named by an object of the category of elements of `F` is the image under the
isomorphism of the section of `F` that object names. -/
theorem sectionOfObj_equivalenceOverOfIso (i : F ≅ F')
    (X : (presheafOfCategories (F ⋙ typeToCat)).obj) {W : C}
    (h : (presheafOfCategories (F ⋙ typeToCat)).p.obj X = W) :
    sectionOfObj (equivalenceOverOfIso i) X h =
      i.hom.app (op W) (sectionOfObj
        (StacksRepresentableCFG.EquivalenceOver.refl
          (presheafOfCategories (F ⋙ typeToCat)).p) X h) := by
  subst h
  rfl

/-- **Naming a section through the trivial equivalence after a first one.** The section named by
the image of `z` under an equivalence over the site, read through the identity equivalence of the
category of elements, is the section named by `z`. -/
theorem sectionOfObj_refl_hom_obj
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (z : 𝒮) {W : C} (hz : p.obj z = W) :
    sectionOfObj
        (StacksRepresentableCFG.EquivalenceOver.refl
          (presheafOfCategories (F ⋙ typeToCat)).p)
        (eF.hom.functor.obj z) ((Functor.congr_obj eF.hom.w z).trans hz) =
      sectionOfObj eF z hz := rfl

/-- **Naming a section through an equivalence composed with an isomorphism of presheaves.** -/
theorem sectionOfObj_trans_equivalenceOverOfIso
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (i : F ≅ F') (z : 𝒮) {W : C} (hz : p.obj z = W) :
    sectionOfObj (eF.trans (equivalenceOverOfIso i)) z hz =
      i.hom.app (op W) (sectionOfObj eF z hz) := by
  rw [sectionOfObj_trans, sectionOfObj_equivalenceOverOfIso, sectionOfObj_refl_hom_obj]

end CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04SW against an isomorphism of representing presheaves.** Let `𝒜` be equivalent over
the big fppf site of `S` to the category of elements of `F`, let `i : F ≅ F'`, and let `𝒞` be
equivalent to the category of elements of `G`. Then the morphism `F' ⟶ G` induced by a 1-morphism
`h : 𝒜 ⟶ 𝒞` through the transported equivalence, precomposed with `i`, is the morphism `F ⟶ G`
induced through the original one. -/
theorem representingMap_trans_equivalenceOverOfIso
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (i : F ≅ F') (h : 𝒜 ⟶ 𝒞) :
    representingMap B S hS 𝒜 𝒞 F G eF eG h =
      i.hom ≫ representingMap B S hS 𝒜 𝒞 F' G
        (eF.trans (PresheafOfCategories.equivalenceOverOfIso i)) eG h := by
  refine morphismSpaceEquiv_eq_of_sectionOfObj B S hS 𝒜 𝒞 F G eF eG _ _ (fun z W hz => ?_)
  show (representingMap B S hS 𝒜 𝒞 F' G
      (eF.trans (PresheafOfCategories.equivalenceOverOfIso i)) eG h).app (op W)
      (i.hom.app (op W) (PresheafOfCategories.sectionOfObj eF z hz)) = _
  rw [← PresheafOfCategories.sectionOfObj_trans_equivalenceOverOfIso eF i z hz]
  exact morphismSpaceEquiv_app_sectionOfObj B S hS 𝒜 𝒞 F' G
    (eF.trans (PresheafOfCategories.equivalenceOverOfIso i)) eG _ z hz

end AlgebraicGeometry.Stack

end

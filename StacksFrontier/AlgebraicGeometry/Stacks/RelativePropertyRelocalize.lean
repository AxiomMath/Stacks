module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty

/-!
# A relative property read on the lower-shriek extension (Stacks 03YK, 04SG)

Stacks 03YK tests a relative property of a representable 1-morphism `f : 𝒳 ⟶ 𝒴` on the
structural morphism of each algebraic space representing a base change of `f` along a
scheme-valued point `U → 𝒴`. That algebraic space lives over `U`, and the structural morphism it
is tested through is the one of Stacks 04SG, obtained by applying the forward functor
`AlgebraicGeometry.spacesOverSmallerBaseFunctor`.

This file replaces that structural morphism by the explicit one: the forward functor of Stacks
04SG is the lower-shriek extension `Λ_U` of Stacks 03I5 part (2), with structural morphism
`CategoryTheory.OverShriek.relocalizeToYoneda` reading off the factorization a section carries.
So the test of Stacks 03YK is the test of `P` on `Λ_U F ⟶ h_U`, for `F` ranging over the
presheaves representing the base change.

That is the form in which the test is compared with the algebraic-space-valued test of
Stacks 04XC, where the base change is presented as a morphism of representing presheaves and
not as an abstract algebraic space over `U`.

## Main results

* `AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff`: the structural morphism of Stacks 04SG
  and `CategoryTheory.OverShriek.relocalizeToYoneda` have the same properties.
* `AlgebraicGeometry.Stack.hasRelativeProperty_iff_relocalize`: **Stacks 03YK** read through
  that identification.

## Implementation notes

The identification is `AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso`, which says the
forward functor of Stacks 04SG followed by forgetting the structural morphism is the lower-shriek
extension, together with
`AlgebraicGeometry.spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app`, which says that
identification is one *over* the representable algebraic space of `U`. Since `P` respects
isomorphisms, that is all the comparison needs.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The structural morphism of Stacks 04SG is the structural morphism of the lower-shriek
extension.** An algebraic space `F` over a scheme `U` over `S`, read as an algebraic space over
`S` with a morphism to the representable algebraic space of `U` by the forward functor of
Stacks 04SG, has structural morphism isomorphic to
`CategoryTheory.OverShriek.relocalizeToYoneda`; so the two have the same properties. -/
theorem prop_algebraicSpaceMap_iff
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    (U : BigFppfOver B S hS) (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F) :
    P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) ↔
      P (ObjectProperty.homMk (OverShriek.relocalizeToYoneda U.hom F) :
        (⟨(OverShriek.relocalizePresheafFunctor U.hom).obj F,
            isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom F hF⟩ :
          AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) := by
  set i := (spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).app ⟨F, hF⟩
  refine P.arrow_mk_iso_iff (Arrow.isoMk (ObjectProperty.isoMk _ i) (Iso.refl _) ?_)
  apply ObjectProperty.hom_ext
  show i.hom ≫ OverShriek.relocalizeToYoneda U.hom F = _ ≫ 𝟙 _
  rw [Category.comp_id]
  apply (cancel_epi i.inv).mp
  simp only [Iso.inv_hom_id_assoc]
  ext W s
  exact (spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U.left.1 S U.left.2 hS U.hom
    ⟨F, hF⟩ W s).symm

/-- **Stacks 03YK read on the lower-shriek extension.** A representable 1-morphism has the
relative property `P` exactly when, for every scheme-valued point of the target and every
presheaf representing the base change along it, the structural morphism of the lower-shriek
extension of that presheaf has `P` as a morphism of algebraic spaces over `S`. -/
theorem hasRelativeProperty_iff_relocalize
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    HasRelativeProperty B S hS P f hf ↔
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (ObjectProperty.homMk (OverShriek.relocalizeToYoneda U.hom F) :
          (⟨(OverShriek.relocalizePresheafFunctor U.hom).obj F,
              isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom F hF⟩ :
            AlgebraicSpaces B S hS) ⟶
          (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) := by
  constructor <;> intro H U y hy F hF he
  · exact (prop_algebraicSpaceMap_iff B S hS P U F hF).mp (H U y hy F hF he)
  · exact (prop_algebraicSpaceMap_iff B S hS P U F hF).mpr (H U y hy F hF he)

end AlgebraicGeometry.Stack

end

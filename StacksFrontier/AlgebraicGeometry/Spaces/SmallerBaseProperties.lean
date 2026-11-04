module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Properties of morphisms viewed over a larger base

Let `g : S ⟶ S'` be a morphism of a big fppf site, let `F` be an algebraic space over `S` and let
`f : h_T ⟶ F` be a morphism from the representable algebraic space of an object `T` of the big
fppf site of `S`. Viewing `F` over `S'` through the forward functor
`AlgebraicGeometry.spacesOverSmallerBaseFunctor` of Stacks 04SG carries `f` to a morphism of
presheaves on the big fppf site of `S'`, and a property of morphisms of schemes tested on
representable base changes holds for one exactly when it holds for the other.

## Main results

* `AlgebraicGeometry.presheaf_property_map_base_iff`: **Stacks 03I6**, a representable property
  of a morphism from a scheme to an algebraic space is unchanged by viewing both over a larger
  base.

## Implementation notes

Forgetting the structural morphism to the representable algebraic space of `S` identifies the
image of `f` with the lower-shriek extension `Λ_g f`
(`AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso`), so the two morphisms have isomorphic
arrows and `CategoryTheory.MorphismProperty.arrow_mk_iso_iff` moves the property between them.

For `Λ_g` itself the statement is the general-site pair
`CategoryTheory.OverShriek.presheaf_map_relocalize` and
`CategoryTheory.OverShriek.presheaf_of_presheaf_map_relocalize`: a represented base change of
`Λ_g f` is `Λ_g` of a represented base change of `f`, over an object of the big fppf site of `S`
with the same underlying scheme. Since `Over.map g` does not change the underlying scheme of an
object or of a morphism, the two inverse-image properties agree on the nose, and the transport
hypotheses of those two lemmas are satisfied by the identity.

Representability of `f` is not assumed: it comes from the representable diagonal of `F`.

## References

* [Stacks Project, Tag 03I6](https://stacks.math.columbia.edu/tag/03I6)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 03I6.** Let `g : S ⟶ S'` be a morphism of a big fppf site and let `P` be a property
of morphisms of schemes stable under base change. For an algebraic space `F` over `S` and a
morphism `f : h_T ⟶ F` from the representable algebraic space of an object `T` of the big fppf
site of `S`, the morphism `P`-property of representable base changes holds for the image of `f`
under the forward functor of Stacks 04SG exactly when it holds for `f`. -/
@[stacks 03I6]
theorem presheaf_property_map_base_iff
    (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (T : BigFppfOver B S hS) (F : AlgebraicSpaces B S hS) (f : yoneda.obj T ⟶ F.obj) :
    MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S' hS'))
        ((spacesOverSmallerBaseFunctor B S S' hS hS' g).map
          (ObjectProperty.homMk f :
            (schemeSpace T : AlgebraicSpaces B S hS) ⟶
              F)).hom.left ↔
      MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS)) f := by
  set Tspace : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  set fspace : Tspace ⟶ F := ObjectProperty.homMk f
  have _ : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  set Q' := P.inverseImage (BigFppfOver.toScheme B S' hS')
  set Λ := OverShriek.relocalizePresheafFunctor g
  set i := spacesOverSmallerBaseFunctorForgetIso B S S' hS hS' g
  -- The image of `f` and the lower-shriek extension `Λ_g f` have isomorphic arrows.
  have hnat : ((spacesOverSmallerBaseFunctor B S S' hS hS' g).map fspace).hom.left ≫
      i.hom.app F = i.hom.app Tspace ≫ Λ.map f := i.hom.naturality fspace
  have harrow : MorphismProperty.presheaf Q'
        ((spacesOverSmallerBaseFunctor B S S' hS hS' g).map fspace).hom.left ↔
      MorphismProperty.presheaf Q' (Λ.map f) :=
    MorphismProperty.arrow_mk_iso_iff _
      (Arrow.isoMk (i.app Tspace) (i.app F) (by simpa using hnat.symm))
  have _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  refine harrow.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact OverShriek.presheaf_of_presheaf_map_relocalize g (fun _ hk => hk)
      (F.property.diagonal_representable.of_diag f) h
  · exact OverShriek.presheaf_map_relocalize g (fun _ hk => hk) h

end AlgebraicGeometry

end

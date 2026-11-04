module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeFibreRestrict

/-!
# Representability of a map of presheaves and of its fibred category (Stacks 0458)

Let `S` be a scheme contained in a big fppf site `B` and let `a : F ⟶ G` be a map of set-valued
presheaves on the big fppf site of `S`. Then `a` is representable by algebraic spaces in the sense
of Stacks 02YQ — every base change of `a` along a scheme-valued point of `G` is an algebraic space
over `S` — exactly when the 1-morphism of categories fibred in groupoids it induces is
representable by algebraic spaces in the sense of Stacks 02ZW. A property of morphisms of
algebraic spaces over `S` which is stable under base change and local on the target then holds of
`a` in the sense of Stacks 03XZ exactly when it holds of that 1-morphism in the relative sense of
Stacks 03YK.

Both sides test the same object. A scheme-valued point of the category of elements of `G` over a
scheme `U` over `S` names a section of `G` over `U` and conversely, and the base change of the
1-morphism along such a point is represented by the fibre of `a` over that section, a presheaf on
the big fppf site of `U`. The relocalization of that fibre along the structure morphism of `U` is
the base change of `a` along the section, so the two conditions differ only by passing between an
algebraic space over `U` and its lower-shriek extension to `S`, which is Stacks 03I5 (2) in one
direction and a fibre product of algebraic spaces over `U` in the other.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_fibreOfSection`: the fibre of a map of presheaves over
  a scheme-valued point of its target is an algebraic space over that scheme as soon as the base
  change of the map along that point is an algebraic space over `S`.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_associatedMap`: **Stacks 0458**,
  representability equivalence.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_associatedMap`: the same equivalence under the
  shorter name used by the consumers that quantify only over maps of presheaves.
* `AlgebraicGeometry.Stack.holdsOnEverySchemePoint_iff_hasRelativeProperty`: **Stacks 045A**.

## Implementation notes

The representing presheaf of a base change is
`CategoryTheory.PresheafOfCategories.twoFibreProductPresheaf`, and
`CategoryTheory.PresheafOfCategories.fibreOfSection_eq_twoFibreProductPresheaf` identifies it with
`CategoryTheory.OverShriek.fibreOfSection`; everything else is read off the two cartesian squares
that fibre carries. One slice up,
`CategoryTheory.PresheafOfCategories.exists_isPullback_relocalize_twoFibreProductPresheaf` says
its relocalization is the base change of `a` along the section, which gives the implication from
the 1-morphism to the map of presheaves by Stacks 03I5 (2). On the slice of `U`,
`CategoryTheory.OverShriek.isPullback_fibreOfSectionι` says the fibre is the fibre product of the
restriction of `a` and of the point named by the section; pasting that with the restriction of the
cartesian square of the base change exhibits it as a fibre product of restrictions of algebraic
spaces, where Stacks 02X2 and Stacks 03I5 (1) apply. That pasting is the content of
`AlgebraicGeometry.Space.isAlgebraicSpace_fibreOfSection`, and it is where the implication from
the map of presheaves to the 1-morphism is paid for.

The representing presheaf a consumer of Stacks 02ZW supplies is arbitrary, so in that direction it
is first identified with the canonical one by
`CategoryTheory.PresheafOfCategories.isoOfEquivalenceOver`.

The induced 1-morphism is `AlgebraicGeometry.Stack.associatedMap`, which is packaged as a subtype
recording its value in each fibre; the representability statement is about its underlying based
functor, so the statement reads the first component. The category of elements of a presheaf of
discrete groupoids and the category of elements of the same presheaf viewed as a presheaf of
discrete categories agree by construction, which is what lets the apparatus of
`CategoryTheory.PresheafOfCategories` apply to `AlgebraicGeometry.Stack.fibredCategory`.

Stacks 045A is stated here rather than alongside the comparison it rests on, because the relative
property of Stacks 03YK carries a representability witness for the 1-morphism in its signature
and the only hypothesis the statement has is representability of `a`: the witness is the image of
that hypothesis under the equivalence proved above. Both directions rest on the single comparison
`AlgebraicGeometry.Stack.prop_pullback_iff_prop_representative`, which is stated for a point of
the category of elements of `G` *and* a section of `G` naming the same family of elements. The
forward direction feeds it the section `CategoryTheory.PresheafOfCategories.sectionOfPoint` that
the point names, the backward direction the point
`AlgebraicGeometry.Stack.pointOfSchemePoint` that the section names.

## References

* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 02YQ](https://stacks.math.columbia.edu/tag/02YQ)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045A](https://stacks.math.columbia.edu/tag/045A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.OverShriek Opposite
open CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace Space

/-- **The fibre of a map of presheaves over a scheme-valued point of its target is an algebraic
space over that scheme**, as soon as the base change of the map along that point is an algebraic
space over `S`.

The fibre is the fibre product, on the big fppf site of `U`, of the restriction of `a` along the
structure morphism of `U` and of the point of the restriction of `G` named by `β`
(`CategoryTheory.OverShriek.isPullback_fibreOfSectionι`). Restricting the cartesian square of the
base change identifies that fibre product with one whose three other corners are restrictions of
algebraic spaces over `S`, namely of the base change, of the representable presheaf of `U` and of
the representable presheaf of the identity of `U`; Stacks 03I5 (1) and Stacks 02X2 then apply. -/
theorem isAlgebraicSpace_fibreOfSection (U : BigFppfOver B S hS)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (β : yoneda.obj (Over.mk U.hom) ⟶ G)
    (hβ : IsAlgebraicSpace B S hS (pullback β a)) :
    IsAlgebraicSpace B U.left.1 U.left.2 (fibreOfSection U.hom a β) := by
  have hrestrict := (IsPullback.of_hasPullback β a).map (relocalizeRestrict U.hom)
  have hpaste := (IsPullback.of_hasPullback
    ((relocalizeRestrict U.hom).map (pullback.fst β a))
    (pointOfSection U.hom (𝟙 (yoneda.obj (Over.mk U.hom))))).paste_horiz hrestrict.flip
  rw [← pointOfSection_eq U.hom β] at hpaste
  refine isAlgebraicSpace_of_iso B U.left.1 U.left.2
    (hpaste.isoIsPullback _ _ (isPullback_fibreOfSectionι U.hom a β)) ?_
  exact isAlgebraicSpace_pullback B U.left.1 U.left.2 _ _
    (isAlgebraicSpace_relocalizeRestrict B U.left.1 S U.left.2 hS U.hom _ hβ)
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 (Over.mk (𝟙 U.left)))
    (isAlgebraicSpace_relocalizeRestrict B U.left.1 S U.left.2 hS U.hom _
      (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)))

end Space

namespace Stack

/-- **Stacks 0458**, representability equivalence. A map `a : F ⟶ G` of set-valued presheaves on
the big fppf site of `S` is representable by algebraic spaces exactly when the 1-morphism of
categories fibred in groupoids it induces, `AlgebraicGeometry.Stack.associatedMap`, is.

A scheme-valued point of the category of elements of `G` over a scheme `U` over `S` and a section
of `G` over `U` naming the same family of elements have the same base change of `a`: the presheaf
representing the base change of the 1-morphism along the point is the fibre of `a` over the
section, and the relocalization of that fibre along the structure morphism of `U` is the base
change of `a` along the section. -/
@[stacks 0458 "representability equivalence"]
theorem isRepresentableByAlgebraicSpaces_iff_associatedMap
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    Space.IsRepresentableByAlgebraicSpaces B S hS a ↔
      IsRepresentableByAlgebraicSpaces B S hS (associatedMap B S hS a).1.hom := by
  constructor
  · intro ha U _ _ y hy
    refine ⟨twoFibreProductPresheaf y hy (elementsMap a) (elementsMap_comp_eq a), ?_,
      nonempty_equivalenceOver_twoFibreProductPresheaf U.hom (elementsMap a)
        (elementsMap_comp_eq a) y hy⟩
    obtain ⟨β, hβ⟩ := exists_section_sectionOfBasedFunctor_eq U.hom y hy
    rw [← fibreOfSection_eq_twoFibreProductPresheaf U.hom (elementsMap a)
      (elementsMap_comp_eq a) y hy β hβ, natTransOfBasedFunctor_elementsMap a]
    exact Space.isAlgebraicSpace_fibreOfSection B S hS U a β (ha (Over.mk U.hom) β)
  · intro hf U ξ
    obtain ⟨H, hH, ⟨eH⟩⟩ := hf U (pointOfSchemePoint B S hS U ξ)
      (pointOfSchemePoint_comp_eq B S hS U ξ)
    obtain ⟨eW⟩ := nonempty_equivalenceOver_twoFibreProductPresheaf U.hom (elementsMap a)
      (elementsMap_comp_eq a) (pointOfSchemePoint B S hS U ξ)
      (pointOfSchemePoint_comp_eq B S hS U ξ)
    have eH' : StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) (discreteProjection F) (discreteProjection G)
          (pointOfSchemePoint B S hS U ξ) (elementsMap a)) (discreteProjection H) := eH
    have hW := Space.isAlgebraicSpace_of_iso B U.left.1 U.left.2 (isoOfEquivalenceOver eH' eW) hH
    obtain ⟨c, hc⟩ := exists_isPullback_relocalize_twoFibreProductPresheaf U.hom (elementsMap a)
      (elementsMap_comp_eq a) (pointOfSchemePoint B S hS U ξ)
      (pointOfSchemePoint_comp_eq B S hS U ξ) ξ
      (sectionOfBasedFunctor_pointOfSchemePoint B S hS U ξ)
    rw [natTransOfBasedFunctor_elementsMap a] at hc
    exact Space.isAlgebraicSpace_of_iso B S hS hc.flip.isoPullback
      (Space.isAlgebraicSpace_relocalizePresheaf B S hS U _ hW)

/-- **Stacks 045A.** Let `P` be a property of morphisms of algebraic spaces over `S` which is
stable under base change and local on the target for the fppf precoverage. A map `a : F ⟶ G` of
presheaves on the big fppf site of `S` which is representable by algebraic spaces has `P` in the
sense of Stacks 03XZ exactly when the 1-morphism of categories fibred in groupoids attached to it
by Stacks 0458 has the relative property `P` of Stacks 03YK. -/
@[stacks 045A]
theorem holdsOnEverySchemePoint_iff_hasRelativeProperty
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : Space.IsRepresentableByAlgebraicSpaces B S hS a) :
    Space.HasProperty B S hS P a ha ↔
      HasRelativeProperty B S hS P (associatedMap B S hS a).1
        ((isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS a).1 ha) := by
  have hf := (isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS a).1 ha
  constructor
  · intro h U y hy H hH hE
    obtain ⟨eH⟩ := hE
    obtain ⟨β, hβ⟩ := exists_section_sectionOfBasedFunctor_eq U.hom y hy
    exact (prop_pullback_iff_prop_representative B S hS P a ha U y hy H hH eH β hβ).1
      (h (Over.mk U.hom) β)
  · intro h U ξ
    obtain ⟨H, hH, ⟨eH⟩⟩ := hf U (pointOfSchemePoint B S hS U ξ)
      (pointOfSchemePoint_comp_eq B S hS U ξ)
    exact (prop_pullback_iff_prop_representative B S hS P a ha U
      (pointOfSchemePoint B S hS U ξ) (pointOfSchemePoint_comp_eq B S hS U ξ) H hH eH ξ
      (sectionOfBasedFunctor_pointOfSchemePoint B S hS U ξ)).2
      (h U (pointOfSchemePoint B S hS U ξ) (pointOfSchemePoint_comp_eq B S hS U ξ) H hH ⟨eH⟩)

end Stack

end AlgebraicGeometry

end

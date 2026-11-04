module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements

/-!
# The two tests of a relative property, at one scheme-valued point (Stacks 045A)

Let `a : F ⟶ G` be a map of presheaves on the big fppf site of `S` which is representable by
algebraic spaces, and let `P` be a property of morphisms of algebraic spaces over `S`. Then `a`
has `P` in the sense of Stacks 03XZ — every base change of `a` to a scheme-valued point of `G`
has `P` — exactly when the 1-morphism of categories fibred in groupoids attached to `a` by
Stacks 0458 has the relative property `P` of Stacks 03YK. This file proves the comparison of the
two tests at a single scheme-valued point; the equivalence itself,
`AlgebraicGeometry.Stack.holdsOnEverySchemePoint_iff_hasRelativeProperty`, is stated in
`StacksFrontier.AlgebraicGeometry.Stacks.PresheafRepresentability`, where the representability
equivalence of Stacks 0458 that its statement calls on is available.

Both sides test `P` on a base change of `a`. On the left the base change is taken along a point
`ξ : h_U ⟶ G` of the presheaf; on the right along a point `y : (Sch/U)_fppf ⥤ S_G` of the
category of elements, and the resulting algebraic space is only pinned down up to equivalence
over the site. The two are matched by the two constructions that pass between a point of `S_G`
and a section of `G`: `CategoryTheory.PresheafOfCategories.sectionOfPoint` in one direction and
`AlgebraicGeometry.Stack.pointOfSchemePoint` in the other.

## Main definitions

* `AlgebraicGeometry.Stack.pointOfSchemePoint`: the scheme-valued point of `S_G` named by a
  scheme-valued point `h_U ⟶ G` of `G`.

## Main results

* `AlgebraicGeometry.Stack.prop_pullback_iff_prop_representative`: the two tests of Stacks 045A
  agree at one scheme-valued point.

## Implementation notes

The representing algebraic space of the base change is arbitrary, so it is first identified with
`CategoryTheory.PresheafOfCategories.twoFibreProductPresheaf` by
`CategoryTheory.PresheafOfCategories.isoOfEquivalenceOver`, whose relocalization is the fibre
product of `a` with the section by
`CategoryTheory.PresheafOfCategories.exists_isPullback_relocalize_twoFibreProductPresheaf`. The
passage from that relocalization to the morphism of algebraic spaces over `S` that Stacks 03YK
speaks about is `AlgebraicGeometry.Space.prop_relocalizeToYoneda_iff` of Stacks 04SG. Only
`CategoryTheory.MorphismProperty.RespectsIso` is used of `P` by that comparison; the two standing
instances of Stacks 03YK appear because its definition carries them.

## References

* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 045A](https://stacks.math.columbia.edu/tag/045A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.OverShriek Opposite
open CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The scheme-valued point of `S_G` named by a scheme-valued point of `G`.** A point
`ξ : h_U ⟶ G` of a presheaf `G` on the big fppf site of `S` sends an object `τ` of the big fppf
site of `U` to the restriction of `ξ` along the tautological morphism of `τ`, and that family of
elements of `G` is a 1-morphism from the big fppf site of `U` to the category of elements of `G`
over `CategoryTheory.Over.map U.hom`.

It is the composite of the identification of the big fppf site of `U` with the slice of the big
fppf site of `S` at `U`, of `CategoryTheory.PresheafOfCategories.sliceToElements` and of the
1-morphism of categories of elements induced by `ξ`. -/
def pointOfSchemePoint (U : BigFppfOver B S hS) {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (ξ : yoneda.obj U ⟶ G) :
    BigFppfOver B U.left.1 U.left.2 ⥤ (presheafOfCategories (G ⋙ typeToCat)).obj :=
  Over.iteratedSliceBackward U ⋙ sliceToElements U ⋙ elementsMap ξ

/-- `AlgebraicGeometry.Stack.pointOfSchemePoint` is a scheme-valued point: it lies over
`CategoryTheory.Over.map U.hom`. -/
theorem pointOfSchemePoint_comp_eq (U : BigFppfOver B S hS)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ξ : yoneda.obj U ⟶ G) :
    pointOfSchemePoint B S hS U ξ ⋙ discreteProjection G = Over.map U.hom :=
  rfl

/-- **The point `AlgebraicGeometry.Stack.pointOfSchemePoint` names the family of restrictions of
`ξ`.** This is the hypothesis of
`CategoryTheory.PresheafOfCategories.exists_isPullback_relocalize_twoFibreProductPresheaf` for
the point attached to a section, and it holds by construction. -/
theorem sectionOfBasedFunctor_pointOfSchemePoint (U : BigFppfOver B S hS)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ξ : yoneda.obj U ⟶ G)
    (τ : BigFppfOver B U.left.1 U.left.2) :
    ξ.app (op ((Over.map U.hom).obj τ)) (overMapTautHom U.hom τ) =
      sectionOfBasedFunctor (pointOfSchemePoint B S hS U ξ)
        (pointOfSchemePoint_comp_eq B S hS U ξ) τ :=
  rfl

/-- **The two tests of Stacks 045A agree, at one scheme-valued point.** Let `a : F ⟶ G` be a map
of presheaves representable by algebraic spaces, let `y` be a scheme-valued point of the category
of elements of `G` over a scheme `U` over `S`, let `H` be *any* presheaf on the big fppf site of
`U` representing the base change of `El a` along `y`, and let `ξ` be a section of `G` over `U`
naming the same family of elements as `y`. Then the structural morphism of the lower-shriek
extension of `H` has `P` exactly when the base change of `a` along `ξ` does.

Both are base changes of `a` along `ξ`: the relocalization of the presheaf
`CategoryTheory.PresheafOfCategories.twoFibreProductPresheaf` is one by
`CategoryTheory.PresheafOfCategories.exists_isPullback_relocalize_twoFibreProductPresheaf`, and
`H` is isomorphic to that presheaf because both represent the same base change. -/
theorem prop_pullback_iff_prop_representative
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : Space.IsRepresentableByAlgebraicSpaces B S hS a)
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ (presheafOfCategories (G ⋙ typeToCat)).obj)
    (hy : y ⋙ discreteProjection G = Over.map U.hom)
    (H : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hH : IsAlgebraicSpace B U.left.1 U.left.2 H)
    (eH : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) (discreteProjection F) (discreteProjection G) y
        (elementsMap a)) (discreteProjection H))
    (ξ : yoneda.obj (Over.mk U.hom) ⟶ G)
    (hξ : ∀ τ : BigFppfOver B U.left.1 U.left.2,
      ξ.app (op ((Over.map U.hom).obj τ)) (overMapTautHom U.hom τ) =
        sectionOfBasedFunctor y hy τ) :
    P (ObjectProperty.homMk (pullback.fst ξ a) :
        (⟨pullback ξ a, ha (Over.mk U.hom) ξ⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩) ↔
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨H, hH⟩)) := by
  obtain ⟨eW⟩ := nonempty_equivalenceOver_twoFibreProductPresheaf U.hom (elementsMap a)
    (elementsMap_comp_eq a) y hy
  have iso : H ≅ twoFibreProductPresheaf y hy (elementsMap a) (elementsMap_comp_eq a) :=
    isoOfEquivalenceOver eH eW
  have hW : IsAlgebraicSpace B U.left.1 U.left.2
      (twoFibreProductPresheaf y hy (elementsMap a) (elementsMap_comp_eq a)) :=
    Space.isAlgebraicSpace_of_iso B U.left.1 U.left.2 iso hH
  obtain ⟨c, hc⟩ := exists_isPullback_relocalize_twoFibreProductPresheaf U.hom (elementsMap a)
    (elementsMap_comp_eq a) y hy ξ hξ
  rw [natTransOfBasedFunctor_elementsMap a] at hc
  rw [← Space.prop_relocalizeToYoneda_iff B S hS P U H hH,
    Space.prop_relocalizeToYoneda_congr B S hS P U hH hW iso]
  refine (P.arrow_mk_iso_iff (Arrow.isoMk
    (ObjectProperty.isoMk _ hc.flip.isoPullback :
      (⟨(relocalizePresheafFunctor U.hom).obj
          (twoFibreProductPresheaf y hy (elementsMap a) (elementsMap_comp_eq a)),
        Space.isAlgebraicSpace_relocalizePresheaf B S hS U _ hW⟩ : AlgebraicSpaces B S hS) ≅
        ⟨pullback ξ a, ha (Over.mk U.hom) ξ⟩)
    (Iso.refl _) ?_)).symm
  apply ObjectProperty.hom_ext
  exact hc.flip.isoPullback_hom_fst.trans (Category.comp_id _).symm

end AlgebraicGeometry.Stack

end

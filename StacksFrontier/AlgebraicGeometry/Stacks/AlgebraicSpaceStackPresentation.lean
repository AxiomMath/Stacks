module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangePoint

/-!
# The stack of an algebraic space is Deligne-Mumford (Stacks 03YS, part (2))

Let `S` be a scheme contained in a big fppf site `B` and let `F` be an algebraic space over `S`.
The category of elements `S_F` of `F`, read as a category fibred in groupoids over the big fppf
site of `S`, is an algebraic stack, and in fact a Deligne-Mumford stack.

Three of the four clauses are already available: it is fibred in groupoids by construction, it is a
stack in groupoids because `F` is an fppf sheaf (Stacks 0432,
`AlgebraicGeometry.Stack.isStackInGroupoids_fibredCategory`), and its diagonal is representable
by algebraic spaces by Stacks 02ZZ
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_diagonalBasedFunctor`). What is proved
here is the presentation clause. A scheme atlas `h_U ⟶ F` of `F` is surjective and étale, hence
also surjective and smooth (Stacks 04XX), and the 1-morphism `(Sch/U)_fppf ⟶ S_F` it induces
inherits those properties — which is the instance of Stacks 045A that the source's proof of
Stacks 03YS cites.

That step is here for an arbitrary property `P` of morphisms of algebraic spaces over `S` stable
under base change: *the structural morphism of the lower-shriek extension of any presheaf
representing the base change of the induced 1-morphism along any scheme-valued point of `S_F` is
a base change of the atlas itself*
(`AlgebraicGeometry.Stack.prop_presentationBasedFunctor`). The surjective, smooth and étale
cases are instances.

## Main definitions

* `AlgebraicGeometry.Stack.presentationBasedFunctor`: the 1-morphism `(Sch/U)_fppf ⟶ S_F`
  induced by a morphism of presheaves `h_U ⟶ F`.
* `AlgebraicGeometry.Stack.algebraicSpaceStack`: an algebraic space over `S`, regarded as an
  object of the 2-category of algebraic stacks over `S`.

## Main results

* `AlgebraicGeometry.Stack.prop_relocalizeToYoneda_of_point`: the relative test of Stacks 03YK
  for a morphism of presheaves, at an arbitrary scheme-valued point of the target and an
  arbitrary representing presheaf of the base change, is a base change of that morphism. This is
  the content of the instance of Stacks 045A that Stacks 03YS uses.
* `AlgebraicGeometry.Stack.prop_presentationBasedFunctor`: the same statement for the induced
  1-morphism, i.e. with the base change read over the slice `(Sch/U)_fppf` rather than over the
  category of elements of `h_U`.
* `AlgebraicGeometry.Stack.isAlgebraicStack_fibredCategory`: the stack of an algebraic space is
  an algebraic stack, **Stacks 026O** for `S_F`.
* `AlgebraicGeometry.Stack.isDeligneMumfordStack_fibredCategory`: **Stacks 03YS**, part (2).

## Implementation notes

The presentation clause of `AlgebraicGeometry.Stack.IsAlgebraicStack` quantifies over *every*
presheaf representing the base change, so the first step is to identify an arbitrary such
presheaf with the one the machinery of Stacks 02ZZ produces,
`CategoryTheory.PresheafOfCategories.twoFibreProductPresheaf`; that is
`CategoryTheory.PresheafOfCategories.isoOfEquivalenceOver`, and `P` absorbs the comparison
because `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` implies
`CategoryTheory.MorphismProperty.RespectsIso`. The relocalization of that presheaf is then the
fibre product of the atlas with the representable presheaf of the point, by
`CategoryTheory.PresheafOfCategories.exists_isPullback_relocalize_of_point` — the point names the
section of `F` to base change along. The square is cartesian in the category of algebraic spaces
because the inclusion of that full subcategory reflects fibre products, which is
`CategoryTheory.IsPullback.of_map_of_faithful` against
`AlgebraicGeometry.Space.algebraicSpaceProperty_isClosedUnderLimitsOfShape_walkingCospan`.

The source of the induced 1-morphism is the slice `(Sch/U)_fppf`, not the category of elements of
`h_U`, so the base change has to be transported along
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`. That is
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_fst_of_equivalence_source`, which moves the
*second factor* of the 2-fibre product and commutes with the first projection on the nose.

No locality hypothesis on `P` is used, and in particular neither the fppf
`CategoryTheory.MorphismProperty.IsLocalAtTarget` instance of Stacks 0429 nor Stacks 04YL is
needed: the test is identified with a base change of one fixed morphism, not glued from a
covering. That is why the combined surjective-and-smooth and surjective-and-étale conditions,
for which no locality instance is available, can be discharged.

The descent universe of the stack condition is free, as it is in
`AlgebraicGeometry.Stack.isStackInGroupoids_fibredCategory`: an algebraic space is an fppf sheaf,
so its category of elements is a stack in sets at every descent universe, and nothing else in the
definition mentions that universe.

Stacks 045A itself — the comparison of the relative property of a morphism of presheaves with
that of its associated 1-morphism — is not stated here: its left-hand side is the property of
Bootstrap, Definition 03XZ, which this library does not have.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 02ZZ](https://stacks.math.columbia.edu/tag/02ZZ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03YS](https://stacks.math.columbia.edu/tag/03YS)
* [Stacks Project, Tag 045A](https://stacks.math.columbia.edu/tag/045A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.OverShriek
open CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace Space

/-- **The structural morphism of a lower-shriek extension depends on the presheaf only up to
isomorphism.** Isomorphic algebraic spaces over a scheme `U` over `S` have, as algebraic spaces
over `S` with their structural morphism to the representable algebraic space of `U`, the same
properties, as soon as `P` respects isomorphisms. -/
theorem prop_relocalizeToYoneda_congr (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.RespectsIso] (U : BigFppfOver B S hS)
    {F F' : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hF' : IsAlgebraicSpace B U.left.1 U.left.2 F') (e : F ≅ F') :
    P (ObjectProperty.homMk (relocalizeToYoneda U.hom F) :
        (⟨(relocalizePresheafFunctor U.hom).obj F,
            isAlgebraicSpace_relocalizePresheaf B S hS U F hF⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩) ↔
      P (ObjectProperty.homMk (relocalizeToYoneda U.hom F') :
        (⟨(relocalizePresheafFunctor U.hom).obj F',
            isAlgebraicSpace_relocalizePresheaf B S hS U F' hF'⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩) := by
  refine P.arrow_mk_iso_iff (Arrow.isoMk
    (ObjectProperty.isoMk _ ((relocalizePresheafFunctor U.hom).mapIso e)) (Iso.refl _) ?_)
  exact ObjectProperty.hom_ext _
    ((relocalizePresheafFunctor_map_comp_relocalizeToYoneda U.hom e.hom).trans
      (Category.comp_id _).symm)

end Space

namespace Stack

/-- **The relative test of Stacks 03YK for a morphism of presheaves is a base change of that
morphism.** Let `a : X ⟶ F` be a morphism of algebraic spaces over `S`, let `y` be a
scheme-valued point of the category of elements of `F` over a scheme `V` over `S`, and let `G` be
any presheaf on the big fppf site of `V` representing the base change of `El a` along `y`. Then
the structural morphism of the lower-shriek extension of `G` is a base change of `a`, so it has
every property of `a` that is stable under base change.

The point `y` names a section of `F` over `V`, and `G` is identified with
`CategoryTheory.PresheafOfCategories.twoFibreProductPresheaf`, whose relocalization is the fibre
product of `a` with that section. -/
theorem prop_relocalizeToYoneda_of_point
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    {Xp F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hXp : IsAlgebraicSpace B S hS Xp) (hF : IsAlgebraicSpace B S hS F)
    (atl : Xp ⟶ F)
    (hatl : P (ObjectProperty.homMk atl : (⟨Xp, hXp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩))
    (V : BigFppfOver B S hS)
    (y : BigFppfOver B V.left.1 V.left.2 ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hy : y ⋙ discreteProjection F = Over.map V.hom)
    (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hG : IsAlgebraicSpace B V.left.1 V.left.2 G)
    (he : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom) (discreteProjection Xp) (discreteProjection F) y
        (elementsMap atl))
      (discreteProjection G))) :
    P (algebraicSpaceMap B S hS V
      ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩)) := by
  obtain ⟨eG⟩ := he
  obtain ⟨eW⟩ := nonempty_equivalenceOver_twoFibreProductPresheaf V.hom (elementsMap atl)
    (elementsMap_comp_eq atl) y hy
  -- The arbitrary representing presheaf is the one the machinery of Stacks 02ZZ produces.
  have iso : G ≅ twoFibreProductPresheaf y hy (elementsMap atl) (elementsMap_comp_eq atl) :=
    isoOfEquivalenceOver eG eW
  have hW : IsAlgebraicSpace B V.left.1 V.left.2
      (twoFibreProductPresheaf y hy (elementsMap atl) (elementsMap_comp_eq atl)) :=
    isAlgebraicSpace_of_iso B V.left.1 V.left.2 iso.symm hG
  -- Its relocalization is the fibre product of `atl` with the section of `F` that `y` names.
  obtain ⟨β, c, hc⟩ := exists_isPullback_relocalize_of_point V.hom y hy (elementsMap atl)
    (elementsMap_comp_eq atl)
  rw [natTransOfBasedFunctor_elementsMap atl] at hc
  have hsq : IsPullback
      (ObjectProperty.homMk c :
        (⟨(relocalizePresheafFunctor V.hom).obj
            (twoFibreProductPresheaf y hy (elementsMap atl) (elementsMap_comp_eq atl)),
          Space.isAlgebraicSpace_relocalizePresheaf B S hS V _ hW⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨Xp, hXp⟩)
      (ObjectProperty.homMk (relocalizeToYoneda V.hom
          (twoFibreProductPresheaf y hy (elementsMap atl) (elementsMap_comp_eq atl))) :
        (⟨(relocalizePresheafFunctor V.hom).obj
            (twoFibreProductPresheaf y hy (elementsMap atl) (elementsMap_comp_eq atl)),
          Space.isAlgebraicSpace_relocalizePresheaf B S hS V _ hW⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj (Over.mk V.hom), isAlgebraicSpace_yoneda B S hS (Over.mk V.hom)⟩)
      (ObjectProperty.homMk atl : (⟨Xp, hXp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)
      (ObjectProperty.homMk β :
        (⟨yoneda.obj (Over.mk V.hom), isAlgebraicSpace_yoneda B S hS (Over.mk V.hom)⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hc
  exact (Space.prop_relocalizeToYoneda_iff B S hS P V G hG).1
    ((Space.prop_relocalizeToYoneda_congr B S hS P V hG hW iso).2
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq hatl))

/-- **The 1-morphism `(Sch/U)_fppf ⟶ S_F` attached to a morphism of presheaves `h_U ⟶ F`**: the
slice is the category of elements of `h_U` by
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`, and a morphism of presheaves
induces a 1-morphism of categories of elements. This is the presentation of Stacks 026O that a
scheme atlas of an algebraic space supplies. -/
def presentationBasedFunctor (U : BigFppfOver B S hS)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (atl : yoneda.obj U ⟶ F) :
    (schemeFibredCategory B S hS U).val ⥤ᵇ (fibredCategory B S hS F).val :=
  BasedFunctor.comp
    ⟨(sliceElementsEquivalenceOver U).hom.functor, (sliceElementsEquivalenceOver U).hom.w⟩
    ⟨elementsMap atl, elementsMap_comp_eq atl⟩

/-- The 1-morphism `(Sch/U)_fppf ⟶ S_F` attached to a morphism of presheaves `h_U ⟶ F` is
faithful: it is an equivalence followed by the functor of categories of elements, which keeps
the underlying morphism of the site. -/
theorem faithful_presentationBasedFunctor (U : BigFppfOver B S hS)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (atl : yoneda.obj U ⟶ F) :
    (presentationBasedFunctor B S hS U atl).toFunctor.Faithful := by
  have := (sliceElementsEquivalenceOver U).isEquivalence_hom_functor
  have := faithful_elementsMap atl
  exact Functor.Faithful.comp (sliceElementsEquivalenceOver U).hom.functor (elementsMap atl)

/-- The 1-morphism `(Sch/U)_fppf ⟶ S_F` attached to a monomorphism of presheaves `h_U ⟶ F` is
full: it is an equivalence followed by the functor of categories of elements, which is full
because a monomorphism of presheaves of sets is injective on sections. -/
theorem full_presentationBasedFunctor_of_mono (U : BigFppfOver B S hS)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (atl : yoneda.obj U ⟶ F) [Mono atl] :
    (presentationBasedFunctor B S hS U atl).toFunctor.Full := by
  have := (sliceElementsEquivalenceOver U).isEquivalence_hom_functor
  have := full_elementsMap_of_injective atl fun X =>
    (mono_iff_injective (atl.app X)).mp inferInstance
  exact Functor.Full.comp (sliceElementsEquivalenceOver U).hom.functor (elementsMap atl)

/-- **The instance of Stacks 045A that Stacks 03YS uses.** A property `P` of morphisms of
algebraic spaces over `S` which is stable under base change passes from a morphism of presheaves
`h_U ⟶ F` to the 1-morphism `(Sch/U)_fppf ⟶ S_F` it induces, in the sense of the presentation
clause of `AlgebraicGeometry.Stack.IsAlgebraicStack`: every presheaf representing a base change
of that 1-morphism along a scheme-valued point of `S_F` has structural morphism with `P`.

The base change is read over the slice rather than over the category of elements of `h_U`, so it
is transported by
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_fst_of_equivalence_source` before
`AlgebraicGeometry.Stack.prop_relocalizeToYoneda_of_point` applies. -/
theorem prop_presentationBasedFunctor
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    (U : BigFppfOver B S hS) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (atl : yoneda.obj U ⟶ F)
    (hatl : P (ObjectProperty.homMk atl :
      (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩))
    (V : BigFppfOver B S hS)
    (y : BigFppfOver B V.left.1 V.left.2 ⥤ (fibredCategory B S hS F).val.obj)
    (hy : y ⋙ (fibredCategory B S hS F).val.p = Over.map V.hom)
    (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hG : IsAlgebraicSpace B V.left.1 V.left.2 G)
    (he : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom) (schemeFibredCategory B S hS U).val.p
        (fibredCategory B S hS F).val.p y (presentationBasedFunctor B S hS U atl).toFunctor)
      (presheafOfCategories (G ⋙ typeToCat)).p)) :
    P (algebraicSpaceMap B S hS V
      ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩)) := by
  have : Functor.IsEquivalence
      (⟨(sliceElementsEquivalenceOver U).hom.functor,
          (sliceElementsEquivalenceOver U).hom.w⟩ :
        (schemeFibredCategory B S hS U).val ⥤ᵇ
          (fibredCategory B S hS (yoneda.obj U)).val).toFunctor :=
    (sliceElementsEquivalenceOver U).isEquivalence_hom_functor
  obtain ⟨et⟩ := nonempty_equivalenceOver_fst_of_equivalence_source B S hS
    (𝒳' := schemeFibredCategory B S hS U)
    (𝒳 := fibredCategory B S hS (yoneda.obj U)) (𝒴 := fibredCategory B S hS F)
    ⟨(sliceElementsEquivalenceOver U).hom.functor, (sliceElementsEquivalenceOver U).hom.w⟩
    ⟨elementsMap atl, elementsMap_comp_eq atl⟩ V y hy
  exact prop_relocalizeToYoneda_of_point B S hS P (isAlgebraicSpace_yoneda B S hS U) hF atl hatl
    V y hy G hG (he.map fun e => et.symm.trans e)

/-- **Stacks 026O for the stack of an algebraic space.** The category of elements of an algebraic
space `F` over `S`, read as a category fibred in groupoids over the big fppf site of `S`, is an
algebraic stack.

It is a stack in groupoids because `F` is an fppf sheaf, its diagonal is representable by
algebraic spaces by Stacks 02ZZ, and a scheme atlas of `F` presents it: the atlas is surjective
and smooth, and `AlgebraicGeometry.Stack.prop_presentationBasedFunctor` carries both properties
to the induced 1-morphism. -/
theorem isAlgebraicStack_fibredCategory (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    IsAlgebraicStack.{u, w} B S hS (fibredCategory B S hS F).val := by
  obtain ⟨U, atl, hsurj, hsmooth⟩ := Space.exists_isSurjective_isSmooth_atlas B S hS hF
  refine ⟨(fibredCategory B S hS F).isFiberedInGroupoids,
    ⟨isStack_fibredCategory B S hS F hF, isStackInGroupoids_fibredCategory B S hS F hF⟩,
    isRepresentableByAlgebraicSpaces_diagonalBasedFunctor B S hS (fibredCategory B S hS F)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF),
    U, presentationBasedFunctor B S hS U atl,
    isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpace B S hS
      (fibredCategory B S hS F)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF) U
      (presentationBasedFunctor B S hS U atl),
    fun V y hy G hG he => ⟨?_, ?_⟩⟩
  · exact prop_presentationBasedFunctor B S hS (Space.surjectiveMorphismProperty B S hS) U hF
      atl hsurj V y hy G hG he
  · exact prop_presentationBasedFunctor B S hS (Space.smoothMorphismProperty B S hS) U hF
      atl hsmooth V y hy G hG he

/-- **Stacks 03YS, part (2).** The category of elements of an algebraic space `F` over `S`, read
as a category fibred in groupoids over the big fppf site of `S`, is a Deligne-Mumford stack.

It is an algebraic stack by `AlgebraicGeometry.Stack.isAlgebraicStack_fibredCategory`, and the
same scheme atlas of `F` presents it étale-ly: the atlas of Stacks 025Y is surjective and étale,
and `AlgebraicGeometry.Stack.prop_presentationBasedFunctor` carries both properties to the
induced 1-morphism. -/
@[stacks 03YS "part (2)"]
theorem isDeligneMumfordStack_fibredCategory (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    IsDeligneMumfordStack.{u, w} B S hS (fibredCategory B S hS F).val := by
  obtain ⟨U, atl, hsurjp, hetalep⟩ := hF.exists_atlas
  have hsurj : Space.IsSurjective B S hS atl :=
    (Space.surjective_iff_surjective_pointsMap B S hS F hF U atl).1 hsurjp
  have hetale : Space.IsEtale B S hS atl :=
    (Space.isEtale_iff_presheaf_of_yoneda B S hS atl).2 hetalep
  refine ⟨isAlgebraicStack_fibredCategory.{u, w} B S hS F hF,
    (fibredCategory B S hS F).isFiberedInGroupoids, U,
    Bicategory.InducedBicategory.mkHom (presentationBasedFunctor B S hS U atl),
    isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpace B S hS
      (fibredCategory B S hS F)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF) U
      (presentationBasedFunctor B S hS U atl),
    fun V y hy G hG he => ⟨?_, ?_⟩⟩
  · exact prop_presentationBasedFunctor B S hS (Space.surjectiveMorphismProperty B S hS) U hF
      atl hsurj V y hy G hG he
  · exact prop_presentationBasedFunctor B S hS (Space.etaleMorphisms B S hS) U hF
      atl hetale V y hy G hG he

/-- **An algebraic space over `S`, regarded as an algebraic stack over `S`**: its category of
elements, together with
`AlgebraicGeometry.Stack.isAlgebraicStack_fibredCategory`. This is the first construction of an
object of `AlgebraicGeometry.Stack.AlgebraicStacks` the library has, and it is the one Stacks
04YF and Stacks 0CIF compare a stack with. -/
abbrev algebraicSpaceStack (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) : AlgebraicStacks.{u, w} B S hS :=
  ⟨fibredCategory B S hS F, isAlgebraicStack_fibredCategory.{u, w} B S hS F hF⟩

end Stack

end AlgebraicGeometry

end

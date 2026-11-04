module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasArrowSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackDiagonalUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance

/-!
# The quotient stack with its morphisms shrunk

The quotient stack `[U/R]` of a groupoid in algebraic spaces is a stackification, and its morphism
types live one universe above the site's (`AlgebraicGeometry.Stack.quotientStack`). Statements
about categories fibred in groupoids whose morphisms live at the site's universe — Artin's theorem
on flat groupoids, Stacks 06DC, among them — do not apply to it as it stands. When its morphism
types are essentially small (`AlgebraicGeometry.Stack.small_hom_quotientStack`, from Stacks
04TB), and `AlgebraicGeometry.Stack.smallQuotientStackBased` is the equivalent category over the
site with the same objects and morphisms in the site's universe. This file carries every input of
Stacks 06FI across that equivalence:

* the small quotient stack is a stack (Stacks 042W);
* the projection `S_U ⟶ [U/R]` of Stacks 044R, read with the object space at its own universes and
  the small quotient stack as target, is representable by algebraic spaces (Stacks 04WZ through
  Stacks 0457);
* it is surjective, flat and locally of finite presentation when the source and target of the
  groupoid are (Stacks 06FH through Stacks 0457);
* algebraicity of the small quotient stack gives algebraicity of `[U/R]` (Stacks 03YQ in
  independent universes).

## Main definitions

* `AlgebraicGeometry.Stack.smallQuotientStackCFG`: the small model of `[U/R]` as a category
  fibred in groupoids.
* `AlgebraicGeometry.Stack.smallQuotientStackProjection`: the projection from the object space
  into it.

## Main results

* `AlgebraicGeometry.Stack.isStack_smallQuotientStackCFG`
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_smallQuotientStackProjection`
* `AlgebraicGeometry.Stack.surjective_flat_lfp_smallQuotientStackProjection`
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_small`

## References

* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 042X](https://stacks.math.columbia.edu/tag/042X)
* [Stacks Project, Tag 04TB](https://stacks.math.columbia.edu/tag/04TB)
* [Stacks Project, Tag 04WZ](https://stacks.math.columbia.edu/tag/04WZ)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} {A : AlgebraicSpaces C S hS}
  (G : GroupoidInAlgebraicSpaces C S hS A)

/-- The canonical 1-morphism from the fibred category of the object space up to its universe lift
`AlgebraicGeometry.Stack.liftedObjectSpace`, inverse on the nose to
`AlgebraicGeometry.Stack.objectSpaceLiftDown`. -/
def objectSpaceLiftUp :
    (fibredCategory C S hS G.objects.obj).val ⥤ᵇ (liftedObjectSpace G).val :=
  ⟨ULiftHom.up, rfl⟩

/-- The lift `AlgebraicGeometry.Stack.objectSpaceLiftUp` of the object space to its universe lift
is an equivalence of categories. -/
instance : (objectSpaceLiftUp G).toFunctor.IsEquivalence :=
  (ULiftHom.equiv (C := (fibredCategory C S hS G.objects.obj).val.obj)).isEquivalence_functor

/-- The small model `AlgebraicGeometry.Stack.smallQuotientStackBased` of the quotient stack
`[U/R]`, as a category fibred in groupoids over the big fppf site whose morphisms live at the
site's universe. It is fibred in groupoids by Stacks 042X, being equivalent to `[U/R]`. -/
noncomputable def smallQuotientStackCFG :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS) :=
  CatFiberedInGroupoids.mk (smallQuotientStackBased G)
    (StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver
      (smallQuotientStackEquivalenceOver G).symm (isFiberedInGroupoids_quotientStack G))

/-- The equivalence over the site between the small quotient stack and the quotient stack. -/
noncomputable def smallQuotientStackEquivalence :
    BasedCategory.Equivalence (smallQuotientStackCFG G).val (quotientStack G) :=
  (smallQuotientStackEquivalenceOver G).symm.toBasedEquivalence

/-- The functor of the equivalence `AlgebraicGeometry.Stack.smallQuotientStackEquivalence` from the
small quotient stack to `[U/R]` is an equivalence of categories. -/
instance : (smallQuotientStackEquivalence G).functor.toFunctor.IsEquivalence :=
  inferInstanceAs (ShrinkHoms.inverse (quotientStack G).obj).IsEquivalence

/-- The projection `S_U ⟶ [U/R]` of Stacks 044R, with the object space at its own universes and
the small quotient stack as target. -/
noncomputable def smallQuotientStackProjection :
    fibredCategory C S hS G.objects.obj ⟶ smallQuotientStackCFG G :=
  Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp (objectSpaceLiftUp G)
      (BasedFunctor.comp (quotientStackProjectionHom G).hom
        (smallQuotientStackEquivalence G).inverse))

/-- The square comparing the two projections commutes up to an isomorphism with identity
components: shrinking and then restoring the morphisms of `[U/R]` is the identity. -/
noncomputable def smallQuotientStackProjectionSquare :
    BasedFunctor.comp (objectSpaceLiftUp G) (quotientStackProjectionHom G).hom ≅
      BasedFunctor.comp (smallQuotientStackProjection G).hom
        (smallQuotientStackEquivalence G).functor :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerLeft
      ((objectSpaceLiftUp G).toFunctor ⋙ (quotientStackProjectionHom G).hom.toFunctor)
      (ShrinkHoms.equivalence (quotientStack G).obj).unitIso)
    (fun _ => IsHomLift.id rfl)

/-- **The small quotient stack is a stack**, by Stacks 042W from Stacks 044Q. -/
theorem isStack_smallQuotientStackCFG :
    (smallQuotientStackCFG G).val.p.IsStack (BigFppfOver.topology C S hS) :=
  (BasedCategory.isStack_iff_of_equivalence (smallQuotientStackEquivalence G)
    (BigFppfOver.topology C S hS)).mpr (isStack_quotientStack G)

/-- **The projection into the small quotient stack is representable by algebraic spaces**: Stacks
04WZ for the projection of Stacks 044R, transported by Stacks 0457. -/
theorem isRepresentableByAlgebraicSpaces_smallQuotientStackProjection :
    IsRepresentableByAlgebraicSpaces C S hS (smallQuotientStackProjection G).hom :=
  (isRepresentableByAlgebraicSpaces_iff_of_equivalences C S hS
    (smallQuotientStackProjection G).hom (quotientStackProjectionHom G).hom
    (objectSpaceLiftUp G) (smallQuotientStackEquivalence G).functor
    (smallQuotientStackProjectionSquare G)).mp
    (representable_quotientStackProjectionHom_unconditional G)

/-- **Stacks 06FH for the projection into the small quotient stack.** If the source and target of
the groupoid are flat and locally of finite presentation, then every algebraic space representing a
base change of the projection along a scheme-valued point is surjective, flat and locally of finite
presentation over the test scheme. -/
theorem surjective_flat_lfp_smallQuotientStackProjection
    (hsflat : Space.IsFlat C S hS G.source.hom)
    (htflat : Space.IsFlat C S hS G.target.hom)
    (hslfp : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (htlfp : Space.IsLocallyOfFinitePresentation C S hS G.target.hom)
    (V : BigFppfOver C S hS)
    (y : BigFppfOver C V.left.1 V.left.2 ⥤ (smallQuotientStackCFG G).val.obj)
    (hy : y ⋙ (smallQuotientStackCFG G).val.p = Over.map V.hom)
    (F : (BigFppfOver C V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace C V.left.1 V.left.2 F)
    (he : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom) (fibredCategory C S hS G.objects.obj).val.p
        (smallQuotientStackCFG G).val.p y
        (CatFiberedInGroupoids.homFunctor (smallQuotientStackProjection G)))
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    let g := (algebraicSpaceMap C S hS V
      ((spacesOverSmallerBaseFunctor C V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
    Space.IsSurjective C S hS g ∧ Space.IsFlat C S hS g ∧
      Space.IsLocallyOfFinitePresentation C S hS g := by
  obtain ⟨hsurj, hflat, hlfp⟩ :=
    QuotientAtlas.surjective_flat_lfp_quotientStackProjectionHom G hsflat htflat hslfp htlfp
      (representable_quotientStackProjectionHom_unconditional G)
  have transport := fun (P : MorphismProperty (AlgebraicSpaces C S hS)) hP =>
    relativeProperty_of_equivalences C S hS P
      (smallQuotientStackProjection G).hom (quotientStackProjectionHom G).hom
      (objectSpaceLiftUp G) (smallQuotientStackEquivalence G).functor
      (smallQuotientStackProjectionSquare G) hP V y hy F hF he
  exact ⟨transport (Space.surjectiveMorphismProperty C S hS) hsurj,
    transport (flatSpaceProperty C S hS) hflat,
    transport (locallyOfFinitePresentationSpaceProperty C S hS) hlfp⟩

/-- **Algebraicity descends from the small quotient stack to `[U/R]`**, by Stacks 03YQ in
independent universes. -/
theorem isAlgebraicStack_quotientStack_of_small
    (h : IsAlgebraicStack.{u, w} C S hS (smallQuotientStackCFG G).val) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack G) :=
  isAlgebraicStack_of_equivalenceOver C S hS (smallQuotientStackEquivalenceOver G).symm h

end AlgebraicGeometry.Stack

end

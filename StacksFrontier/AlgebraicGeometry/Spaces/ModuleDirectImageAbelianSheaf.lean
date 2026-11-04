module

public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleConjugateToSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianDirectImageGeneral

/-!
# The abelian sheaf underlying a direct image of modules, with no hypothesis on the morphism

`AlgebraicGeometry.Space.modulePushforwardCompToSheafIso` is the compatibility of Stacks 03D1
with the forgetful functor to abelian sheaves, and it carries a hypothesis that the statement does
not need: it asks that the underlying morphism of presheaves be relatively representable, and its
right-hand side is `AlgebraicGeometry.Space.smallEtaleAbelianPushforward`, which exists only under
that hypothesis.

The hypothesis is an artefact of the route.  The direct image of modules is built on
`AlgebraicGeometry.Space.smallEtaleDirectImage`, which is unconditional, and the direct image of
abelian sheaves `AlgebraicGeometry.Space.smallEtaleAbelianDirectImage` is unconditional too: both
are the same three-factor conjugate of the spaces-étale direct image of Stacks 03G2, part (1) by
the comparison equivalences of Stacks 03G1, one with coefficients in `Type u` and one in
`AddCommGrpCat.{u + 1}`.  Representability enters only through
`AlgebraicGeometry.Space.smallEtaleDirectImageIsoSheafPushforward`, which re-expresses the
conjugate as a restriction along base change of étale *scheme* charts; the restriction form is what
the sites-level lemma used there demands.  Comparing the two conjugates directly instead needs no
hypothesis, and that is what this file does, at the coefficient universe of the structure rings.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleSheafDirectImage`: the conjugate itself, with coefficients in
  an arbitrary category.  It is not a third direct image: it is
  `AlgebraicGeometry.Space.smallEtaleDirectImage` at `Type u` and
  `AlgebraicGeometry.Space.smallEtaleAbelianDirectImage` at `AddCommGrpCat.{u + 1}`, both on the
  nose.

## Main results

* `AlgebraicGeometry.Space.smallEtaleSheafDirectImage_type` and
  `AlgebraicGeometry.Space.smallEtaleSheafDirectImage_addCommGrp`: those two identifications.
* `AlgebraicGeometry.Space.modulePushforwardOfStructureMapCompToSheafIso`: **the compatibility of
  Stacks 03D1 with the forgetful functor to abelian sheaves, with no hypothesis on the
  morphism**, for the direct image of Stacks 03D6, part (1) attached to an arbitrary structure
  map.
* `AlgebraicGeometry.Space.modulePushforwardCompToSheafDirectImageIso`: the same for
  `AlgebraicGeometry.Space.modulePushforward`, the direct image attached to the structure map
  `f♯` of Stacks 03G8.

## Implementation notes

The coefficients are arbitrary because the comparison of Stacks 03G1 is
(`AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence`), and because only the *source*
side of the conjugate inverts a comparison: the other two factors are restrictions along
continuous functors, which need nothing of the coefficients.  So a single instance assumption,
that the comma categories indexing the right Kan extension along the comparison for the source
have limits, carries the definition.  At `AddCommGrpCat.{u}` that assumption is
`AlgebraicGeometry.Space.hasLimitsOfShape_structuredArrow_comparisonFunctor_op_addCommGrp`, and
it is what makes the statement available at the universe of the module sections at all.

The structure map is a parameter of the main comparison rather than fixed to `f♯`.  That is not
generality for its own sake: restriction of scalars along it is absorbed by the forgetful functor
definitionally, and at a free structure map the kernel discharges that in no time, where at
`AlgebraicGeometry.Space.structureSharp` — a composite through
`AlgebraicGeometry.Space.smallEtaleDirectImageRan` — it does not.  The same discipline is why the
three factors of the conjugate are handed to
`Stacks.Sheaves.ToposPullback.pullbackModuleToSheafIsoComp` rather than written into one chain.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe w v u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The direct image of sheaves on the small étale sites along an arbitrary morphism, with
coefficients in an arbitrary category**: the spaces-étale direct image of Stacks 03G2, part (1),
conjugated by the comparison equivalences of Stacks 03G1.

No hypothesis is placed on `f`.  This is not a third direct image:
`AlgebraicGeometry.Space.smallEtaleSheafDirectImage_type` and
`AlgebraicGeometry.Space.smallEtaleSheafDirectImage_addCommGrp` identify it with
`AlgebraicGeometry.Space.smallEtaleDirectImage` and with
`AlgebraicGeometry.Space.smallEtaleAbelianDirectImage` on the nose.  What the coefficient
generality buys is the statement at `AddCommGrpCat.{u}`, where the abelian sheaf underlying a
module of this development lives, and which the geometric stalk of an abelian sheaf cannot
reach. -/
def smallEtaleSheafDirectImage (A : Type w) [Category.{v} A]
    [∀ W : (SpacesEtale B S hS X)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow W (comparisonFunctor B S hS X).op) A]
    (f : X ⟶ Y) :
    Sheaf (SmallEtale.topology B S hS X.1) A ⥤ Sheaf (SmallEtale.topology B S hS Y.1) A :=
  ((comparisonFunctor B S hS X).sheafPushforwardContinuous A
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).inv ⋙
    (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous A
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
    (comparisonFunctor B S hS Y).sheafPushforwardContinuous A
      (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)

/-- At sheaves of sets in the universe of the structure rings the conjugate is
`AlgebraicGeometry.Space.smallEtaleDirectImage`. -/
theorem smallEtaleSheafDirectImage_type (f : X ⟶ Y) :
    smallEtaleSheafDirectImage B S hS (Type u) f = smallEtaleDirectImage B S hS f := rfl

/-- At abelian sheaves one universe above the structure rings the conjugate is
`AlgebraicGeometry.Space.smallEtaleAbelianDirectImage`, the direct image of abelian sheaves of
Stacks 03G2, part (1) for an arbitrary morphism. -/
theorem smallEtaleSheafDirectImage_addCommGrp (f : X ⟶ Y) :
    smallEtaleSheafDirectImage B S hS AddCommGrpCat.{u + 1} f =
      smallEtaleAbelianDirectImage B S hS f := rfl

section Bridge

variable (f : X ⟶ Y)

/-- The compatibility of Stacks 03D1 with the forgetful functor to abelian sheaves for the
restriction along the comparison functor of Stacks 03G1 of the target, at the universe of the
structure rings. -/
def comparisonRestrictionCompToSheafIso (O : Sheaf (SpacesEtale.topology B S hS Y) RingCat.{u}) :
    pullbackModuleFunctor (SmallEtale.topology B S hS Y.1)
          (smallEtaleComparisonRestriction B S hS Y) O ⋙
        SheafOfModules.toSheaf.{u} (pullbackRingSheaf.{u, u, u, u + 1, u + 1, u + 1}
          (SmallEtale.topology B S hS Y.1)
          (smallEtaleComparisonRestriction B S hS Y) O) ≅
      SheafOfModules.toSheaf.{u} O ⋙
        (comparisonFunctor B S hS Y).sheafPushforwardContinuous AddCommGrpCat.{u}
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) :=
  pullbackModuleCompToSheafIso (SmallEtale.topology B S hS Y.1)
    (SpacesEtale.topology B S hS Y) (comparisonFunctor B S hS Y) O
    (smallEtaleComparisonRestriction B S hS Y) (Iso.refl _)

/-- The compatibility of Stacks 03D1 with the forgetful functor to abelian sheaves for the
restriction along spaces-étale base change — the direct image of Stacks 03G2, part (1) — at the
universe of the structure rings. -/
def spacesBaseChangeCompToSheafIso (O : Sheaf (SpacesEtale.topology B S hS X) RingCat.{u}) :
    pullbackModuleFunctor (SpacesEtale.topology B S hS Y)
          ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) O ⋙
        SheafOfModules.toSheaf.{u} (pullbackRingSheaf.{u, u, u + 1, u + 1, u + 1, u + 1}
          (SpacesEtale.topology B S hS Y)
          ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) O) ≅
      SheafOfModules.toSheaf.{u} O ⋙
        (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous AddCommGrpCat.{u}
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) :=
  pullbackModuleCompToSheafIso (SpacesEtale.topology B S hS Y)
    (SpacesEtale.topology B S hS X) (spacesBaseChange B S hS f).functor O _ (Iso.refl _)

/-- The compatibility of Stacks 03D1 with the forgetful functor to abelian sheaves for the
*inverse* of the comparison equivalence of Stacks 03G1 of the source, at the universe of the
structure rings.  This is the factor of the conjugate that is not a restriction, and
`Stacks.Sheaves.ToposPullback.pullbackModuleInverseToSheafIso` is what supplies it. -/
def comparisonInverseCompToSheafIso (O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}) :
    pullbackModuleFunctor (SpacesEtale.topology B S hS X)
          (smallEtaleComparisonRestriction B S hS X).inv O ⋙
        SheafOfModules.toSheaf.{u} (pullbackRingSheaf.{u, u, u + 1, u + 1, u, u + 1}
          (SpacesEtale.topology B S hS X)
          (smallEtaleComparisonRestriction B S hS X).inv O) ≅
      SheafOfModules.toSheaf.{u} O ⋙
        ((comparisonFunctor B S hS X).sheafPushforwardContinuous AddCommGrpCat.{u}
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).inv :=
  pullbackModuleInverseToSheafIso (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X) O

/-- The compatibility for the two restriction factors of the conjugate taken together. -/
def spacesBaseChangeComparisonCompToSheafIso
    (O : Sheaf (SpacesEtale.topology B S hS X) RingCat.{u}) :
    pullbackModuleFunctor (SmallEtale.topology B S hS Y.1)
          ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
              (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
            smallEtaleComparisonRestriction B S hS Y) O ⋙
        SheafOfModules.toSheaf.{u} (pullbackRingSheaf.{u, u, u, u + 1, u + 1, u + 1}
          (SmallEtale.topology B S hS Y.1)
          ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
              (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
            smallEtaleComparisonRestriction B S hS Y) O) ≅
      SheafOfModules.toSheaf.{u} O ⋙
        (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous AddCommGrpCat.{u}
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
          (comparisonFunctor B S hS Y).sheafPushforwardContinuous AddCommGrpCat.{u}
            (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) :=
  pullbackModuleToSheafIsoComp (SmallEtale.topology B S hS Y.1)
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
    (smallEtaleComparisonRestriction B S hS Y) _ _ _
    (comparisonRestrictionCompToSheafIso B S hS) (spacesBaseChangeCompToSheafIso B S hS f) O

/-- **The abelian sheaf underlying the direct image of an `𝒪_X`-module is the direct image of the
abelian sheaf underlying it, with no hypothesis on the morphism.**  For an arbitrary morphism
`f : X ⟶ Y` of algebraic spaces over `S` and an arbitrary structure map
`f♯ : 𝒪_Y ⟶ f_*𝒪_X`, the direct image of `𝒪_X`-modules of Stacks 03D6, part (1) followed by the
forgetful functor to abelian sheaves on the small étale site of `Y` is the forgetful functor
followed by the conjugate direct image of abelian sheaves, at the universe of the structure
rings.

This is `AlgebraicGeometry.Space.modulePushforwardCompToSheafIso` with its representability
hypothesis removed: the three factors of the conjugate are treated one at a time — two
restrictions and the inverse of the comparison equivalence of Stacks 03G1 — rather than the
conjugate being re-expressed as a restriction along base change of étale scheme charts, which is
the step that needed `f` to be representable.  Restriction of scalars along `f♯` is invisible to
the forgetful functor. -/
def modulePushforwardOfStructureMapCompToSheafIso
    (fSharp : structureRingSheaf B S hS Y ⟶ structureRingSheafDirectImage B S hS f) :
    modulePushforwardOfStructureMap B S hS f fSharp ⋙
        SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y) ≅
      SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X) ⋙
        smallEtaleSheafDirectImage B S hS AddCommGrpCat.{u} f :=
  compRestrictScalarsToSheafIso (moduleDirectImage B S hS f) fSharp ≪≫
    pullbackModuleToSheafIsoComp (SmallEtale.topology B S hS Y.1)
      (SpacesEtale.topology B S hS X) (SmallEtale.topology B S hS X.1)
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        smallEtaleComparisonRestriction B S hS Y)
      (smallEtaleComparisonRestriction B S hS X).inv _ _
      (spacesBaseChangeComparisonCompToSheafIso B S hS f)
      (comparisonInverseCompToSheafIso B S hS) (structureRingSheaf B S hS X)

/-- **The abelian sheaf underlying the direct image of an `𝒪_X`-module is the direct image of the
abelian sheaf underlying it, with no hypothesis on the morphism**, for the direct image
`AlgebraicGeometry.Space.modulePushforward` of Stacks 03LU — that is, at the structure map `f♯`
of Stacks 03G8. -/
def modulePushforwardCompToSheafDirectImageIso :
    modulePushforward B S hS f ⋙
        SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y) ≅
      SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X) ⋙
        smallEtaleSheafDirectImage B S hS AddCommGrpCat.{u} f :=
  modulePushforwardOfStructureMapCompToSheafIso B S hS f (structureSharp B S hS f)

end Bridge

end AlgebraicGeometry.Space

end

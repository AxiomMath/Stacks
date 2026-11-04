module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImageAbelianSheaf
public import Mathlib.Algebra.Category.Grp.Ulift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The direct image of abelian sheaves and the universe lift of the coefficients

`AlgebraicGeometry.Space.modulePushforwardCompToSheafDirectImageIso` is the compatibility of
Stacks 03D1 with the forgetful functor to abelian sheaves, with no hypothesis on the morphism, at
the coefficient universe `u` of the module sections.  That is not the universe the direct image of
abelian sheaves of Stacks 03G2, part (1) is used at: the geometric stalk of an abelian sheaf on
the small étale site is a filtered colimit over a neighbourhood category whose objects sit one
universe above the sections, so `AlgebraicGeometry.Space.smallEtaleAbelianDirectImage` and
everything Stacks 0AER says about it live at `AddCommGrpCat.{u + 1}`.

This file lifts the compatibility to that universe.  The pullback half of the lift is
`AlgebraicGeometry.Space.modulePullbackCompToSheafInverseImageIso`; this is the pushforward half,
and together they are the dictionary between the four functors the `𝒪_X`-module of Stacks 0AEX is
built from and the four abelian functors the two-term complexes of Stacks 0AER are built from.

## Main results

* `CategoryTheory.Functor.sheafComposeCompInvIso`: the inverse of the equivalence of sheaf
  categories induced by a continuous functor of sites commutes with postcomposition of
  coefficients.
* `AlgebraicGeometry.Space.smallEtaleSheafDirectImageCompSheafComposeIso`: the direct image of
  Stacks 03G2, part (1) on the small étale sites commutes with postcomposition of coefficients,
  with no hypothesis on the morphism.
* `AlgebraicGeometry.Space.modulePushforwardCompToSheafAbelianDirectImageIso`: **the Stacks 03D1
  compatibility at the universe where the geometric stalk of an abelian sheaf lives, with no
  hypothesis on the morphism.**

## Implementation notes

Restriction along a continuous functor of sites commutes with postcomposition of coefficients on
the nose — both read the same sections — which is
`CategoryTheory.Functor.sheafPushforwardContinuous_comp_sheafCompose`.  Two of the three factors
of the conjugate are such restrictions and need nothing further.  The third is the inverse of the
comparison equivalence of Stacks 03G1, which is not computed on sections, and for it the
commutation is the unit and counit of the two equivalences applied to the equality above; that is
`CategoryTheory.Functor.sheafComposeCompInvIso`.

The coefficient functor is a parameter throughout, and is only instantiated at
`AddCommGrpCat.uliftFunctor` in the last statement.  As in
`StacksFrontier/AlgebraicGeometry/Spaces/ToposModuleConjugateToSheaf.lean`, that is what keeps the
definitional steps checkable: at a free coefficient functor the commutation above is `rfl` in no
time.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 0AER](https://stacks.math.columbia.edu/tag/0AER)
* [Stacks Project, Tag 0AEX](https://stacks.math.columbia.edu/tag/0AEX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe w w' v v' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D) [G.IsContinuous J K]
  {A : Type w} [Category.{v} A] {A' : Type w'} [Category.{v'} A'] (F : A ⥤ A')
  [J.HasSheafCompose F] [K.HasSheafCompose F]

/-- **Restriction along a continuous functor of sites commutes with postcomposition of
coefficients, on the nose.**  Both sides are the same sections over the same object of the
source site, with the coefficient functor applied. -/
theorem sheafPushforwardContinuous_comp_sheafCompose :
    G.sheafPushforwardContinuous A J K ⋙ sheafCompose J F =
      sheafCompose K F ⋙ G.sheafPushforwardContinuous A' J K := rfl

/-- **The inverse of the equivalence of sheaf categories induced by a continuous functor of sites
commutes with postcomposition of coefficients.**  Restriction itself commutes on the nose by
`CategoryTheory.Functor.sheafPushforwardContinuous_comp_sheafCompose`; the inverse inherits that
through the counit of the equivalence at `A` and the unit of the equivalence at `A'`. -/
def sheafComposeCompInvIso [(G.sheafPushforwardContinuous A J K).IsEquivalence]
    [(G.sheafPushforwardContinuous A' J K).IsEquivalence] :
    sheafCompose J F ⋙ (G.sheafPushforwardContinuous A' J K).inv ≅
      (G.sheafPushforwardContinuous A J K).inv ⋙ sheafCompose K F :=
  isoWhiskerRight (leftUnitor (sheafCompose J F)).symm
        (G.sheafPushforwardContinuous A' J K).inv ≪≫
    isoWhiskerRight
      (isoWhiskerRight (G.sheafPushforwardContinuous A J K).asEquivalence.counitIso.symm
        (sheafCompose J F)) (G.sheafPushforwardContinuous A' J K).inv ≪≫
    isoWhiskerRight
      (associator (G.sheafPushforwardContinuous A J K).inv
        (G.sheafPushforwardContinuous A J K) (sheafCompose J F))
      (G.sheafPushforwardContinuous A' J K).inv ≪≫
    isoWhiskerRight
      (isoWhiskerLeft (G.sheafPushforwardContinuous A J K).inv
        (eqToIso (sheafPushforwardContinuous_comp_sheafCompose J K G F)))
      (G.sheafPushforwardContinuous A' J K).inv ≪≫
    associator (G.sheafPushforwardContinuous A J K).inv
      (sheafCompose K F ⋙ G.sheafPushforwardContinuous A' J K)
      (G.sheafPushforwardContinuous A' J K).inv ≪≫
    isoWhiskerLeft (G.sheafPushforwardContinuous A J K).inv
      (associator (sheafCompose K F) (G.sheafPushforwardContinuous A' J K)
          (G.sheafPushforwardContinuous A' J K).inv ≪≫
        isoWhiskerLeft (sheafCompose K F)
          (G.sheafPushforwardContinuous A' J K).asEquivalence.unitIso.symm ≪≫
        rightUnitor (sheafCompose K F))

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe w w' v v' u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

section Coefficients

variable {A : Type w} [Category.{v} A] {A' : Type w'} [Category.{v'} A'] (F : A ⥤ A')
  [∀ W : (SpacesEtale B S hS X)ᵒᵖ,
    HasLimitsOfShape (StructuredArrow W (comparisonFunctor B S hS X).op) A]
  [∀ W : (SpacesEtale B S hS X)ᵒᵖ,
    HasLimitsOfShape (StructuredArrow W (comparisonFunctor B S hS X).op) A']
  [(SmallEtale.topology B S hS X.1).HasSheafCompose F]
  [(SmallEtale.topology B S hS Y.1).HasSheafCompose F]
  [(SpacesEtale.topology B S hS X).HasSheafCompose F]
  [(SpacesEtale.topology B S hS Y).HasSheafCompose F]

/-- **The direct image of sheaves on the small étale sites commutes with postcomposition of
coefficients, with no hypothesis on the morphism.**  Of the three factors of the conjugate of
Stacks 03G1 the two restrictions commute on the nose
(`CategoryTheory.Functor.sheafPushforwardContinuous_comp_sheafCompose`) and the inverse of the
comparison equivalence commutes by
`CategoryTheory.Functor.sheafComposeCompInvIso`. -/
def smallEtaleSheafDirectImageCompSheafComposeIso (f : X ⟶ Y) :
    smallEtaleSheafDirectImage B S hS A f ⋙
        sheafCompose (SmallEtale.topology B S hS Y.1) F ≅
      sheafCompose (SmallEtale.topology B S hS X.1) F ⋙
        smallEtaleSheafDirectImage B S hS A' f :=
  Functor.associator
      ((comparisonFunctor B S hS X).sheafPushforwardContinuous A
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).inv
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous A
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        (comparisonFunctor B S hS Y).sheafPushforwardContinuous A
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y))
      (sheafCompose (SmallEtale.topology B S hS Y.1) F) ≪≫
    Functor.isoWhiskerLeft
      ((comparisonFunctor B S hS X).sheafPushforwardContinuous A
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).inv
      (Functor.associator
          ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous A
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X))
          ((comparisonFunctor B S hS Y).sheafPushforwardContinuous A
            (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y))
          (sheafCompose (SmallEtale.topology B S hS Y.1) F) ≪≫
        Functor.isoWhiskerLeft
          ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous A
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X))
          (eqToIso (Functor.sheafPushforwardContinuous_comp_sheafCompose
            (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)
            (comparisonFunctor B S hS Y) F)) ≪≫
        (Functor.associator
          ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous A
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X))
          (sheafCompose (SpacesEtale.topology B S hS Y) F)
          ((comparisonFunctor B S hS Y).sheafPushforwardContinuous A'
            (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y))).symm ≪≫
        Functor.isoWhiskerRight
          (eqToIso (Functor.sheafPushforwardContinuous_comp_sheafCompose
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
            (spacesBaseChange B S hS f).functor F))
          ((comparisonFunctor B S hS Y).sheafPushforwardContinuous A'
            (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)) ≪≫
        Functor.associator
          (sheafCompose (SpacesEtale.topology B S hS X) F)
          ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous A'
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X))
          ((comparisonFunctor B S hS Y).sheafPushforwardContinuous A'
            (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y))) ≪≫
    (Functor.associator
      ((comparisonFunctor B S hS X).sheafPushforwardContinuous A
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).inv
      (sheafCompose (SpacesEtale.topology B S hS X) F)
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous A'
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        (comparisonFunctor B S hS Y).sheafPushforwardContinuous A'
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y))).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.sheafComposeCompInvIso (SmallEtale.topology B S hS X.1)
        (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X) F).symm
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous A'
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        (comparisonFunctor B S hS Y).sheafPushforwardContinuous A'
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)) ≪≫
    Functor.associator (sheafCompose (SmallEtale.topology B S hS X.1) F)
      ((comparisonFunctor B S hS X).sheafPushforwardContinuous A'
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).inv
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous A'
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        (comparisonFunctor B S hS Y).sheafPushforwardContinuous A'
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y))

end Coefficients

/-- **The abelian sheaf underlying the direct image of an `𝒪_X`-module is the direct image of the
abelian sheaf underlying it, with no hypothesis on the morphism, at the universe where the
geometric stalk of an abelian sheaf lives.**  For an arbitrary morphism `f : X ⟶ Y` of algebraic
spaces over `S`, the direct image of `𝒪_X`-modules of Stacks 03LU followed by the forgetful
functor to abelian sheaves and the universe lift is the forgetful functor and the universe lift
followed by `AlgebraicGeometry.Space.smallEtaleAbelianDirectImage`.

This is the Stacks 03D1 compatibility in the form the omitted diagram chase of Stacks 0AF0 needs:
`AlgebraicGeometry.Space.isPullback_directImageStalkMap` is a cartesian square of geometric stalks
of abelian sheaves at `u + 1`, and
`AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_glueingKernel_app` one of geometric
module stalks at `u`, so pasting them needs exactly this.  It is
`AlgebraicGeometry.Space.modulePushforwardCompToSheafIso` with its representability hypothesis
removed and with the coefficients lifted, and it is the pushforward companion of
`AlgebraicGeometry.Space.modulePullbackCompToSheafInverseImageIso`. -/
@[sga "4 IV 13.2.3" "special case"]
def modulePushforwardCompToSheafAbelianDirectImageIso (f : X ⟶ Y) :
    modulePushforward B S hS f ⋙
        SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y) ⋙
          sheafCompose (SmallEtale.topology B S hS Y.1)
            AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X) ⋙
        sheafCompose (SmallEtale.topology B S hS X.1)
            AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙
          smallEtaleAbelianDirectImage B S hS f :=
  (Functor.associator (modulePushforward B S hS f)
      (SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y))
      (sheafCompose (SmallEtale.topology B S hS Y.1)
        AddCommGrpCat.uliftFunctor.{u + 1, u})).symm ≪≫
    Functor.isoWhiskerRight (modulePushforwardCompToSheafDirectImageIso B S hS f)
      (sheafCompose (SmallEtale.topology B S hS Y.1)
        AddCommGrpCat.uliftFunctor.{u + 1, u}) ≪≫
    Functor.associator (SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X))
      (smallEtaleSheafDirectImage B S hS AddCommGrpCat.{u} f)
      (sheafCompose (SmallEtale.topology B S hS Y.1)
        AddCommGrpCat.uliftFunctor.{u + 1, u}) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X))
      (smallEtaleSheafDirectImageCompSheafComposeIso B S hS
          AddCommGrpCat.uliftFunctor.{u + 1, u} f ≪≫
        Functor.isoWhiskerLeft
          (sheafCompose (SmallEtale.topology B S hS X.1)
            AddCommGrpCat.uliftFunctor.{u + 1, u})
          (eqToIso (smallEtaleSheafDirectImage_addCommGrp B S hS f)))

end AlgebraicGeometry.Space

end

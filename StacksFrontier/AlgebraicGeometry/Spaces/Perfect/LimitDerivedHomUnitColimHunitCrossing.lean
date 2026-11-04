module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimCrossPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimDerivedReadingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelHomId
public import StacksFrontier.CategoryTheory.PullbackData.LimitDerivedHomUnitColimStagesCrossing

/-!
# The derived pullbacks on the spaces-étale models as a pullback datum, and their crossing

The colimit statement of Stacks 09RI, `CategoryTheory.PullbackData.LimitSystem.IsColim`, is
stated for `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, whose inverse images are the
derived pullbacks along the morphisms of small étale ringed topoi of Stacks 03G8.  The
point-tensor engine of the tag computes instead with the derived pullbacks
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback
(AlgebraicGeometry.Space.spacesEtaleModelHom f)` along the morphisms of models of the ringed
spaces-étale sites.

This file assembles those model-side derived pullbacks into a pullback pseudofunctor datum and
crosses it into the datum of the tag along the equivalences of Stacks 03G1.

## What the crossing needs, and what is still carried

`CategoryTheory.PullbackData.Crossing` has two fields: the crossing isomorphism, which is
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso` and is unconditional, and its
composition law, which is
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso_comp_of_underivedCocycle` and
carries one hypothesis: the **underived** cocycle
`AlgebraicGeometry.Space.SpacesEtaleModelPullbackHomotopyIsoCocycle` of the identification of the
two degreewise inverse images, on homotopy categories.  That hypothesis is carried here as `hχ`;
it is not weakened and it is not assumed anywhere else.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackData`: **the derived pullbacks along
  the morphisms of models of the ringed spaces-étale sites, with the unit law of
  `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackIdIso` and the composition comparison
  of `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIso`, as a pullback
  pseudofunctor datum.**
* `AlgebraicGeometry.Space.spacesEtaleModelCrossing`: **the crossing of that datum into
  `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`** along the derived equivalences of
  Stacks 03G1, from the underived cocycle.

## Main results

* `AlgebraicGeometry.Space.isColim_spacesEtaleModelDerivedPullbackData_iff`: **the colimit
  statement of Stacks 09RI for the model-side datum at `Xm`, `Ym` is the colimit statement for
  the datum of the tag at their images under the derived equivalences** — in both directions.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe w u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The derived pullbacks along the morphisms of models of the ringed spaces-étale sites, as a
pullback pseudofunctor datum.**  The inverse image along `f` is the derived pullback along
`AlgebraicGeometry.Space.spacesEtaleModelHom` of `f`, the unit law is
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackIdIso`, and the composition comparison is
the inverse of `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIso`, which is
Stacks 0D6D on the models. -/
def spacesEtaleModelDerivedPullbackData :
    PullbackData (AlgebraicSpaces B S hS)
      (fun X => DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules) where
  pull f := derivedPullback (spacesEtaleModelHom B S hS f)
  idIso X := spacesEtaleModelDerivedPullbackIdIso B S hS X
  compIso f g := (spacesEtaleModelDerivedPullbackCompIso B S hS f g).symm

/-- **The crossing of the model-side datum of derived pullbacks into the datum of Stacks 09RI**,
along the derived equivalences `AlgebraicGeometry.Space.spacesEtaleModelModulesDerivedFunctor` of
Stacks 03G1.

The crossing isomorphism is `AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso`, which
is unconditional; its composition law is
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso_comp_of_underivedCocycle`, whose
only hypothesis is the underived cocycle `hχ`.  Since the composition law is stated for the
inverses of the crossing isomorphisms and the field
`CategoryTheory.PullbackData.Crossing.iso_triangle` for their `hom`s, the two are matched by
`CategoryTheory.Iso.inv_eq_inv`; the reassociation is the one `CategoryTheory.Iso.trans` forces on
the inverse of a threefold composite. -/
def spacesEtaleModelCrossing
    (hχ : ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
      SpacesEtaleModelPullbackHomotopyIsoCocycle B S hS f g) :
    PullbackData.Crossing (spacesEtaleModelDerivedPullbackData B S hS)
      (smallEtaleDerivedPullbackData B S hS)
      (fun X => spacesEtaleModelModulesDerivedFunctor B S hS X) :=
  PullbackData.Crossing.ofCompIso
    (fun f => smallEtaleDerivedPullbackDataModelIso B S hS f)
    (fun {X Y Z} f g K => by
      refine (Iso.inv_eq_inv
        ((spacesEtaleModelModulesDerivedFunctor B S hS X).mapIso
            ((spacesEtaleModelDerivedPullbackCompIso B S hS f g).app K).symm ≪≫
          (smallEtaleDerivedPullbackDataModelIso B S hS f).app
              ((derivedPullback (X := spacesEtaleModelRingedTopos B S hS Y)
                (Y := spacesEtaleModelRingedTopos B S hS Z)
                (spacesEtaleModelHom B S hS g)).obj K) ≪≫
          ((smallEtaleDerivedPullbackData B S hS).pull f).mapIso
            ((smallEtaleDerivedPullbackDataModelIso B S hS g).app K))
        ((smallEtaleDerivedPullbackDataModelIso B S hS (f ≫ g)).app K ≪≫
          ((smallEtaleDerivedPullbackData B S hS).compIso f g).app
            ((spacesEtaleModelModulesDerivedFunctor B S hS Z).obj K))).mp ?_
      exact (Category.assoc _ _ _).trans
        (smallEtaleDerivedPullbackDataModelIso_comp_of_underivedCocycle B S hS f g (hχ f g)
          K).symm)

/-- **The colimit statement of Stacks 09RI crosses between the spaces-étale models and the small
étale sites.**  For a directed system `Sys` of algebraic spaces over `X₀` and objects `Xm`, `Ym`
of the derived category of the model of `X₀`, the colimit statement for the model-side derived
pullbacks at `Xm`, `Ym` and the one for the derived pullbacks of Stacks 09RI at their images
under the derived equivalences of Stacks 03G1 are the same statement.

This is `CategoryTheory.PullbackData.Crossing.isColim_iff` for
`AlgebraicGeometry.Space.spacesEtaleModelCrossing`, the functors of the derived equivalences
being fully faithful. -/
theorem isColim_spacesEtaleModelDerivedPullbackData_iff
    (hχ : ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
      SpacesEtaleModelPullbackHomotopyIsoCocycle B S hS f g)
    {X₀ : AlgebraicSpaces B S hS} {J : Type w} [Preorder J]
    (Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) X₀ J)
    (Xm Ym : DerivedCategory (spacesEtaleModelRingedTopos B S hS X₀).Modules) :
    Sys.IsColim (spacesEtaleModelDerivedPullbackData B S hS) Xm Ym ↔
      Sys.IsColim (smallEtaleDerivedPullbackData B S hS)
        ((spacesEtaleModelModulesDerivedFunctor B S hS X₀).obj Xm)
        ((spacesEtaleModelModulesDerivedFunctor B S hS X₀).obj Ym) :=
  (spacesEtaleModelCrossing B S hS hχ).isColim_iff
    (fun a => (spacesEtaleModelDerivedEquiv B S hS a).fullyFaithfulFunctor) Sys Xm Ym

end AlgebraicGeometry.Space

end

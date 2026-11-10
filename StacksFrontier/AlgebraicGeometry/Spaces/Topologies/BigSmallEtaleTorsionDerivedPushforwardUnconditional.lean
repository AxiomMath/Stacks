module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleTorsionDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeUnconditional

/-!
# Proper base change for algebraic spaces in the derived category, unconditionally

This development proves, granted the proper base change theorem
for sheaves of sets on schemes (Stacks 0A3U, `h0A3U`) and the proper base change theorem for
schemes (Stacks 095T, `h095T`):

* the proper base change theorem for algebraic spaces (Stacks 0DG2) and its derived form for
  bounded below complexes with torsion cohomology sheaves (Stacks 0DG3);
* `π_X⁻¹ R f_{small,*} K ≅ R f_{big,*} π_Y⁻¹ K` for `f` proper and `K` bounded below with torsion
  cohomology sheaves (Stacks 0DGD, part (2)).

Both inputs are now proved: Stacks 0A3U is
`AlgebraicGeometry.isIso_smallEtaleSetBaseChange_of_isProper_forall` and Stacks 095T is
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`. This file supplies them.

## Main results

All in the namespace `AlgebraicGeometry.BigEtaleSpaceSite`:

* `isIso_spacesEtaleDerivedBaseChange_app_of_isProper`: Stacks 0DG3.
* `isIso_spacesEtaleDerivedBaseChange_app_singleFunctor_of_isProper`: Stacks 0DG2.
* `isIso_bigToSmallEtaleDerivedBaseChange_app_of_isProper` and
  `bigToSmallEtaleDerivedPushforwardIsoOfIsProper`: Stacks 0DGD, part (2).

## Implementation notes

The derived categories are those of the ported development, in the model
`HasDerivedCategory.standard`. The tags 0DG2, 0DG3 and 0DGD are registered elsewhere, so nothing
here carries a Stacks attribute.

## References

* [Stacks Project, Tag 0DG2](https://stacks.math.columbia.edu/tag/0DG2)
* [Stacks Project, Tag 0DG3](https://stacks.math.columbia.edu/tag/0DG3)
* [Stacks Project, Tag 0DGD](https://stacks.math.columbia.edu/tag/0DGD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Homology.DerivedSquare (totalRightDerived)

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard bigToSmallAbelianInverseImage_additive
  smallEtaleAbelianInverseImage_additive

/-- **Stacks 0DG3.** Let `Y' = Y ×_X X'` be a cartesian square of algebraic spaces over `S` with
`f : Y ⟶ X` proper. For every bounded below complex `E` of abelian sheaves on the spaces-étale
site of `Y` with torsion cohomology sheaves, the base change map
`g⁻¹ R f_* E ⟶ R f'_* (g')⁻¹ E` is an isomorphism. -/
theorem isIso_spacesEtaleDerivedBaseChange_app_of_isProper
    {X Y X' Y' : T.Spaces} (f : Y ⟶ X) (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g)
    (E : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1})) (n : ℤ) (hE : E.IsGE n) (hT : HasTorsionCohomology T E) :
    IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app E) :=
  isIso_spacesEtaleDerivedBaseChange_app_of_isProper_of_representable T
    isIso_smallEtaleSetBaseChange_of_isProper_forall
    (fun f _ ↦ Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f)
    f hf g g' f' sq E n hE hT

/-- **Stacks 0DG2.** Let `Y' = Y ×_X X'` be a cartesian square of algebraic spaces over `S` with
`f : Y ⟶ X` proper. For every torsion abelian sheaf `F` on the spaces-étale site of `Y`, the base
change map `g⁻¹ R f_* F ⟶ R f'_* (g')⁻¹ F` is an isomorphism. -/
theorem isIso_spacesEtaleDerivedBaseChange_app_singleFunctor_of_isProper
    {X Y X' Y' : T.Spaces} (f : Y ⟶ X) (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g)
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F) :
    IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app
      ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  isIso_spacesEtaleDerivedBaseChange_app_singleFunctor_of_isProper_of_representable T
    isIso_smallEtaleSetBaseChange_of_isProper_forall
    (fun f _ ↦ Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f)
    f hf g g' f' sq F hF

/-- **Stacks 0DGD, part (2), as invertibility of the base change map.** For a proper morphism
`f : Y ⟶ X` of algebraic spaces of the big étale site and every bounded below `K` on the
spaces-étale site of `Y` with torsion cohomology sheaves, the canonical base change map
`π_X⁻¹ R f_{small,*} K ⟶ R f_{big,*} π_Y⁻¹ K` is an isomorphism. -/
theorem isIso_bigToSmallEtaleDerivedBaseChange_app_of_isProper {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (K : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1})) (n : ℤ) (hK : K.IsGE n) (hT : HasTorsionCohomology T K) :
    IsIso ((bigToSmallEtaleDerivedBaseChange T f).app K) :=
  isIso_bigToSmallEtaleDerivedBaseChange_app T f hf isIso_smallEtaleSetBaseChange_of_isProper_forall
    (fun f _ ↦ Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f) K n hK hT

/-- **Stacks 0DGD, part (2).** For a proper morphism `f : Y ⟶ X` of algebraic spaces of the big
étale site and every bounded below `K` on the spaces-étale site of `Y` with torsion cohomology
sheaves, `π_X⁻¹ R f_{small,*} K ≅ R f_{big,*} π_Y⁻¹ K`, by the canonical base change map. -/
def bigToSmallEtaleDerivedPushforwardIsoOfIsProper {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (K : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1})) (n : ℤ) (hK : K.IsGE n) (hT : HasTorsionCohomology T K) :
    (CategoryTheory.Sites.abelianInverseImage (bigToSmallEtaleMorphism T X)).mapDerivedCategory.obj
        ((totalRightDerived (smallEtalePushforward T f)).obj K) ≅
      (totalRightDerived (bigEtalePushforward T f)).obj
        ((CategoryTheory.Sites.abelianInverseImage
          (bigToSmallEtaleMorphism T Y)).mapDerivedCategory.obj K) :=
  haveI := isIso_bigToSmallEtaleDerivedBaseChange_app_of_isProper T f hf K n hK hT
  asIso ((bigToSmallEtaleDerivedBaseChange T f).app K)

end AlgebraicGeometry.BigEtaleSpaceSite

end

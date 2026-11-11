module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModelNaiveCotangentHomologyCoherent
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsBaseIso
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentHomologyZero
public import StacksFrontier.Cotangent.SheavesOfRings.HomologyZero
public import StacksFrontier.Deformation.Artin.Obstruction.SpaceExtFunctors

/-!
# `H⁰` of the cotangent complex on the model is the sheaf of differentials

Let `g : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. Its cotangent complex
`L_{X/Y}` is formed on the `Type u` model of the small étale site of `X`
(`AlgebraicGeometry.Space.modelRingedToposHom`). This file identifies its degree `0` cohomology
sheaf with the sheaf of differentials `Ω_{X/Y}`, carried to the model by the Comparison Lemma
(`AlgebraicGeometry.Space.modelCotangentHomologyZeroIso`).

The steps are:

* `H⁰(L_{X/Y})` is the sheaf of relative differentials of the structure map `g⁻¹𝒪_Y ⟶ 𝒪_X` of
  the model (Stacks 08UR, `CategoryTheory.Sheaf.cotangentComplex_homologyZeroIso`);
* this structure map is the restriction to the model of the structure map of the small étale
  ringed topoi, precomposed with an isomorphism of the base rings
  (`sheafPushforwardContinuous_map_fSharpInverseImage`, in the namespace
  `Deformation.ToposThickening.RingedToposExtensionProblem`), which does not change the sheaf of
  differentials
  (`AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSiteIsoOfEqComp`);
* the sheaf of differentials of the restricted structure map is `H⁰` of the naive cotangent
  complex on the model (Stacks 08TY), which, carried back to `X`, is `Ω_{X/Y}`
  (`AlgebraicGeometry.Space.modelNaiveCotangentHomologyZeroIso`).

## Main definitions

* `AlgebraicGeometry.Space.modelCotangentHomologyZeroIso`: `H⁰(L_{X/Y}) ≅ Ω_{X/Y}` on the model.

## References

* [Stacks Project, Tag 08UR](https://stacks.math.columbia.edu/tag/08UR)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
* [Stacks Project, Tag 0D0Y](https://stacks.math.columbia.edu/tag/0D0Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian
  AlgebraicGeometry.Space.modelHasSheafifyULift
  AlgebraicGeometry.Space.modelWEqualsLocallyBijectiveULift

namespace AlgebraicGeometry.Space

open Deformation.ToposThickening.RingedToposExtensionProblem

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}
  (g : X ⟶ Y)

/-- **`H⁰(L_{X/Y})` is `Ω_{X/Y}` on the model**: the degree `0` cohomology sheaf of the cotangent
complex of `g`, formed on the model of the small étale site of `X`, is the sheaf of differentials
of `g` carried to the model by the Comparison Lemma. -/
def modelCotangentHomologyZeroIso :
    (modelRingedToposHom g).cotangentComplex.homology 0 ≅
      (smallEtaleModelModulesEquiv B S hS X).functor.obj (sheafOfDifferentials B S hS g) :=
  Sheaf.cotangentComplex_homologyZeroIso (modelTopos X).J
      (modelRingedToposHom g).fSharpInverseImage ≪≫
    (SheafOfModules.moduleOfDifferentialsOfSiteIsoOfEqComp.{u, u, u, u} _ _
      (sheafPushforwardContinuous_map_fSharpInverseImage (X := smallEtaleRingedTopos B S hS X)
        (B := smallEtaleRingedTopos B S hS Y) (smallEtaleModelTopology B S hS X.1)
        (smallEtaleModelEquiv B S hS X) (smallEtaleRingedToposHom B S hS g))).symm ≪≫
    (Stacks.SheafOfModules.naiveCotangentComplexHomologyZeroIso.{u, u, u, u}
      (smallEtaleModelTopology B S hS X.1) _ _ (modelBaseMap B S hS g)).symm ≪≫
    (smallEtaleModelModulesEquiv B S hS X).counitIso.symm.app _ ≪≫
    (smallEtaleModelModulesEquiv B S hS X).functor.mapIso
      (modelNaiveCotangentHomologyZeroIso B S hS g)

end AlgebraicGeometry.Space

end

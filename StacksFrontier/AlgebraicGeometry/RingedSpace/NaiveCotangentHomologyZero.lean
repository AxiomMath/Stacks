module

public import StacksFrontier.AlgebraicGeometry.RingedSpace.NaiveCotangentComplex
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentHomologyZero
public import StacksFrontier.Topology.Sheaves.Modules.DifferentialsOfSiteBridge

/-!
# The degree zero cohomology sheaf of the naive cotangent complex of a morphism of ringed spaces

For a morphism of ringed spaces `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)`, the naive cotangent complex
`NL_{X/Y}` is the naive cotangent complex of the homomorphism of sheaves of rings
`f^{-1}𝒪_Y ⟶ 𝒪_X`. Its degree `0` cohomology sheaf is therefore the sheaf of relative
differentials of that homomorphism.

## Main definitions

* `AlgebraicGeometry.RingedSpace.naiveCotangentComplexHomologyZeroIso`:
  `H⁰(NL_{X/Y}) ≅ Ω_{X/Y}`.

## Implementation notes

The site-level `Stacks.SheafOfModules.naiveCotangentComplexHomologyZeroIso` is applied at the
open-cover site of `X`, where it produces
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite`, and that is rewritten to the
open-cover-site spelling `AlgebraicGeometry.SheafOfModules.moduleOfDifferentials` by
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite_eq_moduleOfDifferentials`.

This is the level at which the rewrite can be performed. Both lemmas are applied with their
site, their sheaves of rings and their structural morphism supplied, exactly as in
`AlgebraicGeometry.RingedSpace.naiveCotangentComplex` itself; nothing is left for the
elaborator to unify between the `TopCat.Sheaf` and the `CategoryTheory.Sheaf` spellings of the
sheaves of rings of a ringed space.

## References

* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
* [Stacks Project, Tag 08TN](https://stacks.math.columbia.edu/tag/08TN), the naive cotangent
  complex of a morphism of ringed spaces.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Stacks 08TY in degree `0`,** for a morphism of ringed spaces. The degree `0` cohomology
sheaf of `NL_{X/Y}` is the sheaf of relative differentials `Ω_{X/Y}` of the homomorphism of
sheaves of rings `f^{-1}𝒪_Y ⟶ 𝒪_X`. -/
noncomputable def naiveCotangentComplexHomologyZeroIso :
    (naiveCotangentComplex f).homology 0 ≅
      AlgebraicGeometry.SheafOfModules.moduleOfDifferentials.{u, u, u}
        (inverseImageStructureMap f) :=
  Stacks.SheafOfModules.naiveCotangentComplexHomologyZeroIso.{u, u, u, u}
      (Opens.grothendieckTopology X.carrier) (inverseImageSheaf f) X.sheaf
      (inverseImageStructureMap f) ≪≫
    eqToIso
      (AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite_eq_moduleOfDifferentials.{
          u, u, u}
        (inverseImageSheaf f) X.sheaf (inverseImageStructureMap f))

end AlgebraicGeometry.RingedSpace

end

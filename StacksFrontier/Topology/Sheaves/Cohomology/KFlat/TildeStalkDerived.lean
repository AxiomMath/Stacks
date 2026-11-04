module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictScalarsDerived

/-!
# The derived-category form of Stacks 01HV

Let `A` be a commutative ring and `x` a point of `Spec A`. Stacks 01HV says that the stalk at `x`
of the sheaf associated to an `A`-module is the base change of that module along the germ map
`A ⟶ 𝒪_{Spec A, x}`. `Stacks.TildeStalk.tildeStalkFunctorIso` is that statement for modules and
`Stacks.TildeStalk.tildeStalkComplexIso` is its degreewise form on cochain complexes. This module
adds the form the derived category needs: the **derived** stalk at `x` of the object of
`D(𝒪_{Spec A})` attached to a complex `K` of `A`-modules is the image in `D(𝒪_{Spec A, x})` of the
degreewise base change of `K`.

That is the form in which an object of `D(𝒪_{Spec A})` presented through `~` can be read at a
point — which is what the Tor clause of Stacks 0DJZ needs of an affine chart, where the avatar of
`Stacks.AlgebraicGeometry.RingedSpace.exists_isPseudoCoherent_iso_mapDerivedCategory_tilde` has to
be compared with the derived stalk at a point of the chart.

## Main results

* `Stacks.TildeStalk.tildeDerivedStalkIso`: the derived stalk of the degreewise sheafification of
  `K`, identified with the image of the degreewise base change of `K`.
* `Stacks.TildeStalk.derivedStalkMapDerivedCategoryTildeIso`: the same with the sheafification
  itself read in the derived category, which is the shape the affine avatar of a pseudo-coherent
  object comes in.

## The functor-level form does not exist

The natural reading of "the derived form of Stacks 01HV" would be an isomorphism of functors

`(~).mapDerivedCategory ⋙ ((-)_x).mapDerivedCategory ≅ (𝒪_{Spec A, x} ⊗_A -).mapDerivedCategory`

obtained from `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` applied to
`tildeStalkFunctorIso`. **It cannot be formed**: `CategoryTheory.Functor.mapDerivedCategory` asks
its functor to be additive and to preserve finite limits and finite colimits, and for the
base-change side `Stacks.TildeStalk.tildeStalkBaseChange`, which is
`ModuleCat.extendScalars` along the germ map, *neither* exactness instance is available — both
`PreservesFiniteLimits` and `PreservesFiniteColimits` fail to synthesize at it. Only its
additivity is an instance
(`Stacks.TildeStalk.tildeStalkBaseChange_additive`, which obtains preservation of colimits by a
`haveI` from the adjunction rather than by instance search). Extension of scalars is exact only
along a flat ring homomorphism, and the germ map's flatness is nowhere seated.

So the statement is made at a cochain complex and `CategoryTheory.DerivedCategory.Q` of it, with
`CategoryTheory.Functor.mapDerivedCategoryFactors` on the stalk side, where only the *stalk*
functor has to be exact. This is the same shape, and for the same reason, as
`AlgebraicGeometry.AffineRelativeTorAmplitude.relativeFiberDerivedIso`, the derived fibre
comparison of Stacks 0DHY.

## Implementation notes

The stalk functor is written out as
`AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafOfRings (Spec A).toRingedSpace) x`
and **not** as `Stacks.TildeStalk.specStalkFunctor`, although the two are equal by definition.
`specStalkFunctor` is a `def`, so `PreservesFiniteLimits (specStalkFunctor A x)` does not match
the generic instance for a variable sheaf of rings at the transparency instance search runs at;
both exactness instances fail at it. At the written-out spelling all three fire with no
help, including the `HasSheafify` and `WEqualsLocallyBijective` side conditions of the generic
instances, which are found automatically because `Spec A` is a scheme. No restatement at a
variable sheaf of rings is needed here.

Left exactness of `~` itself is `AlgebraicGeometry.tilde.preservesFiniteLimits` of
`StacksFrontier.AlgebraicGeometry.Modules.TildeExactness`, which Mathlib does not prove, so that
module is imported explicitly; preservation of finite colimits comes from `~` being a left
adjoint, which Mathlib does supply. A warm check of this file does not see the missing import,
because the instance is in the import closure of whatever else is already loaded; the cold
build is what caught it.

Everything is read at `CategoryTheory.HasDerivedCategory.standard`, the model the stalkwise
criterion of Stacks 09U9 and the affine avatar are both stated at.

No `stacks` attribute is placed: Stacks 01HV is registered where it is proved, and this is the
descent of that statement to the derived categories, not a further clause of it.

## References

* [Stacks Project, Lemma 25.5.1 (Tag 01HV)](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Lemma 36.10.4 (Tag 0DHY)](https://stacks.math.columbia.edu/tag/0DHY)
* [Stacks Project, Lemma 37.71.3 (Tag 0DJZ)](https://stacks.math.columbia.edu/tag/0DJZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect AlgebraicGeometry

universe u

namespace Stacks.TildeStalk

attribute [local instance 10000] HasDerivedCategory.standard

variable (A : CommRingCat.{u}) (x : (Spec A).carrier)

/-- **The derived-category form of Stacks 01HV.** For a cochain complex `K` of `A`-modules, the
derived stalk at `x` of the degreewise sheafification `K̃^•` is the image in `D(𝒪_{Spec A, x})` of
the degreewise base change of `K` along the germ map `A ⟶ 𝒪_{Spec A, x}`.

The stalk functor is exact, so its descent to the derived categories is computed degreewise
(`CategoryTheory.Functor.mapDerivedCategoryFactors`), and degreewise it is
`tildeStalkComplexIso`. -/
public def tildeDerivedStalkIso (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} (Spec A).toRingedSpace) x).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj
        (((tildeStalkBaseChange A x).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings.{u} (Spec A).toRingedSpace) x).mapDerivedCategoryFactors.app
      (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≪≫
    DerivedCategory.Q.mapIso (tildeStalkComplexIso A x K)

/-- **Stacks 01HV with the sheafification itself read in the derived category.** The derived stalk
at `x` of the image under `(~).mapDerivedCategory` of the class of `K` is the image of the
degreewise base change of `K`.

This is `tildeDerivedStalkIso` preceded by the degreewise computation of the derived functor of
`~`, which is exact; it is the shape the affine avatar
`AlgebraicGeometry.RingedSpace.exists_isPseudoCoherent_iso_mapDerivedCategory_tilde` produces its
object in, so it is the form a consumer of that avatar can use. -/
public def derivedStalkMapDerivedCategoryTildeIso (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} (Spec A).toRingedSpace) x).mapDerivedCategory.obj
        ((tilde.functor A).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≅
      DerivedCategory.Q.obj
        (((tildeStalkBaseChange A x).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings.{u} (Spec A).toRingedSpace) x).mapDerivedCategory.mapIso
      ((tilde.functor A).mapDerivedCategoryFactors.app K) ≪≫
    tildeDerivedStalkIso A x K

end Stacks.TildeStalk

end

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat

/-!
# The symmetric monoidal derived category of a scheme

For a scheme `X` the derived category `D(𝒪_X)` of sheaves of `𝒪_X`-modules is symmetric monoidal
under the derived tensor product. This is the scheme-level reading of the ringed-site statement
of [Stacks, Tag 0FPT] in `StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory`
and `StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat`.

A scheme is a ringed site — the site of its open sets with the open-cover topology and its own
structure sheaf — and `Mod(𝒪_X)` in that reading *is* Mathlib's
`AlgebraicGeometry.Scheme.Modules`, by `rfl` (`AlgebraicGeometry.Scheme.Modules.mod_sheaf_eq`).
The three structures below are the ringed-site ones, applied at `X.sheaf`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.derivedMonoidal` — the monoidal structure on `D(𝒪_X)` given
  by the derived tensor product.
* `AlgebraicGeometry.Scheme.Modules.derivedSymmetric` — its commutativity constraint, the one
  induced by the Koszul symmetry of complexes.
* `AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal` — the same structure re-seated so
  that its tensor product *is* the derived tensor product of [Stacks, Tag 06YU] and its unit
  *is* `𝒪_X[0]`, both as equalities and not merely up to isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Modules.mod_sheaf_eq` — the category of modules on the ringed site of
  `X` is `X.Modules`.
* `AlgebraicGeometry.Scheme.Modules.curriedTensor_canonicalDerivedMonoidal`,
  `AlgebraicGeometry.Scheme.Modules.tensorUnit_canonicalDerivedMonoidal` — the two on-the-nose
  identifications carried by `canonicalDerivedMonoidal`.

## Implementation notes

None of the three is an `instance`, matching the ringed-site originals: a second ambient monoidal
structure on a derived category breaks instance search, so one is introduced where it is needed.
They are `@[instance_reducible]` for the same reason the originals are.

`D(𝒪_X)` is an instance *argument*, so a consumer reads these at whatever model it already works
in — in particular at the locally small model of
`StacksFrontier.Homology.DerivedCategory.LocallySmall`. The imported definition `X.Modules`
is exposed locally so that the given derived-category model is used directly in the native
ringed-site constructions, without introducing another model or a representation bridge.

Which universes this pins is inherited, not chosen here: the ringed-site construction assembles
K-flat resolutions from free modules on the representable presheaves, which ties the ring
universe to the site's hom universe, and a scheme `X : Scheme.{u}` meets that at `u` because
`Opens X` is a `u`-small category whose homs live in `Type u`.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u w

namespace AlgebraicGeometry.Scheme.Modules

attribute [local implicit_reducible] _root_.AlgebraicGeometry.Scheme.Modules
  _root_.AlgebraicGeometry.Scheme.Modules.Hom _root_.AlgebraicGeometry.Scheme.Modules.instCategory
  _root_.AlgebraicGeometry.SheafedSpace.sheaf TopCat.Sheaf CategoryTheory.sheafCompose

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : Scheme.{u})

/-- The category of modules on the ringed site attached to a scheme is Mathlib's category of
`𝒪_X`-modules. The two are the same category, not merely equivalent ones. -/
public theorem mod_sheaf_eq :
    Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf = X.Modules :=
  rfl

variable [derivedModel : HasDerivedCategory.{w} X.Modules]

/-- **The derived category of a scheme is monoidal**, under the derived tensor product. This is
the ringed-site structure of [Stacks, Tag 0FPT] read at `X.sheaf`. -/
@[instance_reducible]
public def derivedMonoidal : MonoidalCategory (DerivedCategory X.Modules) :=
  @Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal _ _ _ X.sheaf _ _ derivedModel

/-- **The derived category of a scheme is symmetric monoidal**, the commutativity constraint
being the one induced by the Koszul symmetry of complexes. -/
@[instance_reducible]
public def derivedSymmetric :
    @SymmetricCategory (DerivedCategory X.Modules) _ (derivedMonoidal X) :=
  @Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric _ _ _ X.sheaf _ _ derivedModel

/-- **The derived category of a scheme is monoidal with the derived tensor product of
[Stacks, Tag 06YU] as its tensor product and `𝒪_X[0]` as its unit**, both on the nose. This is
`AlgebraicGeometry.Scheme.Modules.derivedMonoidal` re-seated along those two identifications. -/
@[instance_reducible]
public def canonicalDerivedMonoidal : MonoidalCategory (DerivedCategory X.Modules) :=
  @Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal _ _ _ X.sheaf _ _ derivedModel

/-- The tensor product of `AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal` is the
derived tensor product of [Stacks, Tag 06YU]. -/
public theorem curriedTensor_canonicalDerivedMonoidal :
    @curriedTensor (DerivedCategory X.Modules) _ (canonicalDerivedMonoidal X) =
      @Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        _ _ _ X.sheaf _ _ derivedModel
        (Stacks.SheafOfModules.Tensor.sheafTensor_additive X.sheaf)
        (fun moduleSheaf =>
          Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive X.sheaf moduleSheaf)
        (fun leftComplex rightComplex =>
          Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor X.sheaf
            leftComplex rightComplex) :=
  @Stacks.SheafOfModules.DerivedMonoidal.curriedTensor_canonicalDerivedMonoidal
    _ _ _ X.sheaf _ _ derivedModel

/-- The unit of `AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal` is the structure
sheaf in degree zero. -/
public theorem tensorUnit_canonicalDerivedMonoidal :
    @tensorUnit (DerivedCategory X.Modules) _
        (canonicalDerivedMonoidal X).toMonoidalCategoryStruct =
      (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf) :=
  @Stacks.SheafOfModules.DerivedMonoidal.tensorUnit_canonicalDerivedMonoidal
    _ _ _ X.sheaf _ _ derivedModel

end AlgebraicGeometry.Scheme.Modules

end

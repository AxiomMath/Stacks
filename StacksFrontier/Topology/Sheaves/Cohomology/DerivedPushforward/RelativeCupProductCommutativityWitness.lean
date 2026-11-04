module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductCommutativity
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedTwoFactorWitness
public import StacksFrontier.Topology.Sheaves.RingedSpace.SheafifyOpens

/-!
# A non-degenerate instance of the commutativity of the relative cup product

`Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_braiding` of Stacks 0FP5 is
stated for an arbitrary morphism of ringed spaces and arbitrary `K, L ∈ D(𝒪_X)`, with no
hypothesis.  A statement with no hypothesis still says nothing if its binders cannot be filled,
or can be filled only by zero objects, so this file fills them with named terms that assume
nothing and shows the filling is not degenerate.

## Main results

* `Stacks.Cohomology.DerivedRelativeCupProduct.Witness.relativeCupProduct_braiding_ofArbitrary`:
  the four instance binders of the tagged theorem — `HasSheafify` and `WEqualsLocallyBijective`
  for the open-cover sites of the source and the target — are derivable for *every*
  `RingedSpace.{u, u}`, the open-cover site being essentially small.  So they restrict nothing
  and the tagged statement applies to every morphism of ringed spaces at those universes.
* `Stacks.Cohomology.DerivedRelativeCupProduct.Witness.not_isZero_singleFunctor_obj`: the
  degree-zero single functor into the derived category reflects zero objects.
* `Stacks.Cohomology.DerivedRelativeCupProduct.Witness.not_isZero_derivedStructureModuleWitness`:
  the object of `D(𝒪_W)` used below is **not** a zero object.
* `Stacks.Cohomology.DerivedRelativeCupProduct.Witness.relativeCupProduct_braiding_witness`:
  the commutativity square of Stacks 0FP5 at the completely explicit input `W`, `𝟙 W`,
  `K = L = 𝒪_W[0]`, every binder instantiated at once and `K` provably nonzero.

## Implementation notes

`W` is `Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.witnessSpace`: one point, with
`ℤ × ℤ` as its ring of sections.  It is built there from declarations that assume nothing, and
`...TwoFactorWitness.not_subsingleton_structureSheaf` is the proof that its structure sheaf has
more than one section, which is what makes `𝒪_W` a nonzero module and hence `𝒪_W[0]` a nonzero
object of `D(𝒪_W)`.

*A correction to a note in a neighbouring file.*  The module docstring of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/GlobalCupProduct.lean` says that
"the statements of Tags 0FP4 and 0FP5 in this repository carry undischarged hypotheses".  That
has not been true since both were discharged: `relativeCupProduct_braiding` (Stacks 0FP5) in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/RelativeCupProductCommutativity.lean`
and `relativeCupProduct_assoc` (Stacks 0FP4) in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/RelativeCupProductAssociativity.lean`
each bind only the source data — the two ringed spaces, the morphism, and the objects of
`D(𝒪_X)` — together with the four instance binders this file discharges for every ringed space.
The correction is recorded here rather than in that file because that file is under concurrent
edit elsewhere.  What *is* still undischarged there is `OnePointComparison`, which is a
different statement: it is about Section 0FKU's pairing on `RΓ`, not about Tag 0FP4 or 0FP5.

## References

* [Stacks Project, Tag 0FP5](https://stacks.math.columbia.edu/tag/0FP5)
* [Stacks Project, Tag 0FP4](https://stacks.math.columbia.edu/tag/0FP4)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  TopologicalSpace
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.SheafOfModules.DerivedMonoidal

namespace Stacks.Cohomology.DerivedRelativeCupProduct.Witness

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

/-- **No instance binder of Stacks 0FP5 restricts anything.**  For an arbitrary morphism of
ringed spaces at `RingedSpace.{u, u}` and arbitrary `K, L ∈ D(𝒪_X)`, the two instances assumed
by `relativeCupProduct_braiding` for each of the source and the target are supplied by the
essential smallness of the open-cover site, so the commutativity square of Stacks 0FP5 commutes
for every morphism of ringed spaces with no instance hypothesis carried by the caller. -/
def relativeCupProduct_braiding_ofArbitrary (X Y : RingedSpace.{u, u}) (f : X ⟶ Y)
    (K L : DerivedCategory (Mod X.sheaf)) :=
  relativeCupProduct_braiding f K L

/-! ### The instance is not degenerate -/

/-- **The degree-zero single functor reflects zero objects**: if `M` is a nonzero object of an
abelian category then `M` placed in degree zero is a nonzero object of its derived category. -/
theorem not_isZero_singleFunctor_obj {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (M : C) (hM : ¬ IsZero M) :
    ¬ IsZero ((DerivedCategory.singleFunctor C 0).obj M) := fun h =>
  hM (IsZero.of_iso ((DerivedCategory.homologyFunctor C 0).map_isZero h)
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app M).symm)

/-- The ringed space of the witness: one point, with `ℤ × ℤ` as its ring of sections. -/
abbrev witnessRingedSpace : RingedSpace.{u, u} :=
  Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.witnessSpace

/-- `𝒪_W` as a module over itself. -/
abbrev structureModuleWitness : Mod witnessRingedSpace.{u}.sheaf :=
  SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf witnessRingedSpace.{u}.sheaf)

/-- **`𝒪_W` is not a zero module**: its sections over the whole space are `ℤ × ℤ`, which is not
a subsingleton. -/
theorem not_isZero_structureModuleWitness : ¬ IsZero structureModuleWitness.{u} := fun h =>
  Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.not_subsingleton_structureSheaf
    (T := Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.onePointTop.{u})
    PUnit.unit PUnit.unit
    Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.intRing.{u}
    Stacks.Cohomology.InvertibleDerived.TwoFactorWitness.intRing.{u}
    (Stacks.subsingleton_of_isZero h (Opposite.op (⊤ : Opens _)))

/-- `𝒪_W` placed in degree zero, as an object of `D(𝒪_W)`. -/
abbrev derivedStructureModuleWitness : DerivedCategory (Mod witnessRingedSpace.{u}.sheaf) :=
  (DerivedCategory.singleFunctor (Mod witnessRingedSpace.{u}.sheaf) 0).obj
    structureModuleWitness.{u}

/-- **The object of `D(𝒪_W)` the witness below uses is not a zero object.**  So the instance of
Stacks 0FP5 it produces is not an identity between morphisms of a zero object. -/
theorem not_isZero_derivedStructureModuleWitness :
    ¬ IsZero derivedStructureModuleWitness.{u} :=
  not_isZero_singleFunctor_obj _ not_isZero_structureModuleWitness

/-- **Every binder of Stacks 0FP5 instantiated at once**, by named terms that assume nothing:
the ringed space `W`, its identity morphism, and `K = L = 𝒪_W[0]`, which
`not_isZero_derivedStructureModuleWitness` shows is not a zero object. -/
def relativeCupProduct_braiding_witness :=
  relativeCupProduct_braiding (𝟙 witnessRingedSpace.{u})
    derivedStructureModuleWitness.{u} derivedStructureModuleWitness.{u}

end Stacks.Cohomology.DerivedRelativeCupProduct.Witness

end

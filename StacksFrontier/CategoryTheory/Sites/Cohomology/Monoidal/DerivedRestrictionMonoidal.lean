module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.Homology.DerivedCategory.Monoidal.MapDerivedCategoryMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidalSheafTensor

/-!
# Derived restriction to a localized site is monoidal

Let `(C, O)` be a ringed site and `U` an object of `C`.  Restriction of sheaves of modules to
the localized site `C/U` is exact, so it induces a functor

`D(O) ⟶ D(O_U)`

on unbounded derived categories, namely
`Stacks.DerivedTensor.ExtensionByZero.restriction X U |>.mapDerivedCategory`; this is the functor
`Stacks.SheafOfModules.derivedRestrict` of Stacks 08DL reads on a ringed space.  This file equips
it with a **strong monoidal** structure for the derived tensor product of Stacks 0FPT —
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` — on each side.

The derived tensor product of a ringed site is the localization of the total tensor product of
complexes at the quasi-isomorphisms between K-flat complexes.  So a functor on derived categories
is monoidal as soon as the functor on complexes inducing it is monoidal *and carries K-flat
complexes to K-flat complexes*; that descent is the general
`CategoryTheory.Functor.mapDerivedCategoryMonoidal` of
`StacksFrontier.Homology.DerivedCategory.Monoidal.MapDerivedCategoryMonoidal`.  For restriction both
inputs are about restriction alone:

* K-flatness of the restriction of a K-flat complex is **Stacks 0E8K**,
  `Stacks.DerivedTensor.ExtensionByZero.kFlat_restrictionComplex`, restated below as
  `kFlat_restriction`; and
* monoidality of restriction on sheaves of modules — a statement about *sheaves*, with no
  derived category and no K-flatness in it — is
  `Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidalSheafTensor`, restated below as
  `sheafRestrictionMonoidal`.

Both are discharged, so the monoidal structure built here is unconditional.

## Main definitions

* `Stacks.Cohomology.DerivedRestriction.SheafRestrictionMonoidal`: a monoidal structure on
  restriction of sheaves of modules, for the tensor product
  `Stacks.SheafOfModules.Tensor.sheafTensor` on each side, and
  `Stacks.Cohomology.DerivedRestriction.sheafRestrictionMonoidal`, the one it carries.
* `Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal`: **derived restriction to a
  localized site is a strong monoidal functor.**

## Main results

* `Stacks.Cohomology.DerivedRestriction.kFlat_restriction`: Stacks 0E8K read at the spelling
  `CochainComplex.KFlatBifunctor.KFlat (curriedTensor _)` that the descent consumes.
* `Stacks.Cohomology.DerivedRestriction.preservesColimitsOfSize_restriction`: restriction
  preserves the coproducts a total complex is assembled from.

## What is proved

The **descent**: the induced functor on derived categories is monoidal, strongly — its
tensorator is invertible, which is what `CategoryTheory.ExactPairing.map` needs in order to carry
an exact pairing of `D(O)` forward to `D(O_U)`.  Nothing here is an assumption: every hypothesis
of the descent is discharged (exactness of restriction, additivity, preservation of the
coproducts of a total complex, existence of K-flat resolutions on both sites, K-flatness of a
restricted K-flat complex, and monoidality of restriction on sheaves of modules).

The sheaf-level input is not `Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidal` directly:
that is stated for the strict structure of Tag 01CA,
`Stacks.SheafOfModules.Strict.monoidalCategory`, whose tensor product is
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, while the derived tensor product is built
on `SheafOfModules.monoidalCategorySheafTensor`, whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor`.  The two structures are *not* the same term — the
equality of `Stacks.SheafOfModules.Strict.monoidalCategory` at
`Stacks.SheafOfModules.Tensor.ringSheaf R` with `SheafOfModules.monoidalCategorySheafTensor R`
fails even at `with_unfolding_all` transparency — and a `CategoryTheory.Functor.Monoidal` is a
structure over a particular pair of monoidal structures, so one does not transport to the other for
free.  What carries it across is that the two structures agree on every structural morphism: tensor
product on objects, unit and associator by `rfl`, whiskerings by
`Stacks.SheafOfModules.Strict.whiskerLeft_eq_sheafTensor` and `whiskerRight_eq_sheafTensor`, and
the two unitors by `SheafOfModules.leftUnitor_eq_strict` and `rightUnitor_eq_strict` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree` — each unitor being
the unit constraint `𝒪 ⊗_𝒪 ℱ ≅ ℱ` of the tensor product sheaf.  Hence the identity functor is
monoidal between them, in both directions, and restriction for the re-seated structure is a
composite of three monoidal functors; that is
`Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidalSheafTensor`.

No `@[stacks …]` attribute is attached anywhere in this file: this is infrastructure, not a
clause of a tag.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT), the derived tensor
  product as a monoidal structure.
* [Stacks Project, Tag 0E8K](https://stacks.math.columbia.edu/tag/0E8K), K-flatness of the
  restriction of a K-flat complex.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA), the tensor product
  sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction)

universe u

namespace Stacks.Cohomology.DerivedRestriction

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Restriction to a localized site carries K-flat complexes to K-flat complexes**, in the
form the descent of `CategoryTheory.Functor.mapDerivedCategoryMonoidal` consumes.  This is
Stacks 0E8K, `Stacks.DerivedTensor.ExtensionByZero.kFlat_restrictionComplex`, read at the
spelling `CochainComplex.KFlatBifunctor.KFlat (curriedTensor _)`: the tensor product of
`SheafOfModules.monoidalCategorySheafTensor` *is* `Stacks.SheafOfModules.Tensor.sheafTensor`, by
`SheafOfModules.curriedTensor_sheafTensor`, so the two readings are the same proposition and
nothing is transported. -/
theorem kFlat_restriction (K : CochainComplex (Modules X.O) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Modules X.O)) K) :
    CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Modules (X.O.over U)))
      (((restriction X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  Stacks.DerivedTensor.ExtensionByZero.kFlat_restrictionComplex X U K hK

/-- Restriction to the localized site preserves all small colimits, hence in particular the
coproducts a total tensor complex is assembled from.  It is the pushforward of sheaves of
modules along `Over.forget U`, which is continuous and cocontinuous, so this needs no products
on the site; see the implementation notes of
`Stacks.SheafOfModules.KFlatRestriction.preservesColimitsOfShape_restriction_of_cocontinuous`. -/
instance preservesColimitsOfSize_restriction :
    PreservesColimitsOfSize.{0, 0} (restriction X U) :=
  have _h : PreservesColimitsOfSize.{u, u} (restriction X U) :=
    Stacks.SheafOfModules.pushforward_preservesColimits (J := X.J.over U) (K := X.J)
      (Over.forget U) (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O).over U))
  preservesColimitsOfSize_shrink _

/-- A monoidal structure on restriction of sheaves of `O`-modules to the localized site `C/U`,
for the tensor product `Stacks.SheafOfModules.Tensor.sheafTensor` — that is, for
`SheafOfModules.monoidalCategorySheafTensor` — on each side.

It is named so that `mapDerivedCategoryMonoidal` can be read without unfolding which pair of
monoidal structures the sheaf-level input is taken over.  It is inhabited by
`sheafRestrictionMonoidal`. -/
abbrev SheafRestrictionMonoidal : Type (u + 1) := (restriction X U).Monoidal

/-- **Restriction of sheaves of `O`-modules to the localized site `C/U` is monoidal for the
tensor product `Stacks.SheafOfModules.Tensor.sheafTensor`.**  This is
`Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidalSheafTensor`: restriction is monoidal
for the structure of Tag 01CA by
`Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidal`, and the two monoidal structures
with that tensor product agree on every structural morphism, so the identity functor carries the
one to the other. -/
@[instance_reducible]
def sheafRestrictionMonoidal : SheafRestrictionMonoidal X U :=
  Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidalSheafTensor X.O U

/-- **Derived restriction to a localized site is a strong monoidal functor.**  For a ringed site
`(C, O)` and an object `U` of `C`, the functor

`D(O) ⟶ D(O_U)`

induced by restriction of sheaves of modules to `C/U` is monoidal for the derived tensor product
of Stacks 0FPT on each side.

The structure is **strong**, not lax: its tensorator is invertible.  That is what
`CategoryTheory.ExactPairing.map` consumes, so an exact pairing in `D(O)` is carried forward to
one in `D(O_U)` by this structure alone.

Every hypothesis of the descent is discharged: restriction is monoidal on sheaves of modules
(`sheafRestrictionMonoidal`), exact
(`Stacks.DerivedTensor.ExtensionByZero.preservesFiniteLimits_restriction` and
`preservesFiniteColimits_restriction`, Stacks 04BD (2) and local surjectivity of an
epimorphism), additive, and preserves the coproducts of a total complex
(`preservesColimitsOfSize_restriction`); both sites have K-flat resolutions (Stacks 06YS,
`Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution`); and the restriction of a K-flat
complex is K-flat (Stacks 0E8K, `kFlat_restriction`).  The descent itself is
`CategoryTheory.Functor.mapDerivedCategoryMonoidal`. -/
@[instance_reducible]
def mapDerivedCategoryMonoidal :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (X.O.over U)
    (restriction X U).mapDerivedCategory.Monoidal :=
  letI := sheafRestrictionMonoidal X U
  Functor.mapDerivedCategoryMonoidal (restriction X U) (kFlat_restriction X U)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.O)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution (X.O.over U))

end Stacks.Cohomology.DerivedRestriction

end

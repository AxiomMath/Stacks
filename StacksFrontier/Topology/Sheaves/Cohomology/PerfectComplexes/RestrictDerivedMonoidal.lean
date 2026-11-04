module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RestrictModulesMonoidalSheafTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedPullback
public import StacksFrontier.Homology.DerivedCategory.Monoidal.MapDerivedCategoryMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# Derived restriction to an open of a ringed space is monoidal

Let `(X, O_X)` be a ringed space and `U` an open subset. Restriction of sheaves of modules to the
open subspace `X|_U` induces a functor `D(O_X) ⥤ D(O_{X|_U})`, and this file equips it with a
**strong** monoidal structure for the derived tensor product of Stacks 0FPB on each side. As a
consequence an exact pairing `M ⊣ N` of `D(O_X)` — a left dual in the sense of Categories,
Definition 0FFP — restricts to an exact pairing of `D(O_{X|_U})`.

This is the shrinking step of the proof of Stacks 0FPD: *"it suffices to find an open
neighbourhood `U` of `x` such that `M` restricts to a perfect complex over `U`. Hence during the
proof we can (finitely often) replace `X` by an open neighbourhood of `x`"* — legitimate only
because the left dual restricts with `M`.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.mapDerivedCategoryMonoidalOfSheafTensor`: an additive,
  exact, coproduct-preserving functor between categories of modules on two ringed sites, monoidal
  for `SheafOfModules.monoidalCategorySheafTensor` and carrying K-flat complexes to K-flat
  complexes, is monoidal on derived categories for the derived tensor products of Stacks 0FPT.
* `Stacks.Cohomology.LeftDualPerfect.restrictDerivedMonoidal`: derived restriction to an open of a
  ringed space is monoidal for `Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory`
  on each side.
* `Stacks.Cohomology.LeftDualPerfect.exactPairingRestrictOpen`: an exact pairing of `D(O_X)`
  restricts to an exact pairing of `D(O_{X|_U})`.

## Implementation notes

The descent itself is `CategoryTheory.Functor.mapDerivedCategoryMonoidal`. It is first stated for
a general pair of ringed sites, where the instance arguments of the tensor product of sheaves of
modules are found at a variable sheaf of rings, and only then read at a ringed space: at
`X.sheaf` the instance `SheafOfModules.monoidalCategorySheafTensor`, stated at module universe
`max u v`, is not found against the diagonal universe of a space. Its inputs at a ringed space
are the monoidality of restriction of sheaves of modules,
`Stacks.Cohomology.LeftDualPerfect.restrictModulesRing_monoidalSheafTensor`, the preservation of
K-flatness by restriction to an open,
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_restrictComplex`, and the exactness of
restriction, which is a left adjoint
(`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.siteRestrictionAdjunction`) and preserves
finite limits (`AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits`).

## References

* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open TopologicalSpace Stacks.SheafOfModules.DerivedMonoidal Stacks.Cohomology.MonoidalDerived

universe u d d'

namespace Stacks.SheafOfModules.DerivedMonoidal

section Generic

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {C' : Type u} [SmallCategory.{u} C'] {J' : GrothendieckTopology C'}
  (R' : Sheaf J' CommRingCat.{u})
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Mod R)] [HasDerivedCategory.{d'} (Mod R')]

/-- **A monoidal exact functor of modules preserving K-flatness is monoidal on derived
categories**, for the derived tensor products of Stacks 0FPT on the two ringed sites. This is
`CategoryTheory.Functor.mapDerivedCategoryMonoidal` with the K-flat resolutions of Stacks 06YS on
each side. -/
@[instance_reducible]
def mapDerivedCategoryMonoidalOfSheafTensor (F : Mod R ⥤ Mod R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesColimitsOfSize.{0, 0} F] (hmon : F.Monoidal)
    (hF : ∀ K : Complexes R, KFlat R K →
      KFlat R' ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :
    letI := derivedMonoidal R
    letI := derivedMonoidal R'
    F.mapDerivedCategory.Monoidal :=
  Functor.mapDerivedCategoryMonoidal F hF (exists_kFlat_resolution R) (exists_kFlat_resolution R')

end Generic

end Stacks.SheafOfModules.DerivedMonoidal

namespace Stacks.Cohomology.LeftDualPerfect

variable (X : RingedSpace.{u, u}) (U : Opens X)

/-- Restriction of `O_X`-modules to the open subspace `X|_U`, in the spelling of the module
categories that the derived tensor product of Stacks 0FPB is stated at. -/
abbrev restrictMod : Mod X.sheaf ⥤ Mod (X.restrict U.isOpenEmbedding).sheaf :=
  Stacks.Cohomology.ClosedSupportPerfect.restrictModulesRing X U

/-- Restriction to an open is additive. -/
instance restrictMod_additive : (restrictMod X U).Additive :=
  inferInstanceAs (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U).Additive

/-- Restriction to an open carries K-flat complexes to K-flat complexes. -/
theorem kFlat_restrictMod (K : Complexes X.sheaf) (hK : KFlat X.sheaf K) :
    KFlat (X.restrict U.isOpenEmbedding).sheaf
      (((restrictMod X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_restrictComplex U K hK

/-- Restriction to an open is a left adjoint, so it preserves colimits. -/
instance restrictMod_preservesColimits : PreservesColimitsOfSize.{u, u} (restrictMod X U) :=
  Adjunction.leftAdjoint_preservesColimits
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.siteRestrictionAdjunction X U)

/-- Restriction to an open preserves the colimits a total complex is built from. -/
instance restrictMod_preservesColimits₀ : PreservesColimitsOfSize.{0, 0} (restrictMod X U) :=
  preservesColimitsOfSize_shrink _

/-- Restriction to an open preserves finite limits. -/
instance restrictMod_preservesFiniteLimits : PreservesFiniteLimits (restrictMod X U) :=
  AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits X U

/-- **Derived restriction to an open of a ringed space is a strong monoidal functor** for the
derived tensor product of Stacks 0FPB on `D(O_X)` and on `D(O_{X|_U})`. -/
@[instance_reducible]
def restrictDerivedMonoidal [HasDerivedCategory.{d} (Mod X.sheaf)]
    [HasDerivedCategory.{d'} (Mod (X.restrict U.isOpenEmbedding).sheaf)] :
    letI := derivedCategoryMonoidalCategory X
    letI := derivedCategoryMonoidalCategory (X.restrict U.isOpenEmbedding)
    (restrictMod X U).mapDerivedCategory.Monoidal :=
  mapDerivedCategoryMonoidalOfSheafTensor X.sheaf (X.restrict U.isOpenEmbedding).sheaf
    (restrictMod X U) (restrictModulesRing_monoidalSheafTensor X U) (kFlat_restrictMod X U)

/-- **An exact pairing of `D(O_X)` restricts to an open.** If `N` is a left dual of `M` for the
derived tensor product of Stacks 0FPB, then `N|_U` is a left dual of `M|_U` in `D(O_{X|_U})`:
this is `CategoryTheory.ExactPairing.map` along `restrictDerivedMonoidal`. -/
@[instance_reducible]
def exactPairingRestrictOpen [HasDerivedCategory.{d} (Mod X.sheaf)]
    [HasDerivedCategory.{d'} (Mod (X.restrict U.isOpenEmbedding).sheaf)]
    (M N : DerivedModules X.sheaf)
    (pair : letI := derivedCategoryMonoidalCategory X; ExactPairing M N) :
    letI := derivedCategoryMonoidalCategory (X.restrict U.isOpenEmbedding)
    ExactPairing ((restrictMod X U).mapDerivedCategory.obj M)
      ((restrictMod X U).mapDerivedCategory.obj N) :=
  letI := derivedCategoryMonoidalCategory X
  letI := derivedCategoryMonoidalCategory (X.restrict U.isOpenEmbedding)
  letI := restrictDerivedMonoidal X U
  ExactPairing.map _ M N

end Stacks.Cohomology.LeftDualPerfect

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Associativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorConstraints
import StacksCore.Tactic.StacksAttribute

/-!
# The associativity constraint of a prescribed derived tensor product, on K-flat complexes

Let `(C, O)` be a ringed site and let `T` be a derived tensor product on `D(Mod(O))` in the
sense of `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, i.e. [Stacks, Tag 06YU]. Its
associativity constraint `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator` is the
associator of the symmetric monoidal structure of [Stacks, Tag 0FPT] re-seated onto the
prescribed bifunctor, and as such it came with its three naturality squares and with no
description on complexes.

This file supplies that description. For K-flat complexes `K`, `L`, `M`, the comparison
`Stacks.SheafOfModules.DerivedMonoidal.kFlatComparison` of the tensor product of `D(Mod(O))`
with the total tensor product of complexes carries the associator of `D(Mod(O))` to the
associator of `Comp(Mod(O))` — that is
`Stacks.SheafOfModules.DerivedMonoidal.kFlatComparison_associator` — and the whole content here
is to move that statement across the re-seating, which is done once and for all over an
abstract bifunctor by `CategoryTheory.MonoidalCategory.reseat_associativity`.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.kFlatTensorComparison`: the comparison
  `T(Q K, Q L) ≅ Q(Tot(K ⊗_O L))` on K-flat complexes, for the prescribed bifunctor.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator_hom`: the associator of the
  prescribed bifunctor is the associator of [Stacks, Tag 0FPT], conjugated by the comparison of
  the two bifunctors.
* `Stacks.SheafOfModules.DerivedMonoidal.kFlatTensorComparison_associator`: **the
  associativity constraint of a prescribed derived tensor product is the associator of the total
  tensor product of complexes**, read through the comparison on K-flat complexes.

## What this corrects

The implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/Associativity.lean`,
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/MiddleSwap.lean`,
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/DerivedTensorReseat.lean` and
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/DerivedCategory.lean` all record the
compatibility of the K-flat comparison with the associator as **absent** from this
development. That was already out of date for the monoidal structure of
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`: the compatibility is
`kFlatComparison_associator`, and
`Stacks.SheafOfModules.DerivedMonoidal.symmetricMonoidalDerivedTensor` carries the tag for
[Stacks, Tag 0FPT] with that clause as a field. What was genuinely missing was the transport of
it to the *prescribed* bifunctor, which is what the re-seated associator is stated over and
hence what every consumer of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.middleSwapIso` needs; that transport is
`kFlatTensorComparison_associator` below. The notes are corrected in place.

No project tag is placed here. [Stacks, Tag 0FPT] is registered on
`symmetricMonoidalDerivedTensor`, whose comparison is the one for the tensor product of
`derivedMonoidal`; what is below is the same clause read for a prescribed bifunctor, which is
not a further part of that tag.

## Implementation notes

The comparison for the prescribed bifunctor has to be `kFlatComparison` precomposed with the
component of `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso` and not some
other isomorphism, because that component is the only identification of the two bifunctors the
development has, and it is the one `derivedTensorAssociator` is defined by.

Both proofs are a single term. The rewriting — the two whiskerings of the re-seated structure
and the re-seated associator — happens one level up, in a bare monoidal context, in
`StacksFrontier/CategoryTheory/Monoidal/Reseat.lean`; a caller in a derived category pays the
`isDefEq` cost of each such rewrite at objects for which it is not cheap, which is the
discipline of the neighbouring files.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization CochainComplex.KFlatBifunctor

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

/- The pinned-universe monoidal structures of `CanonicalDerivedTensorComparison`, back in
scope.  `SheafOfModules.monoidalCategorySheafTensor` has sections in `max u v w` for a `w`
that the `u` of `Mod R` does not determine, and the associator below cannot be reduced
through a structure whose universe is still a metavariable. -/
attribute [local instance] monoidalCategoryMod symmetricCategoryMod monoidalPreadditiveMod
  monoidalClosedMod hasTensorMod monoidalComplexes

attribute [local instance] CochainComplex.KFlatMonoidal.homotopyMonoidal
  CochainComplex.KFlatMonoidal.homotopyBraided
  kFlatQ_isLocalization derivedMonoidal derivedSymmetric

attribute [local instance] homQMonoidal homQBraided kFlatQMonoidal kFlatQBraided
  kFlatQuotientMonoidal kFlatQuotientLaxBraided kFlatComplexQMonoidal kFlatComplexQLaxBraided

variable (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct R)

/-- **The associator of a prescribed derived tensor product is the associator of
[Stacks, Tag 0FPT], conjugated by the comparison of the two bifunctors.** The three objects are
read into the prescribed bifunctor by the components of
`Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso` on the source and on the
target, and in the middle stands the associator of
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`, untouched.

This is `CategoryTheory.MonoidalCategory.reseat_associator` at the re-seating that
`Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator` is defined by, and it is what
carries a computation of the associator of `derivedMonoidal` over to the prescribed
bifunctor. -/
theorem derivedTensorAssociator_hom (K L M : DerivedModules R) :
    (derivedTensorAssociator R T K L M).hom =
      ((reseatIso (derivedTensorMonoidalIso R T) ((T.tensor.obj K).obj L) M).inv ≫
          ((reseatIso (derivedTensorMonoidalIso R T) K L).inv ⊗ₘ 𝟙 M)) ≫
        (α_ K L M).hom ≫
          (𝟙 K ⊗ₘ (reseatIso (derivedTensorMonoidalIso R T) L M).hom) ≫
            (reseatIso (derivedTensorMonoidalIso R T) K ((T.tensor.obj L).obj M)).hom :=
  reseat_associator (derivedTensorMonoidalIso R T) (canonicalUnitIso R) K L M

/-- **For K-flat complexes a prescribed derived tensor product is the total tensor product of
complexes.** This is `Stacks.SheafOfModules.DerivedMonoidal.kFlatComparison`, the comparison for
the tensor product of `D(Mod(O))`, read through the identification
`Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso` of that tensor product with the
prescribed bifunctor. -/
abbrev kFlatTensorComparison {K L : Complexes R} (hK : KFlat R K) (hL : KFlat R L) :
    (T.tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (K ⊗ L) :=
  (reseatIso (derivedTensorMonoidalIso R T) (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj L)).symm ≪≫ kFlatComparison R hK hL

/-- **The associativity constraint of a prescribed derived tensor product is the associator of
the total tensor product of complexes**: on K-flat complexes `K`, `L`, `M` the comparison
`kFlatTensorComparison` carries `derivedTensorAssociator` to
`DerivedCategory.Q.map (α_ K L M).hom`.

This is the clause of [Stacks, Tag 0FPT] that the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/Associativity.lean` and of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/MiddleSwap.lean` recorded as absent
for the prescribed bifunctor. It is `kFlatComparison_associator`, which is the same statement
for the tensor product of `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`, moved across
the re-seating by `CategoryTheory.MonoidalCategory.reseat_associativity`. -/
theorem kFlatTensorComparison_associator {K L M : Complexes R}
    (hK : KFlat R K) (hL : KFlat R L) (hM : KFlat R M) :
    (T.tensor.map (kFlatTensorComparison R T hK hL).hom).app (DerivedCategory.Q.obj M) ≫
        (kFlatTensorComparison R T
            (CochainComplex.KFlatMonoidal.kFlat_tensor (Mod R) hK hL) hM).hom ≫
          DerivedCategory.Q.map (α_ K L M).hom =
      (derivedTensorAssociator R T (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
            (DerivedCategory.Q.obj M)).hom ≫
        (T.tensor.obj (DerivedCategory.Q.obj K)).map (kFlatTensorComparison R T hL hM).hom ≫
          (kFlatTensorComparison R T hK
            (CochainComplex.KFlatMonoidal.kFlat_tensor (Mod R) hL hM)).hom :=
  reseat_associativity (derivedTensorMonoidalIso R T) (kFlatComparison R hK hL)
    (kFlatComparison R (CochainComplex.KFlatMonoidal.kFlat_tensor (Mod R) hK hL) hM)
    (kFlatComparison R hL hM)
    (kFlatComparison R hK (CochainComplex.KFlatMonoidal.kFlat_tensor (Mod R) hL hM))
    (derivedTensorAssociator_hom R T _ _ _) (kFlatComparison_associator R hK hL hM)

end Stacks.SheafOfModules.DerivedMonoidal

end

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.MapOutOfAConstantComplex
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingModulesCompatibility

/-!
# The two readings of `Mod(C, Λ)` agree over the constant ringed site

Stacks 09BD is in the library as
`AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap_constant`, stated for sheaves of
modules over the structure sheaf of the constant ringed site restricted to an object `U`, with
the complex of constant sheaves of modules produced by
`AlgebraicGeometry.RingedSite.constantFunctorOver`. Stacks 09BE is being assembled in the other
reading of `Mod(C, Λ)`, namely `Sheaf (J.over U) (ModuleCat Λ)`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafComplexLocalHom`.

This file puts the two readings of 09BD's own ambient category in bijection, and identifies
09BD's constant-complex functor with the constant sheaf functor across that bijection. It is the
instance at the constant ringed site of the two compatibilities of
`StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingModulesCompatibility`.

## Main definitions

* `Stacks.ConstantRingModules.constantRingedSiteModuleEquivalence`: the equivalence
  `SheafOfModules (Λ̲|_U) ≌ Sheaf (J.over U) (ModuleCat Λ)` over the constant ringed site.
* `Stacks.ConstantRingModules.constantFunctorOverIso`: across that equivalence, 09BD's
  `constantFunctorOver` is `constantSheaf (J.over U) (ModuleCat Λ)`.

## Implementation notes

Two steps separate the two readings, and both were available. Restriction of scalars along the
identification of the restricted structure sheaf with the constant sheaf of rings on `C/U` --
`AlgebraicGeometry.RingedSite.constantRingSheafOverIso` -- is an equivalence by
`Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso`, and its functor is 09BD's own
`AlgebraicGeometry.RingedSite.constantRestrict`. What remains is the equivalence
`Stacks.ConstantRingModules.constantModuleSheafEquivalence` at the site `C/U`. The identification
of the constant functors is then `Stacks.ConstantRingModules.constantModuleSheafFunctorIso` at
`C/U`, the restriction of scalars cancelling against its own inverse.

**What this does not do.** It does not port Stacks 09BD itself. The statement of 09BD is a
statement about morphisms of the derived category `D(Λ̲|_U)`, and carrying it across the
equivalence needs the equivalence's induced functor on derived categories together with
`CategoryTheory.Functor.mapDerivedCategoryFactors`, which is not done here. The two
compatibilities the previous pass recorded as owed -- with the constant-sheaf functors and with
slicing -- are what this file and
`StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingModulesCompatibility` supply; the derived
transport is a separate obligation and no claim about it is made.

The derived forms of both definitions below are in
`StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingedSiteDerivedComparison`, namely
`Stacks.ConstantRingModules.constantRingedSiteModuleDerivedEquivalence` and
`constantFunctorOverDerivedIso`; that file carries the input side of the transport, and its own
note records what of it is still owed.

No `@[stacks]` attribute is attached. Nothing here is an assertion of 09BD or of 09BE.

## References

* [Stacks Project, Tag 09BD](https://stacks.math.columbia.edu/tag/09BD)
* [Stacks Project, Tag 09BE](https://stacks.math.columbia.edu/tag/09BE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ConstantRingModules

open AlgebraicGeometry.RingedSite Stacks.SheafOfModules.Constant Stacks.Sheaves.RingedPoint

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
  [HasWeakSheafify J CommRingCat.{u}] [HasWeakSheafify J RingCat.{u}]
  (U : C) [HasWeakSheafify (J.over U) RingCat.{u}]
  [(J.over U).WEqualsLocallyBijective RingCat.{u}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (J.over U) (ModuleCat.{u} Λ)]
  [(J.over U).WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [(J.over U).HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- **The two readings of `Mod(C/U, Λ)` agree over the constant ringed site.** Sheaves of
modules over the restriction to `U` of the structure sheaf of the constant ringed site are
sheaves of `Λ`-modules on the slice site `C/U`: restrict the scalars along
`AlgebraicGeometry.RingedSite.constantRingSheafOverIso` to land over the constant sheaf of rings
on `C/U`, and then apply the equivalence of
`StacksFrontier.CategoryTheory.Sites.Modules.ModuleSheavesAsConstantRingModules`.

This is the ambient category of Stacks 09BD on the left and of Stacks 09BE on the right. -/
def constantRingedSiteModuleEquivalence :
    _root_.SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O).over U) ≌
      Sheaf (J.over U) (ModuleCat.{u} Λ) :=
  (restrictScalarsEquivalenceOfIso (constantRingSheafOverIso_general J Λ U)).symm.trans
    (constantModuleSheafEquivalence Λ (J.over U))

/-- **Stacks 09BD's complex of constant sheaves of modules is the complex of constant sheaves.**
Across `Stacks.ConstantRingModules.constantRingedSiteModuleEquivalence`, the functor
`AlgebraicGeometry.RingedSite.constantFunctorOver` -- the `Φ` at which 09BD instantiates Stacks
08FR -- is `constantSheaf (J.over U) (ModuleCat Λ)`, which is the functor Stacks 09BE is stated
over. -/
def constantFunctorOverIso :
    constantFunctorOver_general J Λ U ⋙ (constantRingedSiteModuleEquivalence J Λ U).functor ≅
      constantSheaf (J.over U) (ModuleCat.{u} Λ) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (constantModuleSheafFunctor (J.over U) (R := Λ))
        (restrictScalarsEquivalenceOfIso (constantRingSheafOverIso_general J Λ U)).unitIso.symm)
      (toModuleSheaf.{u} Λ (J.over U) (constantRingMap Λ (J.over U))) ≪≫
    constantModuleSheafFunctorIso.{u} Λ (J.over U)

end Stacks.ConstantRingModules

end

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingedSiteDerivedComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingedSiteTwoReadings

/-!
# The second object of Stacks 09BE as a target for Stacks 09BD

Stacks 09BD, `AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap_constant`, takes a
morphism `K̲^• ⟶ F` of `D(Λ̲|_U)` whose target `F` is an **arbitrary** complex of sheaves of
modules. Stacks 09BE is about a morphism `K̲ ⟶ L̲` whose target is the constant object on a
second object `L` of `D(Λ)`. The source statement therefore needs that second object exhibited
as a complex 09BD can be applied to.

This file does it: a complex of `Λ`-modules representing `L` is carried termwise by 09BD's own
constant-complex functor `AlgebraicGeometry.RingedSite.constantFunctorOver`, and the resulting
complex represents `L̲|_U` -- the constant object on `L`, restricted to the slice site `C/U` and
read in 09BD's model of `Mod(C/U, Λ)`.

## Main results

* `Stacks.ConstantRingModules.exists_constantFunctorOver_model`: every object `L` of `D(Λ)` is
  represented, in 09BD's ambient category, by the termwise constant complex on a representative
  of `L`; across the identification of the two readings this is the class of `L̲` on the slice
  site.
* `Stacks.ConstantRingModules.constantFunctorOverTwoReadingsIso`: 09BD's constant-complex
  functor is the constant sheaf functor in the reading whose slicing squares are available, namely
  `Stacks.ConstantRingModules.toModuleSheaf` along
  `Stacks.ConstantRingModules.overRingMap`.

## Implementation notes

The representative is `DerivedCategory.Q.objPreimage`, so the statement is an existence
statement rather than a construction: nothing canonical chooses a complex representing an
object of `D(Λ)`, and 09BD does not need one -- it needs some complex, together with the
identification of its class with the one the hypothesis of 09BE is about.

The identification is read through `Stacks.ConstantRingModules.constantFunctorOverDerivedIso`
and Mathlib's `CategoryTheory.Functor.mapDerivedCategoryFactors` for the constant sheaf functor
on `C/U`. The exactness of that functor is what makes the second of these available: it is
additive (`Stacks.ConstantSheaf.constantSheaf_moduleCat_additive`), left exact
(`Stacks.ConstantSheaf.constantSheaf_preservesFiniteLimits`) and right exact on a slice site
(`Stacks.ConstantSheaf.preservesFiniteColimits_constantSheaf_over`, the left adjoint of
evaluation at the terminal object `𝟙 U` of `C/U`) -- the last of the three being the reason this
is stated on a slice and not on `C`, where no terminal object is in force.

`constantFunctorOverTwoReadingsIso` is `Stacks.ConstantRingModules.constantFunctorOverIso`
transported along `constantRingedSiteModuleEquivalence_functor_eq`. It is recorded here because
the assembly of 09BE needs 09BD's constant complex in the reading that
`Stacks.ConstantRingModules.toModuleSheafOverMapIso` and its derived form are stated over, and
not in the one `constantFunctorOverIso` uses.

## References

* [Stacks Project, Tag 09BD](https://stacks.math.columbia.edu/tag/09BD)
* [Stacks Project, Tag 09BE](https://stacks.math.columbia.edu/tag/09BE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ConstantRingModules

open AlgebraicGeometry.RingedSite Stacks.SheafOfModules.Constant Stacks.Sheaves.RingedPoint

attribute [local instance] additive_constantRingedSiteModuleEquivalence_functor
  additive_constantRingedSiteModuleEquivalence_inverse

universe d u

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
  [HasWeakSheafify J CommRingCat.{u}] [HasWeakSheafify J RingCat.{u}]
  (U : C) [HasWeakSheafify (J.over U) RingCat.{u}]
  [(J.over U).WEqualsLocallyBijective RingCat.{u}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (J.over U) (ModuleCat.{u} Λ)]
  [(J.over U).WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [(J.over U).HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- **Stacks 09BD's constant-complex functor, in the reading whose slicing squares are
available.** `AlgebraicGeometry.RingedSite.constantFunctorOver`, read through
`Stacks.ConstantRingModules.toModuleSheaf` along the restriction to `C/U` of the global map out
of the constant presheaf of rings, is `constantSheaf (J.over U) (ModuleCat Λ)`.

This is `Stacks.ConstantRingModules.constantFunctorOverIso` transported along
`Stacks.ConstantRingModules.constantRingedSiteModuleEquivalence_functor_eq`. -/
def constantFunctorOverTwoReadingsIso :
    constantFunctorOver_general J Λ U ⋙
        toModuleSheaf.{u} Λ (J.over U) (overRingMap Λ J (constantRingedSiteRingMap J Λ) U) ≅
      constantSheaf (J.over U) (ModuleCat.{u} Λ) :=
  Functor.isoWhiskerLeft (constantFunctorOver_general J Λ U)
      (eqToIso (constantRingedSiteModuleEquivalence_functor_eq J Λ U).symm) ≪≫
    constantFunctorOverIso J Λ U

variable [HasDerivedCategory.{d}
    (_root_.SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedSite_general J Λ).O).over U))]
  [HasDerivedCategory.{d} (Sheaf (J.over U) (ModuleCat.{u} Λ))]
  [HasDerivedCategory.{d} (ModuleCat.{u} Λ)]

/-- **The second object of Stacks 09BE, as a target Stacks 09BD applies to.** Let `L` be an
object of `D(Λ)`. Then `L` is represented by a complex `T` of `Λ`-modules whose termwise image
under 09BD's constant-complex functor `AlgebraicGeometry.RingedSite.constantFunctorOver`
represents, across the identification of the two readings of `D(C/U, Λ)`, the restriction to
`C/U` of the constant object `L̲`.

Stacks 09BD is stated for an arbitrary complex of sheaves of modules as its target; this is what
lets it be applied with the target of Stacks 09BE's morphism, which is a constant object on a
second object of `D(Λ)` and not a complex at all. -/
theorem exists_constantFunctorOver_model (L : DerivedCategory (ModuleCat.{u} Λ)) :
    ∃ T : CochainComplex (ModuleCat.{u} Λ) ℤ,
      Nonempty (DerivedCategory.Q.obj T ≅ L) ∧
      Nonempty ((constantRingedSiteModuleEquivalence J Λ U).functor.mapDerivedCategory.obj
          (DerivedCategory.Q.obj
            (((constantFunctorOver_general J Λ U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj T)) ≅
        (constantSheaf (J.over U) (ModuleCat.{u} Λ)).mapDerivedCategory.obj L) := by
  refine ⟨DerivedCategory.Q.objPreimage L, ⟨DerivedCategory.Q.objObjPreimageIso L⟩, ⟨?_⟩⟩
  exact (constantFunctorOverDerivedIso J Λ U).app (DerivedCategory.Q.objPreimage L) ≪≫
    ((constantSheaf (J.over U) (ModuleCat.{u} Λ)).mapDerivedCategoryFactors.app
      (DerivedCategory.Q.objPreimage L)).symm ≪≫
    (constantSheaf (J.over U) (ModuleCat.{u} Λ)).mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso L)

end Stacks.ConstantRingModules

end

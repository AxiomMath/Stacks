module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianAcyclicityFromContinuity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ModuleDerivedLowerShriek
import StacksCore.Tactic.StacksAttribute

/-!
# Derived sections over an object along a continuous and cocontinuous functor of sites

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites and let
`g : Sh(C) ⟶ Sh(D)` be the corresponding morphism of topoi. **Stacks 0DD8** says that for an
object `U` of `C`

1. `RΓ(U, g⁻¹M) = RΓ(u(U), M)` for `M` in `D(D)`, and
2. `RΓ(U, g^*M) = RΓ(u(U), M)` for `M` in `D(O_D)`, when `O_D` is a sheaf of rings on `D` and
   `O_C = g⁻¹O_D`.

`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/DerivedSectionsAlongAFunctor.lean`
proves both from the derived adjunction `Lg_! ⊣ g^*` of Stacks 07AC, taking as inputs the
existence of `Lg_!`, its absoluteness against derived restriction, and the invertibility of the
derived lower-shriek counit at the single complex on the generator `j_{U!}O_U`. This file
discharges all three for a continuous and cocontinuous functor in the sense of Sites,
Definition 00WV, and states the two parts at the source's hypotheses.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.derivedAbelianSectionsRestrictionIso_of_continuous`:
  **Stacks 0DD8**, part (1).
* `Stacks.Cohomology.DerivedLowerShriek.derivedModuleSectionsRestrictionIso_of_continuous`:
  **Stacks 0DD8**, part (2).

## Implementation notes

Continuity in the sense of the source (Stacks 00WV) is `Functor.IsContinuous` together with its
covering-pullback clause `Stacks.Sites.PreservesCoveringPullbacks`: a site in the sense of
Stacks 00VH has the fibre products of its coverings along arbitrary arrows, and a continuous
functor preserves them. `Functor.IsContinuous` records only that restriction along `u`
preserves sheaves and implies neither; the clause is the only input the proof uses beyond
`Functor.IsContinuous` and `Functor.IsCocontinuous`.

The acyclicity statement of Stacks 0794 for lower shriek is proved from Stacks 0D6X, hence from
the covering-pullback clause, in `ModuleDerivedLowerShriek.lean` for modules
(`lowerShriekModules_acyclic`) and in `AbelianAcyclicityFromContinuity.lean` for abelian sheaves
(`abelianLowerShriekAcyclic_of_continuous`). Those files make the existence of `Lg_!` and its
absoluteness against derived restriction instances, and prove the counit invertible on bounded
above complexes of direct sums of the generators
(`isIso_derivedLowerShriekComparison_app`, `isIso_derivedAbelianLowerShriekComparison_app`),
the single complex on `j_{U!}O_U` being one of them.

The two sites, their morphisms and the coefficients are in one universe `u`, the sites being
small: this is the library's standard one-universe convention for sites, under which the
categories of sheaves are Grothendieck abelian and `Sh(C)` is a topos as in the source. The
structure sheaf of part (2) is a sheaf of commutative rings, which is what a sheaf of rings is in
the source (Stacks 0006: a ring is a commutative ring with `1`).

## References

* [Stacks Project, Tag 0DD8](https://stacks.math.columbia.edu/tag/0DD8)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.DerivedLowerShriek

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
  [Stacks.Sites.PreservesCoveringPullbacks J f] (U : C)

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks Project, Tag 0DD8, part (1).** Let `u : C ⥤ D` be a continuous and cocontinuous
functor of sites and let `g : Sh(C) ⟶ Sh(D)` be the corresponding morphism of topoi. For every
object `U` of `C` and every `M` in the unbounded derived category of abelian sheaves on `D`,
`RΓ(U, g⁻¹M) = RΓ(u(U), M)`, naturally in `M`.

This is `derivedAbelianSectionsRestrictionIso` with all of its inputs discharged. The
invertibility of the derived lower-shriek counit at the single complex on `j_{U!} ℤ_U` is
`isIso_derivedAbelianLowerShriekComparison_app`, which holds because that complex is cellular
for the class with which `Lg_!^{Ab}` is built; the existence of `Lg_!^{Ab}` and its
absoluteness against derived restriction are the two instances of
`AbelianAcyclicityFromContinuity.lean`. All three come from the acyclicity statement of
Stacks 0794 for lower shriek on abelian sheaves, which that file derives from Stacks 0D6X and so
from the covering-pullback clause `Stacks.Sites.PreservesCoveringPullbacks` of continuity in the
sense of Sites, Definition 00WV. -/
@[stacks 0DD8 "part (1); the two sites are small and the coefficients are in their universe, \
the library's standard one-universe convention for sites"]
def derivedAbelianSectionsRestrictionIso_of_continuous :
    derivedAbelianRestriction.{u} J K f ⋙ derivedAbelianSections J U ≅
      derivedAbelianSections K (f.obj U) :=
  have : IsGrothendieckAbelian.{u} (Sheaf K AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} K AddCommGrpCat.{u}
  have : IsGrothendieckAbelian.{u} (Sheaf J AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} J AddCommGrpCat.{u}
  derivedAbelianSectionsRestrictionIso J K f U
    (isIso_derivedAbelianLowerShriekComparison_app J K f _
      (isSumOfExtensionByZeroUnitsAb_single J U))

/-- **Stacks Project, Tag 0DD8, part (2).** Let `u : C ⥤ D` be a continuous and cocontinuous
functor of sites, let `g : Sh(C) ⟶ Sh(D)` be the corresponding morphism of topoi, let `O_D` be a
sheaf of rings on `D` and let `O_C = g⁻¹O_D`. For every object `U` of `C` and every `M` in the
unbounded derived category of `O_D`-modules, `RΓ(U, g^*M) = RΓ(u(U), M)`, naturally in `M`.

This is `derivedModuleSectionsRestrictionIso` with all of its inputs discharged. The
invertibility of the derived lower-shriek counit at the single complex on `j_{U!} O_U` is
`isIso_derivedLowerShriekComparison_app`, and the existence of `Lg_!` and its absoluteness
against derived restriction are the two instances of `ModuleDerivedLowerShriek.lean`; all three
come from `lowerShriekModules_acyclic`, the acyclicity statement of Stacks 0794 for lower shriek
on modules, which that file derives from Stacks 0D6X and so from the covering-pullback clause
`Stacks.Sites.PreservesCoveringPullbacks` of continuity in the sense of Sites,
Definition 00WV. -/
@[stacks 0DD8 "part (2); the two sites are small and the module sections are in their \
universe, the library's standard one-universe convention for sites; the structure sheaf is a \
sheaf of commutative rings, which is what a sheaf of rings is in the source (Stacks 0006)"]
def derivedModuleSectionsRestrictionIso_of_continuous (O : Sheaf K CommRingCat.{u}) :
    derivedRestriction J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) ⋙
        derivedModuleSections J (inverseImageRing J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) U ≅
      derivedModuleSections K (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)
        (f.obj U) :=
  derivedModuleSectionsRestrictionIso J K f _ U
    (isIso_derivedLowerShriekComparison_app J K f O _
      (isSumOfExtensionByZeroUnits_single J _ U))

end Stacks.Cohomology.DerivedLowerShriek

end

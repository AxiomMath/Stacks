module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictKInjective
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# The unit and the counit of `Lε^* ⊣ Rε_*`

Let `S` be a scheme and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites of
Stacks 070R/08H7.  Its inverse image of sheaves of modules is the associated-module functor `ε^*`
of Stacks 03DU (4), `AlgebraicGeometry.SmallEtale.associatedModule`, and its direct image is
`AlgebraicGeometry.SmallEtale.restrictModule`; the two are adjoint, by
`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction`.

The derived adjunction itself — the functor `ε^* : D(𝒪_S) ⥤ D(S_étale, 𝒪)` induced on the
unbounded derived categories by the exact `ε^*` is left adjoint to the total right derived functor
`Rε_*` of Stacks 07A5 at `ε` — is
`AlgebraicGeometry.SmallEtale.derivedAssociatedModuleAdjunction`, in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedPushforward.lean`, where
`Rε_*` is built.  Since `ε` is flat (Stacks 08H8,
`AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap`) the functor induced by
`ε^*` *is* the `Lε^*` of the source, so that adjunction is `Lε^* ⊣ Rε_*` — the adjunction
Stacks 071Q is proved with.

What this file adds is the identification of its **unit and counit** with the ones the underived
adjunction `ε^* ⊣ ε_*` induces on homotopy categories, read through the two derived-functor
comparison maps.  That is `Stacks.DerivedFunctor.derivedAdjunction_unit_app` and
`Stacks.DerivedFunctor.derivedAdjunction_counit_app` — Stacks 09T5 for derived categories of
abelian categories — at `ε`, whose inputs are all available and are only assembled here:

* exactness of `ε^*` is the second assertion of Stacks 08H8,
  `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModuleOfSheaf`, together with
  right exactness of a left adjoint,
  `AlgebraicGeometry.SmallEtale.preservesFiniteColimits_associatedModuleOfSheaf`;
* enough K-injective complexes of `𝒪`-modules on `S_étale` is Stacks 079P, available because
  those module sheaves are Grothendieck abelian at the universe of their sections
  (`AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheafOfModules`); it is
  `AlgebraicGeometry.SmallEtale.exists_quasiIso_isKInjective`.

Nothing is assumed beyond the two `CategoryTheory.HasDerivedCategory` instances that
`AlgebraicGeometry.SmallEtale.derivedRestrictModule` itself carries.

## Why the left-hand functor is spelled `(associatedModuleOfSheaf B S hS).mapDerivedCategory`

That composite is the derived functor of the exact `ε^*` on the unbounded derived categories, and
it is the spelling the development uses at *free* `CategoryTheory.HasDerivedCategory` instances —
`AlgebraicGeometry.SmallEtale.derivedAssociatedModule`, the functor of Stacks 071Q, is it
corestricted to the complexes with quasi-coherent cohomology.  The name
`AlgebraicGeometry.SmallEtale.derivedAssociatedModuleFunctor` is the *same* construction, but it
is declared under a file-wide `CategoryTheory.HasDerivedCategory.standard`, which on the small
étale side is `HasDerivedCategory.{u + 1}` and on the Zariski side `HasDerivedCategory.{u}`; the
statements below are made at the free instances and specialize to the pinned name whenever the two
agree.

## Main results

* `AlgebraicGeometry.SmallEtale.derivedAssociatedModuleAdjunction_unit_app` and
  `AlgebraicGeometry.SmallEtale.derivedAssociatedModuleAdjunction_counit_app`: the unit and counit
  of the derived adjunction are the ones induced by the unit and counit of `ε^* ⊣ ε_*` together
  with the two derived-functor comparison maps.

## References

* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.SmallEtale

universe w u

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B S hS))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]

/-- The unit of `Lε^* ⊣ Rε_*` is the one induced by the unit of `ε^* ⊣ ε_*` and the two
derived-functor comparison maps. -/
theorem derivedAssociatedModuleAdjunction_unit_app
    (M : HomotopyCategory (SheafOfModules.{u} S.ringCatSheaf) (ComplexShape.up ℤ)) :
    (derivedAssociatedModuleAdjunction.{w, w} B S hS).unit.app (DerivedCategory.Qh.obj M) ≫
        (derivedRestrictModule.{w, w} B S hS).map
          ((associatedModuleOfSheaf B S hS).mapDerivedCategoryFactorsh.hom.app M) =
      DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction
            (F := restrictModuleOfSheaf B S hS) (G := associatedModuleOfSheaf B S hS)
            (associatedModuleAdjunction B S hS) (ComplexShape.up ℤ)).unit.app M) ≫
        (derivedRestrictModuleUnit.{w, w} B S hS).app
          (((associatedModuleOfSheaf B S hS).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) :=
  Stacks.DerivedFunctor.derivedAdjunction_unit_app
    (F := restrictModuleOfSheaf B S hS) (G := associatedModuleOfSheaf B S hS)
    (associatedModuleAdjunction B S hS) (derivedRestrictModule.{w, w} B S hS)
    (derivedRestrictModuleUnit.{w, w} B S hS)
    (exists_quasiIso_isKInjective B S hS) M

/-- The counit of `Lε^* ⊣ Rε_*` is the one induced by the counit of `ε^* ⊣ ε_*` and the two
derived-functor comparison maps. -/
theorem derivedAssociatedModuleAdjunction_counit_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheaf B S hS)) (ComplexShape.up ℤ)) :
    (associatedModuleOfSheaf B S hS).mapDerivedCategory.map
          ((derivedRestrictModuleUnit.{w, w} B S hS).app K) ≫
        (derivedAssociatedModuleAdjunction.{w, w} B S hS).counit.app
          (DerivedCategory.Qh.obj K) =
      (associatedModuleOfSheaf B S hS).mapDerivedCategoryFactorsh.hom.app
          (((restrictModuleOfSheaf B S hS).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction
            (F := restrictModuleOfSheaf B S hS) (G := associatedModuleOfSheaf B S hS)
            (associatedModuleAdjunction B S hS) (ComplexShape.up ℤ)).counit.app K) :=
  Stacks.DerivedFunctor.derivedAdjunction_counit_app
    (F := restrictModuleOfSheaf B S hS) (G := associatedModuleOfSheaf B S hS)
    (associatedModuleAdjunction B S hS) (derivedRestrictModule.{w, w} B S hS)
    (derivedRestrictModuleUnit.{w, w} B S hS)
    (exists_quasiIso_isKInjective B S hS) K

end AlgebraicGeometry.SmallEtale

end

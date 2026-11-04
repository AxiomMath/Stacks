module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.DerivedGlobalSectionsAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsOnABigSite
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion

/-!
# Derived sections over an object of a site form an additive functor

`Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedAbelianSections`, the unbounded right
derived functor `RΓ(U, -)` of sections over an object `U` of a site that need not be small, is
defined as a total right derived functor, which comes with no additivity instance. This file
supplies it: sections over `U` are additive, the category of abelian sheaves is Grothendieck
abelian so every complex has a K-injective resolution
(`Stacks.Injectives.exists_kInjective_resolution_of_grothendieck`), and a right derived functor
of an additive functor computed by K-injectives is additive
(`Stacks.SmallDerivedCategory.additive_of_exists_quasiIso_isKInjective`). In particular
`RΓ(U, -)` preserves zero morphisms and sends a zero object to a zero object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u₁

namespace Stacks.Cohomology.DerivedLowerShriek.BigSite

variable {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C)

attribute [local instance] HasDerivedCategory.standard

/-- `RΓ(U, -)` on the unbounded derived category of abelian sheaves on a site is additive. -/
instance additive_derivedAbelianSections (U : C)
    [HasSheafify J AddCommGrpCat.{max u₁ v w}]
    [IsGrothendieckAbelian.{max u₁ v w} (Sheaf J AddCommGrpCat.{max u₁ v w})] :
    (derivedAbelianSections.{w} J U).Additive :=
  Stacks.SmallDerivedCategory.additive_of_exists_quasiIso_isKInjective
    ((abelianSections.{w} J U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (derivedAbelianSections.{w} J U)
    (((abelianSections.{w} J U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ)))
    Stacks.Injectives.exists_kInjective_resolution_of_grothendieck

end Stacks.Cohomology.DerivedLowerShriek.BigSite

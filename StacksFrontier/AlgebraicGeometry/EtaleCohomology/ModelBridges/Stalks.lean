module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionStalkCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionStalkCriterionUnconditional

/-!
# Stalks of étale sheaves of modules in the three models

A sheaf of `Λ`-modules on Mathlib's small étale site of `X` (`Stacks.EtaleCohomology.EtaleModules`)
has two stalks at a geometric point `t`: the stalk (Tag 040R) of its transport to the small étale
site of Tag 021B of a big étale site containing `X` (`AlgebraicGeometry.etaleStalk`), a `Λ`-module,
and the stalk of its underlying abelian sheaf on Mathlib's small étale site
(`AlgebraicGeometry.smallEtaleStalkAb`), an abelian group. This file identifies the underlying
abelian group of the first with the second.

The sheaves are taken with coefficients `ModuleCat.{u + 1} Λ` for a ring `Λ` in any universe
`r`: this is `EtaleModules.{u, r} Λ X` for `r = 0` and for `r = u + 1`, the two cases in use. The
abelian stalk functor `AlgebraicGeometry.smallEtaleStalkAb` is defined at `Ab.{u + 1}` only.

## Main definitions

* `Stacks.EtaleCohomology.etaleStalkForgetIsoSmallEtaleStalkAb`: the identification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type r) [Ring Λ] (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)

/-- **The `Λ`-module stalk of the transport of an étale sheaf of `Λ`-modules is the abelian stalk
of its underlying abelian sheaf.** Forgetting the `Λ`-structure commutes with colimits, and the
abelian stalks in the two models agree (`AlgebraicGeometry.etaleStalkIsoSmallEtaleStalkAb`). -/
def etaleStalkForgetIsoSmallEtaleStalkAb (t : GeometricPoint X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        (etaleStalk B X hX t
          ((SmallEtale.sheafEquiv B X hX (ModuleCat.{u + 1} Λ)).inverse.obj F).obj) ≅
      (smallEtaleStalkAb t.hom).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) :=
  preservesColimitIso (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) _ ≪≫
    etaleStalkIsoSmallEtaleStalkAb B hX t
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)

end Stacks.EtaleCohomology

end

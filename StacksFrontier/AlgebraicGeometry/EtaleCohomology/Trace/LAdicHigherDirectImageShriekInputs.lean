module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibleHomology

/-!
# Constructibility of the cohomology sheaves of `Rf_!`

This file states, as one proposition, the constructibility of the cohomology sheaves of `Rf_!`
of a constructible torsion sheaf of `Λ`-modules, for a Noetherian ring `Λ`
([Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0)).

## Main definitions

* `Stacks.EtaleCohomology.LowerShriekConstructibilityInput`: for `f` separated of finite type
  with Noetherian target and a compactification of `f`, every cohomology sheaf of `Rf_! F` of a
  constructible torsion sheaf `F` of `Λ`-modules is constructible.

## References

* [Stacks Project, Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **Constructibility of `Rf_!`** (Tag 0GL0): for `f : X ⟶ Y` separated of finite type with `Y`
Noetherian, a compactification `j` of `f`, a Noetherian ring `Λ` and a sheaf `F` of `Λ`-modules
on `X_étale` which is constructible and torsion, every cohomology sheaf of `Rf_! F` is
constructible. -/
def LowerShriekConstructibilityInput (B : BigEtaleSite.{u}) : Prop :=
  ∀ {X Y : B.Scheme} [IsNoetherian Y.obj] (f : X.obj ⟶ Y.obj) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (j : CompactificationOf (Over.mk f)) (Λ : Type)
    [CommRing Λ] [IsNoetherianRing Λ] (F : EtaleModules.{u, 0} Λ X.obj),
    IsBigSiteConstructibleEtaleModule B X Λ F → IsTorsionEtaleModule Λ X.obj F → ∀ n : ℤ,
      IsBigSiteConstructibleEtaleModule B Y Λ ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))

end Stacks.EtaleCohomology

module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackExists
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackBoundedAbove
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackKFlat

/-!
# K-flat complexes of modules on the small étale site of an algebraic space

The class of K-flat complexes of `𝒪_Y`-modules with flat terms, on which the derived pullback
`Lf^* = AlgebraicGeometry.Space.smallEtaleDerivedModulePullback f` of a morphism of algebraic
spaces is computed by degreewise pullback, and the three facts about it that are used to compute
`Lf^*` — every complex is resolved by one (Stacks 06YS), a bounded above complex of flat modules
is one (Stacks 06YQ), and degreewise pullback preserves the class (Stacks 0G7E) — are proved in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackKFlat`, which this file
imports. This file adds, as instances, the existence of `Lf^*` for morphisms out of, into and
between the algebraic spaces represented by objects of the big fppf site.

## Main results

In the namespace `AlgebraicGeometry.Space`, `Lf^*` exists for a represented source, target, or
both:

* `hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy_ofRepresentedSource`;
* `hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy_ofRepresentedTarget`;
* `hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy_ofRepresented`.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat hasResolutions_isKFlat)

namespace AlgebraicGeometry.Space

universe u

/- The standard model of the derived category: the derived functors this file uses (derived
pullback, pushforward, tensor product and internal Hom on ringed sites and topoi) are stated
on it, so the statements here must be too. -/
attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

attribute [local instance] Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize in
/-- `AlgebraicGeometry.Space.hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy` for a
morphism out of the algebraic space represented by an object of the big fppf site. Instance
search matches up to reducible unfolding, and through the abbreviation
`AlgebraicGeometry.Space.smallEtaleRingedTopos` the represented source unfolds to a term that the
general instance, stated for a variable source, does not match. -/
instance hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy_ofRepresentedSource
    {T' : BigFppfOver B S hS} {Y : AlgebraicSpaces B S hS}
    (k : (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS) ⟶ Y) :
    (smallEtaleModulePullbackOnHomotopy B S hS k).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS Y) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS _

/-- `AlgebraicGeometry.Space.hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy` for a
morphism into the algebraic space represented by an object of the big fppf site. -/
instance hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy_ofRepresentedTarget
    {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    (k : X ⟶ (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS)) :
    (smallEtaleModulePullbackOnHomotopy B S hS k).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS _

/-- `AlgebraicGeometry.Space.hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy` for a
morphism between algebraic spaces represented by objects of the big fppf site. -/
instance hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy_ofRepresented
    {T' T : BigFppfOver B S hS}
    (k : (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) :
    (smallEtaleModulePullbackOnHomotopy B S hS k).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) :=
  hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS _

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicAnySite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
import all StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective
public import StacksFrontier.Homology.CompositeCollapse

/-!
# The direct image of an injective module along a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, and let `𝓘` be an injective `𝒪_X`-module on the small étale site of `X`.  Then the direct
image `f_*𝓘` is totally acyclic (Stacks 072Z), and hence acyclic for the global sections of
`𝒪_Y`-modules (Stacks 0731, part (3)): `H^p(Y, f_*𝓘) = 0` for `p > 0`.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardToSheafIso`: the abelian sheaf underlying the direct
  image of a module is the abelian direct image, along the morphism of small étale topoi
  `AlgebraicGeometry.Space.smallToposMorphismTypeU`, of the underlying abelian sheaf.

## Main results

* `AlgebraicGeometry.Space.isTotallyAcyclic_modulePushforward_of_injective`: **Stacks 072Z** for
  the direct image of modules along a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.acyclic_globalSectionsFunctor_modulePushforward_of_injective`: the
  direct image of an injective module is acyclic for global sections on `Y`.

## Implementation notes

The small étale site of an algebraic space over a `Scheme.{u}` has its objects in `Type (u + 1)`
and its morphisms, structure sheaf and modules in `Type u`, so neither the ringed-topos form of
Stacks 072Z nor the small-site form of Stacks 0731 (3) applies to it.  Both are used here in the
forms proved for sites of any size:
`Stacks.Cohomology.isTotallyAcyclic_abelianPushforward_of_injective` and
`Stacks.Cohomology.isZero_rightDerived_globalSectionsFunctor_of_isTotallyAcyclic`.  The only
input specific to algebraic spaces is that the direct image of modules
`AlgebraicGeometry.Space.modulePushforward` has, on the nose, the direct image of sheaves of sets
along `AlgebraicGeometry.Space.smallToposMorphismTypeU` as its underlying sheaf of sets, which
`Stacks.Cohomology.abelianSheafNatIsoOfUnderlying` upgrades to an isomorphism of abelian sheaves.

The `Ext`-groups of abelian sheaves and of modules on the small étale site are taken at the
universe `u + 1` of the objects of the site, by `CategoryTheory.HasExt.standard`; the
homological instances that instance search does not find on these sites, at both the reduced
and the projection spelling of the topology, are the ones declared in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineChartCohomologyVanishing.lean`, made local instances
here.

## References

* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 0731](https://stacks.math.columbia.edu/tag/0731)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Topos.AbelianPushforward

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtale
  AlgebraicGeometry.Space.hasExt_sheaf_smallEtale
  AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtaleRingedSite
  AlgebraicGeometry.Space.hasExt_sheaf_smallEtaleRingedSite
  AlgebraicGeometry.Space.enoughInjectives_modules AlgebraicGeometry.Space.hasExt_modules

variable {X Y : AlgebraicSpaces B S hS}

/-- **The abelian sheaf underlying a direct image of modules is the abelian direct image.**  For
a morphism `f : X ⟶ Y` of algebraic spaces, forgetting the module structure of `f_*𝓜` gives the
direct image of the underlying abelian sheaf of `𝓜` along the morphism of small étale topoi
`AlgebraicGeometry.Space.smallToposMorphismTypeU`.  The two have the same underlying sheaf of
sets on the nose, and `Stacks.Cohomology.abelianSheafNatIsoOfUnderlying` lifts the identity of
the underlying sheaves of sets to the abelian sheaves. -/
def modulePushforwardToSheafIso (f : X ⟶ Y) :
    modulePushforward B S hS f ⋙ SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf _ ⋙ abelianPushforward (smallEtaleRingedSite B S hS X.1 X.2).J
        (smallToposMorphismTypeU B S hS f) := by
  have := modulePushforward_additive B S hS f
  have : HasZeroObject (Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u}) :=
    hasZeroObject_of_hasTerminal_object
  have : HasZeroObject (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :=
    hasZeroObject_of_hasTerminal_object
  have : (Sites.abelianInverseImage (smallToposMorphismTypeU B S hS f)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  have : (Sites.abelianInverseImage (smallToposMorphismTypeU B S hS f)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have h : (abelianPushforward (SmallEtale.topology B S hS X.1)
      (smallToposMorphismTypeU B S hS f)).Additive :=
    (abelianInverseImageAdjPushforward _ (smallToposMorphismTypeU B S hS f)).right_adjoint_additive
  have : (abelianPushforward (smallEtaleRingedSite B S hS X.1 X.2).J
      (K := (smallEtaleRingedSite B S hS Y.1 Y.2).J)
      (smallToposMorphismTypeU B S hS f)).Additive := h
  exact Stacks.Cohomology.abelianSheafNatIsoOfUnderlying
    (smallEtaleRingedSite B S hS Y.1 Y.2).J _ _ (Iso.refl _)

/-- **Stacks 072Z for algebraic spaces.**  For a morphism `f : X ⟶ Y` of algebraic spaces and an
injective `𝒪_X`-module `𝓘`, the abelian sheaf underlying `f_*𝓘` is totally acyclic: its
cohomology over every sheaf of sets on the small étale site of `Y` vanishes in positive degrees.

This is `Stacks.Cohomology.isTotallyAcyclic_abelianPushforward_of_injective` for the morphism of
small étale topoi of `f`, read through `AlgebraicGeometry.Space.modulePushforwardToSheafIso`. -/
theorem isTotallyAcyclic_modulePushforward_of_injective (f : X ⟶ Y)
    (Z : Modules.{u, u} B S hS X.1 X.2) [hZ : Injective Z] :
    Stacks.Cohomology.IsTotallyAcyclic (smallEtaleRingedSite B S hS Y.1 Y.2).J
      ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS f).obj Z)) := by
  intro K p hp
  refine subsingleton_ext_of_iso_right ((modulePushforwardToSheafIso B S hS f).app Z) p ?_
  exact Stacks.Cohomology.isTotallyAcyclic_abelianPushforward_of_injective
    (J := (smallEtaleRingedSite B S hS X.1 X.2).J) (K := (smallEtaleRingedSite B S hS Y.1 Y.2).J)
    (smallToposMorphismTypeU B S hS f) (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite
        B S hS X.1 X.2).O)
    Z K p hp

/-- **The direct image of an injective module is acyclic for global sections.**  For a morphism
`f : X ⟶ Y` of algebraic spaces and an injective `𝒪_X`-module `𝓘`, the higher cohomology
`H^p(Y, f_*𝓘)` vanishes for every `p > 0`: `f_*𝓘` is totally acyclic by
`AlgebraicGeometry.Space.isTotallyAcyclic_modulePushforward_of_injective` (Stacks 072Z), and a
totally acyclic module is acyclic for global sections by
`Stacks.Cohomology.isZero_rightDerived_globalSectionsFunctor_of_isTotallyAcyclic`
(Stacks 0731, part (3)). -/
theorem acyclic_globalSectionsFunctor_modulePushforward_of_injective (f : X ⟶ Y)
    (Z : Modules.{u, u} B S hS X.1 X.2) [Injective Z] :
    have := enoughInjectives_modules B S hS Y.1 Y.2
    Stacks.RightDerivedComp.acyclic (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1,
      u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
      ((modulePushforward B S hS f).obj Z) := by
  intro _ n hn
  exact Stacks.Cohomology.isZero_rightDerived_globalSectionsFunctor_of_isTotallyAcyclic
    (smallEtaleRingedSite B S hS Y.1 Y.2).J _ _
    (isTotallyAcyclic_modulePushforward_of_injective B S hS f Z) n hn

end AlgebraicGeometry.Space

end

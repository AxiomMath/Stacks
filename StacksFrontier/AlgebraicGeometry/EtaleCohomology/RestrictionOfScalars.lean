module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactModuleSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors

/-!
# Restriction of coefficients for sheaves of modules on the small étale site

Let `φ : Λ₁ → Λ₂` be a homomorphism of rings and let `X` be a scheme.  A sheaf of
`Λ₂`-modules on the small étale site of `X` becomes a sheaf of `Λ₁`-modules by letting `Λ₁`
act through `φ`, and nothing about the underlying sheaf changes.  This file records that
functor, `res`, and the three properties of it that every later use needs: it is additive, it
is faithful, and it is exact.  Exactness is what lets it be carried to the unbounded derived
categories, which is the shape in which the restriction functor of [Stacks, Tag 0GL6] occurs.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleRestrictScalarsUniv`: the functor `res`, postcomposition of a
  sheaf with `ModuleCat.restrictScalars φ`.
* `Stacks.EtaleCohomology.etaleModuleDerivedRestrictScalars`: the induced functor
  `D(X_étale, Λ₂) ⥤ D(X_étale, Λ₁)` on unbounded derived categories.

## Main results

* `Stacks.EtaleCohomology.etaleModuleRestrictScalarsUniv_additive` and
  `Stacks.EtaleCohomology.etaleModuleRestrictScalarsUniv_preservesFiniteColimits`: `res` is
  additive and preserves finite colimits.  That it preserves finite limits, and that it is
  faithful, are already instances.

## Implementation notes

The functor is `CategoryTheory.sheafCompose` of `ModuleCat.restrictScalars φ`; that this
preserves the sheaf condition is Mathlib's
`CategoryTheory.hasSheafComposeEssentiallySmallSite`, the small étale site being essentially
small in the coefficient universe.

The two halves of exactness come from the two adjunctions `ModuleCat.restrictScalars φ` sits in,
and they are genuinely different arguments.

* *Finite limits.* Restriction of scalars is right adjoint to extension of scalars
  (`ModuleCat.extendRestrictScalarsAdj`), hence so is `res` by
  `CategoryTheory.Sheaf.adjunction`; a right adjoint preserves limits.  This is the only place
  commutativity of the coefficient rings is used, Mathlib's extension of scalars being
  constructed for commutative rings.  The source states Tag 0GL6 for torsion rings, which are
  commutative under the conventions of the Stacks project, so nothing is lost.
* *Finite colimits.* This cannot go through the underlying presheaf, which does not compute
  colimits of sheaves.  Restriction of scalars is also *left* adjoint, to coextension of scalars
  (`ModuleCat.restrictCoextendScalarsAdj`), so it preserves sheafification
  (`CategoryTheory.Sheaf.preservesSheafification_of_adjunction`), and
  `CategoryTheory.Sheaf.preservesColimitsOfShape_sheafCompose` turns that into preservation of
  colimits of sheaves.  The instance has to be supplied by hand rather than found: searching for
  it exhausts the heartbeat budget of typeclass resolution.

Both coefficient rings are taken in one universe `r`.  The coefficient category of
`Stacks.EtaleCohomology.EtaleModules` is `ModuleCat.{max (u + 1) r} Λ` for a scheme universe
`u`, and `ModuleCat.restrictScalars` needs one module universe on both sides, so two rings in
different universes could not be compared without widening `EtaleModules` itself.

## References

* [Stacks Project, Tag 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

section Functor

variable {Λ₁ Λ₂ : Type r} [Ring Λ₁] [Ring Λ₂] (φ : Λ₁ →+* Λ₂)

/-- **Restriction of coefficients.**  A sheaf of `Λ₂`-modules on the small étale site of `X`,
read as a sheaf of `Λ₁`-modules by letting `Λ₁` act through `φ`.  The underlying sheaf is
unchanged. -/
abbrev etaleModuleRestrictScalarsUniv (X : Scheme.{u}) :
    EtaleModules.{u, r} Λ₂ X ⥤ EtaleModules.{u, r} Λ₁ X :=
  sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{max (u + 1) r} φ)

end Functor

section Exactness

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)

/-- Restriction of coefficients is additive: it preserves binary products, being a right
adjoint. -/
instance etaleModuleRestrictScalarsUniv_additive (X : Scheme.{u}) :
    (etaleModuleRestrictScalarsUniv.{u, r} φ X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restriction of coefficients preserves finite colimits.  Restriction of scalars is a left
adjoint, hence preserves sheafification, and postcomposition with a sheafification-preserving
functor commutes with colimits of sheaves. -/
instance etaleModuleRestrictScalarsUniv_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (etaleModuleRestrictScalarsUniv.{u, r} φ X) where
  preservesFiniteColimits _ _ _ :=
    haveI : X.smallEtaleTopology.PreservesSheafification
        (ModuleCat.restrictScalars.{max (u + 1) r} φ) :=
      Sheaf.preservesSheafification_of_adjunction _
        (ModuleCat.restrictCoextendScalarsAdj.{max (u + 1) r} φ)
    Sheaf.preservesColimitsOfShape_sheafCompose X.smallEtaleTopology
      (ModuleCat.restrictScalars.{max (u + 1) r} φ)

/-- **Restriction of coefficients on unbounded derived categories.**  The functor
`D(X_étale, Λ₂) ⥤ D(X_étale, Λ₁)` induced by the exact functor
`Stacks.EtaleCohomology.etaleModuleRestrictScalarsUniv`, applied degreewise. -/
abbrev etaleModuleDerivedRestrictScalars (X : Scheme.{u}) :
    DerivedCategory (EtaleModules.{u, r} Λ₂ X) ⥤
      DerivedCategory (EtaleModules.{u, r} Λ₁ X) :=
  (etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategory

end Exactness

end Stacks.EtaleCohomology

end

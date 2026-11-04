module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.KInjectivePredicateBridge
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
import StacksCore.Tactic.StacksAttribute

/-!
# `ε_*` carries K-injective complexes to K-injective complexes

Let `S` be a scheme and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites of
Stacks 070R/08H7.  Stacks 093Y says that the direct image along a *flat* morphism of ringed topoi
carries K-injective complexes to K-injective complexes, and its purely categorical content
(Stacks 070G, Lemma 13.31.9, i.e. Stacks 08BJ) is
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact`: a right adjoint of an exact functor
does so.

At `ε` the left adjoint is the associated-module functor `ε^*` of Stacks 03DU (4), which is
exact — right exactness because it is a left adjoint, left exactness being the second assertion
of Stacks 08H8, proved as
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModuleOfSheaf`.  So the hypothesis
is discharged and this file records the conclusion for `ε`.

## Implementation notes

The categorical lemma is used in the form
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact` (Stacks 08BJ), whose two abelian
categories live in independent universes.  This matters at `ε`: the `𝒪`-modules on the small
étale site have their morphisms in `Type (u + 1)`, the site's objects being there, while the
`𝒪_S`-modules on the small Zariski site have theirs in `Type u`.

## Main results

* `AlgebraicGeometry.SmallEtale.isKInjective_restrictModule`: **Stacks 093Y at `ε`** — degreewise
  `ε_*` carries a K-injective complex of `𝒪`-modules on `S_étale` to a K-injective complex of
  `𝒪_S`-modules.
* `AlgebraicGeometry.SmallEtale.computesSecond_restrictModule`: consequently `ε_*` satisfies
  the hypothesis `Stacks.Cohomology.LerayUnbounded.ComputesSecond` against any additive functor
  out of the `𝒪_S`-modules, which is what the composition law behind the clause of Stacks 0D6H
  on sections over an object consumes.

## References

* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
* [Stacks Project, Tag 070G](https://stacks.math.columbia.edu/tag/070G)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.SmallEtale

universe w v₁ u₁ u

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 093Y at `ε`.**  Degreewise `ε_*` carries a K-injective complex of `𝒪`-modules on the
small étale site of `S` to a K-injective complex of `𝒪_S`-modules.

`ε_*` is a right adjoint of `ε^*`, which is exact: right exact because it is a left adjoint, and
left exact by the second assertion of Stacks 08H8.  So this is the categorical lemma
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact` (Stacks 070G, Lemma 13.31.9) with
its hypothesis discharged.

No `@[stacks 093Y]` attribute: the tag is about an arbitrary flat morphism of ringed topoi, and
this is its instance at `ε`. -/
theorem isKInjective_restrictModule
    (I : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ) (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((restrictModuleOfSheaf B S hS).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have := hI
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact (restrictModuleOfSheaf B S hS)
    (associatedModuleOfSheaf B S hS) (associatedModuleAdjunction B S hS) I

variable [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B S hS))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]

omit [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B S hS))] in
/-- **`ε_*` computes the second functor of any composite.**  For every additive functor `G` out
of the `𝒪_S`-modules, the comparison `G J ⟶ RG J` is invertible at `J = ε_* I` for every
K-injective complex `I` of `𝒪`-modules on `S_étale`.

This is `Stacks.Cohomology.LerayUnbounded.ComputesSecond` for `ε_*` and `G`, discharged from
`isKInjective_restrictModule`: the comparison of a right derived functor is invertible on a
K-injective complex, and `ε_* I` is one.  It is the hypothesis under which the composition law
behind the clause of Stacks 0D6H on sections over an object gives
`RG ∘ Rε_* ≅ R(G ∘ ε_*)`. -/
theorem computesSecond_restrictModule {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{w} C] (G : SheafOfModules.{u} S.ringCatSheaf ⥤ C) [G.Additive] :
    Stacks.Cohomology.LerayUnbounded.ComputesSecond (restrictModuleOfSheaf B S hS) G :=
  Stacks.Cohomology.LerayUnbounded.computesSecond_of_isKInjective _ _
    (isKInjective_restrictModule B S hS)

end AlgebraicGeometry.SmallEtale

end

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksCore.Tactic.StacksAttribute

/-!
# Mathlib's module functors on a scheme are the ringed-space ones

Let `h : T ⟶ S` be a morphism of schemes.  Mathlib's pushforward and pullback of sheaves of
modules along `h`, `Scheme.Modules.pushforward h` and `Scheme.Modules.pullback h`, agree on the
nose with the ringed-space functors `RingedSpaceModuleAdjunction.modulePushforward` and
`modulePullback` of the underlying morphism of sheafed spaces.  This file records those two
identities, each of which holds by `rfl`, so that no transport between the two vocabularies is
needed where the projection formula is developed over an affine morphism.

## Main results

* `Stacks.ProjectionFormula.modulePushforward_eq_schemePushforward` and
  `Stacks.ProjectionFormula.modulePullback_eq_schemePullback`: the two identifications.

## Implementation notes

The projection-formula map `h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)` itself — its construction by
adjunction out of the comparison morphism of Stacks 01CD, its naturality in both module
arguments and the identity computing its composite with the tensorized unit of `h^* ⊣ h_*` — is
  `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap`
and the lemmas around it, in
`StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula`.  That module is deliberately
*not* imported here: the two identities below are about the pushforward and pullback functors
alone, and the affine route to Stacks 0FZE that consumes them,
`StacksFrontier.AlgebraicGeometry.ProjectionFormulaAffine.Basic`, imports both.  Importing it here
would make the namespace `Stacks.AlgebraicGeometry` visible to every consumer of this module,
and that shadows the root `AlgebraicGeometry` wherever an `open AlgebraicGeometry` sits inside a
`Stacks.*` namespace.

The affine models of pullback and pushforward, `pullbackTildeIso` and `pushforwardΓIso` of
Stacks 01I9, are stated for Mathlib's scheme-level functors; the two identities below are what
makes them apply to the ringed-space functors the projection-formula map is written in.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Stacks.ProjectionFormula

open RingedSpaceModuleAdjunction

universe u

/-- Mathlib's pushforward of modules along a morphism of schemes is the ringed-space
pushforward of `RingedSpaceModuleAdjunction`. -/
lemma modulePushforward_eq_schemePushforward {T S : Scheme.{u}} (h : T ⟶ S) :
    modulePushforward h.toLRSHom.toShHom = Scheme.Modules.pushforward h := rfl

/-- Mathlib's pullback of modules along a morphism of schemes is the ringed-space pullback of
`RingedSpaceModuleAdjunction`. -/
lemma modulePullback_eq_schemePullback {T S : Scheme.{u}} (h : T ⟶ S) :
    modulePullback h.toLRSHom.toShHom = Scheme.Modules.pullback h := rfl

end Stacks.ProjectionFormula

end

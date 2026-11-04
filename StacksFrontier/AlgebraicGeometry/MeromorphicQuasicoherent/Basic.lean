module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.GenericPointProduct.Decomposition

/-!
# The generic-point contributions are quasi-coherent

The sheaf of meromorphic functions on a scheme whose weakly associated points are generic points
of irreducible components, and whose quasi-compact opens have finitely many irreducible
components, is the product over the generic points of the pushed-forward structure sheaves of the
local schemes there. This file establishes quasi-coherence of the individual factors, which is the
first half of the quasi-coherence of the product.

## Main results

* `Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.isAffineHom_fromSpecStalk`: the canonical
  morphism `Spec 𝒪_{X, η} ⟶ X` at a *generic* point is an affine morphism.
* `Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.isQuasicoherent_genericPointStalkModule`: the
  contribution of a generic point to the sheaf of meromorphic functions is quasi-coherent.
The statement that a generic point's contribution restricts to zero on any open set missing
that point is **not** declared here. It is
`Stacks.AlgebraicGeometry.GenericPointCoproduct.isZero_restrict_genericPointStalkModule`, with the
module-valued form `AlgebraicGeometry.isZero_restrict_genericPointStalkModuleOf`.

The entry promised it under *this* namespace, where it does not exist.
The leaf name was findable — which is what made
the index look sound — so the lesson is to check the **fully-qualified** name: a wrong
namespace in an index is invisible to a grep for the leaf.

## Implementation notes

At a generic point the range of `Spec 𝒪_{X, η} ⟶ X` is the single point `η`, so the preimage of
*any* open set is the whole of `Spec 𝒪_{X, η}` or empty, by
`Stacks.AlgebraicGeometry.GenericPointGluing.fromSpecStalk_preimage_eq_top` and
`fromSpecStalk_preimage_eq_bot`. Both are affine, so the morphism is affine, and quasi-coherence of
the pushforward is Tag 02KG. This is specific to generic points: `Spec 𝒪_{X, x} ⟶ X` is not affine
in general, since the preimage of an affine open is the open subscheme of `Spec 𝒪_{X, x}` on which
the point `x` is carried into it.

## References

* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.MeromorphicQuasicoherent

open Stacks.AlgebraicGeometry.GenericPointDecomposition
open Stacks.AlgebraicGeometry.GenericPointGluing

/-- At a generic point `η` of a scheme `X`, the canonical morphism `Spec 𝒪_{X, η} ⟶ X` is affine:
the preimage of an open set is the whole of `Spec 𝒪_{X, η}` when it contains `η` and empty
otherwise, and both are affine. -/
theorem isAffineHom_fromSpecStalk {X : Scheme.{u}} {η : X} (hη : η ∈ genericPoints X) :
    IsAffineHom (X.fromSpecStalk η) := by
  refine ⟨fun U _ ↦ ?_⟩
  by_cases h : η ∈ U
  · rw [fromSpecStalk_preimage_eq_top hη h]
    exact isAffineOpen_top _
  · rw [fromSpecStalk_preimage_eq_bot hη h]
    exact isAffineOpen_bot _

/-- The contribution of a generic point to the sheaf of meromorphic functions is quasi-coherent:
it is the direct image of a quasi-coherent module along an affine morphism. -/
instance isQuasicoherent_genericPointStalkModule (X : Scheme.{u}) (η : genericPoints X) :
    (genericPointStalkModule X η).IsQuasicoherent :=
  letI : IsAffineHom (X.fromSpecStalk η.1) := isAffineHom_fromSpecStalk η.2
  AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom (X.fromSpecStalk η.1)
    (SheafOfModules.unit (Spec (X.presheaf.stalk η.1)).ringCatSheaf)

end Stacks.AlgebraicGeometry.MeromorphicQuasicoherent

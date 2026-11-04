module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Basic

/-!
# The Stein factorization of a proper morphism

Let `f : X ⟶ S` be a proper morphism of schemes.  Being proper, `f` is universally closed and
separated, so the factorization `X ⟶ f.normalization ⟶ S` of
`Stacks.SteinFactorization.toNormalization_fromNormalization` is available.  Here we record that
its first factor is again proper.

## Main results

* `Stacks.SteinFactorization.isProper_toNormalization`: the first map of the factorization of a
  proper morphism is proper.

## Implementation notes

The factorization itself and the integrality of its second factor are not restated for a proper
morphism: a proper morphism is quasi-compact and quasi-separated, so
`Stacks.SteinFactorization.toNormalization_fromNormalization` and
`Stacks.SteinFactorization.isIntegralHom_fromNormalization` already apply to it, and they carry
the corresponding clauses of [Stacks Project, Tag 03H2].

## References

* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.SteinFactorization

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]

/-- **Stacks Project, Tag 03H2.**  The first map of the factorization of a proper morphism is
proper.  It is universally closed because `f` is, separated and locally of finite type by
cancellation along the second map. -/
-- Clause (1) of the pin is a conjunction, "`f'` is proper **with geometrically connected
-- fibres**", and only this properness half is proved here.  The connectedness conjunct needs
-- `Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper` (Stacks 0G7X); the
-- pin's own proof of it is already in Lean, conditional on exactly that, as
-- `Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_etaleNeighborhood`.
@[stacks 03H2 "proper_first_map"]
public theorem isProper_toNormalization : IsProper f.toNormalization := by
  have : IsProper (f.toNormalization ≫ f.fromNormalization) := by
    rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
  have : IsSeparated f.toNormalization := .of_comp f.toNormalization f.fromNormalization
  have : LocallyOfFiniteType f.toNormalization :=
    locallyOfFiniteType_of_comp f.toNormalization f.fromNormalization
  exact ⟨⟩

end Stacks.SteinFactorization

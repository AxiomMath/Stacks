module

public import StacksFrontier.AlgebraicGeometry.LimitFPObjectDescent.Approximation
public import StacksCore.Tactic.StacksAttribute

/-!
# Absolute Noetherian approximation

[Stacks, Tag 01ZA] says that a quasi-compact and quasi-separated scheme `S` is the limit of an
inverse system `(S_i, f_{ii'})` indexed by a directed set, in which the transition morphisms are
affine and every `S_i` is of finite type over `ℤ`.

This is `AlgebraicGeometry.LimitFPObjectDescent.finiteTypeSchemeApproximation`, which produces a
`FiniteTypeSchemeApproximation S` for every `S` with `[CompactSpace S]` and
`[QuasiSeparatedSpace S]`. The fields of that structure are the conditions of the tag: the index
type carries a `Preorder` and is nonempty and directed; `stages` is a functor out of its opposite,
so an inverse system; `limit` says the given scheme is the limit of that system;
`transition_affine` is condition (1); and `stage_locallyOfFiniteType` together with
`stage_quasiCompact` is condition (2), finite type over the terminal scheme `Spec ℤ`.

## Main results

This file proves nothing; it registers
`AlgebraicGeometry.LimitFPObjectDescent.finiteTypeSchemeApproximation` against
[Stacks, Tag 01ZA].

## Implementation notes

The registration uses the `add_to_stacks` command rather than an `@[stacks]` attribute, since the
declaration is defined in another module; the command writes the same environment extension as
the attribute.

## References

* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

namespace AlgebraicGeometry.LimitFPObjectDescent

add_to_stacks 01ZA
  AlgebraicGeometry.LimitFPObjectDescent.finiteTypeSchemeApproximation

end AlgebraicGeometry.LimitFPObjectDescent

end

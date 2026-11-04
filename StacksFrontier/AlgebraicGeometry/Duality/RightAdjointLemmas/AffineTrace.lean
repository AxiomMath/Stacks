module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality.BaseChange

/-!
# The trace map of an affine morphism

Let `A → B` be a homomorphism of commutative rings, let `Y = Spec A` and `X = Spec B`, and let
`f : X ⟶ Y` be the induced morphism. The right adjoint of `Rf_*` sends an object `K` of
`D(A) = D_QCoh(𝒪_Y)` to `RHom_A(B, K)` in `D(B) = D_QCoh(𝒪_X)`, and the trace map
`Tr_{f, K} : RHom_A(B, K) ⟶ RHom_A(A, K) = K` is the map induced by the `A`-module map
`A ⟶ B`.

Both halves of that statement are already available in the algebraic form in which they are
proved: the trace is the counit of the derived restriction–Hom adjunction
`Dualizing.derivedHomAdjunction`, and `Dualizing.derivedHomAdjunction_counit_app` says that on
complexes this counit is induced by the evaluation counit of ordinary coextension of scalars,
that is by precomposition with `A ⟶ B`. This file records the Stacks tag on those two
declarations rather than restating them.

## Implementation notes

Naturality of the trace in `K` is carried by the counit being a natural transformation, so no
separate naturality statement is needed. The identification of the right adjoint of `Rf_*`
with `RHom_A(B, -)` itself is [Stacks, Tag 0A9F].

## References

* [Stacks Project, Tag 0B6L](https://stacks.math.columbia.edu/tag/0B6L)
* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
-/

add_to_stacks 0B6L "the trace map" Dualizing.derivedHomAdjunction
add_to_stacks 0B6L "induced by the ring map" Dualizing.derivedHomAdjunction_counit_app

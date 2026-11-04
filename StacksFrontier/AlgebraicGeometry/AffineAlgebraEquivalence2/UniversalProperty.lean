module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Faithful
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Full

/-!
# The universal property of the relative spectrum

Let `S` be a scheme and let `Y` be a scheme affine over `S`.  For an *arbitrary* scheme `X` over
`S` the canonical map on pushed-forward structure sheaves is a bijection
```
Hom_S(X, Y) ≃ Hom_{𝒪_S-alg}(Y.hom _* 𝒪_Y, X.hom _* 𝒪_X).
```
This is the universal property which makes `Y` the relative spectrum of the `𝒪_S`-algebra
`Y.hom _* 𝒪_Y`, and it is the form in which the anti-equivalence of Stacks Tag 01SA is used to
compare objects over `S` that are not themselves affine over `S`.

## Main definitions

* `Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom` is the bijection above.

## Main results

* `Stacks.AffineAlgebraEquivalence.overHomOfAlgebraHom_pushforwardAlgebraMap` is the half of the
  bijection that was not already available: gluing the local morphisms attached to the canonical
  map of a morphism over `S` recovers that morphism.
* `Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom_apply` and
  `Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom_symm_apply` identify the bijection and
  its inverse with `pushforwardAlgebraMap` and `overHomOfAlgebraHom`.

## Implementation notes

The two halves of the bijection are built from lemmas that are already available, and the point
of this file is that they hold under a hypothesis on the *target* alone.  The full
faithfulness of `X ↦ X.hom _* 𝒪_X` is stated as `Functor.Full` and `Functor.Faithful` instances
for the functor
`affinePushforwardAlgebraFunctor S` on the category of schemes affine over `S`, which makes it
look as though both schemes must be affine over `S`.  They need not: the underlying lemmas
`eq_of_pushforwardAlgebraMap_eq` and `pushforwardAlgebraMap_overHomOfAlgebraHom` assume only
`IsAffineHom Y.hom`, because the morphism `X ⟶ Y` is built by gluing the local morphisms
`localHom` over the affine opens `V` of `S`, and these are produced from the affine open
`Y.hom ⁻¹ᵁ V` of the target by `homOfAppLE`, the source entering only through its sections.
Recording the bijection separately keeps that generality visible.

No naturality lemmas are stated here: under `overHomEquivAlgebraHom_apply` the naturality of the
bijection in both variables is exactly `pushforwardAlgebraMap_comp`.

The two `Equiv` projections are proved by `Equiv.coe_fn_mk` and `Equiv.coe_fn_symm_mk` rather
than by `rfl`.  Deciding them by `rfl` sends the kernel through `pushforwardAlgebra`, whose
`TopCat.Sheaf.pushforward` is a left Kan extension, and the `getColimitCocone` behind it is not
exposed; the elaborator spends its whole heartbeat budget in `whnf` and then reports a
non-definitional equality.  Naming the projection lemma avoids the unfolding entirely, so no
raised heartbeat limit is needed.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AffineAlgebraEquivalence

variable {S : Scheme.{u}}

/-- Gluing the local morphisms attached to the canonical map on pushed-forward structure sheaves
of a morphism over `S` recovers that morphism, when its target is affine over `S`. -/
public theorem overHomOfAlgebraHom_pushforwardAlgebraMap {X Y : Over S} [IsAffineHom Y.hom]
    (u : X ⟶ Y) : overHomOfAlgebraHom (pushforwardAlgebraMap u) = u :=
  eq_of_pushforwardAlgebraMap_eq
    (pushforwardAlgebraMap_overHomOfAlgebraHom (pushforwardAlgebraMap u))

/-- **The universal property of the relative spectrum.**  For `Y` affine over `S` and `X` an
arbitrary scheme over `S`, a morphism `X ⟶ Y` of schemes over `S` is the same thing as a
morphism `Y.hom _* 𝒪_Y ⟶ X.hom _* 𝒪_X` of sheaves of `𝒪_S`-algebras. -/
public noncomputable def overHomEquivAlgebraHom (X Y : Over S) [IsAffineHom Y.hom] :
    (X ⟶ Y) ≃ (pushforwardAlgebra Y.hom ⟶ pushforwardAlgebra X.hom) where
  toFun u := pushforwardAlgebraMap u
  invFun ψ := overHomOfAlgebraHom ψ
  left_inv u := overHomOfAlgebraHom_pushforwardAlgebraMap u
  right_inv ψ := pushforwardAlgebraMap_overHomOfAlgebraHom ψ

/-- The bijection of `overHomEquivAlgebraHom` is the canonical map on pushed-forward structure
sheaves. -/
@[simp]
public theorem overHomEquivAlgebraHom_apply {X Y : Over S} [IsAffineHom Y.hom] (u : X ⟶ Y) :
    overHomEquivAlgebraHom X Y u = pushforwardAlgebraMap u :=
  congrFun (Equiv.coe_fn_mk _ _ _ _) u

/-- The inverse of the bijection of `overHomEquivAlgebraHom` is the glued morphism
`overHomOfAlgebraHom`. -/
@[simp]
public theorem overHomEquivAlgebraHom_symm_apply {X Y : Over S} [IsAffineHom Y.hom]
    (ψ : pushforwardAlgebra Y.hom ⟶ pushforwardAlgebra X.hom) :
    (overHomEquivAlgebraHom X Y).symm ψ = overHomOfAlgebraHom ψ :=
  congrFun (Equiv.coe_fn_symm_mk _ _ _ _) ψ

end Stacks.AffineAlgebraEquivalence

end

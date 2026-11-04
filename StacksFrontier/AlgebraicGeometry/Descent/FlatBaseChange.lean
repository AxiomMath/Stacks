module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The inverse-image square of a commutative square of schemes

Let
```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```
be a commutative square of schemes.  For a module `M` on `X` there is a canonical comparison
morphism
`g^* f_* M ⟶ f'_* (g')^* M`,
natural in `M`.  That morphism is
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, the unique base-change
transformation of this repository.  It admits two descriptions: as the mate, in the sense of
`CategoryTheory.mateEquiv`, of the comparison isomorphism `f'_* g_* ≅ g'_* f_*` of pushforward
functors along the *vertical* adjunctions, which is the definition; and as the mate of the
comparison isomorphism `(f')^* g^* ≅ (g')^* f^*` of pullback functors along the *horizontal*
adjunctions `f^* ⊣ f_*` and `(f')^* ⊣ (f')_*`.  Equivalently, in the form in which the second
description is usually recognised, it is the adjoint transpose of
`(f')^* g^* f_* M ≅ (g')^* f^* f_* M ⟶ (g')^* M`,
where the second map is `(g')^*` applied to the counit of `f^* ⊣ f_*`.

This file supplies the input of the second description: the comparison isomorphism of pullback
functors and the `2`-square it forms.  The description itself, and the identities that
characterise the base-change morphism through it, are in
`StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeComparison`.

The content of flat base change, [Stacks, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH),
is that the base-change morphism is an isomorphism when the square is cartesian, `g` is flat,
`f` is quasi-compact and quasi-separated and `M` is quasi-coherent.  That invertibility
statement is not proved here.

## Main definitions

* `Stacks.Modules.pullbackSquareIso` is the comparison isomorphism
  `g^* ⋙ (f')^* ≅ f^* ⋙ (g')^*` of pullback functors attached to a commutative square.
* `Stacks.Modules.pullbackTwoSquare` is the `2`-square it forms, which is the datum
  `CategoryTheory.mateEquiv` transposes into the base-change morphism.

## Main results

* `Stacks.Modules.isIso_pullbackTwoSquare_natTrans`: the `2`-square is invertible, with no
  hypothesis on the square.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.pullbackCongr` is `CategoryTheory.eqToIso`, so
`pullbackSquareIso` is a composite of `AlgebraicGeometry.Scheme.Modules.pullbackComp` with an
`eqToIso`; in particular it is an isomorphism by construction and no invertibility hypothesis is
needed for it.  The passage from that isomorphism to its mate is where the hypotheses of
Tag 02KH would be needed, and that mate is the base-change morphism, so nothing in this file
asserts invertibility of anything but the `2`-square itself.

Everything stays inside the categories `X.Modules`, so none of the declarations here meet the
mismatch between `AlgebraicGeometry.Scheme.Modules.Hom` and `SheafOfModules.Hom`.

## References

* [Stacks Project, Tag 02KF](https://stacks.math.columbia.edu/tag/02KF)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Functor

universe u

namespace Stacks.Modules

variable {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)

/-- For a commutative square `g' ≫ f = f' ≫ g` of schemes, the canonical comparison isomorphism
`g^* ⋙ (f')^* ≅ f^* ⋙ (g')^*` between the two ways of pulling a module on `S` back to `X'`.
It is the composite of the two instances of
`AlgebraicGeometry.Scheme.Modules.pullbackComp` with the isomorphism of pullback functors
induced by the equality of the two composites. -/
def pullbackSquareIso (w : g' ≫ f = f' ≫ g) :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f' ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g' :=
  Scheme.Modules.pullbackComp f' g ≪≫ Scheme.Modules.pullbackCongr w.symm ≪≫
    (Scheme.Modules.pullbackComp g' f).symm

/-- The `2`-square of `pullbackSquareIso`, which is the datum `CategoryTheory.mateEquiv`
transposes into the base-change morphism. -/
def pullbackTwoSquare (w : g' ≫ f = f' ≫ g) :
    TwoSquare (Scheme.Modules.pullback g) (Scheme.Modules.pullback f)
      (Scheme.Modules.pullback f') (Scheme.Modules.pullback g') :=
  .mk _ _ _ _ (pullbackSquareIso f f' g g' w).hom

/-- The `2`-square of a commutative square of schemes is an isomorphism, being the forward
direction of `pullbackSquareIso`. -/
instance isIso_pullbackTwoSquare_natTrans (w : g' ≫ f = f' ≫ g) :
    IsIso (pullbackTwoSquare f f' g g' w).natTrans :=
  inferInstanceAs (IsIso (pullbackSquareIso f f' g g' w).hom)

end Stacks.Modules

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order

/-!
# Universal first-order thickenings of algebraic spaces

Let `Z ⟶ X` be a morphism of algebraic spaces over a scheme `S`, presented as a closed subspace
`Z` of an algebraic space `Z'` together with a morphism `p : Z' ⟶ X`. The first-order thickening
`Z ⊂ Z'` is *universal* when every first-order thickening `T ⊂ T'` over `X` mapping to `Z`
extends uniquely over `X`: for every `a : T ⟶ Z` and every `b : T' ⟶ X` making the solid diagram

```
    Z  ←--a--  T
   ↙               ↘
 Z'                  T'
   ↘               ↙
          X
```

commute, there is exactly one `c : T' ⟶ Z'` restricting to `a` on `T` and lying over `X`.

A universal first-order thickening need not exist; when it does, the unique-extension property
makes it unique up to a unique isomorphism, and `Z ⟶ X` is then formally unramified.

## Main definitions

* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening`: **Stacks 0602**, the universal
  lifting property of a first-order thickening of algebraic spaces over a base algebraic space.

## Implementation notes

As for the other thickening conditions of this directory, the smaller space of a thickening is
given as a `CategoryTheory.Subfunctor` of its ambient algebraic space, so that the inclusion is
the canonical one; the first-order condition is
`AlgebraicGeometry.Space.IsFirstOrderThickening`, which already contains the assertion that the
subfunctor is a closed subspace, hence itself an algebraic space. The morphism `Z ⟶ X` of the
source is not a separate datum: it is the composite `Z.ι ≫ p.hom` of the inclusion with the
structure morphism of the ambient space, which is why only `p` appears.

The two equations of the unique-extension clause say that the dotted arrow restricts to the
given `a : T ⟶ Z` and that it lies over `X`; together with the hypothesis
`T.ι ≫ b = a ≫ Z.ι ≫ p.hom`, which is commutativity of the solid diagram, they say that
`(a, c)` is a morphism of thickenings over `X`. Uniqueness is `ExistsUnique`, so no choice of
extension is made.

## References

* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Space

universe u

/-- **Stacks 0602.** A first-order thickening `Z ⊂ Z'` of algebraic spaces over `S`, equipped
with a morphism `p : Z' ⟶ X`, is a *universal first-order thickening* of `Z` over `X` when
every compatible solid diagram built from a first-order thickening `T ⊂ T'` over `X` admits a
unique morphism `T' ⟶ Z'` restricting to the given `T ⟶ Z` and lying over `X`. -/
@[stacks 0602]
structure IsUniversalFirstOrderThickening (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Z' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.1)
    (p : Z' ⟶ X) : Prop where
  /-- The given inclusion is a first-order thickening. -/
  firstOrder : IsFirstOrderThickening B S hS Z' Z
  /-- Every compatible solid diagram has a unique dotted arrow. -/
  existsUnique_lift : ∀ {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.1),
      IsFirstOrderThickening B S hS T' T →
      ∀ (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1),
        T.ι ≫ b = a ≫ Z.ι ≫ p.hom →
        ∃! c : T'.1 ⟶ Z'.1, T.ι ≫ c = a ≫ Z.ι ∧ c ≫ p.hom = b

end AlgebraicGeometry.Space

end

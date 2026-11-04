module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationsOverSpace

/-!
# Invariant morphisms of algebraic spaces

Let `B` be an algebraic space over a base scheme `S` of a big fppf site. A *pre-relation*
from `R` to `U` over `B` is a morphism of algebraic spaces over `B` to the product
`U ×_B U`; its two projections are its *target* and *source* maps. A morphism out of `U`
is *invariant* under such a pre-relation when it takes the same value at the target and
the source of every arrow.

When instead `U` carries an action of a group algebraic space `G`, invariance says that
acting does not change the value of the morphism. That condition is stated in the slice
`Over B.obj` of presheaves rather than in the category of algebraic spaces, so that
Mathlib's group-object and module-object API applies to it directly.

## Main definitions

* `AlgebraicGeometry.Space.flippedRelation`: the map `r ↦ (s(r), t(r))` to `U ×_B U`
  attached to a pre-relation.
* `AlgebraicGeometry.Space.composedRelation`: the map `(r, r') ↦ (t(r), s(r'))` to `U ×_B U`
  on composable pairs of arrows of a pre-relation.
* `AlgebraicGeometry.Space.IsInvariant`: invariance of a morphism under a pre-relation.
* `AlgebraicGeometry.Space.IsGroupInvariant`: invariance of a morphism under the action of a
  group algebraic space.

## Implementation notes

Algebraic spaces over `B` are objects of `CategoryTheory.Over B`, whose categorical
product is the fibre product over `B`; so a pre-relation, `AlgebraicGeometry.Space.PreRelation`,
is a morphism to a categorical product. The third natural map to `U ×_B U`, the diagonal, is
Mathlib's `CategoryTheory.Limits.diag`.

`IsInvariant` is stated over an arbitrary base object of an arbitrary category whose slice has
binary products, so that it applies both in the slice of `AlgebraicGeometry.AlgebraicSpaces`
over an algebraic space and in the slice of presheaves over a presheaf. Its codomain is an
arbitrary object of the ambient category, not necessarily one over the base.

`Stacks.Groupoids.PreRelation` is a different declaration: the scheme-level pre-relation,
taken in `Over S` for a scheme `S`.

## References

* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 048E](https://stacks.math.columbia.edu/tag/048E)
* [Stacks Project, Tag 048S](https://stacks.math.columbia.edu/tag/048S)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

variable {site : BigFppfSite.{u}} {S : Scheme.{u}}
  {hS : site.Contains S} {B : AlgebraicSpaces site S hS}

/-! ### The three maps to `U ×_B U` attached to a pre-relation (Stacks 048S) -/

-- The diagonal map `U ⟶ U ×_B U` is Mathlib's binary-product diagonal.
add_to_stacks 048S "diagonal map" CategoryTheory.Limits.diag
add_to_sga "4 IV 5.11.1" CategoryTheory.Limits.diag
add_to_ega "I 10.15.1" CategoryTheory.Limits.diag
add_to_ega "I 5.3.1" CategoryTheory.Limits.diag
add_to_ega "IV 17.13.9" "binary diagonal" CategoryTheory.Limits.diag

/-- The *flipped* arrow of a pre-relation, `r ↦ (s(r), t(r))`: the map to `U ×_B U` that
reverses each arrow of `j`. -/
@[stacks 048S "flip map"]
noncomputable def flippedRelation {R U : Over B} (j : PreRelation R U) : R ⟶ U ⨯ U :=
  prod.lift j.source j.target

/-- The endpoint map on composable pairs, `(r, r') ↦ (t(r), s(r'))`: the map to `U ×_B U`
recording the outer endpoints of a pair of arrows of `j` that compose. -/
@[stacks 048S "composable-pair map"]
noncomputable def composedRelation {R U : Over B} (j : PreRelation R U) :
    pullback j.source j.target ⟶ U ⨯ U :=
  prod.lift (pullback.fst _ _ ≫ j.target) (pullback.snd _ _ ≫ j.source)

/-- A morphism `φ` out of `U` is *invariant* under a pre-relation `j : R ⟶ U ×_Z U` when it
identifies the target and the source of every arrow of `j`. -/
@[stacks 048E "R-invariant"]
noncomputable abbrev IsInvariant {C : Type*} [Category C] {Z : C}
    [HasBinaryProducts (Over Z)] {R U : Over Z} {X : C}
    (j : PreRelation R U) (φ : U.left ⟶ X) : Prop :=
  j.target.left ≫ φ = j.source.left ≫ φ

/-- A morphism `φ` out of an object `U` carrying an action of a group algebraic space `G` is
*invariant* when acting does not change its value. -/
@[stacks 048E "G-invariant", sga "3 IV 3.2.1" "special case"]
noncomputable abbrev IsGroupInvariant
    (G : Over B.obj) {U X : Over B.obj} [GrpObj G] [ModObj G U]
    (φ : U ⟶ X) : Prop :=
  γ[G, U] ≫ φ = snd G U ≫ φ

end AlgebraicGeometry.Space

end

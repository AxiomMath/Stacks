module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.JointlyFaithful

/-!
# Precomposing a 2-commutative square, with prescribed legs (Stacks 003O)

Let `P` be a 2-commutative square over a cospan `(f, g)` in a bicategory (**Stacks 003O**) and let
`p : t ⟶ P.pt` be a 1-morphism into its apex. `CategoryTheory.Bicategory.TwoCommSq.precompose`
reindexes `P` along `p`, giving the square with legs `p ≫ P.fst` and `p ≫ P.snd`. In practice the
legs one wants are 1-morphisms `u` and `v` which are only 2-isomorphic to those composites — for
instance a relative diagonal of a composite and the composite of two relative diagonals. This file
records the square with legs `u` and `v` and the filler of `P.precompose p` transported along the
two 2-isomorphisms, together with the pre-morphism of squares to `P` it carries.

## Main definitions

* `CategoryTheory.Bicategory.TwoCommSq.precomposeLegs`: the square with apex `t`, legs `u`, `v`.
* `CategoryTheory.Bicategory.TwoCommSq.PreHom.ofPrecomposeLegs`: the pre-morphism of squares
  `P.precomposeLegs p u v eu ev ⟶ P` on `p`, with comparison 2-cells `eu` and `ev`.

## Implementation notes

`TwoCommSq.precomposeLegs` is marked `@[implicit_reducible]`, as `TwoCommSq.precompose` is and for
the same reason (see `StacksFrontier.CategoryTheory.TwoFibreProduct.JointlyFaithful`): the
compatibility square of a pre-morphism out of it is typed through its apex and legs.

The pre-morphism's compatibility square is a formal consequence of the definition of the filler,
which is why that filler is the one recorded: a consumer whose square has, up to definitional
unfolding, this filler gets the pre-morphism with no 2-cell computation of its own.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- **A 2-commutative square precomposed with a 1-morphism into its apex, with prescribed legs.**
For a 2-commutative square `P` over `(f, g)` (**Stacks 003O**), `p : t ⟶ P.pt`, and 1-morphisms
`u : t ⟶ x`, `v : t ⟶ y` with 2-isomorphisms `eu : u ≅ p ≫ P.fst` and `ev : v ≅ p ≫ P.snd`, the
square with apex `t`, legs `u` and `v`, and filler that of `P.precompose p` read through `eu` and
`ev`. -/
@[implicit_reducible]
def TwoCommSq.precomposeLegs (P : TwoCommSq f g) {t : B} (p : t ⟶ P.pt) (u : t ⟶ x) (v : t ⟶ y)
    (eu : u ≅ p ≫ P.fst) (ev : v ≅ p ≫ P.snd) : TwoCommSq f g where
  pt := t
  fst := u
  snd := v
  iso := whiskerRightIso eu f ≪≫ (P.precompose p).iso ≪≫ (whiskerRightIso ev g).symm

/-- The filler of `CategoryTheory.Bicategory.TwoCommSq.precomposeLegs`, as a 2-cell. -/
@[simp]
theorem TwoCommSq.precomposeLegs_iso_hom (P : TwoCommSq f g) {t : B} (p : t ⟶ P.pt)
    (u : t ⟶ x) (v : t ⟶ y) (eu : u ≅ p ≫ P.fst) (ev : v ≅ p ≫ P.snd) :
    (P.precomposeLegs p u v eu ev).iso.hom =
      eu.hom ▷ f ≫ ((α_ p P.fst f).hom ≫ p ◁ P.iso.hom ≫ (α_ p P.snd g).inv) ≫ ev.inv ▷ g :=
  rfl

/-- **The pre-morphism of squares out of a precomposed square with prescribed legs.** The
1-morphism `p` is a pre-morphism of 2-commutative squares `P.precomposeLegs p u v eu ev ⟶ P`
(**Stacks 003O**), with comparison 2-cells `eu` and `ev`. -/
def TwoCommSq.PreHom.ofPrecomposeLegs (P : TwoCommSq f g) {t : B} (p : t ⟶ P.pt)
    (u : t ⟶ x) (v : t ⟶ y) (eu : u ≅ p ≫ P.fst) (ev : v ≅ p ≫ P.snd) :
    TwoCommSq.PreHom (P.precomposeLegs p u v eu ev) P where
  hom := p
  isoFst := eu
  isoSnd := ev
  compat := by simp

end CategoryTheory.Bicategory

end

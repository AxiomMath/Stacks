module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp

/-!
# The identity morphism of a ringed topos

A morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` is a morphism of the
underlying topoi together with `f♯ : O_D ⟶ f_*O_C`. Its composition is
`AlgebraicGeometry.RingedToposHom.comp`; this file supplies the identity for that composition.

The underlying morphism of topoi is the identity: both the direct and the inverse image are
`𝟭`, adjoint by `CategoryTheory.Adjunction.id`. The structure map is *not* the identity of
`O_X`, because the direct image of sheaves of commutative rings along the identity morphism of
topoi is `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctor X.J (𝟭 _)`, which
transports the ring operations along `𝟭` and is therefore isomorphic, but not equal, to `𝟭`.
The structure map is the inverse of that comparison, which is
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorId`; on underlying sheaves of sets it
is the identity, which is
`AlgebraicGeometry.RingedToposHom.forgetRing_map_id_fSharp` below.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.id`: the identity morphism of a ringed topos.

## Main results

* `AlgebraicGeometry.RingedToposHom.id_toToposHom_pushforward` and `.id_toToposHom_inverseImage`:
  its underlying morphism of topoi has `𝟭` for both images.
* `AlgebraicGeometry.RingedToposHom.forgetRing_map_id_fSharp`: its structure map is the
  identity on underlying sheaves of sets.

## Implementation notes

Only the comparison of the direct image along `𝟭` with `𝟭` is needed, not a full identity law
for `AlgebraicGeometry.RingedToposHom.comp`: `comp` is not the composition of a category
instance on ringed topoi — its two arguments may live in different universes — so there is no
`id_comp`/`comp_id` pair to prove, and the consumers of the identity morphism use it as the
reduction map of a thickening of a ringed topos by itself.

`forgetRing_map_id_fSharp` is stated in the spelling its consumers want — the structure map
read through `AlgebraicGeometry.RingedTopos.forgetRing`, as in
`AlgebraicGeometry.RingedToposHom.comp_fSharp_forget` — so that the two ways of writing the
identity on underlying sheaves of sets never have to be identified inside a proof.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback (pullbackCommRingSheafFunctorId)

universe v u w

namespace AlgebraicGeometry

namespace RingedToposHom

variable (X : RingedTopos.{v, u, w})
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The identity morphism of a ringed topos: the identity morphism of the underlying topos,
with the inverse of the comparison of the direct image along it with the identity functor as
structure map. -/
noncomputable def id : RingedToposHom X X where
  toToposHom :=
    { pushforward := 𝟭 X.Topos
      inverseImage := 𝟭 X.Topos
      adj := Adjunction.id
      preservesFiniteLimits := inferInstance }
  fSharp := (pullbackCommRingSheafFunctorId X.J).inv.app X.O

/-- The direct image of the identity morphism of a ringed topos is the identity functor. -/
@[simp]
theorem id_toToposHom_pushforward : (id X).toToposHom.pushforward = 𝟭 X.Topos := rfl

/-- The inverse image of the identity morphism of a ringed topos is the identity functor. -/
@[simp]
theorem id_toToposHom_inverseImage : (id X).toToposHom.inverseImage = 𝟭 X.Topos := rfl

/-- The structure map of the identity morphism of a ringed topos is the identity on underlying
sheaves of sets. -/
theorem forgetRing_map_id_fSharp [X.J.HasSheafCompose (forget CommRingCat.{w})] :
    X.forgetRing.map (id X).fSharp = 𝟙 (X.forgetRing.obj X.O) :=
  rfl

end RingedToposHom

end AlgebraicGeometry

end

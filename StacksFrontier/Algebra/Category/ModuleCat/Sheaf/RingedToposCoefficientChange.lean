module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomOfRestriction
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback

/-!
# Change of coefficient rings for a ringed topos on a fixed site

Fix a site `(C, J)`. A map `α : O ⟶ O'` of sheaves of commutative rings on it makes every
`O'`-module an `O`-module by restriction of scalars, and that restriction is the module
pullback of a morphism of ringed topoi `(Sh(J), O') ⟶ (Sh(J), O)` whose underlying geometric
morphism is the identity of `Sh(J)`. This file builds that morphism.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.coefficientMorphism`: the morphism of ringed topoi
  `(Sh(J), O') ⟶ (Sh(J), O)` attached to a map `O ⟶ O'` of structure sheaves.

## Main results

* `AlgebraicGeometry.RingedToposHom.coefficientMorphism_toToposHom`: its underlying geometric
  morphism is the identity.
* `AlgebraicGeometry.RingedToposHom.coefficientMorphism_fSharpInverseImage`: its structure map
  in inverse-image form is the given map `α`, read through the identification of the inverse
  image along the identity with the identity.

## Implementation notes

The direction is the geometric one: `O ⟶ O'` is a map *of* coefficient sheaves, so the induced
morphism of ringed topoi goes `(Sh(J), O') ⟶ (Sh(J), O)`, exactly as `Spec B' → Spec B` for a
ring map `B → B'`. The structure map of a morphism of ringed topoi is recorded in direct-image
form `f♯ : O_Y ⟶ f_*O_X`, so the content is supplied in inverse-image form and transported by
the adjunction of Stacks 00YV, which is what
`AlgebraicGeometry.RingedToposHom.ofInverseImageMap` does.

The identity geometric morphism does not make the construction trivial: the inverse image of a
sheaf of *commutative rings* along the identity functor of `Sh(J)` is isomorphic but not equal
to that sheaf, because the ring operations are transported through the functor. The comparison
is `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorId`, and it is the only thing this
construction adds to `α`.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O O' : Sheaf J CommRingCat.{w}}

/-- **Change of coefficient rings on a fixed site.** A map `α : O ⟶ O'` of sheaves of
commutative rings on `(C, J)` induces a morphism of ringed topoi `(Sh(J), O') ⟶ (Sh(J), O)`
whose underlying geometric morphism is the identity of `Sh(J)` and whose structure map is
`α`. -/
noncomputable def coefficientMorphism (α : O ⟶ O') :
    RingedToposHom (X := (⟨C, J, O'⟩ : RingedTopos.{v, u, w}))
      (Y := (⟨C, J, O⟩ : RingedTopos.{v, u, w})) :=
  ofInverseImageMap (MorphismOfTopoi.id (Sheaf J (Type w)))
    ((pullbackCommRingSheafFunctorId J).hom.app O ≫ α)

/-- The geometric morphism underlying a change of coefficient rings is the identity. -/
@[simp]
lemma coefficientMorphism_toToposHom (α : O ⟶ O') :
    (coefficientMorphism J α).toToposHom = MorphismOfTopoi.id (Sheaf J (Type w)) :=
  rfl

/-- The structure map of a change of coefficient rings is the given map of coefficient sheaves,
read through the identification of the inverse image along the identity with the identity. -/
lemma coefficientMorphism_fSharpInverseImage (α : O ⟶ O') :
    (coefficientMorphism J α).fSharpInverseImage =
      (pullbackCommRingSheafFunctorId J).hom.app O ≫ α :=
  ofInverseImageMap_fSharpInverseImage _ _

end AlgebraicGeometry.RingedToposHom

end

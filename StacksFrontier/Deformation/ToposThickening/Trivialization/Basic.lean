module

public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp
import StacksCore.Tactic.StacksAttribute

/-!
# Trivial first order thickenings of ringed topoi

A first order thickening of ringed topoi is *trivial* when its inclusion admits a retraction,
and a *trivialization* is a choice of such a retraction. Both notions make sense for an
arbitrary morphism of ringed topoi; the first order condition belongs to the thickening, not to
the notion of a retraction, so they are defined here at that generality.

## Main definitions

* `Deformation.ToposThickening.Trivialization`: a morphism of ringed topoi in the reverse
  direction whose composite with the given one is the identity, up to an invertible
  2-morphism.
* `Deformation.ToposThickening.IsTrivial`: the assertion that a trivialization exists.

## Main results

* `Deformation.ToposThickening.Trivialization.ext`: trivializations with the same retraction
  are equal.

## Implementation notes

Equality of morphisms of ringed topoi is expressed by an invertible natural transformation of
their direct-image functors, compatible with the structure-sheaf map. That is the appropriate
identity equation because the direct-image functor of a composite need not be strictly equal to
the identity functor: `AlgebraicGeometry.RingedToposHom.comp` composes the underlying
direct images, and `f_* ⋙ g_*` is not `𝟭` on the nose even when `f` and `g` are inverse
equivalences.

The compatibility with the structure map is stated on underlying sheaves of sets, through
`AlgebraicGeometry.RingedTopos.forgetRing`, because that is the form in which the composite
structure map is computed (`AlgebraicGeometry.RingedToposHom.comp_fSharp_forget`) and the form
the consumers of this definition use.

The isomorphism is a proposition-valued witness rather than additional data of the
trivialization, so equality of trivializations is determined by equality of their retractions;
the extensionality lemma lets clients use `ext` without unpacking the witness.

## References

* [Stacks Project, Tag 08MG](https://stacks.math.columbia.edu/tag/08MG)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)

universe v u w v' u' w'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- A retraction of a morphism of ringed topoi: a morphism in the reverse direction whose
composite direct-image functor is identified with the identity, compatibly with the
structure-sheaf map. -/
@[stacks 08MG "trivial_first_order_thickening_and_trivialization"]
structure Trivialization (i : RingedToposHom X Y) where
  /-- The morphism in the reverse direction. -/
  retraction : RingedToposHom Y X
  /-- The composite is the identity morphism of ringed topoi. -/
  comp_id : ∃ α : (retraction.comp i).toToposHom.pushforward ≅ 𝟭 X.Topos,
    X.forgetRing.map (retraction.comp i).fSharp ≫
      α.hom.app (X.forgetRing.obj X.O) = 𝟙 (X.forgetRing.obj X.O)

/-- Trivializations with the same retraction are equal. -/
@[ext]
theorem Trivialization.ext {i : RingedToposHom X Y} {s t : Trivialization i}
    (h : s.retraction = t.retraction) : s = t := by
  cases s
  cases t
  cases h
  rfl

/-- A morphism of ringed topoi is trivial if it admits a trivialization. -/
@[stacks 08MG "trivial_first_order_thickening_and_trivialization"]
abbrev IsTrivial (i : RingedToposHom X Y) : Prop := Nonempty (Trivialization i)

end Deformation.ToposThickening

module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentPushforwardAlgebra

/-!
# Stacks 081V reduced to one assertion about the direct-image functor

`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` has five fields: an anti-equivalence
`(AffineOver X)ᵒᵖ ≌ QuasicoherentAlgebra X` for every algebraic space `X`, a direct-image functor
between the same two categories, two compatibilities saying that the functor really is direct
image, and a natural isomorphism identifying the anti-equivalence's functor with it.  More than
twenty modules of this development carry the whole structure as a hypothesis
`(E : AffineAlgebraAntiEquivalence B S hS)`, and nothing inhabits it unconditionally.

This file shows that four of those five fields are free.  Take the direct-image functor to be
`AlgebraicGeometry.Space.affineQuasicoherentPushforwardAlgebraFunctor`, the functor `f ↦ f_* 𝒪_Y`
with its codomain restricted to the quasi-coherent algebras; then the two compatibility fields
hold by `rfl`, the identification of the anti-equivalence's functor with it is the identity, and
the structure as a whole follows from the single assertion that this one functor is an
equivalence.  So the entire packaging cost of the structure is zero, and the mathematical content
of the first sentence of Stacks 081V is exactly

```
∀ X, (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).IsEquivalence
```

i.e. fullness, faithfulness and essential surjectivity of direct image.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardQuasicoherentObjIso` is the `pushforward_obj` field of the
  structure for this choice of `pushforward`: the identity isomorphism.
* `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence.ofIsEquivalence` builds the whole
  structure from the assertion that direct image is an equivalence.

## Main results

* `AlgebraicGeometry.Space.pushforwardQuasicoherentObjIso_map_right` is the `pushforward_map`
  field for the same choice: under the identity identifications, the functor's action on
  morphisms is `AlgebraicGeometry.Space.pushforwardRingMap` on the nose.

## Implementation notes

Nothing here carries Stacks 081V.  The tag asserts an anti-equivalence *and* its compatibility
with arbitrary base change; this file asserts neither, it reduces the first to one `Prop` and
says nothing about the second.  The two facet attributes for the direct-image functor remain on
`AlgebraicGeometry.Space.pushforwardAlgebraMap` and
`AlgebraicGeometry.Space.affinePushforwardAlgebraFunctor` in
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism`.

Both compatibility fields are closed by `rfl`, but each is stated as its own declaration rather
than written into the structure instance.  Inlining them exhausts the heartbeat budget: the
elaborator must then reduce `CategoryTheory.ObjectProperty.lift` and the three composed
direct-image comparison isomorphisms of `AlgebraicGeometry.Space.pushforwardRingMap` under a
metavariable for the field's type, whereas against a declared type the same `rfl` is immediate.

`pushforward_obj` is the identity because
`AlgebraicGeometry.Space.affineQuasicoherentPushforwardAlgebraFunctor` is a codomain restriction
along `CategoryTheory.ObjectProperty.lift`, whose action on objects is the original functor's; so
composing it back with the inclusion of the full subcategory returns `f_* 𝒪_Y` definitionally,
not merely isomorphically.  The same holds for `pushforwardIso`, since
`CategoryTheory.Functor.asEquivalence` has the functor it is built from as its `functor` field.

## What remains, and where it is

What is *not* reduced here is the assertion that direct image is an equivalence.  The route of
the source — choose a scheme chart `φ : U ⟶ X`, apply the scheme-level Stacks 01SA to `φ^* 𝒜`,
and descend — needs three things of which this development has the module analogue and not the
algebra one:

* a comparison between the quasi-coherent algebra sheaves on the small étale site of the
  algebraic space represented by a scheme `U` and the quasi-coherent algebras on `U` itself.
  This is now **supplied in the direction the route uses it**, as
  `AlgebraicGeometry.Space.representedQuasicoherentAlgebraSchemeFunctor` of
  `StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentAlgebra`, which lands in the
  quasi-coherent `𝒪`-algebras on the Zariski site of the scheme underlying `U` — the category
  the scheme-level Stacks 01SA states its anti-equivalence in.  The change of shape and the
  change to the small étale site of that scheme are an *equivalence* there,
  `AlgebraicGeometry.Space.representedQuasicoherentAlgebraEquivalence`, resting on the match of
  the two structure sheaves of commutative rings,
  `AlgebraicGeometry.Space.representedCommSheafCongr_inverse_obj`, which is `rfl`.  What is
  only a functor, and not known to be an equivalence, is the last leg from the small étale site
  of the scheme to its Zariski site,
  `AlgebraicGeometry.SmallEtale.restrictQuasicoherentAlgebraToZariski`; the implementation notes
  there name the two statements an equivalence would need.
* an algebra analogue of Stacks 03M3.  The module statement is proved in full, as
  `AlgebraicGeometry.Space.equivalenceQuasicoherentFromSpaceBase` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseEquivalence`,
  together with the category `AlgebraicGeometry.Space.QuasicoherentModule` of quasi-coherent
  modules on a groupoid in algebraic spaces; there is no category of quasi-coherent *algebras* on
  such a groupoid.
* descent for sheaves of commutative rings on the small étale site.  What is available there is
  descent for sheaves of *sets*,
  `AlgebraicGeometry.Space.SpacesEtale.isEquivalence_toDescentData_smallEtaleSheafSystem` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleSheafDescent`.

Two obstructions recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence` are no longer obstructions:
Stacks 03M3 is stated and proved there for a target which is an algebraic space, and the
base-change clause of the scheme-level Stacks 01SA is discharged unconditionally by
`Stacks.AffineAlgebraEquivalence.isQuasicoherentAlgebraPullback`, which makes
`Stacks.AffineAlgebraEquivalence.affineAlgebraAntiEquivalence` carry that tag with no hypotheses.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `pushforward_obj` field of `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` for the
direct-image functor `AlgebraicGeometry.Space.affineQuasicoherentPushforwardAlgebraFunctor`: the
value of that functor at an algebraic space `Y` affine over `X`, read back in all algebra
sheaves, is `Y.hom_* 𝒪_Y`.

This is the identity isomorphism: restricting the codomain of a functor along
`CategoryTheory.ObjectProperty.lift` does not change its action on objects. -/
def pushforwardQuasicoherentObjIso (X : AlgebraicSpaces B S hS) (Y : AffineOver B S hS X) :
    (quasicoherentAlgebraInclusion B S hS X).obj
        ((affineQuasicoherentPushforwardAlgebraFunctor B S hS X).obj (.op Y)) ≅
      pushforwardAlgebra B S hS Y.obj :=
  Iso.refl _

/-- The `pushforward_map` field of `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` for the
direct-image functor `AlgebraicGeometry.Space.affineQuasicoherentPushforwardAlgebraFunctor`:
under the identifications of
`AlgebraicGeometry.Space.pushforwardQuasicoherentObjIso`, the action of that functor on a
morphism over `X` is the canonical map `AlgebraicGeometry.Space.pushforwardRingMap` on
direct-image sheaves of rings. -/
theorem pushforwardQuasicoherentObjIso_map_right (X : AlgebraicSpaces B S hS)
    {Y Z : AffineOver B S hS X} (f : Y ⟶ Z) :
    ((pushforwardQuasicoherentObjIso B S hS X Z).inv ≫
      (quasicoherentAlgebraInclusion B S hS X).map
        ((affineQuasicoherentPushforwardAlgebraFunctor B S hS X).map f.op) ≫
      (pushforwardQuasicoherentObjIso B S hS X Y).hom).right =
      pushforwardRingMap B S hS f.hom :=
  rfl

/-- **Stacks 081V reduced to one assertion.**  If the direct-image functor
`AlgebraicGeometry.Space.affineQuasicoherentPushforwardAlgebraFunctor` is an equivalence over
every algebraic space, then the data of
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` exists: the anti-equivalence is that
functor's own `CategoryTheory.Functor.asEquivalence`, and the three remaining fields are
identities.

This does not carry Stacks 081V, which also asserts compatibility with arbitrary base change;
see `AlgebraicGeometry.Space.BaseChangeCompatibility` for that. -/
def AffineAlgebraAntiEquivalence.ofIsEquivalence
    (h : ∀ X : AlgebraicSpaces B S hS,
      (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).IsEquivalence) :
    AffineAlgebraAntiEquivalence B S hS where
  equivalence X :=
    haveI := h X
    (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).asEquivalence
  pushforward X := affineQuasicoherentPushforwardAlgebraFunctor B S hS X
  pushforward_obj := pushforwardQuasicoherentObjIso B S hS
  pushforward_map := fun X {_ _} f => pushforwardQuasicoherentObjIso_map_right B S hS X f
  pushforwardIso _ := Iso.refl _

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposMorphismLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSmallModelAbstractHom
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp
import StacksCore.Tactic.StacksAttribute

/-!
# Localizing a morphism of ringed topoi through the equi-universe small model

`AlgebraicGeometry.RingedToposHom.localized` — Stacks 04IF — is stated for a morphism of
`AlgebraicGeometry.RingedTopos.{u, u, u}`, and that binder is load-bearing: the site of elements
of a sheaf is a comma category over presheaves, so the universe of the sections and the universe
of the morphisms of the site must agree, and the pointwise right Kan extension that computes the
inverse image of sheaves is a size condition of the same kind.  The sites of algebraic geometry
do not have that shape: the objects of a small étale site lie one universe *above* its morphisms
and above the sections of its structure sheaf.

They are nevertheless essentially small at the universe of the sections, so each of them has an
equi-universe model (`AlgebraicGeometry.RingedTopos.smallModel`) and the comparison with that
model is an *equivalence* of ringed topoi
(`AlgebraicGeometry.RingedTopos.toSmallModelAbstractHom`, whose structure map is invertible by
`AlgebraicGeometry.RingedTopos.isIso_toSmallModelAbstractHom_fSharp`).  Conjugating a morphism of
ringed topoi by those two equivalences produces a morphism between the two models, to which
Stacks 04IF applies verbatim.

This file performs that conjugation once, at free universes.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.smallModelTransport`: a morphism of ringed topoi, transported
  to the equi-universe models of its source and target.
* `AlgebraicGeometry.RingedToposHom.localizedSmallModelTransport`: **Stacks 04IF through the
  model.**  The localization of the transported morphism at a sheaf `G` on the model of the
  target and at the inverse image of `G` on the model of the source.

## Main results

* `AlgebraicGeometry.RingedToposHom.smallModelTransport_toToposHom`: the morphism of topoi
  underlying the transport is the conjugate of the given one by the two comparisons.

Nothing is lost in the transport: the structure map of each of the two comparisons it is composed
with is an isomorphism, by `AlgebraicGeometry.RingedTopos.isIso_toSmallModelAbstractHom_fSharp`,
and the direct image of each is an equivalence of categories, by
`AlgebraicGeometry.RingedTopos.isEquivalence_smallModelToposMorphism_pushforward` — so each is an
equivalence of ringed topoi and not merely a morphism.

## Implementation notes

The transport is taken as the composite `(model X) ⟶ X ⟶ Y ⟶ (model Y)`, with the first factor
`AlgebraicGeometry.RingedTopos.toSmallModelAbstractHom` and the last
`AlgebraicGeometry.RingedTopos.fromSmallModelAbstractHom`, which is the inverse of the comparison
of the target with its model.  Composition of morphisms of ringed topoi is
`AlgebraicGeometry.RingedToposHom.comp`, available with all three section universes free, so the
composite is formed at the universes the two sites actually have and only its *value* lies in the
equi-universe shape.

## References

* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w v u v' u'

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [EssentiallySmall.{w} X.C] [EssentiallySmall.{w} Y.C]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (ψ : RingedToposHom X Y)

/-- **A morphism of ringed topoi, transported to the equi-universe models of its source and its
target.**  It is the composite

`(model X) ⟶ X ⟶ Y ⟶ (model Y)`,

whose outer factors are the comparison of the source with its model and the inverse of the
comparison of the target with its model.  Both of its ringed topoi are
`AlgebraicGeometry.RingedTopos.{w, w, w}`, the universe shape in which the localization of
Stacks 04IF is available. -/
def smallModelTransport :
    RingedToposHom (RingedTopos.smallModel.{w} X.J X.O) (RingedTopos.smallModel.{w} Y.J Y.O) :=
  (RingedTopos.fromSmallModelAbstractHom.{w} Y).comp
    (ψ.comp (RingedTopos.toSmallModelAbstractHom.{w} X))

/-- The morphism of topoi underlying the transport is the conjugate of the given one by the two
comparisons with the models. -/
@[simp]
theorem smallModelTransport_toToposHom :
    (smallModelTransport.{w} ψ).toToposHom =
      (RingedTopos.smallModelToposMorphism.{w} Y).inverse.comp
        (ψ.toToposHom.comp (RingedTopos.smallModelToposMorphism.{w} X)) :=
  rfl

/-- **Stacks 04IF, through the equi-universe model.**  The localization of a morphism of ringed
topoi `ψ : X ⟶ Y` whose two sites are essentially small at the universe of the sections of their
structure sheaves: the localization of the transport of `ψ` to the two models, at a sheaf `G` on
the model of the target and at its inverse image on the model of the source.

The transport is an equivalence of ringed topoi on each side, so this is the localization of `ψ`
itself, read on the models. -/
def localizedSmallModelTransport (G : (RingedTopos.smallModel.{w} Y.J Y.O).Topos) :
    RingedToposHom
      ((RingedTopos.smallModel.{w} X.J X.O).localizedRingedTopos
        ((smallModelTransport.{w} ψ).toToposHom.inverseImage.obj G))
      ((RingedTopos.smallModel.{w} Y.J Y.O).localizedRingedTopos G) :=
  (smallModelTransport.{w} ψ).localized G

/-- The morphism of topoi underlying the localization through the model is the localized morphism
of topoi of the transport. -/
@[simp]
theorem localizedSmallModelTransport_toToposHom
    (G : (RingedTopos.smallModel.{w} Y.J Y.O).Topos) :
    (localizedSmallModelTransport.{w} ψ G).toToposHom =
      localizedToposMorphism (smallModelTransport.{w} ψ) G :=
  rfl

end AlgebraicGeometry.RingedToposHom

end

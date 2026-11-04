module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSmallModelRingedTopos
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.SmallModelMorphismLocalization
import StacksCore.Tactic.StacksAttribute

/-!
# Localizing a morphism of small étale ringed topoi of algebraic spaces

Stacks 04IF localizes a morphism of ringed topoi `(f, f♯) : (Sh(C), O) ⟶ (Sh(D), O')` at a sheaf
`G` on the target and at `F = f⁻¹G` on the source.  Its form in the library,
`AlgebraicGeometry.RingedToposHom.localized`, is stated for a morphism of
`AlgebraicGeometry.RingedTopos.{u, u, u}`, and that binder cannot be widened: the site of
elements of a sheaf is a comma category over presheaves, so the universe of the sections and the
universe of the morphisms of the site must agree, and the pointwise right Kan extension computing
the inverse image of sheaves is a size condition of the same kind.

`AlgebraicGeometry.Space.smallEtaleRingedTopos` is an `AlgebraicGeometry.RingedTopos.{u, u + 1, u}`
— the étale scheme charts of an algebraic space lie one universe above its morphisms and above
the sections of its structure sheaf — so the library's Stacks 04IF does not apply to it.  The small
étale site is nevertheless essentially small at `u`
(`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`), so it has an equi-universe model
whose comparison with it is an *equivalence* of ringed topoi, and conjugating by that equivalence
on both sides lands a morphism of small étale ringed topoi in the shape Stacks 04IF is stated at.

This file is that conjugation, at the small étale ringed topoi of two algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.localizedSmallModelMorphism`: **Stacks 04IF for a morphism of the
  small étale ringed topoi of two algebraic spaces**, read on the equi-universe models.

## Implementation notes

The whole construction is
`AlgebraicGeometry.RingedToposHom.localizedSmallModelTransport` instantiated; nothing here is
special to the small étale site of an algebraic space.  What this file adds is the registration
of Stacks 04IF at the site the development needs it at, which the generic statement cannot carry
in the generic module: that module's own ringed topoi are arbitrary.

No essential-smallness argument is handed over by hand, unlike at the small étale site of a
scheme: `AlgebraicGeometry.Space.smallEtaleRingedTopos` is a reducible abbreviation, so its
projections reduce at instance transparency and instance search finds
`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall` at the generic spelling on its own.

Nothing is lost in the transport.  The structure map of the comparison of each of the two small
étale ringed topoi with its model is an isomorphism, by
`AlgebraicGeometry.RingedTopos.isIso_toSmallModelAbstractHom_fSharp` — which at the spelling of
the small étale site of an algebraic space is
`AlgebraicGeometry.Space.isIso_toSmallEtaleModelHom_fSharp` — and the direct image of each is an
equivalence of categories, so each comparison is an equivalence of ringed topoi.

## References

* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 04IF for the small étale ringed topoi of algebraic spaces.**  Let
`ψ : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` be a morphism of the small étale ringed topoi of two
algebraic spaces and let `G` be a sheaf of sets on the equi-universe model of the target.  This is
the localized morphism of ringed topoi `ψ'` of Stacks 04IF, from the localization of the model of
the source at the inverse image of `G` to the localization of the model of the target at `G`.

It is obtained by transport: `ψ` is conjugated by the comparisons of the two small étale ringed
topoi with their equi-universe models — an equivalence of ringed topoi on each side, so nothing is
lost — and the library's Stacks 04IF is applied to the conjugate, whose two ringed topoi are
`AlgebraicGeometry.RingedTopos.{u, u, u}`. -/
@[stacks 04IF "the localized morphism of ringed topoi of a morphism of the small étale ringed
  topoi of two algebraic spaces, obtained by transporting the morphism through the `Type u`
  equi-universe models of the two small étale ringed topoi, to which the statement at
  `RingedTopos.{u, u, u}` applies"]
def localizedSmallModelMorphism
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (G : (RingedTopos.smallModel.{u} (SmallEtale.topology B S hS Y.1)
      (structureSheaf B S hS Y.1 Y.2)).Topos) :
    RingedToposHom
      ((RingedTopos.smallModel.{u} (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2)).localizedRingedTopos
        ((RingedToposHom.smallModelTransport.{u} ψ).toToposHom.inverseImage.obj G))
      ((RingedTopos.smallModel.{u} (SmallEtale.topology B S hS Y.1)
        (structureSheaf B S hS Y.1 Y.2)).localizedRingedTopos G) :=
  RingedToposHom.localizedSmallModelTransport.{u} ψ G

end AlgebraicGeometry.Space

end

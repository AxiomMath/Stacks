module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModel
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.SmallModelMorphismLocalization
import StacksCore.Tactic.StacksAttribute

/-!
# Localizing a morphism of small étale ringed topoi of schemes

Stacks 04IF localizes a morphism of ringed topoi `(f, f♯) : (Sh(C), O) ⟶ (Sh(D), O')` at a sheaf
`G` on the target and at `F = f⁻¹G` on the source.  Its form in the library,
`AlgebraicGeometry.RingedToposHom.localized`, is stated for a morphism of
`AlgebraicGeometry.RingedTopos.{u, u, u}`, and that binder cannot be widened: the site of
elements of a sheaf is a comma category over presheaves, so the universe of the sections and the
universe of the morphisms of the site must agree, and the pointwise right Kan extension computing
the inverse image of sheaves is a size condition of the same kind.

`AlgebraicGeometry.SmallEtale.ringedTopos` is an `AlgebraicGeometry.RingedTopos.{u, u + 1, u}` —
the objects of the small étale site of a scheme lie one universe above its morphisms and above
the sections of its structure sheaf — so the library's Stacks 04IF does not apply to it.  The small
étale site is nevertheless essentially small at `u`
(`AlgebraicGeometry.SmallEtale.essentiallySmall`), so it has an equi-universe model
`AlgebraicGeometry.SmallEtale.smallModelRingedTopos` whose comparison with it is an *equivalence*
of ringed topoi, and conjugating by that equivalence on both sides lands a morphism of small
étale ringed topoi in the shape Stacks 04IF is stated at.

This file is that conjugation, at the small étale ringed topoi of two schemes of one big étale
site.

## Main definitions

* `AlgebraicGeometry.SmallEtale.localizedSmallModelMorphism`: **Stacks 04IF for a morphism of the
  small étale ringed topoi of two schemes**, read on the equi-universe models.

## Implementation notes

The whole construction is
`AlgebraicGeometry.RingedToposHom.localizedSmallModelTransport` instantiated; nothing here is
special to the small étale site of a scheme.  What this file adds is the registration of
Stacks 04IF at the site the development needs it at, which the generic statement cannot carry in
the generic module: that module's own ringed topoi are arbitrary.

Essential smallness is handed over in a `letI`, as everywhere the generic model machinery is used
at the small étale site of a scheme: `AlgebraicGeometry.SmallEtale.ringedTopos` is a `def`, so
the projection `(ringedTopos B S hS).C` does not reduce at instance transparency and
`AlgebraicGeometry.SmallEtale.essentiallySmall` is not found at the generic spelling.  The same
`letI` appears in the statement, since the sheaf the source is localized at is the inverse image
of `G` along the transport.

Nothing is lost in the transport.  The structure map of the comparison of each of the two small
étale ringed topoi with its model is an isomorphism, by
`AlgebraicGeometry.SmallEtale.isIso_toEtaleAbstractRingedToposHom_fSharp`, and the direct image of
each is an equivalence of categories by
`AlgebraicGeometry.SmallEtale.isEquivalence_toEtaleAbstract_pushforward`, so each comparison is an
equivalence of ringed topoi.

## References

* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S T : Scheme.{u}) (hS : B.Contains S) (hT : B.Contains T)

/-- **Stacks 04IF for the small étale ringed topoi of schemes.**  Let
`ψ : (S_étale, 𝒪_S) ⟶ (T_étale, 𝒪_T)` be a morphism of the small étale ringed topoi of two
schemes of a big étale site and let `G` be a sheaf of sets on the equi-universe model of the
target.  This is the localized morphism of ringed topoi `ψ'` of Stacks 04IF, from the
localization of the model of the source at the inverse image of `G` to the localization of the
model of the target at `G`.

It is obtained by transport: `ψ` is conjugated by the comparisons of the two small étale ringed
topoi with their equi-universe models — an equivalence of ringed topoi on each side, so nothing
is lost — and Stacks 04IF is applied to the conjugate, whose two ringed topoi are
`AlgebraicGeometry.RingedTopos.{u, u, u}`. -/
@[stacks 04IF "the localized morphism of ringed topoi of a morphism of the small étale ringed
  topoi of two schemes, obtained by transporting the morphism through the `Type u` equi-universe
  models of the two small étale ringed topoi, to which the statement at `RingedTopos.{u, u, u}`
  applies"]
def localizedSmallModelMorphism
    (ψ : RingedToposHom (ringedTopos B S hS) (ringedTopos B T hT))
    (G : (smallModelRingedTopos B T hT).Topos) :
    RingedToposHom
      ((smallModelRingedTopos B S hS).localizedRingedTopos
        (letI : EssentiallySmall.{u} (ringedTopos B S hS).C := essentiallySmall B S hS
         letI : EssentiallySmall.{u} (ringedTopos B T hT).C := essentiallySmall B T hT
         (RingedToposHom.smallModelTransport.{u} ψ).toToposHom.inverseImage.obj G))
      ((smallModelRingedTopos B T hT).localizedRingedTopos G) :=
  letI : EssentiallySmall.{u} (ringedTopos B S hS).C := essentiallySmall B S hS
  letI : EssentiallySmall.{u} (ringedTopos B T hT).C := essentiallySmall B T hT
  RingedToposHom.localizedSmallModelTransport.{u} ψ G

end AlgebraicGeometry.SmallEtale

end

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRingBaseChange

/-!
# The variety of vanishing cycles of a base change

Let

```
X' --g'--> X
|f'        |f
S' --g---> S
```

be a cartesian square of schemes, let `x'` be a geometric point of `X'` with images `x = g'(x')`
in `X`, `s' = f'(x')` in `S'` and `s = f(x)` in `S`, and suppose the attached square of étale
local rings is a pushout,

`𝒪^sh_{X',x'} = 𝒪^sh_{S',s'} ⊗_{𝒪^sh_{S,s}} 𝒪^sh_{X,x}`.

Then for every geometric point `t'` of `Spec 𝒪^sh_{S',s'}` the variety of vanishing cycles of `f'`
at `x'` and `t'` is the variety of vanishing cycles of `f` at `x` and the image `t` of `t'` in
`Spec 𝒪^sh_{S,s}`, compatibly with the projections to `Spec 𝒪^sh_{X,x}`:

`F_{x',t'} ≅ F_{x,t}` over `Spec 𝒪^sh_{X,x}`.

This file proves that, as `AlgebraicGeometry.vanishingCyclesFibreBaseChangeIso` together with the
compatibility `AlgebraicGeometry.vanishingCyclesFibreBaseChangeIso_hom_toStrictHenselization`.

## The route

Nothing here touches a tensor product. Taking `Spec` of a pushout square of rings gives a
pullback square of affine schemes, which for the square of étale local rings is
`AlgebraicGeometry.isPullback_strictHenselizationSquareMap_of_isPushout`: the strict
henselization at `x'` is the fibre product of the strict henselizations at `s'` and at `x` over
the one at `s`. The variety of vanishing cycles at `x'` and `t'` is by definition a second
pullback square, placed to the left of that one, and pasting the two exhibits it as a pullback of
the geometric point `t'` read in `Spec 𝒪^sh_{S,s}` against the strict henselization at `x`. That
is the defining square of `F_{x,t}`, so the two agree by the uniqueness of a pullback, and the
projection the uniqueness provides is the required one.

Reading `t'` in `Spec 𝒪^sh_{S,s}` is what
`AlgebraicGeometry.baseChangeStrictHenselizationMap` is for. The image in `S` of `x'` is read
through `X` throughout, as in
`AlgebraicGeometry.isPushout_etaleLocalRingHom_of_isIntegralHom`, so the geometric point `t` is a
geometric point of `Spec 𝒪^sh_{S,(x'.map g').map f}` on the nose and no transport along the
commutativity of the cartesian square is left over: the one such transport the comparison needs
is already carried by `AlgebraicGeometry.baseChangeEtaleLocalRingHom`.

## Main definitions

* `AlgebraicGeometry.baseChangeStrictHenselizationMap` — the morphism of strict henselizations of
  the base attached to a cartesian square, the spectrum of
  `AlgebraicGeometry.baseChangeEtaleLocalRingHom`. Its target is the strict henselization at the
  image of the geometric point read through the first factor.
* `AlgebraicGeometry.vanishingCyclesFibreBaseChangeIso` — the identification of the two varieties
  of vanishing cycles.

## Main results

* `AlgebraicGeometry.isPullback_strictHenselizationSquareMap_of_isPushout` — a pushout square of
  étale local rings over a cartesian square of schemes is a cartesian square of strict
  henselizations.
* `AlgebraicGeometry.vanishingCyclesFibreBaseChangeIso_hom_toStrictHenselization` — the
  identification lies over the strict henselization at the image of the geometric point, which is
  what makes it usable for transporting the canonical map of Tag 0GJN.

## References

* [Stacks Project, Tag 0GIP](https://stacks.math.columbia.edu/tag/0GIP)
* [Stacks Project, Tag 0GJS](https://stacks.math.columbia.edu/tag/0GJS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section BaseChange

variable (B : BigEtaleSite.{u}) {X S S' X' : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (hS' : B.Contains S') (hX' : B.Contains X') {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
  {f' : X' ⟶ S'}

/-- The morphism of strict henselizations of the base attached to a cartesian square: the
spectrum of `AlgebraicGeometry.baseChangeEtaleLocalRingHom`. It goes from the strict henselization
of `S'` at the image of a geometric point of the fibre product to the strict henselization of `S`
at the image of that point *read through the first factor*, which is the reading the square of
étale local rings uses. -/
public def baseChangeStrictHenselizationMap (sq : IsPullback g' f' f g)
    (x' : GeometricPoint X') :
    strictHenselization B S' hS' (x'.map f') ⟶
      strictHenselization B S hS ((x'.map g').map f) :=
  Spec.map (CommRingCat.ofHom (baseChangeEtaleLocalRingHom B hS hS' sq x'))

/-- **A pushout square of étale local rings is a cartesian square of strict henselizations.**
For a cartesian square of schemes and a geometric point `x'` of the fibre product whose square of
étale local rings is a pushout, the strict henselization at `x'` is the fibre product of the
strict henselizations at the images of `x'` in `X` and in `S'` over the strict henselization at
its image in `S`.

The strict henselizations are spectra of the étale local rings and the morphisms between them are
the spectra of the homomorphisms, so this is
`AlgebraicGeometry.isPullback_SpecMap_of_isPushout`: `Spec` carries a pushout square of
commutative rings to a cartesian square of schemes. -/
public theorem isPullback_strictHenselizationSquareMap_of_isPushout (sq : IsPullback g' f' f g)
    (x' : GeometricPoint X')
    (hpush : IsPushout (CommRingCat.ofHom (baseChangeEtaleLocalRingHom B hS hS' sq x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX hS f (x'.map g')))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hS' f' x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hX g' x'))) :
    IsPullback (strictHenselizationSquareMap B hX' hS' f' x')
      (strictHenselizationSquareMap B hX' hX g' x')
      (baseChangeStrictHenselizationMap B hS hS' sq x')
      (strictHenselizationSquareMap B hX hS f (x'.map g')) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ hpush

/-- **The variety of vanishing cycles of a base change.** For a cartesian square of schemes whose
square of étale local rings at a geometric point `x'` of the fibre product is a pushout, and for a
geometric point `t'` of the strict henselization of `S'` at the image of `x'`, the variety of
vanishing cycles of `f'` at `x'` and `t'` is the variety of vanishing cycles of `f` at the image
`x` of `x'` in `X` and at the image of `t'` in the strict henselization of `S` at the image of
`x`.

Both are pullbacks of the same cospan: the defining square of `F_{x',t'}` pasted onto the
cartesian square of strict henselizations is the defining square of `F_{x,t}`. -/
public def vanishingCyclesFibreBaseChangeIso (sq : IsPullback g' f' f g)
    {x' : GeometricPoint X'} (t' : GeometricPoint (strictHenselization B S' hS' (x'.map f')))
    (hpush : IsPushout (CommRingCat.ofHom (baseChangeEtaleLocalRingHom B hS hS' sq x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX hS f (x'.map g')))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hS' f' x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hX g' x'))) :
    vanishingCyclesFibre B hX' hS' f' x' t' ≅
      vanishingCyclesFibre B hX hS f (x'.map g')
        (t'.map (baseChangeStrictHenselizationMap B hS hS' sq x')) :=
  ((IsPullback.of_hasPullback t'.hom
        (strictHenselizationSquareMap B hX' hS' f' x')).flip.paste_horiz
      (isPullback_strictHenselizationSquareMap_of_isPushout B hX hS hS' hX' sq x'
        hpush).flip).flip.isoPullback

/-- **The identification of the two varieties of vanishing cycles lies over the strict
henselization at the image point.** Followed by the projection of `F_{x,t}` to
`Spec 𝒪^sh_{X,x}` it is the projection of `F_{x',t'}` to `Spec 𝒪^sh_{X',x'}` followed by the
induced morphism of strict henselizations.

This is the property which lets the canonical map of Tag 0GJN at `(x, t)` be transported to the
one at `(x', t')`: the two are maps to derived sections over schemes which the identification
matches *as schemes over the strict henselization at `x`*, not merely as schemes. -/
public theorem vanishingCyclesFibreBaseChangeIso_hom_toStrictHenselization
    (sq : IsPullback g' f' f g) {x' : GeometricPoint X'}
    (t' : GeometricPoint (strictHenselization B S' hS' (x'.map f')))
    (hpush : IsPushout (CommRingCat.ofHom (baseChangeEtaleLocalRingHom B hS hS' sq x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX hS f (x'.map g')))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hS' f' x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hX g' x'))) :
    (vanishingCyclesFibreBaseChangeIso B hX hS hS' hX' sq t' hpush).hom ≫
        vanishingCyclesFibreToStrictHenselization B hX hS f (x'.map g')
          (t'.map (baseChangeStrictHenselizationMap B hS hS' sq x')) =
      vanishingCyclesFibreToStrictHenselization B hX' hS' f' x' t' ≫
        strictHenselizationSquareMap B hX' hX g' x' :=
  IsPullback.isoPullback_hom_snd _

end BaseChange

end AlgebraicGeometry

end

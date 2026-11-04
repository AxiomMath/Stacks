module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceDifferentials
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sheaf of relative differentials of a morphism of schemes

For a morphism of schemes `f : X ⟶ S`, Stacks Project, Tag 01UM defines `Ω_{X/S}` as the module
of differentials of the morphism of sheaves of rings `f⁻¹𝒪_S ⟶ 𝒪_X`. That module of
differentials, for an arbitrary morphism of ringed spaces, is
`Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials`. This file records that applying
it to the ringed space underlying a scheme lands in Mathlib's category
`AlgebraicGeometry.Scheme.Modules` of sheaves of modules on a scheme, with no transport required,
and that its pullback along `a : T ⟶ X` is `AlgebraicGeometry.Scheme.Modules.pullback`.

## Main definitions

* `Stacks.Smooth.ringedSpaceHom` is the morphism of ringed spaces underlying a morphism of
  schemes.
* `Stacks.Smooth.cotangentSheaf f` is `Ω_{X/S}`, as an object of `X.Modules`.
* `Stacks.Smooth.pullbackCotangentSheaf f a` is `a^*Ω_{X/S}`, as an object of `T.Modules`.

## Main results

* `Stacks.Smooth.cotangentSheaf_eq` holds by `rfl`, so the whole API of
  `StacksDraft.Ch17.Sec28.Tag08RU` — in particular the universal derivation
  `Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation`, its universal property
  `Stacks.Sheaves.Differentials.universalDerivation_isUniversal`, and the comparison map of a
  commutative square — applies to `Stacks.Smooth.cotangentSheaf` unchanged.
* `Stacks.Smooth.pullbackCotangentSheafHomEquiv` is the adjunction bijection
  `(a^*Ω_{X/S} ⟶ N) ≃ (Ω_{X/S} ⟶ a_*N)`. Composed with the universal property it identifies
  morphisms `a^*Ω_{X/S} ⟶ N` with derivations of `𝒪_X` over `f⁻¹𝒪_S` valued in `a_*N`, which is
  the group that acts on the lifts of `a` along a square-zero thickening.

## Implementation notes

The identification is on the nose: `Scheme.ringCatSheaf X` and the sheaf of rings that
`Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials` is stated over are both
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf`, so `X.Modules` and the type of the
ringed-space module of differentials of `ringedSpaceHom f` are the same type and
`Stacks.Smooth.cotangentSheaf_eq` is a reflexivity.

The universal property is not restated here in scheme vocabulary. Doing so requires naming the
type `Stacks.Sheaves.Differentials.SheafDerivation` of relative derivations with its three
sheaf-of-rings arguments, and `SheafedSpace.sheaf X.toRingedSpace` elaborates at a universe that
does not unify with the one an abbreviation for that type infers. Since
`Stacks.Smooth.cotangentSheaf_eq` is a reflexivity, the existing statements apply directly to
`ringedSpaceHom f` with no loss. The universal derivation `d_{X/S}` itself *is* named in scheme
vocabulary, as `Stacks.Smooth.cotangentDerivation` in
`StacksFrontier.AlgebraicGeometry.Smooth.CotangentDerivation`; it is kept in a separate module
because the scheme-level structural map `AlgebraicGeometry.inverseImageStructureMap` its type
mentions shares its name with the ringed-space one used throughout this file and the modules
below it, and importing both here makes that name ambiguous in them.

What this file does *not* provide is any computation of the sections of `Ω_{X/S}`. That
computation is Stacks Project, Tag 01UT, and it is
`Stacks.Smooth.existsUnique_linearEquiv_universalD` in
`StacksFrontier.AlgebraicGeometry.Smooth.CotangentSectionsAffineOpen`: for an affine open
`W = Spec B` of `X` lying over an affine open `V = Spec R` of `S`, the sections `Γ(Ω_{X/S}, W)`
are the Kähler differentials `Ω[B⁄R]`, by a unique isomorphism compatible with the
differentials. Its pullback form, stated at the end of the module docstring of
`StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmooth`, is
`Stacks.Smooth.bijective_cotangentComparison`. Tags 01V3 and 02G1 are what these would be
proved from.

## References

* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 08RU](https://stacks.math.columbia.edu/tag/08RU)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Smooth

/-- The morphism of ringed spaces underlying a morphism of schemes. -/
noncomputable def ringedSpaceHom {X S : Scheme.{u}} (f : X ⟶ S) :
    X.toRingedSpace ⟶ S.toRingedSpace :=
  LocallyRingedSpace.forgetToSheafedSpace.map f.toLRSHom

/-- The sheaf of relative differentials `Ω_{X/S}` of a morphism of schemes `f : X ⟶ S`, as a
sheaf of `𝒪_X`-modules: the module of differentials of the morphism of sheaves of rings
`f⁻¹𝒪_S ⟶ 𝒪_X`, which is how Stacks Project, Tag 01UM defines it. -/
@[stacks 01UQ "the sheaf of differentials of a morphism of schemes, namely the differentials \
of the underlying morphism of ringed spaces; the universal S-derivation d_{X/S} it is equipped \
with is `Stacks.Smooth.cotangentDerivation`", sga "6 0 2.1"]
noncomputable def cotangentSheaf {X S : Scheme.{u}} (f : X ⟶ S) : X.Modules :=
  Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials (ringedSpaceHom f)

/-- `Stacks.Smooth.cotangentSheaf` is the ringed-space module of differentials of the underlying
morphism of ringed spaces, on the nose. The point of the statement is that the two types agree,
so that every result about the latter applies to the former. -/
theorem cotangentSheaf_eq {X S : Scheme.{u}} (f : X ⟶ S) :
    cotangentSheaf f =
      Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials (ringedSpaceHom f) :=
  rfl

/-- The pullback `a^*Ω_{X/S}` of the sheaf of relative differentials of `f : X ⟶ S` along a
morphism `a : T ⟶ X`, as a sheaf of `𝒪_T`-modules. -/
noncomputable def pullbackCotangentSheaf {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) :
    T.Modules :=
  (Scheme.Modules.pullback a).obj (cotangentSheaf f)

/-- Morphisms out of `a^*Ω_{X/S}` are morphisms of `Ω_{X/S}` into the pushforward, by the
adjunction between pullback and pushforward of sheaves of modules on schemes. Composed with the
universal property of `Ω_{X/S}` this presents morphisms `a^*Ω_{X/S} ⟶ N` as derivations of
`𝒪_X` over `f⁻¹𝒪_S` with values in `a_*N`. -/
noncomputable def pullbackCotangentSheafHomEquiv {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X)
    (N : T.Modules) :
    (pullbackCotangentSheaf f a ⟶ N) ≃ (cotangentSheaf f ⟶ (Scheme.Modules.pushforward a).obj N) :=
  (Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv _ _

end Stacks.Smooth

end

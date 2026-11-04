module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleToposRingedHom
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp
import StacksCore.Tactic.StacksAttribute

/-!
# `ε : (X_étale, 𝒪_étale) ⟶ (X_Zar, 𝒪_{X_0})` for a represented algebraic space

Let `U` be an object of the big fppf site over `S`, with underlying scheme `X_0`, and let
`X = h_U` be the algebraic space it represents.  The small étale site of `X` is equivalent to
the small étale site of `X_0` (`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`), and
the small étale site of `X_0` carries the comparison `ε` of Equation 75.4.0.1 with the small
Zariski site of `X_0`.  This module composes the two and so puts `ε` on the small étale ringed
topos of the algebraic space:

`(X_étale, 𝒪_X) ⟶ (X_{0, étale}, 𝒪_{étale}) ⟶ (X_{0, Zar}, 𝒪_{X_0})`,

as an `AlgebraicGeometry.RingedToposHom`, i.e. a morphism of ringed topoi in the sense of
Stacks 01D3 (2).

## Why this presentation and not the one already in the library

`ε` is already in the library for the small étale site of a *scheme*, taken in a big *étale*
site: `AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom` records it as a morphism of ringed
sites and `AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom` as a morphism of ringed
topoi.  The small étale site of an *algebraic space* is a different category, built from étale
charts of a presheaf over a big *fppf* site, and the naive cotangent complex
`AlgebraicGeometry.Space.naiveCotangentComplex` of Stacks 0D0V is formed on it.  Nothing carried
`ε` there, so nothing could apply `ε⁻¹` to a sheaf of rings on the small étale site of an
algebraic space, and that is precisely what Stacks 0D0X asks for: its canonical map

`ε⁻¹\NL_{X_0/Y_0} = \NL_{ε⁻¹𝒪_{X_0} / ε⁻¹f_0^{-1}𝒪_{Y_0}} ⟶ \NL_{𝒪_X / f_{small}^{-1}𝒪_Y}`

is built by functoriality of the naive cotangent complex from the square of Derived Categories
of Spaces, Remark 08GH, whose corners are sheaves of rings obtained by applying `ε⁻¹`.

## Main definitions

* `AlgebraicGeometry.Space.representedEtaleToposMorphism`: the equivalence of the small étale
  topos of `h_U` with the small étale topos of the scheme underlying `U`, as a morphism of
  topoi.
* `AlgebraicGeometry.Space.representedEtaleStructureMap`: the comparison of the two structure
  sheaves of commutative rings along that equivalence.  It is the identity on sections.
* `AlgebraicGeometry.Space.representedEtaleRingedToposHom`: that equivalence as a morphism of
  ringed topoi.
* `AlgebraicGeometry.Space.representedToSchemeZariskiRingedToposHom`: **`ε` on the small étale
  ringed topos of a represented algebraic space**, the composite of the two.
* `AlgebraicGeometry.Space.representedZariskiInverseImageCommRing`: **`ε⁻¹` on sheaves of
  commutative rings**, `Sh(X_{0, Zar}, \mathrm{CommRing}) ⥤ Sh(X_étale, \mathrm{CommRing})`.
* `AlgebraicGeometry.Space.representedZariskiStructureSharpInverseImage`: **`ε^♯` in its
  inverse-image form** `ε⁻¹𝒪_{X_0} ⟶ 𝒪_X`.

## Main results

* `AlgebraicGeometry.Space.representedEtaleToposMorphism_pushforward` and
  `AlgebraicGeometry.Space.representedEtaleToposMorphism_inverseImage`: the two functors of the
  comparison of topoi are the two restrictions along the equivalence of sites.
* `AlgebraicGeometry.Space.representedEtalePushCommRingIso`: the abstract direct image of
  sheaves of commutative rings along the comparison is restriction along the equivalence of
  sites.
* `AlgebraicGeometry.Space.representedToSchemeZariskiRingedToposHom_toToposHom`: the underlying
  morphism of topoi of `ε` is the composite of the two.

## Implementation notes

The comparison of structure sheaves is the identity, not merely an isomorphism: both sites send
an object to the global regular functions on its underlying scheme, and the equivalence of sites
does not change that scheme.  This is the same observation that
`AlgebraicGeometry.Space.representedStructureMapInverse` rests on; there it is made for the
sheaves of not necessarily commutative rings in which sheaves of modules are indexed, here for
the sheaves of *commutative* rings that a ringed topos carries.

The universes do not move.  All three ringed topoi have their structure rings in `CommRingCat.{u}`
— the small étale sites of `h_U` and of `X_0` are `RingedTopos.{u, u + 1, u}`, the small Zariski
site of `X_0` a `RingedTopos.{u, u, u}` — so `ε⁻¹` on sheaves of commutative rings is available
at ring universe `u` on a site whose objects form a `Type (u + 1)`.  That is exactly the shape
`Stacks.SheafOfModules.naiveCotangentComplex` is fed at in
`AlgebraicGeometry.Space.naiveCotangentComplex`, where the free module universe is pinned at `u`
and the sheaves of modules it produces come out at `max u (u + 1) = u + 1`.  So no universe
specialization stands between this and the statement of Stacks 0D0X.

What is *not* claimed here.  Nothing is said about `ε^*` on sheaves of modules:
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` pins the module universe of
each side to the universe of its structure rings, so it produces a functor into modules at
universe `u`, one
below the `u + 1` at which `AlgebraicGeometry.Space.naiveCotangentComplex` lives — the same
restriction as for `AlgebraicGeometry.Space.representedAssociatedModule`.  Stacks 0D0X does
not need it: its canonical map is built from `ε⁻¹` on *rings*, by functoriality of the naive
cotangent complex, and the pullback of modules enters only through the identification
`ε^*\NL = ε⁻¹\NL ⊗ 𝒪` that Modules on Sites, Lemma 08TZ supplies.  Neither Lemma 08H8 nor
Lemma 071Q of Section 75.4 is re-proved here; both are already carried, for the small étale site
of a scheme, in `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/`.

## References

* [Stacks Project, Tag 071P](https://stacks.math.columbia.edu/tag/071P), Section 75.4, whose
  Equation 75.4.0.1 is the morphism built here.
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7), that equation.
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3), morphisms of ringed
  topoi and their composition.
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED), the small étale site of
  an algebraic space.
* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X), the statement this
  unblocks.
* [Stacks Project, Tag 08GH](https://stacks.math.columbia.edu/tag/08GH), the square its
  canonical map is built from.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-! ### The comparison of the two small étale topoi -/

/-- **The equivalence of the small étale site of `h_U` with the small étale site of the scheme
underlying `U`, read as a morphism of topoi.**  Its direct image is restriction along the inverse
of the equivalence of sites and its inverse image is restriction back along the equivalence; the
two are the inverse and the functor of Mathlib's equivalence of sheaf categories
`CategoryTheory.Equivalence.sheafCongr`, on the nose, so the adjunction is that equivalence read
as an adjunction and the left exactness of the inverse image is unconditional. -/
public def representedEtaleToposMorphism :
    MorphismOfTopoi
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).Topos
      (_root_.AlgebraicGeometry.SmallEtale.ringedTopos (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).Topos where
  pushforward := (representedSmallEtaleEquivalence B S hS U).inverse.sheafPushforwardContinuous
    (Type u)
    (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (SmallEtale.topology B S hS (yoneda.obj U))
  inverseImage := (representedSmallEtaleEquivalence B S hS U).functor.sheafPushforwardContinuous
    (Type u)
    (SmallEtale.topology B S hS (yoneda.obj U))
    (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
  adj := (Equivalence.sheafCongr (SmallEtale.topology B S hS (yoneda.obj U))
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
      (representedSmallEtaleEquivalence B S hS U) (Type u)).symm.toAdjunction
  preservesFiniteLimits := Functor.preservesFiniteLimits_sheafPushforwardContinuous
    (SmallEtale.topology B S hS (yoneda.obj U))
    (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (representedSmallEtaleEquivalence B S hS U).functor (Type u)

/-- The direct image of `AlgebraicGeometry.Space.representedEtaleToposMorphism` is the
pushforward along the inverse of the comparison equivalence of sites. -/
@[simp]
public theorem representedEtaleToposMorphism_pushforward :
    (representedEtaleToposMorphism B S hS U).pushforward =
      (representedSmallEtaleEquivalence B S hS U).inverse.sheafPushforwardContinuous (Type u)
        (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
        (SmallEtale.topology B S hS (yoneda.obj U)) :=
  rfl

/-- The inverse image of `AlgebraicGeometry.Space.representedEtaleToposMorphism` is the
pushforward along the functor of the comparison equivalence of sites. -/
@[simp]
public theorem representedEtaleToposMorphism_inverseImage :
    (representedEtaleToposMorphism B S hS U).inverseImage =
      (representedSmallEtaleEquivalence B S hS U).functor.sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS (yoneda.obj U))
        (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property) :=
  rfl

/-- **The abstract direct image of sheaves of commutative rings along the comparison is
restriction along the equivalence of sites.**  The identification is the identity on sections. -/
public def representedEtalePushCommRingIso :
    pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (representedEtaleToposMorphism B S hS U) ≅
      (representedSmallEtaleEquivalence B S hS U).inverse.sheafPushforwardContinuous
        CommRingCat.{u}
        (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
        (SmallEtale.topology B S hS (yoneda.obj U)) :=
  NatIso.ofComponents
    (fun O ↦ restrictionCommRingIso
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
      (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U).inverse O)
    (fun a ↦ restrictionCommRingIso_naturality
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
      (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U).inverse a)

/-- The identification of the abstract direct image of the structure sheaf of the small étale
site of `h_U` with its restriction along the equivalence of sites. -/
public abbrev representedEtalePushforwardStructureIso :
    (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (representedEtaleToposMorphism B S hS U)).obj
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O ≅
      ((representedSmallEtaleEquivalence B S hS U).inverse.sheafPushforwardContinuous
        CommRingCat.{u}
        (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
        (SmallEtale.topology B S hS (yoneda.obj U))).obj
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O :=
  (representedEtalePushCommRingIso B S hS U).app _

/-- **The structure sheaf of the small étale site of the scheme underlying `U` is the structure
sheaf of the small étale site of `h_U`, restricted along the equivalence of the two sites.**
Both sides send an object to the global regular functions on the same scheme, so the comparison
is the identity.

This is `AlgebraicGeometry.Space.representedStructureMapInverse` for the sheaves of *commutative*
rings that a ringed topos carries, rather than for the sheaves of rings in which sheaves of
modules are indexed. -/
public def representedEtaleStructureMap :
    (_root_.AlgebraicGeometry.SmallEtale.ringedTopos (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).O ⟶
      ((representedSmallEtaleEquivalence B S hS U).inverse.sheafPushforwardContinuous
        CommRingCat.{u}
        (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
        (SmallEtale.topology B S hS (yoneda.obj U))).obj
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O where
  hom := 𝟙 _

/-- **The equivalence of the two small étale sites as a morphism of ringed topoi**
`(X_étale, 𝒪_X) ⟶ (X_{0, étale}, 𝒪_{étale})`, for `X = h_U` and `X_0` the scheme underlying
`U`.  The geometric datum is `AlgebraicGeometry.Space.representedEtaleToposMorphism` and the
structure map is `AlgebraicGeometry.Space.representedEtaleStructureMap` read through
`AlgebraicGeometry.Space.representedEtalePushforwardStructureIso`. -/
public def representedEtaleRingedToposHom :
    AlgebraicGeometry.RingedToposHom
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U))
      (_root_.AlgebraicGeometry.SmallEtale.ringedTopos (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property) where
  toToposHom := representedEtaleToposMorphism B S hS U
  fSharp := representedEtaleStructureMap B S hS U ≫
    (representedEtalePushforwardStructureIso B S hS U).inv

/-- The underlying morphism of topoi of `AlgebraicGeometry.Space.representedEtaleRingedToposHom`
is `AlgebraicGeometry.Space.representedEtaleToposMorphism`. -/
@[simp]
public theorem representedEtaleRingedToposHom_toToposHom :
    (representedEtaleRingedToposHom B S hS U).toToposHom =
      representedEtaleToposMorphism B S hS U :=
  rfl

/-- The ring map `f^♯` of `AlgebraicGeometry.Space.representedEtaleRingedToposHom` is the
structure-sheaf comparison followed by the inverse of the direct-image isomorphism of the
structure sheaves. -/
@[simp]
public theorem representedEtaleRingedToposHom_fSharp :
    (representedEtaleRingedToposHom B S hS U).fSharp =
      representedEtaleStructureMap B S hS U ≫
        (representedEtalePushforwardStructureIso B S hS U).inv :=
  rfl

/-! ### `ε` on the small étale ringed topos of a represented algebraic space -/

/-- **`ε : (X_étale, 𝒪_X) ⟶ (X_{0, Zar}, 𝒪_{X_0})` as a morphism of ringed topoi**, for `X = h_U`
the algebraic space represented by an object `U` of the big fppf site over `S` and `X_0` the
scheme underlying `U`.

This is Equation 75.4.0.1 of Stacks Section 75.4, read on the small étale site of the algebraic
space: the composite of the equivalence of that site with the small étale site of `X_0`
(`AlgebraicGeometry.Space.representedEtaleRingedToposHom`) with the comparison
`AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom` of the small étale and small
Zariski sites of `X_0`.

Being a morphism of ringed topoi, it carries `ε⁻¹` on sheaves of commutative rings
(`AlgebraicGeometry.Space.representedZariskiInverseImageCommRing`) and the inverse-image form
`ε⁻¹𝒪_{X_0} ⟶ 𝒪_X` of its structure map
(`AlgebraicGeometry.Space.representedZariskiStructureSharpInverseImage`), which is what the
canonical map of Stacks 0D0X is built from. -/
public def representedToSchemeZariskiRingedToposHom :
    AlgebraicGeometry.RingedToposHom
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U))
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos :=
  AlgebraicGeometry.RingedToposHom.comp
    (X := smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U))
    (Y := _root_.AlgebraicGeometry.SmallEtale.ringedTopos (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (Z := ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos)
    (_root_.AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (representedEtaleRingedToposHom B S hS U)

attribute [stacks 08H7 "the morphism ε of the displayed equation, as a morphism of ringed topoi, \
for the small étale site of an algebraic space represented by a scheme — the same ε as \
`AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom`, read along the equivalence of \
that site with the small étale site of the representing scheme"]
  representedToSchemeZariskiRingedToposHom

/-- The morphism of topoi underlying `ε` is the composite of the comparison of the two small
étale topoi with the morphism of topoi of `ε` for the scheme. -/
@[simp]
public theorem representedToSchemeZariskiRingedToposHom_toToposHom :
    (representedToSchemeZariskiRingedToposHom B S hS U).toToposHom =
      (_root_.AlgebraicGeometry.SmallEtale.toZariskiMorphismOfTopoi
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
          U.left.property).comp (representedEtaleToposMorphism B S hS U) :=
  rfl

/-- **`ε⁻¹` on sheaves of commutative rings**: a sheaf of commutative rings on the small Zariski
site of the scheme `X_0` underlying `U` is carried to one on the small étale site of the
algebraic space `h_U`.

This is the functor Stacks 0D0X applies to `f_0^{-1}𝒪_{Y_0}` and to `𝒪_{X_0}`, and it is
available at the universe of the structure rings of all three sites. -/
public abbrev representedZariskiInverseImageCommRing :
    Sheaf (Opens.grothendieckTopology ↥((BigFppfOver.toScheme B S hS).obj U)) CommRingCat.{u} ⥤
      Sheaf (SmallEtale.topology B S hS (yoneda.obj U)) CommRingCat.{u} :=
  inverseImageCommRingFunctor.{u, u, u, u + 1, u, u}
    (representedToSchemeZariskiRingedToposHom B S hS U).toToposHom

/-- **`ε^♯` in its inverse-image form `ε⁻¹𝒪_{X_0} ⟶ 𝒪_X`**, a homomorphism of sheaves of
commutative rings on the small étale site of the represented algebraic space `X = h_U`.

This is the right-hand vertical map of the square of Stacks 08GH, and the morphism of sheaves of
rings whose naive cotangent complex Stacks 0D0X compares with `\NL_{X/Y}`. -/
public abbrev representedZariskiStructureSharpInverseImage :
    (inverseImageCommRingFunctor
        (representedToSchemeZariskiRingedToposHom B S hS U).toToposHom).obj
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O ⟶
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O :=
  (representedToSchemeZariskiRingedToposHom B S hS U).fSharpInverseImage

end AlgebraicGeometry.Space

end

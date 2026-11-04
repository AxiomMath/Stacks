module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesToposPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.CoefficientChangePushforward

/-!
# Coherence is preserved by the pullback along an equivalence of ringed topoi

Stacks 03DL (8) is the one local condition on a sheaf of modules among the eight of that tag
which Stacks 03DO does *not* list, and necessarily so: the pullback along a morphism of ringed
topoi presented by a ring map `A ⟶ B` with `B` non-coherent carries the coherent module `O_D` to
the non-coherent module `O_C`, so the clause is false for an arbitrary morphism.  See the
implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesToposPullback` for the counterexample
written out.

What Stacks 03DM nevertheless asserts is that coherence is *intrinsic*: it is unchanged by the
pullback along a morphism of ringed topoi which is an **equivalence**.  This file proves the
forward half of that at the generality of an arbitrary equivalence of ringed topoi; the `iff` is
`AlgebraicGeometry.RingedToposHom.isCoherentOnSite_iff_pullbackModules` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderEquivalence`, which obtains the
reverse half by applying this one to the inverse equivalence.

## The one-sided square

The seven clauses which Stacks 03DO does state are carried around the *two-sided* square of
Stacks 03CR, whose bottom arrow is presented by a left exact morphism of sites; that bottom
arrow is exactly where the counterexample above lives, so coherence cannot travel along it.
The addendum to Stacks 03CR,
`AlgebraicGeometry.RingedToposHom.exists_oneSided_isDenseSubsite_of_isEquivalence`, factors an
*equivalence* of ringed topoi over a **single** replacement site, with the middle morphism
`(h, h♯)` the identity morphism of topoi together with an isomorphism of the two replacement
structure sheaves.  Along such an `h` the pullback of modules extends no scalars that it does
not also restrict, and coherence travels.  The three sides of the one-sided square are

1. `AlgebraicGeometry.RingedToposHom.isCoherentOnSite_denseSubsiteLift`, which lifts the module
   across the right-hand dense subsite inclusion;
2. `AlgebraicGeometry.RingedToposHom.isCoherentOnSite_pullbackModules_ofIdentityTopos`, the
   middle arrow, proved here; and
3. `AlgebraicGeometry.RingedToposHom.isCoherentOnSite_pullbackModules_ofDenseSubsite`, the
   left-hand dense subsite inclusion.

The identification of the composite with the pullback along the original morphism is
`AlgebraicGeometry.RingedToposHom.twoSidedSquareIso`, which is stated for an arbitrary middle
morphism and a 2-isomorphism and so serves the one-sided square unchanged.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.pullbackModulesIsoRestrictionOfIdentityTopos`: **the
  pullback of modules along a change of coefficient rings on a fixed site is restriction of
  scalars**, up to the restriction of modules along the identity functor of the site.

## Main results

* `AlgebraicGeometry.RingedToposHom.isCoherentOnSite_pullbackModules_ofIdentityTopos`:
  coherence is carried by the pullback of modules along a change of coefficient rings on a
  fixed site whose structure map is invertible.
* `AlgebraicGeometry.RingedToposHom.isCoherentOnSite_pullbackModules_of_oneSided`: **coherence
  travels around the one-sided square of Stacks 03CR.**
* `AlgebraicGeometry.RingedToposHom.isCoherentOnSite_pullbackModules`: **Stacks 03DL (8) is
  preserved by the pullback along an arbitrary equivalence of ringed topoi.**

## Implementation notes

The middle comparison is built exactly as
`AlgebraicGeometry.RingedToposHom.pullbackModulesIsoModuleRestriction` is, by whiskering the
geometric comparison `Stacks.Sheaves.ToposPullback.restrictionModuleIso` at the *identity*
functor of the site against extension of scalars, and then replacing extension of scalars along
the invertible structure map by restriction of scalars along its inverse.  That the inverse
image of the identity morphism of topoi is the restriction along the identity functor of the
site is a definitional equality — `MorphismOfTopoi.id` is built from `𝟭` and
`CategoryTheory.Functor.sheafPushforwardContinuous` at `𝟭` is `𝟭` — so no comparison of its own
is needed.

`AlgebraicGeometry.RingedToposHom.isIso_toModulesHom_fSharpInverseImage_ofIdentityTopos` repeats
an existing instance at the shape taken by a change of coefficient rings: the two ringed topoi
of `AlgebraicGeometry.RingedToposHom.ofIdentityTopos` are given as structure literals rather
than as variables, and instance search does not find the general instance through them.

Every argument the elaborator cannot invent is given: the two ringed topoi of each factor, the
functor of sites, and the site and the two structure sheaves of the middle arrow.  Left to
unification, the pullback of modules along the middle arrow exhausts the heartbeat budget at
`whnf`.

## References

* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom

/-! ### The middle arrow: a change of coefficient rings on a fixed site -/

section IdentityTopos

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget CommRingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O O' : Sheaf J CommRingCat.{w}}
  (φ : O ⟶ (pushforwardCommRingFunctor (MorphismOfTopoi.id (Sheaf J (Type w)))).obj O')
  [IsIso (ofIdentityTopos φ).fSharpInverseImage]

/-- The structure map of a change of coefficient rings along which the pullback of modules
extends scalars is an isomorphism, stated at the two ringed topoi of
`AlgebraicGeometry.RingedToposHom.ofIdentityTopos`, which are structure literals rather than
variables and through which instance search does not see the general instance. -/
instance isIso_toModulesHom_fSharpInverseImage_ofIdentityTopos :
    IsIso (ofIdentityTopos φ).toModulesHom.fSharpInverseImage :=
  isIso_toModulesHom_fSharpInverseImage (ofIdentityTopos φ)

open Stacks.Sheaves.RingedToposModules.RingedToposHom
  (extendScalarsFSharpIsoRestrictScalarsOfIsIso) in
/-- **The pullback of modules along a change of coefficient rings on a fixed site is restriction
of scalars.**  The pullback of Stacks 03D6 is the inverse image of Stacks 03D2 followed by
extension of scalars along the structure map.  Its geometric factor is the inverse image along
the identity morphism of topoi, which is the restriction of sections along the identity functor
of the site on the nose, so `Stacks.Sheaves.ToposPullback.restrictionModuleIso` applies at `𝟭`;
and its scalar factor collapses, the structure map being invertible, to restriction of scalars
along the inverse. -/
def pullbackModulesIsoRestrictionOfIdentityTopos :
    (ofIdentityTopos φ).toModulesHom.pullbackModules ≅
      (restrictionModules J J (𝟭 C) (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
          SheafOfModules.restrictScalars
            (restrictionRingIso J J (𝟭 C) (Stacks.SheafOfModules.Tensor.ringSheaf O)).hom) ⋙
        SheafOfModules.restrictScalars
          (asIso (ofIdentityTopos φ).toModulesHom.fSharpInverseImage).inv :=
  Functor.isoWhiskerRight
      (restrictionModuleIso J J (𝟭 C) (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (Stacks.Sheaves.RingedToposModules.extendScalarsFSharp
        (ofIdentityTopos φ).toModulesHom) ≪≫
    Functor.isoWhiskerLeft _
      (extendScalarsFSharpIsoRestrictScalarsOfIsIso (ofIdentityTopos φ).toModulesHom)

/-- **Coherence is carried by the pullback of modules along a change of coefficient rings on a
fixed site** whose structure map is invertible.  This is the middle arrow of the one-sided
square of Stacks 03CR; the clause travels across the two restrictions of scalars of
`AlgebraicGeometry.RingedToposHom.pullbackModulesIsoRestrictionOfIdentityTopos` and then across
that isomorphism itself, the restriction of modules along the identity functor of the site
leaving the module alone. -/
theorem isCoherentOnSite_pullbackModules_ofIdentityTopos
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (hF : F.IsCoherentOnSite) :
    ((ofIdentityTopos φ).toModulesHom.pullbackModules.obj F).IsCoherentOnSite := by
  have _ : IsIso (asIso (ofIdentityTopos φ).toModulesHom.fSharpInverseImage).inv :=
    Iso.isIso_inv _
  exact Stacks.SheafOfModules.isCoherentOnSite_of_iso
    ((pullbackModulesIsoRestrictionOfIdentityTopos φ).app F).symm
    (Stacks.SheafOfModules.isCoherentOnSite_restrictScalars_of_isIso
      (asIso (ofIdentityTopos φ).toModulesHom.fSharpInverseImage).inv _
      (Stacks.SheafOfModules.isCoherentOnSite_restrictScalars_of_isIso
        (restrictionRingIso J J (𝟭 C) (Stacks.SheafOfModules.Tensor.ringSheaf O)).hom _ hF))

end IdentityTopos

/-! ### Coherence around the one-sided square of Stacks 03CR -/

section OneSided

universe w

variable {X Y : RingedTopos.{w, w, w}}
  (f : RingedToposHom X Y) {C' : Type w} [SmallCategory C']
  {J' : GrothendieckTopology C'} {OX OY : Sheaf J' CommRingCat.{w}}
  {a : X.C ⥤ C'} [a.IsDenseSubsite X.J J']
  {b : Y.C ⥤ C'} [b.IsDenseSubsite Y.J J']
  (φ : OX ⟶ (pushforwardCommRingFunctor
    (Functor.IsDenseSubsite.morphismOfTopoi X.J J' a)).obj X.O) (hφ : IsIso φ)
  (ψ : OY ⟶ (pushforwardCommRingFunctor
    (Functor.IsDenseSubsite.morphismOfTopoi Y.J J' b)).obj Y.O) (hψ : IsIso ψ)
  (χ : OY ⟶ (pushforwardCommRingFunctor
    (MorphismOfTopoi.id (Sheaf J' (Type w)))).obj OX) (hχ : IsIso χ)
  (t : (RingedToposHom.comp (X := X) (Y := (⟨C', J', OX⟩ : RingedTopos.{w, w, w}))
      (Z := (⟨C', J', OY⟩ : RingedTopos.{w, w, w}))
      (ofIdentityTopos (C := C') (J := J') (O := OY) (O' := OX) χ)
      (ofDenseSubsite (X := X) (Y := (⟨C', J', OX⟩ : RingedTopos.{w, w, w})) a φ)).TwoIso
    (RingedToposHom.comp (X := X) (Y := Y) (Z := (⟨C', J', OY⟩ : RingedTopos.{w, w, w}))
      (ofDenseSubsite (X := Y) (Y := (⟨C', J', OY⟩ : RingedTopos.{w, w, w})) b ψ) f))
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

include hφ hψ hχ t in
/-- **Coherence travels around the one-sided square of Stacks 03CR**: the two vertical arrows
are the equivalences attached to dense subsite inclusions into a single replacement site, and
the middle arrow is a change of coefficient rings on that site. -/
theorem isCoherentOnSite_pullbackModules_of_oneSided (hF : F.IsCoherentOnSite) :
    (f.toModulesHom.pullbackModules.obj F).IsCoherentOnSite := by
  have := hφ
  have := hψ
  have := hχ
  have : (ofDenseSubsite (X := X) (Y := (⟨C', J', OX⟩ : RingedTopos.{w, w, w})) a
      φ).toToposHom.pushforward.IsEquivalence :=
    Functor.IsDenseSubsite.morphismOfTopoi_pushforward_isEquivalence X.J J' a
  have : (ofDenseSubsite (X := Y) (Y := (⟨C', J', OY⟩ : RingedTopos.{w, w, w})) b
      ψ).toToposHom.pushforward.IsEquivalence :=
    Functor.IsDenseSubsite.morphismOfTopoi_pushforward_isEquivalence Y.J J' b
  have : (ofIdentityTopos (C := C') (J := J') (O := OY)
      (O' := OX) χ).toToposHom.pushforward.IsEquivalence :=
    inferInstanceAs (𝟭 (Sheaf J' (Type w))).IsEquivalence
  have : IsIso (ofDenseSubsite (X := X) (Y := (⟨C', J', OX⟩ : RingedTopos.{w, w, w})) a
      φ).fSharp := inferInstanceAs (IsIso φ)
  have : IsIso (ofDenseSubsite (X := Y) (Y := (⟨C', J', OY⟩ : RingedTopos.{w, w, w})) b
      ψ).fSharp := inferInstanceAs (IsIso ψ)
  have : IsIso (ofIdentityTopos (C := C') (J := J') (O := OY) (O' := OX) χ).fSharp :=
    inferInstanceAs (IsIso χ)
  have := isIso_fSharpInverseImage
    (ofDenseSubsite (X := X) (Y := (⟨C', J', OX⟩ : RingedTopos.{w, w, w})) a φ)
  have := isIso_fSharpInverseImage
    (ofDenseSubsite (X := Y) (Y := (⟨C', J', OY⟩ : RingedTopos.{w, w, w})) b ψ)
  have := isIso_fSharpInverseImage
    (ofIdentityTopos (C := C') (J := J') (O := OY) (O' := OX) χ)
  exact Stacks.SheafOfModules.isCoherentOnSite_of_iso
    (twoSidedSquareIso (X := X) (Y := Y)
      (X' := (⟨C', J', OX⟩ : RingedTopos.{w, w, w}))
      (Y' := (⟨C', J', OY⟩ : RingedTopos.{w, w, w})) (a := a) (b := b) f φ ψ
      (ofIdentityTopos (C := C') (J := J') (O := OY) (O' := OX) χ) t F)
    (isCoherentOnSite_pullbackModules_ofDenseSubsite
      (X := X) (Y := (⟨C', J', OX⟩ : RingedTopos.{w, w, w})) a φ _
      (isCoherentOnSite_pullbackModules_ofIdentityTopos
          (C := C') (J := J') (O := OY) (O' := OX) χ _
        (isCoherentOnSite_denseSubsiteLift (X := Y)
          (Y := (⟨C', J', OY⟩ : RingedTopos.{w, w, w})) b ψ F hF)))

end OneSided

/-! ### Coherence under an arbitrary equivalence of ringed topoi -/

section General

universe w

variable {X Y : RingedTopos.{w, w, w}} (f : RingedToposHom X Y)
  [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **Coherence is preserved by the pullback along an equivalence of ringed topoi.**  This is
the forward half of Stacks 03DM for the clause 03DL (8); it is *not* an instance of Stacks 03DO,
which omits coherence and could not state it.

The addendum to Stacks 03CR factors the equivalence over a single replacement site, with the
middle morphism the identity morphism of topoi together with an isomorphism of the two
replacement structure sheaves, and the clause travels around that square by
`AlgebraicGeometry.RingedToposHom.isCoherentOnSite_pullbackModules_of_oneSided`. -/
theorem isCoherentOnSite_pullbackModules (hF : F.IsCoherentOnSite) :
    (f.toModulesHom.pullbackModules.obj F).IsCoherentOnSite := by
  obtain ⟨C', instC', J', v, u, instv, instu, hfl, hsub, -, -, -, -, h, hh, hfs, ⟨t⟩⟩ :=
    exists_oneSided_isDenseSubsite_of_isEquivalence X Y f
      (fun z : PEmpty.{w + 1} ↦ z.elim) (fun z : PEmpty.{w + 1} ↦ z.elim)
  obtain ⟨hTop, hSharp⟩ := h
  subst hh
  exact isCoherentOnSite_pullbackModules_of_oneSided f _ (IsIso.id _) _ (IsIso.id _) hSharp hfs
    t F hF

end General

end AlgebraicGeometry.RingedToposHom

end

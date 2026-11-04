module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomOfRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineRingedTopos
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality

/-!
# The morphism of ringed topoi of a 1-morphism, with the structure sheaf's sections lifted

Let `p : 𝒳 ⥤ (Sch/S)` and `q : 𝒴 ⥤ (Sch/S)` be categories fibred in groupoids over the big fppf
category of a scheme `S`, let `F : 𝒳 ⥤ 𝒴` be a 1-morphism between them and let `τ` be a topology
on the schemes of the big site coarser than the fppf one. **Stacks 06TW** says that `F` induces
a morphism of ringed topoi `(Sh(𝒳_τ), 𝒪_𝒳) ⟶ (Sh(𝒴_τ), 𝒪_𝒴)` whose structure map
`f⁻¹𝒪_𝒴 ⟶ 𝒪_𝒳` is the canonical identification. In this library that statement is
`AlgebraicGeometry.Stack.associatedRingedToposHom`, between the ringed topoi
`AlgebraicGeometry.Stack.associatedRingedTopos` whose sections live in the universe `u` of the
schemes.

This file builds the same morphism between the ringed topoi
`AlgebraicGeometry.Stack.fullRingedTopos` of **Stacks 0H0C**, whose structure sheaf is
`AlgebraicGeometry.Stack.liftedStructureSheaf`: the structure sheaf of **Stacks 06TV** with its
sections lifted to the universe `max u v w` containing the site. At that universe the three
universes of the ringed topos can agree — for a category with objects and morphisms in
`Type (u + 1)` the ringed topos is a `RingedTopos.{u + 1, u + 1, u + 1}` — which is the seating
at which the derived-category constructions of this library on a ringed topos are stated.

## Main definitions

* `AlgebraicGeometry.Stack.fullToposMorphism`: the morphism of topoi induced by `F` (Stacks 06NW)
  at the universe `max u v w`: inverse image is restriction along `F`, direct image is the right
  Kan extension along `F.op`.
* `AlgebraicGeometry.Stack.liftedStructureSheafInverseImageIso`: the identification
  `f⁻¹𝒪_𝒴 ≅ 𝒪_𝒳` of the lifted structure sheaves (Stacks 06TW).
* `AlgebraicGeometry.Stack.fullRingedToposHom`: the resulting morphism of ringed topoi.

## Main results

* `AlgebraicGeometry.Stack.sheafPushforwardContinuous_liftedStructureSheaf`: restriction along `F`
  of the lifted structure sheaf of `𝒴` is the lifted structure sheaf of `𝒳`, as an equality.
* `AlgebraicGeometry.Stack.fSharpInverseImage_fullRingedToposHom` and
  `AlgebraicGeometry.Stack.isIso_fSharpInverseImage_fullRingedToposHom`: the structure map in
  inverse-image form is that identification, hence invertible.

## Implementation notes

The direct image is a right Kan extension along `F.op`. At the universe `max u v w` of the lifted
sections its pointwise existence needs no hypothesis: the indexing categories
`StructuredArrow Y F.op` have objects in `max v w` and morphisms in `w`, and `Type (max u v w)`
has limits of that size. This is the difference with
`AlgebraicGeometry.Stack.associatedToposMorphism`, which works at the universe `u` of the unlifted
sections and so needs both sites to be essentially small at `u`.

The two categories fibred in groupoids are taken at the same object and morphism universes, so
that the two ringed topoi have the same universe of sections.

## References

* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 06TW](https://stacks.math.columbia.edu/tag/06TW)
* [Stacks Project, Tag 0H0C](https://stacks.math.columbia.edu/tag/0H0C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v} [Category.{w} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS) (F : 𝒳 ⥤ 𝒴)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- **Stacks 06TW, with the sections lifted.** Restriction along a 1-morphism `F` of the lifted
structure sheaf of `𝒴` is the lifted structure sheaf of `𝒳`, as an equality of sheaves of
commutative rings: `p = F ⋙ q` on the nose, both structure sheaves are restrictions of the
structure sheaf of the base, and lifting the sections commutes with restriction. -/
theorem sheafPushforwardContinuous_liftedStructureSheaf (hF : F ⋙ q = p)
    [F.IsContinuous (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)] :
    (F.sheafPushforwardContinuous CommRingCat.{max u v w} (associatedTopology B S hS p τ)
          (associatedTopology B S hS q τ)).obj (liftedStructureSheaf B S hS q τ hq hτ) =
      liftedStructureSheaf B S hS p τ hp hτ := by
  subst hF
  rfl

variable (hF : p.IsFibredOneMorphism q F)

include hp hq hF

/-- The morphism of topoi induced by a 1-morphism of categories fibred in groupoids (Stacks
06NW), at the universe `max u v w` of the lifted structure sheaf: inverse image is restriction
along `F`, direct image is the right Kan extension along `F.op`, which exists at that universe
with no smallness hypothesis on the sites. -/
noncomputable def fullToposMorphism :
    MorphismOfTopoi (fullRingedTopos B S hS p τ (liftedStructureSheaf B S hS p τ hp hτ)).Topos
      (fullRingedTopos B S hS q τ (liftedStructureSheaf B S hS q τ hq hτ)).Topos :=
  have : p.IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  have h := hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))
  have := h.1
  have := h.2
  { inverseImage := F.sheafPushforwardContinuous (Type (max u v w)) _ _
    pushforward := F.sheafPushforwardCocontinuous (Type (max u v w)) _ _
    adj := hF.sheafAdjunctionInheritedTopology (τ.over (B.obj hS)) (Type (max u v w))
    preservesFiniteLimits :=
      hF.preservesFiniteLimits_inverseImage (τ.over (B.obj hS)) (Type (max u v w)) }

/-- The inverse image of `AlgebraicGeometry.Stack.fullToposMorphism` is restriction of sheaves
along `F`. -/
theorem inverseImage_fullToposMorphism :
    have : p.IsFibered := hp.isFibered
    have : q.IsFibered := hq.isFibered
    have := (hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
    (fullToposMorphism B S hS p q F hp hq τ hτ hF).inverseImage =
      F.sheafPushforwardContinuous (Type (max u v w)) (associatedTopology B S hS p τ)
        (associatedTopology B S hS q τ) := rfl

/-- **Stacks 06TW, with the sections lifted.** The inverse image of the lifted structure sheaf
of `𝒴` along the morphism of topoi induced by `F` is the lifted structure sheaf of `𝒳`: the
inverse image of a sheaf of commutative rings along a morphism of topoi presented by restriction
is its restriction, and restriction of the lifted structure sheaf of `𝒴` along `F` is the lifted
structure sheaf of `𝒳`. -/
noncomputable def liftedStructureSheafInverseImageIso :
    (inverseImageCommRingFunctor (fullToposMorphism B S hS p q F hp hq τ hτ hF)).obj
        (liftedStructureSheaf B S hS q τ hq hτ) ≅
      liftedStructureSheaf B S hS p τ hp hτ :=
  have : p.IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  have := (hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  restrictionCommRingIso (associatedTopology B S hS p τ) (associatedTopology B S hS q τ) F
      (liftedStructureSheaf B S hS q τ hq hτ) ≪≫
    eqToIso (sheafPushforwardContinuous_liftedStructureSheaf B S hS p q F hp hq τ hτ hF.comp_eq)

/-- **Stacks 06TW, with the sections lifted.** The morphism of ringed topoi
`(Sh(𝒳_τ), 𝒪_𝒳) ⟶ (Sh(𝒴_τ), 𝒪_𝒴)` induced by a 1-morphism `F` of categories fibred in
groupoids, between the ringed topoi `AlgebraicGeometry.Stack.fullRingedTopos` of Stacks 0H0C
whose structure sheaves are the structure sheaves of Stacks 06TV with their sections lifted to
the universe `max u v w`: the morphism of topoi of Stacks 06NW together with the structure map
adjoint to the identification of the structure sheaves. -/
noncomputable def fullRingedToposHom :
    RingedToposHom (fullRingedTopos B S hS p τ (liftedStructureSheaf B S hS p τ hp hτ))
      (fullRingedTopos B S hS q τ (liftedStructureSheaf B S hS q τ hq hτ)) :=
  RingedToposHom.ofInverseImageIso
    (X := fullRingedTopos B S hS p τ (liftedStructureSheaf B S hS p τ hp hτ))
    (Y := fullRingedTopos B S hS q τ (liftedStructureSheaf B S hS q τ hq hτ))
    (fullToposMorphism B S hS p q F hp hq τ hτ hF)
    (liftedStructureSheafInverseImageIso B S hS p q F hp hq τ hτ hF)

/-- The underlying morphism of topoi of `AlgebraicGeometry.Stack.fullRingedToposHom` is the one of
Stacks 06NW. -/
theorem toToposHom_fullRingedToposHom :
    (fullRingedToposHom B S hS p q F hp hq τ hτ hF).toToposHom =
      fullToposMorphism B S hS p q F hp hq τ hτ hF := rfl

/-- **Stacks 06TW, with the sections lifted.** The structure map of
`AlgebraicGeometry.Stack.fullRingedToposHom` is, in inverse-image form, exactly the
identification of the lifted structure sheaves. -/
theorem fSharpInverseImage_fullRingedToposHom :
    (fullRingedToposHom B S hS p q F hp hq τ hτ hF).fSharpInverseImage =
      (liftedStructureSheafInverseImageIso B S hS p q F hp hq τ hτ hF).hom :=
  RingedToposHom.ofInverseImageIso_fSharpInverseImage
    (X := fullRingedTopos B S hS p τ (liftedStructureSheaf B S hS p τ hp hτ))
    (Y := fullRingedTopos B S hS q τ (liftedStructureSheaf B S hS q τ hq hτ)) _ _

/-- **Stacks 06TW, with the sections lifted.** The structure map of
`AlgebraicGeometry.Stack.fullRingedToposHom` is an isomorphism. -/
theorem isIso_fSharpInverseImage_fullRingedToposHom :
    IsIso (fullRingedToposHom B S hS p q F hp hq τ hτ hF).fSharpInverseImage :=
  RingedToposHom.isIso_fSharpInverseImage_ofInverseImageIso
    (X := fullRingedTopos B S hS p τ (liftedStructureSheaf B S hS p τ hp hτ))
    (Y := fullRingedTopos B S hS q τ (liftedStructureSheaf B S hS q τ hq hτ)) _ _

end AlgebraicGeometry.Stack

end

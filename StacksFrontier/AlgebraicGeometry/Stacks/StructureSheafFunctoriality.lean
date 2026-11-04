module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomOfRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryRingedTopos
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality

/-!
# Functoriality of the structure sheaf of a category fibred in groupoids (Stacks 06TW)

Let `p : 𝒳 ⥤ (Sch/S)` and `q : 𝒴 ⥤ (Sch/S)` be categories fibred in groupoids over the big
fppf category of a scheme `S`, let `F : 𝒳 ⥤ 𝒴` be a 1-morphism between them, and let `τ` be a
topology on the underlying category of schemes which is coarser than the fppf one. The inverse
image along the induced morphism of topoi of the structure sheaf of `𝒴` (Stacks 06TV) *is* the
structure sheaf of `𝒳`, so the morphism of topoi of Stacks 06NW upgrades to a morphism of
ringed topoi whose structure map is an isomorphism.

The identification is an equality of sheaves of commutative rings, not merely an isomorphism:
the inverse image is restriction along `F`, the structure sheaf of `𝒳` is restriction of the
base structure sheaf along `p`, and `p = F ⋙ q` on the nose, so the two presheaves are the same
composite. The transport of the ring operations along restriction of sheaves of sets is again
restriction of sheaves of commutative rings, which is
`Stacks.Sheaves.ToposPullback.restrictionCommRingNatIso`.

## Main definitions

* `AlgebraicGeometry.Stack.associatedToposMorphism`: the morphism of topoi induced by a
  1-morphism, at the universe in which the structure sheaf takes its sections.
* `AlgebraicGeometry.Stack.structureSheafInverseImageIso`: **Stacks 06TW**, the identification
  `f⁻¹O_𝒴 ≅ O_𝒳` of structure sheaves.
* `AlgebraicGeometry.Stack.associatedRingedToposHom`: **Stacks 06TW**, the resulting morphism of
  ringed topoi.

## Main results

* `AlgebraicGeometry.Stack.sheafPushforwardContinuous_structureSheaf`: **Stacks 06TW**, the
  inverse image of the structure sheaf is the structure sheaf, as an equality.
* `AlgebraicGeometry.Stack.inverseImage_associatedRingedToposHom`: the underlying geometric
  inverse image is restriction of sheaves along `F`.
* `AlgebraicGeometry.Stack.fSharpInverseImage_associatedRingedToposHom` and
  `AlgebraicGeometry.Stack.isIso_fSharpInverseImage_associatedRingedToposHom`: **Stacks 06TW**,
  the structure map in inverse-image form is that identification, hence invertible.

## Implementation notes

The topology argument is an arbitrary topology coarser than the fppf one, as in
`AlgebraicGeometry.Stack.structureSheaf`; the five statements of the source are its values at
the five big topologies.

The direct image of the morphism of topoi is a right Kan extension along `F.op`, and the sheaf
condition has to be preserved by the forgetful functors of rings; both follow from essential
smallness of the two categories at the universe of the structure sheaf's sections, which is why
that is assumed. It holds for the sites of the source by
`AlgebraicGeometry.Stack.essentiallySmall_obj`.

## References

* [Stacks Project, Tag 06TW](https://stacks.math.columbia.edu/tag/06TW)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.Stack

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS) (F : 𝒳 ⥤ 𝒴)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- **Stacks 06TW.** The inverse image of the structure sheaf of `𝒴` along a 1-morphism `F` is
the structure sheaf of `𝒳`, as an equality of sheaves of commutative rings: being a 1-morphism
means `p = F ⋙ q` on the nose, and both structure sheaves are restrictions of one and the same
structure sheaf of the base. -/
@[stacks 06TW "the canonical identification of structure sheaves"]
theorem sheafPushforwardContinuous_structureSheaf (hF : F ⋙ q = p)
    [F.IsContinuous (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)] :
    (F.sheafPushforwardContinuous CommRingCat.{u} (associatedTopology B S hS p τ)
          (associatedTopology B S hS q τ)).obj (structureSheaf B S hS q hq τ hτ) =
      structureSheaf B S hS p hp τ hτ := by
  subst hF
  rfl

section ToposMorphism

variable (hF : p.IsFibredOneMorphism q F) [EssentiallySmall.{u} 𝒳] [EssentiallySmall.{u} 𝒴]

/-- The right Kan extensions along `F.op` computing the direct image exist, because the source
site is essentially small at the universe in which the structure sheaf takes its sections. -/
theorem hasPointwiseRightKanExtension_op (G : 𝒳ᵒᵖ ⥤ Type u) :
    F.op.HasPointwiseRightKanExtension G := fun Y ↦ by
  have := hasLimitsOfShape_of_essentiallySmall.{u} (StructuredArrow Y F.op) (Type u)
  infer_instance

include hp hq hF

/-- The morphism of topoi induced by a 1-morphism of categories fibred in groupoids (Stacks
06NW), at the universe in which the structure sheaf takes its sections: inverse image is
restriction along `F`, direct image is the right Kan extension along `F.op`. -/
noncomputable def associatedToposMorphism :
    MorphismOfTopoi (Sheaf (associatedTopology B S hS p τ) (Type u))
      (Sheaf (associatedTopology B S hS q τ) (Type u)) :=
  have : p.IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  have h := hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))
  have := h.1
  have := h.2
  have := hasPointwiseRightKanExtension_op F
  { inverseImage := F.sheafPushforwardContinuous (Type u) _ _
    pushforward := F.sheafPushforwardCocontinuous (Type u) _ _
    adj := hF.sheafAdjunctionInheritedTopology (τ.over (B.obj hS)) (Type u)
    preservesFiniteLimits :=
      hF.preservesFiniteLimits_inverseImage (τ.over (B.obj hS)) (Type u) }

/-- The inverse image of the morphism of topoi of
`AlgebraicGeometry.Stack.associatedToposMorphism` is restriction of sheaves along `F`. -/
theorem inverseImage_associatedToposMorphism :
    have : p.IsFibered := hp.isFibered
    have : q.IsFibered := hq.isFibered
    have := (hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
    (associatedToposMorphism B S hS p q F hp hq τ hF).inverseImage =
      F.sheafPushforwardContinuous (Type u) (associatedTopology B S hS p τ)
        (associatedTopology B S hS q τ) := rfl

include hτ

/-- **Stacks 06TW.** The inverse image of the structure sheaf of `𝒴` is the structure sheaf of
`𝒳`, as sheaves of commutative rings on the associated site of `𝒳`: the inverse image of a
sheaf of commutative rings along a morphism of topoi presented by restriction is restriction,
and restriction of the structure sheaf of `𝒴` along `F` is the structure sheaf of `𝒳`. -/
@[stacks 06TW "the structure sheaves are identified by the morphism of topoi"]
noncomputable def structureSheafInverseImageIso :
    (inverseImageCommRingFunctor
          (associatedToposMorphism B S hS p q F hp hq τ hF)).obj (structureSheaf B S hS q hq τ hτ) ≅
      structureSheaf B S hS p hp τ hτ :=
  have : p.IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  have := (hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  (restrictionCommRingNatIso.{u, w, v, w', v'} (associatedTopology B S hS p τ)
        (associatedTopology B S hS q τ) F).app (structureSheaf B S hS q hq τ hτ) ≪≫
    eqToIso (sheafPushforwardContinuous_structureSheaf B S hS p q F hp hq τ hτ hF.comp_eq)

/-- **Stacks 06TW.** The morphism of ringed topoi induced by a 1-morphism of categories fibred
in groupoids: the morphism of topoi of Stacks 06NW together with the structure map adjoint to
the identification of the structure sheaves. -/
@[stacks 06TW "the morphism of ringed topoi"]
noncomputable def associatedRingedToposHom :
    RingedToposHom (associatedRingedTopos B S hS p hp τ hτ)
      (associatedRingedTopos B S hS q hq τ hτ) :=
  RingedToposHom.ofInverseImageIso
    (X := associatedRingedTopos B S hS p hp τ hτ) (Y := associatedRingedTopos B S hS q hq τ hτ)
    (associatedToposMorphism B S hS p q F hp hq τ hF)
    (structureSheafInverseImageIso B S hS p q F hp hq τ hτ hF)

/-- The underlying morphism of topoi of
`AlgebraicGeometry.Stack.associatedRingedToposHom` is the one of Stacks 06NW. -/
theorem toToposHom_associatedRingedToposHom :
    (associatedRingedToposHom B S hS p q F hp hq τ hτ hF).toToposHom =
      associatedToposMorphism B S hS p q F hp hq τ hF := rfl

/-- **Stacks 06TW.** The structure map of the induced morphism of ringed topoi is, in
inverse-image form, exactly the identification of the structure sheaves. -/
@[stacks 06TW "the structure map is the canonical identification"]
theorem fSharpInverseImage_associatedRingedToposHom :
    (associatedRingedToposHom B S hS p q F hp hq τ hτ hF).fSharpInverseImage =
      (structureSheafInverseImageIso B S hS p q F hp hq τ hτ hF).hom :=
  RingedToposHom.ofInverseImageIso_fSharpInverseImage
    (X := associatedRingedTopos B S hS p hp τ hτ) (Y := associatedRingedTopos B S hS q hq τ hτ) _ _

/-- **Stacks 06TW.** The structure map of the induced morphism of ringed topoi is an
isomorphism, so the morphism of ringed topoi is a morphism of ringed topoi with invertible
structure map. -/
@[stacks 06TW "the structure map is an isomorphism"]
theorem isIso_fSharpInverseImage_associatedRingedToposHom :
    IsIso (associatedRingedToposHom B S hS p q F hp hq τ hτ hF).fSharpInverseImage :=
  RingedToposHom.isIso_fSharpInverseImage_ofInverseImageIso
    (X := associatedRingedTopos B S hS p hp τ hτ) (Y := associatedRingedTopos B S hS q hq τ hτ) _ _

end ToposMorphism

end AlgebraicGeometry.Stack

end

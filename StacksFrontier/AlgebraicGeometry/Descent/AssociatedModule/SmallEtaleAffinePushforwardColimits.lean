module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward
public import StacksFrontier.AlgebraicGeometry.PushforwardColimits.Basic

/-!
# The small étale direct image along an affine morphism commutes with colimits of quasi-coherent
modules

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site whose underlying morphism of schemes
`r` is affine, and let `ε_a : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` be the morphism of small étale
ringed sites of Stacks 070R (2).  This file proves that `(ε_a)_*` preserves the colimit of a
diagram of quasi-coherent `𝒪`-modules on `X_étale`.

Nothing of the sort holds for a general morphism, nor for a general diagram: `(ε_a)_*` is a right
adjoint, so the content is entirely in the affineness of `r` and the quasi-coherence of the
diagram.  It is the small étale form of [Stacks, Tag 01SB]'s colimit input.

## The route

Everything is transported from the Zariski statement
`Stacks.AlgebraicGeometry.PushforwardColimits.preservesColimit_pushforward_of_isAffineHom` across
the equivalence `QCoh(𝒪_X) ≌ QCoh(X_étale, 𝒪)` of [Stacks, Tag 03DX] (2), whose two halves are
`AlgebraicGeometry.SmallEtale.isIso_counit` with
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule` for the counit, and
`AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent` for the unit.

* A diagram `D` of quasi-coherent modules on `X_étale` is the associated module of its own
  Zariski restriction `D ⋙ ε_*`, naturally, by the counit.
* `associatedModulePushforwardNatTrans` is the comparison `(r_*𝓕)^a ⟶ (ε_a)_*(𝓕^a)`, a natural
  transformation of functors `Mod(𝒪_X) ⥤ Mod(Y_étale, 𝒪)` — assembled from the unit of `X_étale`,
  the square of direct images `AlgebraicGeometry.SmallEtale.restrictModulePushforwardSquareIso`
  and the counit of `Y_étale`, so that naturality is free — whose component at a quasi-coherent
  module is the inverse of `AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso`, hence
  invertible.
* `ε^*` preserves all colimits, being a left adjoint
  (`AlgebraicGeometry.SmallEtale.preservesColimitsOfSize_associatedModule`), and the Zariski
  direct image preserves the colimit of the restricted diagram because `r` is affine.  The
  comparison is invertible at the colimit as well, a colimit of quasi-coherent modules being
  quasi-coherent (`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit`).

## Main definitions

* `AlgebraicGeometry.SmallEtale.associatedModulePushforwardNatTrans`: the comparison
  `(r_*𝓕)^a ⟶ (ε_a)_*(𝓕^a)`, as a natural transformation.

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_associatedModulePushforwardNatTrans_app`: the comparison is
  invertible at a quasi-coherent module.
* `AlgebraicGeometry.SmallEtale.preservesColimit_pushforward_of_isAffineHom`: **the small étale
  direct image along an affine morphism preserves colimits of quasi-coherent modules.**

## Implementation notes

`isColimitMapCoconeOfNatTrans` is the piece of plain category theory the transport needs: a
natural transformation between two functors which is invertible at the objects of a diagram and
at the point of a cocone carries the "is a colimit" property of the image of that cocone from one
functor to the other.  It is stated separately because the natural transformation here is *not*
an isomorphism of functors — it is invertible only at quasi-coherent modules — so
`CategoryTheory.Limits.preservesColimit_of_natIso` does not apply.

The hypotheses `HasColimitsOfShape K W.Modules` and `HasColimitsOfShape K (ModuleCat R)` are the
ones the Zariski statement needs in order for the comparison morphisms to exist at all.  For the
shapes of interest — a discrete shape on a type in `Type u`, or a finite shape — they are
automatic.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₂ u₂ u

/-! ### A colimit transfer along a natural transformation -/

namespace Stacks.ColimitTransfer

variable {J : Type u₂} [Category.{v₂} J] {A : Type*} [Category A] {C : Type*} [Category C]

/-- A natural transformation `γ : F ⟶ G` which is invertible at every object of a diagram `D` and
at the point of a cocone `c` over `D` carries "the image of `c` under `F` is a colimit" to "the
image of `c` under `G` is a colimit".

This is the form of transfer needed when `γ` is invertible only on a class of objects, so that
`CategoryTheory.Limits.preservesColimit_of_natIso` — which asks for an isomorphism of functors —
does not apply. -/
def isColimitMapCoconeOfNatTrans {D : J ⥤ A} (F G : A ⥤ C) (γ : F ⟶ G) {c : Cocone D}
    (hobj : ∀ j, IsIso (γ.app (D.obj j))) (hpt : IsIso (γ.app c.pt))
    (hF : IsColimit (F.mapCocone c)) : IsColimit (G.mapCocone c) :=
  haveI : ∀ j, IsIso ((Functor.whiskerLeft D γ).app j) := fun j ↦ hobj j
  haveI : IsIso (Functor.whiskerLeft D γ) := NatIso.isIso_of_isIso_app _
  letI β : D ⋙ F ≅ D ⋙ G := asIso (Functor.whiskerLeft D γ)
  letI e : F.mapCocone c ≅ (Cocone.precompose β.hom).obj (G.mapCocone c) :=
    Cocone.ext (@asIso _ _ _ _ _ hpt) fun j ↦ by
      simp [β]
  IsColimit.precomposeHomEquiv β (G.mapCocone c) (IsColimit.ofIsoColimit hF e)

end Stacks.ColimitTransfer

namespace AlgebraicGeometry.SmallEtale

open Stacks.ColimitTransfer

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-! ### The comparison `(r_*𝓕)^a ⟶ (ε_a)_*(𝓕^a)` -/

/-- **The comparison of the associated module with the direct image**, as a natural
transformation `(r_*𝓕)^a ⟶ (ε_a)_*(𝓕^a)` of functors `Mod(𝒪_X) ⥤ Mod(Y_étale, 𝒪)`.

It is the transpose, under the adjunction of `Y_étale`, of the composite of `r_*` applied to the
unit of `X_étale` with the inverse of the square of direct images
`AlgebraicGeometry.SmallEtale.restrictModulePushforwardSquareIso`.  Written that way its
naturality is the naturality of the unit, of the square and of the counit, which is why it is
spelled out rather than obtained from
`AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso`: that isomorphism carries a
quasi-coherence hypothesis and so defines no natural transformation. -/
def associatedModulePushforwardNatTrans :
    Scheme.Modules.pushforward (schemeHom B a) ⋙ associatedModule B Y.obj Y.property ⟶
      associatedModule B X.obj X.property ⋙
        SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) :=
  (CategoryTheory.mateEquiv (associatedModuleAdjunction B X.obj X.property)
    (associatedModuleAdjunction B Y.obj Y.property)).symm
      (restrictModulePushforwardSquareIso B a).inv

/-- The comparison `(r_*𝓕)^a ⟶ (ε_a)_*(𝓕^a)` is the inverse of
`AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso` at a quasi-coherent module. -/
theorem associatedModulePushforwardNatTrans_app_eq [IsAffineHom (schemeHom B a)]
    (𝓕 : X.obj.Modules) (h𝓕 : SheafOfModules.IsQuasicoherent (R := X.obj.ringCatSheaf) 𝓕) :
    (associatedModulePushforwardNatTrans B a).app 𝓕 =
      (pushforwardAssociatedModuleIso B a 𝓕 h𝓕).inv := by
  simp [associatedModulePushforwardNatTrans, CategoryTheory.mateEquiv,
    pushforwardAssociatedModuleIso, restrictModulePushforwardObjIso]

/-- **The comparison `(r_*𝓕)^a ⟶ (ε_a)_*(𝓕^a)` is invertible at a quasi-coherent module**, for an
affine morphism: it is there the inverse of
`AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso`. -/
theorem isIso_associatedModulePushforwardNatTrans_app [IsAffineHom (schemeHom B a)]
    (𝓕 : X.obj.Modules) (h𝓕 : SheafOfModules.IsQuasicoherent (R := X.obj.ringCatSheaf) 𝓕) :
    IsIso ((associatedModulePushforwardNatTrans B a).app 𝓕) := by
  rw [associatedModulePushforwardNatTrans_app_eq B a 𝓕 h𝓕]
  infer_instance

/-! ### The colimit statement -/

variable {K : Type u₂} [Category.{v₂} K] [HasColimitsOfShape K AddCommGrpCat.{u}]
  [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
  [∀ W : Scheme.{u}, HasColimitsOfShape K W.Modules]

/-- **The small étale direct image along an affine morphism preserves colimits of quasi-coherent
modules.**  For `a : X ⟶ Y` a morphism of schemes of a big étale site whose underlying morphism of
schemes is affine, the direct image `(ε_a)_*` along the morphism of small étale ringed sites of
Stacks 070R (2) preserves the colimit of a diagram of quasi-coherent `𝒪`-modules on `X_étale`.

This is the small étale form of the colimit input of [Stacks, Tag 01SB].  The diagram is the
associated module of its Zariski restriction through the counit of [Stacks, Tag 03DX] (2); the
Zariski restriction is a diagram of quasi-coherent `𝒪_X`-modules whose colimit the Zariski direct
image preserves, `r` being affine; and the comparison
`AlgebraicGeometry.SmallEtale.associatedModulePushforwardNatTrans` is invertible at every module
of that diagram and at its colimit. -/
theorem preservesColimit_pushforward_of_isAffineHom [IsAffineHom (schemeHom B a)]
    {D : K ⥤ SheafOfModules.{u} (structureSheaf B X.obj X.property)}
    (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite) :
    PreservesColimit D (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)) := by
  have hD' : ∀ k, ((D ⋙ restrictModule B X.obj X.property).obj k).IsQuasicoherent := fun k ↦
    isQuasicoherent_restrictModule B X.obj X.property (D.obj k) (hD k)
  -- the diagram is the associated module of its Zariski restriction
  let α : (D ⋙ restrictModule B X.obj X.property) ⋙ associatedModule B X.obj X.property ≅ D :=
    NatIso.ofComponents
      (fun k ↦ @asIso _ _ _ _ _
        (isIso_counit B X.obj X.property (D.obj k) (hD k) (hD' k)))
      fun φ ↦ (associatedModuleAdjunction B X.obj X.property).counit.naturality (D.map φ)
  have hqc : (colimit (D ⋙ restrictModule B X.obj X.property)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit _ hD'
  have hpf : PreservesColimit (D ⋙ restrictModule B X.obj X.property)
      (Scheme.Modules.pushforward (schemeHom B a)) :=
    Stacks.AlgebraicGeometry.PushforwardColimits.preservesColimit_pushforward_of_isAffineHom
      (schemeHom B a) hD'
  -- the colimit of the Zariski restriction, pushed up
  have key : PreservesColimit
      ((D ⋙ restrictModule B X.obj X.property) ⋙ associatedModule B X.obj X.property)
      (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves (associatedModule B X.obj X.property)
        (colimit.isColimit (D ⋙ restrictModule B X.obj X.property)))
      (isColimitMapCoconeOfNatTrans
        (Scheme.Modules.pushforward (schemeHom B a) ⋙ associatedModule B Y.obj Y.property)
        (associatedModule B X.obj X.property ⋙
          SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
        (associatedModulePushforwardNatTrans B a)
        (fun k ↦ isIso_associatedModulePushforwardNatTrans_app B a _ (hD' k))
        (isIso_associatedModulePushforwardNatTrans_app B a _ hqc)
        (isColimitOfPreserves _
          (colimit.isColimit (D ⋙ restrictModule B X.obj X.property))))
  exact preservesColimit_of_iso_diagram _ α

end AlgebraicGeometry.SmallEtale

end

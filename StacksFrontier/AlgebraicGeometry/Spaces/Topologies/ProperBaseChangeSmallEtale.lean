module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleBaseChangeMate

/-!
# Proper base change for sheaves of sets on the small étale sites of algebraic spaces

Let `S` be a scheme, let `f : X ⟶ Y` and `g : Y' ⟶ Y` be morphisms of algebraic spaces over `S`
with `f` proper, and let `X' = Y' ×_Y X` with projections `f' : X' ⟶ Y'` and `g' : X' ⟶ X`. For
every sheaf of sets `ℱ` on `X_étale` the canonical base-change map
`g⁻¹ f_* ℱ ⟶ f'_* (g')⁻¹ ℱ` is an isomorphism. This is [Stacks, Tag 0DG0].

The canonical map is `AlgebraicGeometry.Space.properBaseChangeMap`, the mate of the comparison of
the two composite direct images of the square on the small étale topoi. Its invertibility is
deduced from that of the same 2-cell on the spaces-étale topoi,
`AlgebraicGeometry.Space.spacesToposBaseChangeSquare_isIso_of_isProper`, proved by reduction to
schemes by Chow's lemma (Stacks 089J) and the descent sequence of Stacks 0DFX, then the case of
schemes (Stacks 0A3U).

## Main definitions

* `AlgebraicGeometry.Space.smallToposBaseChangeTransport`: the base-change 2-cell of a cartesian
  square on the spaces-étale topoi, carried to the small étale topoi along the comparison
  equivalences of Stacks 03G1. No hypothesis on the square is made.

## Main results

* `AlgebraicGeometry.Space.properBaseChangeMap_eq_smallToposBaseChangeTransport`: the transported
  2-cell is the canonical base-change map of the small étale topoi.
* `AlgebraicGeometry.Space.isIso_properBaseChangeMap_of_isIso_spacesToposBaseChangeSquare`: the
  canonical base-change map on the small étale topoi is invertible as soon as the one on the
  spaces-étale topoi is.
* `AlgebraicGeometry.Space.isIso_properBaseChangeMap_of_isProper`: proper base change; for `f`
  proper the canonical base-change map on the small étale topoi is invertible.

## Implementation notes

The étale case of the transport, `AlgebraicGeometry.Space.smallToposBaseChangeSquareIso`, uses the
étaleness of `g` only to know that the spaces-étale 2-cell is invertible; the construction here is
the same with the spaces-étale 2-cell kept as a natural transformation, so it applies to every
cartesian square.

## References

* [Stacks Project, Tag 0DG0](https://stacks.math.columbia.edu/tag/0DG0)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS}
  (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The base-change 2-cell of the spaces-étale topoi of a cartesian square, whiskered by the
comparison equivalences of Stacks 03G1 into the spaces-étale topos of `Y'`. -/
def smallToposBaseChangeTransportLeft (sq : IsPullback i f' f g) :
    (smallEtaleToposEquiv B S hS X).functor ⋙
        (smallToposMorphism B S hS f).pushforward ⋙
          (smallToposMorphism B S hS g).inverseImage ⟶
      ((spacesBaseChange_isMorphismOfSites B S hS i).morphismOfTopoi).inverseImage ⋙
        (spacesBaseChange B S hS f').functor.sheafPushforwardContinuous (Type (u + 1))
            (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X') ⋙
          (smallEtaleToposEquiv B S hS Y').functor :=
  (Functor.isoWhiskerRight (smallToposMorphism_comparison B S hS f)
      (smallToposMorphism B S hS g).inverseImage).hom ≫
    (Functor.isoWhiskerLeft
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X))
      (smallToposMorphism_inverseImage_comparison B S hS g)).hom ≫
    Functor.whiskerRight (spacesToposBaseChangeSquare B S hS i f' f g sq)
      (smallEtaleToposEquiv B S hS Y').functor

/-- The base-change 2-cell of the spaces-étale topoi of a cartesian square, carried to the small
étale topoi and precomposed with the comparison equivalence of `X`. -/
def smallToposBaseChangeTransportBig (sq : IsPullback i f' f g) :
    (smallEtaleToposEquiv B S hS X).functor ⋙
        (smallToposMorphism B S hS f).pushforward ⋙
          (smallToposMorphism B S hS g).inverseImage ⟶
      (smallEtaleToposEquiv B S hS X).functor ⋙
        (smallToposMorphism B S hS i).inverseImage ⋙
          (smallToposMorphism B S hS f').pushforward :=
  smallToposBaseChangeTransportLeft B S hS i f' f g sq ≫
    (smallToposBaseChangeHalfRight B S hS i f').inv

/-- Composing the transported 2-cell with the right half returns the spaces-étale 2-cell
whiskered by the comparisons. -/
theorem smallToposBaseChangeTransportBig_comp (sq : IsPullback i f' f g) :
    smallToposBaseChangeTransportBig B S hS i f' f g sq ≫
        (smallToposBaseChangeHalfRight B S hS i f').hom =
      smallToposBaseChangeTransportLeft B S hS i f' f g sq := by
  rw [smallToposBaseChangeTransportBig, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The base-change 2-cell of a cartesian square, transported to the small étale topoi.** The
spaces-étale base-change 2-cell `AlgebraicGeometry.Space.spacesToposBaseChangeSquare` carried
along the comparison equivalences of Stacks 03G1. -/
def smallToposBaseChangeTransport (sq : IsPullback i f' f g) :
    (smallToposMorphism B S hS f).pushforward ⋙
        (smallToposMorphism B S hS g).inverseImage ⟶
      (smallToposMorphism B S hS i).inverseImage ⋙
        (smallToposMorphism B S hS f').pushforward :=
  ((Functor.whiskeringLeft _ _ _).obj (smallEtaleToposEquiv B S hS X).functor).preimage
    (smallToposBaseChangeTransportBig B S hS i f' f g sq)

/-- The transported 2-cell is compatible, through the comparison equivalences of Stacks 03G1,
with the spaces-étale base-change 2-cell. -/
theorem smallToposBaseChangeTransport_comparison (sq : IsPullback i f' f g)
    (c : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))) :
    (smallToposMorphism B S hS g).inverseImage.map
          ((smallToposMorphism_comparison B S hS f).hom.app c) ≫
        (smallToposMorphism_inverseImage_comparison B S hS g).hom.app
          (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj c) ≫
        (smallEtaleToposEquiv B S hS Y').functor.map
          ((spacesToposBaseChangeSquare B S hS i f' f g sq).app c) =
      (smallToposBaseChangeTransport B S hS i f' f g sq).app
          ((smallEtaleToposEquiv B S hS X).functor.obj c) ≫
        (smallToposMorphism B S hS f').pushforward.map
          ((smallToposMorphism_inverseImage_comparison B S hS i).hom.app c) ≫
        (smallToposMorphism_comparison B S hS f').hom.app
          (((spacesBaseChange_isMorphismOfSites B S hS i).morphismOfTopoi).inverseImage.obj c) := by
  have hpre : (smallToposBaseChangeTransport B S hS i f' f g sq).app
      ((smallEtaleToposEquiv B S hS X).functor.obj c) =
        (smallToposBaseChangeTransportBig B S hS i f' f g sq).app c :=
    NatTrans.congr_app
      (((Functor.whiskeringLeft _ _ _).obj (smallEtaleToposEquiv B S hS X).functor).map_preimage
        (smallToposBaseChangeTransportBig B S hS i f' f g sq)) c
  rw [hpre]
  exact (NatTrans.congr_app (smallToposBaseChangeTransportBig_comp B S hS i f' f g sq) c).symm

/-- **The transported 2-cell is a mate of the direct-image comparison.** For every cartesian
square of algebraic spaces, the mate of the transported 2-cell is the comparison of the two
composite direct images on the small étale topoi. -/
theorem mateEquiv_smallToposBaseChangeTransport (sq : IsPullback i f' f g) :
    mateEquiv (smallToposMorphism B S hS i).adj (smallToposMorphism B S hS g).adj
        (smallToposBaseChangeTransport B S hS i f' f g sq) =
      (smallToposPushforwardBaseChange B S hS f g f' i sq.w).hom := by
  have key := mateEquiv_restrictFullyFaithful_app
    (iC := (smallEtaleToposEquiv B S hS X).functor)
    (iD := (smallEtaleToposEquiv B S hS X').functor)
    (iE := (smallEtaleToposEquiv B S hS Y).functor)
    (iF := (smallEtaleToposEquiv B S hS Y').functor)
    (smallEtaleToposEquiv B S hS X).fullyFaithfulFunctor
    (smallEtaleToposEquiv B S hS X').fullyFaithfulFunctor
    (smallEtaleToposEquiv B S hS Y).fullyFaithfulFunctor
    (smallEtaleToposEquiv B S hS Y').fullyFaithfulFunctor
    (smallToposMorphism B S hS i).adj (smallToposMorphism B S hS g).adj
    (smallToposMorphism_inverseImage_comparison B S hS i)
    (smallToposMorphism_comparison B S hS i)
    (smallToposMorphism_inverseImage_comparison B S hS g)
    (smallToposMorphism_comparison B S hS g)
    (smallToposMorphism_comparison B S hS f) (smallToposMorphism_comparison B S hS f')
    (spacesToposBaseChangeSquare B S hS i f' f g sq)
    (smallToposBaseChangeTransport B S hS i f' f g sq)
    (smallToposBaseChangeTransport_comparison B S hS i f' f g sq)
  rw [smallToposMorphism_restrict_adj, smallToposMorphism_restrict_adj] at key
  have hms : mateEquiv ((spacesBaseChange_isMorphismOfSites B S hS i).morphismOfTopoi).adj
        ((spacesBaseChange_isMorphismOfSites B S hS g).morphismOfTopoi).adj
        (spacesToposBaseChangeSquare B S hS i f' f g sq) =
      spacesPushforwardCompSquare B S hS i f' f g sq.w :=
    (mateEquiv _ _).apply_symm_apply _
  refine ((Functor.whiskeringLeft _ _ _).obj
    (smallEtaleToposEquiv B S hS X').functor).map_injective (NatTrans.ext (funext fun d => ?_))
  have e := congrArg (fun t : (((spacesBaseChange B S hS i).functor.sheafPushforwardContinuous
        (Type (u + 1)) (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS X') ⋙
        (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) ⟶
        ((spacesBaseChange B S hS f').functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X') ⋙
        (spacesBaseChange B S hS g).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS Y'))) =>
      (smallToposMorphism B S hS f).pushforward.map
          ((smallToposMorphism_comparison B S hS i).hom.app d) ≫
        (smallToposMorphism_comparison B S hS f).hom.app
          (((spacesBaseChange B S hS i).functor.sheafPushforwardContinuous (Type (u + 1))
            (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS X')).obj d) ≫
        (smallEtaleToposEquiv B S hS Y).functor.map (t.app d)) hms
  have hfin := (key d).symm.trans (e.trans
    (smallToposPushforwardBaseChange_comparison B S hS i f' f g sq d))
  exact (Iso.cancel_iso_hom_right _ _
    ((smallToposMorphism B S hS g).pushforward.mapIso
        (Iso.app (smallToposMorphism_comparison B S hS f') d) ≪≫
      Iso.app (smallToposMorphism_comparison B S hS g)
        (((spacesBaseChange B S hS f').functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X')).obj d))).mp hfin

/-- The canonical base-change map of every cartesian square on the small étale topoi is the
transport of the spaces-étale base-change 2-cell. -/
theorem properBaseChangeMap_eq_smallToposBaseChangeTransport (sq : IsPullback i f' f g) :
    properBaseChangeMap B S hS f g f' i sq = smallToposBaseChangeTransport B S hS i f' f g sq :=
  (Equiv.symm_apply_eq _).mpr (mateEquiv_smallToposBaseChangeTransport B S hS i f' f g sq).symm

/-- The canonical base-change map of a cartesian square on the small étale topoi is invertible as
soon as the base-change 2-cell of the same square on the spaces-étale topoi is. -/
theorem isIso_properBaseChangeMap_of_isIso_spacesToposBaseChangeSquare (sq : IsPullback i f' f g)
    [IsIso (spacesToposBaseChangeSquare B S hS i f' f g sq)] :
    IsIso (properBaseChangeMap B S hS f g f' i sq) := by
  rw [properBaseChangeMap_eq_smallToposBaseChangeTransport]
  have : IsIso (smallToposBaseChangeTransportLeft B S hS i f' f g sq) := by
    have h : smallToposBaseChangeTransportLeft B S hS i f' f g sq =
        (Functor.isoWhiskerRight (smallToposMorphism_comparison B S hS f)
            (smallToposMorphism B S hS g).inverseImage ≪≫
          Functor.isoWhiskerLeft
            ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
              (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X))
            (smallToposMorphism_inverseImage_comparison B S hS g) ≪≫
          Functor.isoWhiskerRight (asIso (spacesToposBaseChangeSquare B S hS i f' f g sq))
            (smallEtaleToposEquiv B S hS Y').functor).hom := rfl
    rw [h]
    exact Iso.isIso_hom _
  have : IsIso (smallToposBaseChangeTransportBig B S hS i f' f g sq) := by
    rw [smallToposBaseChangeTransportBig]
    infer_instance
  have : IsIso (((Functor.whiskeringLeft _ _ _).obj
      (smallEtaleToposEquiv B S hS X).functor).map
        (smallToposBaseChangeTransport B S hS i f' f g sq)) := by
    rw [smallToposBaseChangeTransport, Functor.map_preimage]
    infer_instance
  exact isIso_of_fully_faithful ((Functor.whiskeringLeft _ _ _).obj
    (smallEtaleToposEquiv B S hS X).functor) _

/-- Let `S` be a scheme, let `f : X ⟶ Y` and `g : Y' ⟶ Y` be morphisms of algebraic spaces over
`S` with `f` proper, and let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be cartesian, that is `X' = Y' ×_Y X` with projections `f'` and `g'`. Then for every sheaf of
sets `ℱ` on `X_étale` the canonical map `g⁻¹ f_* ℱ ⟶ f'_* (g')⁻¹ ℱ` is an isomorphism, naturally
in `ℱ`: the base-change map `AlgebraicGeometry.Space.properBaseChangeMap` of the small étale
topoi is invertible. -/
@[stacks 0DG0]
theorem isIso_properBaseChangeMap_of_isProper (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (sq : IsPullback g' f' f g) :
    IsIso (properBaseChangeMap B S hS f g f' g' sq) := by
  have := spacesToposBaseChangeSquare_isIso_of_isProper B S hS f hf g g' f' sq
  exact isIso_properBaseChangeMap_of_isIso_spacesToposBaseChangeSquare B S hS g' f' f g sq

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RelocalizationFibreSlice
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RelocalizedMorphismComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.SliceBeckChevalley
import StacksCore.Tactic.StacksAttribute

/-!
# The naturality square of the relocalized morphism of ringed topoi

Let `(f, f♯) : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi, let `G` be a sheaf on `D`,
let `F` be a sheaf on `C` and let `s : F ⟶ f⁻¹G` be a morphism of sheaves; let `G'`, `F'`, `s'` be
a second such datum together with `b : G' ⟶ G` and `a : F' ⟶ F` such that `a ≫ s = s' ≫ f⁻¹b`. The
last assertion of Stacks 04J8 is that the square

```
  (Sh(C)/F', O_{F'}) --(f_{s'}, f_{s'}♯)--> (Sh(D)/G', O'_{G'})
        |                                           |
   (j_{F'/F}, …)                               (j_{G'/G}, …)
        v                                           v
  (Sh(C)/F,  O_F)   --(f_s,  f_s♯)  -->     (Sh(D)/G,  O'_G)
```

commutes, the horizontal arrows being the relocalization morphisms of Stacks 04J4. This file proves
it on inverse images, as a square of topoi, and as a square of ringed topoi.

The square is the pasting of two smaller ones along the factorization `f_s = f'_G ∘ j_s` of
Stacks 04J8: the relocalization square `j_{f⁻¹b} ∘ j_{s'} = j_s ∘ j_a`, which holds because both
composites are the relocalization along the one morphism `a ≫ s = s' ≫ f⁻¹b`, and the square
comparing the localized morphism `f'` of Stacks 04IF at `G` with the one at `G'`, which on inverse
images is `localizedCompRelocalizationIso`.

All names are in the namespace `AlgebraicGeometry.RingedToposHom`.

## Main definitions

* `relocalizationCompTwoIso`: relocalizing along `s : F ⟶ H` after relocalizing along `a : F' ⟶ F`
  is relocalizing along `a ≫ s`, as a 2-isomorphism of ringed topoi.
* `relocalizationSquareTwoIso`: consequently a commuting square of sheaves gives a commuting square
  of relocalization morphisms of ringed topoi.
* `relocalizedNaturalityInverseImageSquare`: the naturality square of Stacks 04J8 on inverse
  images.
* `relocalizedNaturalityToposSquare`: the naturality square as a square of topoi, the comparison of
  the two direct images conjugate to the previous one.
* `localizedCompRelocalizationRingedSquare`: the comparison of the localized morphism of
  Stacks 04IF at `G` with the one at `G'`, as a 2-isomorphism of *ringed* topoi.
* `relocalizedNaturalitySquare`: the naturality square as a square of *ringed* topoi.

## Main results

* `relocalizationInverseImage_comp`: the inverse images of two relocalization morphisms compose to
  the inverse image of the relocalization along the composite, on the nose.
* `relocalizationInverseImage_square`: hence a commuting square of sheaves gives an *equality* of
  the two composite relocalization inverse images.
* `inverseImageCompLocalizationIso_baseChange`: Stacks 04IF's comparison of inverse images at `G`,
  restricted along the relocalization at `f⁻¹b`, is Stacks 04IF's comparison at `G'`.

## References

* [Stacks Project, Tag 04J8](https://stacks.math.columbia.edu/tag/04J8)
* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 04H1](https://stacks.math.columbia.edu/tag/04H1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.RingedToposHom

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp

/-! ### Composing two relocalizations -/

/-- **Relocalizing twice is relocalizing along the composite, on inverse images.** For `a : F' ⟶ F`
and `s : F ⟶ H` the two inverse images are the same functor on the nose. -/
theorem relocalizationInverseImage_comp (W : RingedTopos.{u, u, u}) {F' F H : W.Topos}
    (a : F' ⟶ F) (s : F ⟶ H) :
    (W.relocalizationMorphism s).toToposHom.inverseImage ⋙
        (W.relocalizationMorphism a).toToposHom.inverseImage =
      (W.relocalizationMorphism (a ≫ s)).toToposHom.inverseImage :=
  rfl

/-- **The relocalization square on inverse images.** If `a ≫ s = s' ≫ c` then the two composite
relocalization inverse images are equal. -/
theorem relocalizationInverseImage_square (W : RingedTopos.{u, u, u}) {F' F H' H : W.Topos}
    (a : F' ⟶ F) (s : F ⟶ H) (s' : F' ⟶ H') (c : H' ⟶ H) (h : a ≫ s = s' ≫ c) :
    (W.relocalizationMorphism s).toToposHom.inverseImage ⋙
        (W.relocalizationMorphism a).toToposHom.inverseImage =
      (W.relocalizationMorphism c).toToposHom.inverseImage ⋙
        (W.relocalizationMorphism s').toToposHom.inverseImage :=
  (relocalizationInverseImage_comp W a s).trans
    ((congrArg (fun m ↦ (W.relocalizationMorphism m).toToposHom.inverseImage) h).trans
      (relocalizationInverseImage_comp W s' c).symm)

/-- **Stacks 04J4: the relocalization morphisms of ringed topoi compose.** Relocalizing along
`s : F ⟶ H` after relocalizing along `a : F' ⟶ F` is relocalizing along `a ≫ s`. -/
@[stacks 04J4 "the relocalization morphisms of ringed topoi compose"]
noncomputable def relocalizationCompTwoIso (W : RingedTopos.{u, u, u}) {F' F H : W.Topos}
    (a : F' ⟶ F) (s : F ⟶ H) :
    TwoIso (A := W.localizedRingedTopos F') (B := W.localizedRingedTopos H)
      (comp (X := W.localizedRingedTopos F') (Y := W.localizedRingedTopos F)
        (Z := W.localizedRingedTopos H) (W.relocalizationMorphism s) (W.relocalizationMorphism a))
      (W.relocalizationMorphism (a ≫ s)) :=
  TwoIso.ofInverseImageIso (A := W.localizedRingedTopos F') (B := W.localizedRingedTopos H)
    (Iso.refl _) (by
      have ha := forgetRing_relocalizationMorphism_fSharpInverseImage W a
      have hs := forgetRing_relocalizationMorphism_fSharpInverseImage W s
      have hq := forgetRing_relocalizationMorphism_fSharpInverseImage W (a ≫ s)
      have hp : (W.localizedRingedTopos F').forgetRing.map
            (comp (X := W.localizedRingedTopos F') (Y := W.localizedRingedTopos F)
              (Z := W.localizedRingedTopos H) (W.relocalizationMorphism s)
              (W.relocalizationMorphism a)).fSharpInverseImage =
          𝟙 ((W.localizedRingedTopos F').forgetRing.obj (W.localizedRingedTopos F').O) :=
        (comp_fSharpInverseImage_forget
            (X := W.localizedRingedTopos F') (Y := W.localizedRingedTopos F)
            (Z := W.localizedRingedTopos H) (W.relocalizationMorphism s)
            (W.relocalizationMorphism a)).trans
          ((congrArg (fun z ↦ (W.relocalizationMorphism a).toToposHom.inverseImage.map
              ((W.localizedRingedTopos F).forgetRing.map
                (W.relocalizationMorphism s).fSharpInverseImage) ≫ z) ha).trans
            ((Category.comp_id _).trans
              ((congrArg (fun z ↦ (W.relocalizationMorphism a).toToposHom.inverseImage.map z)
                  hs).trans
                ((W.relocalizationMorphism a).toToposHom.inverseImage.map_id _))))
      exact (Category.id_comp _).trans (hp.trans hq.symm))

/-- **Stacks 04J4: a commuting square of sheaves gives a commuting square of relocalizations.** For
`a ≫ s = s' ≫ c`, relocalizing along `s'` and then along `c` agrees with relocalizing along `a` and
then along `s`, as morphisms of ringed topoi. -/
@[stacks 04J4 "a commuting square of sheaves gives a commuting square of relocalization
  morphisms of ringed topoi"]
noncomputable def relocalizationSquareTwoIso (W : RingedTopos.{u, u, u})
    {F' F H' H : W.Topos} (a : F' ⟶ F) (s : F ⟶ H) (s' : F' ⟶ H') (c : H' ⟶ H)
    (h : a ≫ s = s' ≫ c) :
    TwoIso (A := W.localizedRingedTopos F') (B := W.localizedRingedTopos H)
      (comp (X := W.localizedRingedTopos F') (Y := W.localizedRingedTopos H')
        (Z := W.localizedRingedTopos H) (W.relocalizationMorphism c)
        (W.relocalizationMorphism s'))
      (comp (X := W.localizedRingedTopos F') (Y := W.localizedRingedTopos F)
        (Z := W.localizedRingedTopos H) (W.relocalizationMorphism s)
        (W.relocalizationMorphism a)) := by
  refine (relocalizationCompTwoIso W s' c).trans ?_
  rw [← h]
  exact (relocalizationCompTwoIso W a s).symm

/-! ### The naturality square of Stacks 04J8 -/

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom X Y) {G G' : Y.Topos} {F F' : X.Topos}
  (s : F ⟶ f.toToposHom.inverseImage.obj G) (b : G' ⟶ G) (a : F' ⟶ F)
  (s' : F' ⟶ f.toToposHom.inverseImage.obj G')

/-- **Stacks 04J8**, the naturality square on inverse images:
`(j_{F'/F})⁻¹ ∘ (f_s)⁻¹ ≅ (f_{s'})⁻¹ ∘ (j_{G'/G})⁻¹`.

Along the factorization `f_s = f'_G ∘ j_s` this is the relocalization square
`relocalizationInverseImage_square` for `a ≫ s = s' ≫ f⁻¹b`, whiskered by the inverse image of
`f'_G`, pasted with the comparison `localizedCompRelocalizationIso` of the localized morphism
of Stacks 04IF at `G` with the one at `G'`, whiskered by the inverse image of the relocalization
along `s'`. -/
@[stacks 04J8 "the naturality square of the last assertion, on inverse images"]
noncomputable def relocalizedNaturalityInverseImageSquare
    (hs : a ≫ s = s' ≫ f.toToposHom.inverseImage.map b) :
    (comp (X := X.localizedRingedTopos F') (Y := X.localizedRingedTopos F)
        (Z := Y.localizedRingedTopos G) (f.relocalized s)
        (X.relocalizationMorphism a)).toToposHom.inverseImage ≅
      (comp (X := X.localizedRingedTopos F') (Y := Y.localizedRingedTopos G')
        (Z := Y.localizedRingedTopos G) (Y.relocalizationMorphism b)
        (f.relocalized s')).toToposHom.inverseImage :=
  Functor.associator (f.localized G).toToposHom.inverseImage
      (X.relocalizationMorphism s).toToposHom.inverseImage
      (X.relocalizationMorphism a).toToposHom.inverseImage ≪≫
    Functor.isoWhiskerLeft (f.localized G).toToposHom.inverseImage
      (eqToIso (relocalizationInverseImage_square X a s s'
        (f.toToposHom.inverseImage.map b) hs)) ≪≫
    (Functor.associator (f.localized G).toToposHom.inverseImage
      (X.relocalizationMorphism (f.toToposHom.inverseImage.map b)).toToposHom.inverseImage
      (X.relocalizationMorphism s').toToposHom.inverseImage).symm ≪≫
    Functor.isoWhiskerRight (f.localizedCompRelocalizationIso b)
      (X.relocalizationMorphism s').toToposHom.inverseImage ≪≫
    Functor.associator (Y.relocalizationMorphism b).toToposHom.inverseImage
      (f.localized G').toToposHom.inverseImage
      (X.relocalizationMorphism s').toToposHom.inverseImage

/-- **Stacks 04J8**, the naturality square as a square of *topoi*: the comparison of the two direct
images conjugate to `relocalizedNaturalityInverseImageSquare`. -/
@[stacks 04J8 "the naturality square of the last assertion, as a square of topoi"]
noncomputable def relocalizedNaturalityToposSquare
    (hs : a ≫ s = s' ≫ f.toToposHom.inverseImage.map b) :
    (comp (X := X.localizedRingedTopos F') (Y := Y.localizedRingedTopos G')
        (Z := Y.localizedRingedTopos G) (Y.relocalizationMorphism b)
        (f.relocalized s')).toToposHom.pushforward ≅
      (comp (X := X.localizedRingedTopos F') (Y := X.localizedRingedTopos F)
        (Z := Y.localizedRingedTopos G) (f.relocalized s)
        (X.relocalizationMorphism a)).toToposHom.pushforward :=
  conjugateIsoEquiv
    (comp (X := X.localizedRingedTopos F') (Y := Y.localizedRingedTopos G')
      (Z := Y.localizedRingedTopos G) (Y.relocalizationMorphism b)
      (f.relocalized s')).toToposHom.adj
    (comp (X := X.localizedRingedTopos F') (Y := X.localizedRingedTopos F)
      (Z := Y.localizedRingedTopos G) (f.relocalized s)
      (X.relocalizationMorphism a)).toToposHom.adj
    (f.relocalizedNaturalityInverseImageSquare s b a s' hs)

/-! ### The square of ringed topoi -/

/-- **Stacks 04IF's comparison of inverse images is compatible with a change of the sheaf on the
target.** For `b : G' ⟶ G`, the comparison `f⁻¹ ∘ j_{f⁻¹G}⁻¹ ≅ j_G⁻¹ ∘ (f'_G)⁻¹` of Stacks 04IF
at `G`, restricted along the relocalization at `f⁻¹b` and then compared by
`localizedCompRelocalizationIso`, is the comparison at `G'`. -/
theorem inverseImageCompLocalizationIso_baseChange (H : Y.Topos) :
    (X.relocalizationMorphism (f.toToposHom.inverseImage.map b)).toToposHom.inverseImage.map
        ((f.inverseImageCompLocalizationIso G).hom.app H) ≫
      (f.localizedCompRelocalizationIso b).hom.app
        ((Y.localizationMorphism G).toToposHom.inverseImage.obj H) =
    (f.inverseImageCompLocalizationIso G').hom.app H := by
  have := f.toToposHom.preservesFiniteLimits
  have hX : (X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G')).hom.app
        (f.toToposHom.inverseImage.obj H) =
      (X.relocalizationInverseImageSliceIso (f.toToposHom.inverseImage.map b)).hom.app
          ((X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj
            (f.toToposHom.inverseImage.obj H)) ≫
        ((Over.pullback (f.toToposHom.inverseImage.map b)).map
            ((X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G)).hom.app
              (f.toToposHom.inverseImage.obj H)) ≫
          (toOverCompPullbackIso (f.toToposHom.inverseImage.map b)).hom.app
            (f.toToposHom.inverseImage.obj H)) :=
    congrArg (fun i => NatTrans.app (Iso.hom i) (f.toToposHom.inverseImage.obj H))
      (RingedTopos.localizationInverseImageIso_eq_relocalization X
        (f.toToposHom.inverseImage.map b))
  have hY : (Y.localizationInverseImageIso G').inv.app H =
      ((toOverCompPullbackIso b).inv.app H ≫
          (Over.pullback b).map ((Y.localizationInverseImageIso G).inv.app H)) ≫
        (Y.relocalizationInverseImageSliceIso b).inv.app
          ((Y.localizationMorphism G).toToposHom.inverseImage.obj H) :=
    congrArg (fun i => NatTrans.app (Iso.inv i) H)
      (RingedTopos.localizationInverseImageIso_eq_relocalization Y b)
  have hYv : (Over.pullback b).map ((Y.localizationInverseImageIso G).inv.app H) ≫
        (Y.relocalizationInverseImageSliceIso b).inv.app
          ((Y.localizationMorphism G).toToposHom.inverseImage.obj H) =
      (toOverCompPullbackIso b).hom.app H ≫ (Y.localizationInverseImageIso G').inv.app H := by
    refine Eq.symm ?_
    refine Eq.trans (whisker_eq _ hY) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (Category.assoc _ _ _).symm _) ?_
    refine Eq.trans (eq_whisker (eq_whisker ((toOverCompPullbackIso b).hom_inv_id_app H) _) _) ?_
    exact eq_whisker (Category.id_comp _) _
  have hnat : (Over.pullback (f.toToposHom.inverseImage.map b)).map
          ((f.toToposHom.over G).inverseImage.map
            ((Y.localizationInverseImageIso G).inv.app H)) ≫
        (Over.postPullbackIso f.toToposHom.inverseImage b).inv.app
          ((Y.localizationEquivalence G).functor.obj
            ((Y.localizationMorphism G).toToposHom.inverseImage.obj H)) =
      (Over.postPullbackIso f.toToposHom.inverseImage b).inv.app ((toOver G).obj H) ≫
        (Over.post f.toToposHom.inverseImage).map
          ((Over.pullback b).map ((Y.localizationInverseImageIso G).inv.app H)) :=
    (Over.postPullbackIso f.toToposHom.inverseImage b).inv.naturality
      ((Y.localizationInverseImageIso G).inv.app H)
  have hbc := f.toToposHom.inverseImageCompToOverIso_baseChange b H
  have hD2 : (Over.pullback (f.toToposHom.inverseImage.map b)).map
            ((f.toToposHom.inverseImageCompToOverIso G).hom.app H ≫
              (f.toToposHom.over G).inverseImage.map
                ((Y.localizationInverseImageIso G).inv.app H)) ≫
          ((Over.postPullbackIso f.toToposHom.inverseImage b).inv.app
              ((Y.localizationEquivalence G).functor.obj
                ((Y.localizationMorphism G).toToposHom.inverseImage.obj H)) ≫
            (Over.post f.toToposHom.inverseImage).map
              ((Y.relocalizationInverseImageSliceIso b).inv.app
                ((Y.localizationMorphism G).toToposHom.inverseImage.obj H))) =
        (toOverCompPullbackIso (f.toToposHom.inverseImage.map b)).hom.app
            (f.toToposHom.inverseImage.obj H) ≫
          ((f.toToposHom.inverseImageCompToOverIso G').hom.app H ≫
            (Over.post f.toToposHom.inverseImage).map
              ((Y.localizationInverseImageIso G').inv.app H)) := by
    refine Eq.trans
      (eq_whisker ((Over.pullback (f.toToposHom.inverseImage.map b)).map_comp _ _) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (whisker_eq _ (eq_whisker hnat _)) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      ((Over.post f.toToposHom.inverseImage).map_comp _ _).symm)) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (congrArg (fun z => (Over.post f.toToposHom.inverseImage).map z) hYv))) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      ((Over.post f.toToposHom.inverseImage).map_comp _ _))) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker hbc _) ?_
    exact Category.assoc _ _ _
  have core : (X.relocalizationInverseImageSliceIso (f.toToposHom.inverseImage.map b)).hom.app
            ((X.localizationMorphism
              (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj
                (f.toToposHom.inverseImage.obj H)) ≫
          ((Over.pullback (f.toToposHom.inverseImage.map b)).map
              ((X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G)).hom.app
                  (f.toToposHom.inverseImage.obj H) ≫
                (f.toToposHom.inverseImageCompToOverIso G).hom.app H ≫
                  (f.toToposHom.over G).inverseImage.map
                    ((Y.localizationInverseImageIso G).inv.app H)) ≫
            ((Over.postPullbackIso f.toToposHom.inverseImage b).inv.app
                ((Y.localizationEquivalence G).functor.obj
                  ((Y.localizationMorphism G).toToposHom.inverseImage.obj H)) ≫
              (Over.post f.toToposHom.inverseImage).map
                ((Y.relocalizationInverseImageSliceIso b).inv.app
                  ((Y.localizationMorphism G).toToposHom.inverseImage.obj H)))) =
        (X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G')).hom.app
            (f.toToposHom.inverseImage.obj H) ≫
          ((f.toToposHom.inverseImageCompToOverIso G').hom.app H ≫
            (Over.post f.toToposHom.inverseImage).map
              ((Y.localizationInverseImageIso G').inv.app H)) := by
    refine Eq.trans (whisker_eq _ (Eq.trans
      (eq_whisker ((Over.pullback (f.toToposHom.inverseImage.map b)).map_comp _ _) _)
      (Eq.trans (Category.assoc _ _ _) (whisker_eq _ hD2)))) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact eq_whisker hX.symm _
  have hrfl : (f.localizedCompRelocalizationIso b).hom.app
        ((Y.localizationMorphism G).toToposHom.inverseImage.obj H) =
      (X.relocalizationFibreIso (f.toToposHom.inverseImage.map b)).hom.app
          ((Over.post f.toToposHom.inverseImage).obj
            ((Y.localizationEquivalence G).functor.obj
              ((Y.localizationMorphism G).toToposHom.inverseImage.obj H))) ≫
        ((X.localizationEquivalence (f.toToposHom.inverseImage.obj G')).inverse.map
            ((Over.postPullbackIso f.toToposHom.inverseImage b).inv.app
              ((Y.localizationEquivalence G).functor.obj
                ((Y.localizationMorphism G).toToposHom.inverseImage.obj H))) ≫
          (X.localizationEquivalence (f.toToposHom.inverseImage.obj G')).inverse.map
            ((Over.post f.toToposHom.inverseImage).map
              ((Y.relocalizationInverseImageSliceIso b).inv.app
                ((Y.localizationMorphism G).toToposHom.inverseImage.obj H)))) := rfl
  have hinner : (X.relocalizationMorphism
            (f.toToposHom.inverseImage.map b)).toToposHom.inverseImage.map
          ((f.inverseImageCompLocalizationIso G).hom.app H) ≫
        (f.localizedCompRelocalizationIso b).hom.app
          ((Y.localizationMorphism G).toToposHom.inverseImage.obj H) =
      (X.relocalizationMorphism (f.toToposHom.inverseImage.map b)).toToposHom.inverseImage.map
          ((X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).unitIso.hom.app
            ((X.localizationMorphism
              (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj
                (f.toToposHom.inverseImage.obj H))) ≫
        ((X.relocalizationFibreIso (f.toToposHom.inverseImage.map b)).hom.app
            ((X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).functor.obj
              ((X.localizationMorphism
                (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj
                  (f.toToposHom.inverseImage.obj H))) ≫
          (X.localizationEquivalence (f.toToposHom.inverseImage.obj G')).inverse.map
            ((Over.pullback (f.toToposHom.inverseImage.map b)).map
                ((X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G)).hom.app
                    (f.toToposHom.inverseImage.obj H) ≫
                  (f.toToposHom.inverseImageCompToOverIso G).hom.app H ≫
                    (f.toToposHom.over G).inverseImage.map
                      ((Y.localizationInverseImageIso G).inv.app H)) ≫
              ((Over.postPullbackIso f.toToposHom.inverseImage b).inv.app
                  ((Y.localizationEquivalence G).functor.obj
                    ((Y.localizationMorphism G).toToposHom.inverseImage.obj H)) ≫
                (Over.post f.toToposHom.inverseImage).map
                  ((Y.relocalizationInverseImageSliceIso b).inv.app
                    ((Y.localizationMorphism G).toToposHom.inverseImage.obj H))))) := by
    refine Eq.trans (whisker_eq _ hrfl) ?_
    refine Eq.trans (eq_whisker (congrArg
      (fun z => (X.relocalizationMorphism
        (f.toToposHom.inverseImage.map b)).toToposHom.inverseImage.map z)
      (f.inverseImageCompLocalizationIso_hom_app G H)) _) ?_
    refine Eq.trans (eq_whisker ((X.relocalizationMorphism
      (f.toToposHom.inverseImage.map b)).toToposHom.inverseImage.map_comp _ _) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (whisker_eq _ (eq_whisker
      ((X.relocalizationFibreIso (f.toToposHom.inverseImage.map b)).hom.naturality _) _)) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _
      ((X.localizationEquivalence
        (f.toToposHom.inverseImage.obj G')).inverse.map_comp _ _).symm))) ?_
    exact whisker_eq _ (whisker_eq _
      ((X.localizationEquivalence (f.toToposHom.inverseImage.obj G')).inverse.map_comp _ _).symm)
  have hL : (X.localizationEquivalence (f.toToposHom.inverseImage.obj G')).functor.map
          ((X.relocalizationMorphism
                (f.toToposHom.inverseImage.map b)).toToposHom.inverseImage.map
              ((f.inverseImageCompLocalizationIso G).hom.app H) ≫
            (f.localizedCompRelocalizationIso b).hom.app
              ((Y.localizationMorphism G).toToposHom.inverseImage.obj H)) ≫
        (X.localizationEquivalence (f.toToposHom.inverseImage.obj G')).counitIso.hom.app
          ((Over.post f.toToposHom.inverseImage).obj
            ((Y.localizationEquivalence G').functor.obj
              ((Y.localizationMorphism G').toToposHom.inverseImage.obj H))) =
      (X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G')).hom.app
          (f.toToposHom.inverseImage.obj H) ≫
        ((f.toToposHom.inverseImageCompToOverIso G').hom.app H ≫
          (Over.post f.toToposHom.inverseImage).map
            ((Y.localizationInverseImageIso G').inv.app H)) := by
    refine Eq.trans (eq_whisker (congrArg
      (fun z => (X.localizationEquivalence
        (f.toToposHom.inverseImage.obj G')).functor.map z) hinner) _) ?_
    refine Eq.trans (eq_whisker ((X.localizationEquivalence
      (f.toToposHom.inverseImage.obj G')).functor.map_comp _ _) _) ?_
    refine Eq.trans (eq_whisker (whisker_eq _ ((X.localizationEquivalence
      (f.toToposHom.inverseImage.obj G')).functor.map_comp _ _)) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _ ((X.localizationEquivalence
      (f.toToposHom.inverseImage.obj G')).counitIso.hom.naturality _))) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (X.relocalizationInverseImageSliceIso_hom_app
      (f.toToposHom.inverseImage.map b) _).symm _) ?_
    exact core
  have hR : (X.localizationEquivalence (f.toToposHom.inverseImage.obj G')).functor.map
          ((f.inverseImageCompLocalizationIso G').hom.app H) ≫
        (X.localizationEquivalence (f.toToposHom.inverseImage.obj G')).counitIso.hom.app
          ((Over.post f.toToposHom.inverseImage).obj
            ((Y.localizationEquivalence G').functor.obj
              ((Y.localizationMorphism G').toToposHom.inverseImage.obj H))) =
      (X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G')).hom.app
          (f.toToposHom.inverseImage.obj H) ≫
        ((f.toToposHom.inverseImageCompToOverIso G').hom.app H ≫
          (Over.post f.toToposHom.inverseImage).map
            ((Y.localizationInverseImageIso G').inv.app H)) := by
    refine Eq.trans (eq_whisker (congrArg
      (fun z => (X.localizationEquivalence
        (f.toToposHom.inverseImage.obj G')).functor.map z)
      (f.inverseImageCompLocalizationIso_hom_app G' H)) _) ?_
    exact Equivalence.functor_map_unitIso_hom_app_comp_counitIso
      (X.localizationEquivalence (f.toToposHom.inverseImage.obj G')) _
  refine (X.localizationEquivalence (f.toToposHom.inverseImage.obj G')).functor.map_injective ?_
  refine (cancel_mono ((X.localizationEquivalence
    (f.toToposHom.inverseImage.obj G')).counitIso.hom.app
      ((Over.post f.toToposHom.inverseImage).obj
        ((Y.localizationEquivalence G').functor.obj
          ((Y.localizationMorphism G').toToposHom.inverseImage.obj H))))).1 ?_
  exact hL.trans hR.symm

/-- **Stacks 04IF's square over a change of the sheaf on the target, as a 2-isomorphism of
ringed topoi.** For `b : G' ⟶ G` on the target, the localized morphism `f'` of Stacks 04IF at
`G'` followed by the relocalization of `Y` along `b` agrees with the relocalization of `X` along
`f⁻¹b` followed by `f'` at `G`. -/
noncomputable def localizedCompRelocalizationRingedSquare :
    TwoIso (A := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G'))
        (B := Y.localizedRingedTopos G)
      (comp (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G'))
        (Y := Y.localizedRingedTopos G') (Z := Y.localizedRingedTopos G)
        (Y.relocalizationMorphism b) (f.localized G'))
      (comp (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G'))
        (Y := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G))
        (Z := Y.localizedRingedTopos G)
        (f.localized G) (X.relocalizationMorphism (f.toToposHom.inverseImage.map b))) :=
  TwoIso.ofInverseImageIso
      (A := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G'))
      (B := Y.localizedRingedTopos G)
      (p := comp (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G'))
        (Y := Y.localizedRingedTopos G') (Z := Y.localizedRingedTopos G)
        (Y.relocalizationMorphism b) (f.localized G'))
      (q := comp (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G'))
        (Y := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G))
        (Z := Y.localizedRingedTopos G)
        (f.localized G) (X.relocalizationMorphism (f.toToposHom.inverseImage.map b)))
      (f.localizedCompRelocalizationIso b) (by
    have hb := forgetRing_relocalizationMorphism_fSharpInverseImage Y b
    have hc := forgetRing_relocalizationMorphism_fSharpInverseImage X
      (f.toToposHom.inverseImage.map b)
    have hP : (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G')).forgetRing.map
          (comp (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G'))
            (Y := Y.localizedRingedTopos G') (Z := Y.localizedRingedTopos G)
            (Y.relocalizationMorphism b) (f.localized G')).fSharpInverseImage =
        (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G')).forgetRing.map
          (f.localized G').fSharpInverseImage :=
      (comp_fSharpInverseImage_forget
          (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G'))
          (Y := Y.localizedRingedTopos G') (Z := Y.localizedRingedTopos G)
          (Y.relocalizationMorphism b) (f.localized G')).trans
        ((congrArg (fun z ↦ z ≫
            (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G')).forgetRing.map
              (f.localized G').fSharpInverseImage)
          ((congrArg (fun z ↦ (f.localized G').toToposHom.inverseImage.map z) hb).trans
            ((f.localized G').toToposHom.inverseImage.map_id _))).trans (Category.id_comp _))
    have hQ : (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G')).forgetRing.map
          (comp (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G'))
            (Y := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G))
            (Z := Y.localizedRingedTopos G) (f.localized G)
            (X.relocalizationMorphism
              (f.toToposHom.inverseImage.map b))).fSharpInverseImage =
        (X.relocalizationMorphism
            (f.toToposHom.inverseImage.map b)).toToposHom.inverseImage.map
          ((X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).forgetRing.map
            (f.localized G).fSharpInverseImage) :=
      (comp_fSharpInverseImage_forget
          (X := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G'))
          (Y := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G))
          (Z := Y.localizedRingedTopos G) (f.localized G)
          (X.relocalizationMorphism (f.toToposHom.inverseImage.map b))).trans
        ((congrArg (fun z ↦ (X.relocalizationMorphism
            (f.toToposHom.inverseImage.map b)).toToposHom.inverseImage.map
              ((X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).forgetRing.map
                (f.localized G).fSharpInverseImage) ≫ z) hc).trans (Category.comp_id _))
    refine Eq.trans (congrArg (fun z ↦ (f.localizedCompRelocalizationIso b).hom.app
      ((Y.localizedRingedTopos G).forgetRing.obj (Y.localizedRingedTopos G).O) ≫ z) hP)
      (Eq.trans ?_ hQ.symm)
    refine (cancel_epi ((X.relocalizationMorphism
        (f.toToposHom.inverseImage.map b)).toToposHom.inverseImage.map
      ((f.inverseImageCompLocalizationIso G).hom.app (Y.forgetRing.obj Y.O)))).1 ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z ↦ z ≫
      (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G')).forgetRing.map
        (f.localized G').fSharpInverseImage)
      (f.inverseImageCompLocalizationIso_baseChange b
        (Y.forgetRing.obj Y.O))) ?_
    refine Eq.trans (f.localized_fSharpInverseImage_forget G') ?_
    refine Eq.trans ?_ ((X.relocalizationMorphism
      (f.toToposHom.inverseImage.map b)).toToposHom.inverseImage.map_comp
      ((f.inverseImageCompLocalizationIso G).hom.app (Y.forgetRing.obj Y.O))
      ((X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).forgetRing.map
        (f.localized G).fSharpInverseImage))
    exact congrArg (X.relocalizationMorphism
        (f.toToposHom.inverseImage.map b)).toToposHom.inverseImage.map
      (f.localized_fSharpInverseImage_forget G).symm)

/-- **Stacks 04J8**, the naturality square of the last assertion as a square of *ringed* topoi:
```
  (j_{G'/G}, …) ∘ (f_{s'}, f_{s'}♯) ≅ (f_s, f_s♯) ∘ (j_{F'/F}, …) .
```
This is the pasting of `relocalizationSquareTwoIso` for `a ≫ s = s' ≫ f⁻¹b` with
`localizedCompRelocalizationRingedSquare` along the factorization `f_s = f'_G ∘ j_s`. -/
@[stacks 04J8 "the final assertion: for `b`, `a`, `s'` with the compatibility square, the induced square of ringed topoi on the slices commutes"]
noncomputable def relocalizedNaturalitySquare
    (hs : a ≫ s = s' ≫ f.toToposHom.inverseImage.map b) :
    TwoIso (A := X.localizedRingedTopos F') (B := Y.localizedRingedTopos G)
      (comp (X := X.localizedRingedTopos F') (Y := Y.localizedRingedTopos G')
        (Z := Y.localizedRingedTopos G) (Y.relocalizationMorphism b) (f.relocalized s'))
      (comp (X := X.localizedRingedTopos F') (Y := X.localizedRingedTopos F)
        (Z := Y.localizedRingedTopos G) (f.relocalized s) (X.relocalizationMorphism a)) :=
  pastedComparison (X.relocalizationMorphism s') (f.localized G')
    (X.relocalizationMorphism s) (f.localized G) (X.relocalizationMorphism a)
    (X.relocalizationMorphism (f.toToposHom.inverseImage.map b)) (Y.relocalizationMorphism b)
    (relocalizationSquareTwoIso X a s s' (f.toToposHom.inverseImage.map b) hs)
    (f.localizedCompRelocalizationRingedSquare b)

end AlgebraicGeometry.RingedToposHom

end

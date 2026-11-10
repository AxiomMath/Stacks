module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposMorphismLocalization
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.OverPushforwardMate
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# The structure map of the localized morphism of Stacks 04IF is the restricted structure map

Let `(f, f♯) : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi, let `G` be a sheaf of sets
on `D` and put `F = f⁻¹G`.  Stacks 04IF localizes `f` to `(f', (f')♯)` and records its square with
the two localization morphisms twice: on inverse images
(`AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso`) and on the pushforwards
(`AlgebraicGeometry.RingedToposHom.localizationCompPushforwardIso`).  This file proves that the
second is the Beck–Chevalley *mate* of the first, and unfolds the structure map of `(f')♯` on
underlying sheaves of sets factor by factor.

Those two are what the compatibility of the square with the structure maps rests on — **the
inverse-image form of `(f')♯`, read through the inverse-image square, is the restriction of the
inverse-image form of `f♯` to the site of elements of `F`** — which is
`AlgebraicGeometry.RingedToposHom.localized_fSharpInverseImage_forget` in
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RingedToposMorphismLocalization.lean`, and
is the one thing beyond the library's form of Stacks 04IF that commutativity of the localization
square of Stacks 04J8 as a square of *ringed* topoi needs.

## Main results

* `AlgebraicGeometry.RingedToposHom.mateEquiv_inverseImageCompLocalizationIso_inv`: Stacks 04IF's
  pushforward square is the mate of its inverse-image square.
* `AlgebraicGeometry.RingedToposHom.localized_fSharp_forget`: on underlying sheaves of sets, the
  structure map of the localized morphism is the restriction of the structure map of `f` followed
  by the pushforward square.

## Implementation notes

The mate identity is obtained from the corresponding identity for the slice topoi
(`MorphismOfTopoi.mateEquiv_inverseImageCompToOverIso_inv`, Stacks 04H1) by
`Stacks.CategoryTheory.mateEquiv_transport`, which transports a mate identity along the two
equivalences of the localizations with their slice topoi.  The hypotheses of that transport are
`inverseImageCompLocalizationIso_inv_app` and `localizationCompPushforwardIso_inv_app`, which are
the two 04IF isomorphisms written out componentwise; both are proved by `simp`, which needs the
definition of `AlgebraicGeometry.RingedToposHom.localizedToposMorphism` to be transparent, since
otherwise the composites appearing in those isomorphisms are not even type-correct at the
`implicit` transparency level at which `simp` rewrites.  That is what the local
`implicit_reducible` attributes are for.

The passage from the mate identity to the structure maps is
`Stacks.CategoryTheory.homEquiv_symm_mateEquiv`, the element-level mates correspondence: the
structure map in inverse-image form is by definition an adjunct, so transporting it across the
square is exactly the statement that adjuncts and mates commute.  What has to be computed by hand
is that the structure map of `localized` reduces, on underlying sheaves of sets, to the restriction
of `f♯` followed by the pushforward square: three of the four factors of its definition are the
identity on underlying sheaves of sets, and the fourth is the pushforward square itself.

## References

* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 04H1](https://stacks.math.columbia.edu/tag/04H1)
* [Stacks Project, Tag 04J8](https://stacks.math.columbia.edu/tag/04J8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPullback

universe ww vv₁ uu₁ vv₂ uu₂ vv uu

variable {C₁ : Type uu₁} [Category.{vv₁} C₁] {C₂ : Type uu₂} [Category.{vv₂} C₂]
  {D : Type uu} [Category.{vv} D]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂) {K : GrothendieckTopology D}
  [J₁.HasSheafCompose (forget RingCat.{ww})] [J₂.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww})]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J₂.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  (Φ₁ : Sheaf K (Type ww) ⥤ Sheaf J₁ (Type ww)) [PreservesFiniteProducts Φ₁]
  (Φ₂ : Sheaf J₁ (Type ww) ⥤ Sheaf J₂ (Type ww)) [PreservesFiniteProducts Φ₂]

omit [J₂.HasSheafCompose (forget RingCat.{ww})]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})] in
/-- The inverse of the comparison of the two iterated inverse images is also the identity on
underlying sheaves of sets.  This is
`Stacks.Sheaves.ToposPullback.forget_map_pullbackCommRingSheafComp_hom` for the inverse. -/
theorem forget_map_pullbackCommRingSheafComp_inv
    [J₂.HasSheafCompose (forget CommRingCat.{ww})] [K.HasSheafCompose (forget CommRingCat.{ww})]
    (O : Sheaf K CommRingCat.{ww}) :
    (sheafCompose J₂ (forget CommRingCat.{ww})).map
        (pullbackCommRingSheafComp J₁ J₂ Φ₁ Φ₂ O).inv =
      𝟙 ((sheafCompose J₂ (forget CommRingCat.{ww})).obj
        (pullbackCommRingSheaf J₂ (Φ₁ ⋙ Φ₂) O)) := by
  have h0 : (sheafCompose J₂ (forget CommRingCat.{ww})).map
        ((pullbackCommRingSheafComp J₁ J₂ Φ₁ Φ₂ O).inv ≫
          (pullbackCommRingSheafComp J₁ J₂ Φ₁ Φ₂ O).hom) = 𝟙 _ := by
    rw [Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  rw [CategoryTheory.Functor.map_comp, forget_map_pullbackCommRingSheafComp_hom] at h0
  exact (Category.comp_id _).symm.trans h0

/-- `Stacks.Sheaves.ToposPullback.forget_map_pullbackCommRingSheafComp_hom` with the comparison
read off the natural isomorphism of functors. -/
theorem forget_map_pullbackCommRingSheafFunctorComp_hom_app
    [J₂.HasSheafCompose (forget CommRingCat.{ww})] [K.HasSheafCompose (forget CommRingCat.{ww})]
    (O : Sheaf K CommRingCat.{ww}) :
    (sheafCompose J₂ (forget CommRingCat.{ww})).map
        ((pullbackCommRingSheafFunctorComp J₁ J₂ Φ₁ Φ₂).hom.app O) =
      𝟙 ((sheafCompose J₂ (forget CommRingCat.{ww})).obj
        (pullbackCommRingSheaf J₂ (Φ₁ ⋙ Φ₂) O)) :=
  forget_map_pullbackCommRingSheafComp_hom J₁ J₂ Φ₁ Φ₂ O

/-- `Stacks.Sheaves.ToposPullback.forget_map_pullbackCommRingSheafComp_inv` with the comparison
read off the natural isomorphism of functors. -/
theorem forget_map_pullbackCommRingSheafFunctorComp_inv_app
    [J₂.HasSheafCompose (forget CommRingCat.{ww})] [K.HasSheafCompose (forget CommRingCat.{ww})]
    (O : Sheaf K CommRingCat.{ww}) :
    (sheafCompose J₂ (forget CommRingCat.{ww})).map
        ((pullbackCommRingSheafFunctorComp J₁ J₂ Φ₁ Φ₂).inv.app O) =
      𝟙 ((sheafCompose J₂ (forget CommRingCat.{ww})).obj
        (pullbackCommRingSheaf J₂ (Φ₁ ⋙ Φ₂) O)) :=
  forget_map_pullbackCommRingSheafComp_inv J₁ J₂ Φ₁ Φ₂ O

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww'})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  {Φ Φ' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)}
  [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ']
  [J.HasSheafCompose (forget CommRingCat.{ww})] [K.HasSheafCompose (forget CommRingCat.{ww'})]

/-- On underlying sheaves of sets, the inverse of the isomorphism of inverse-image functors of
sheaves of commutative rings induced by a natural isomorphism of the underlying functors *is* the
inverse of that isomorphism. -/
theorem forget_map_pullbackCommRingSheafFunctorIsoOfNatIso_inv_app (e : Φ ≅ Φ')
    (O : Sheaf K CommRingCat.{ww'}) :
    (sheafCompose J (forget CommRingCat.{ww})).map
        ((pullbackCommRingSheafFunctorIsoOfNatIso J e).inv.app O) =
      e.inv.app ((sheafCompose K (forget CommRingCat.{ww'})).obj O) :=
  pullbackCommRingSheafMapOfNatTrans_forget J e.inv O

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPullback

universe ww vv₁ uu₁ vv₂ uu₂ vv₃ uu₃ vv uu

variable {C₁ : Type uu₁} [Category.{vv₁} C₁] {C₂ : Type uu₂} [Category.{vv₂} C₂]
  {C₃ : Type uu₃} [Category.{vv₃} C₃] {D : Type uu} [Category.{vv} D]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂) (J₃ : GrothendieckTopology C₃)
  {K : GrothendieckTopology D}
  [J₁.HasSheafCompose (forget RingCat.{ww})] [J₂.HasSheafCompose (forget RingCat.{ww})]
  [J₃.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J₂.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J₃.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J₂.HasSheafCompose (forget CommRingCat.{ww})] [K.HasSheafCompose (forget CommRingCat.{ww})]
  (Φ₁ : Sheaf K (Type ww) ⥤ Sheaf J₁ (Type ww)) [PreservesFiniteProducts Φ₁]
  (Φ₂ : Sheaf J₁ (Type ww) ⥤ Sheaf J₂ (Type ww)) [PreservesFiniteProducts Φ₂]
  (Ψ₁ : Sheaf K (Type ww) ⥤ Sheaf J₃ (Type ww)) [PreservesFiniteProducts Ψ₁]
  (Ψ₂ : Sheaf J₃ (Type ww) ⥤ Sheaf J₂ (Type ww)) [PreservesFiniteProducts Ψ₂]

/-- **An isomorphism of iterated inverse images of sheaves of commutative rings obtained by
transport along an isomorphism of the underlying functors of sheaves of sets is, on underlying
sheaves of sets, that isomorphism.**  Both comparisons of an iterated inverse image with the
inverse image of the composite are identities there, so only the transport survives. -/
theorem forget_map_pullbackCommRingTransportIso_inv_app (e : Φ₁ ⋙ Φ₂ ≅ Ψ₁ ⋙ Ψ₂)
    (O : Sheaf K CommRingCat.{ww}) :
    (sheafCompose J₂ (forget CommRingCat.{ww})).map
        ((pullbackCommRingSheafFunctorComp J₁ J₂ Φ₁ Φ₂ ≪≫
            pullbackCommRingSheafFunctorIsoOfNatIso J₂ e ≪≫
            (pullbackCommRingSheafFunctorComp J₃ J₂ Ψ₁ Ψ₂).symm).inv.app O) =
      e.inv.app ((sheafCompose K (forget CommRingCat.{ww})).obj O) := by
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, CategoryTheory.Functor.map_comp,
    forget_map_pullbackCommRingSheafFunctorComp_hom_app,
    forget_map_pullbackCommRingSheafFunctorComp_inv_app,
    forget_map_pullbackCommRingSheafFunctorIsoOfNatIso_inv_app]
  exact (Category.comp_id _).trans (Category.id_comp _)

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.RingedToposHom

universe v u u'

variable {X : RingedTopos.{v, u, v}} {Y : RingedTopos.{v, u', v}} [EssentiallySmall.{v} X.C]
  [EssentiallySmall.{v} Y.C] (f : RingedToposHom X Y) (G : Y.Topos)

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.localizedToposMorphism

/-- The components of Stacks 04IF's inverse-image square: the comparison is the slice-level square
of Stacks 04H1 conjugated by the two identifications of the inverse images of the localization
morphisms with `toOver`, and by the unit of the equivalence with the slice topos. -/
theorem inverseImageCompLocalizationIso_inv_app (W : Y.Topos) :
    (f.inverseImageCompLocalizationIso G).inv.app W =
      (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).inverse.map
          ((f.toToposHom.over G).inverseImage.map ((Y.localizationInverseImageIso G).hom.app W)) ≫
        (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).inverse.map
            ((f.toToposHom.inverseImageCompToOverIso G).inv.app W) ≫
          (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).inverse.map
              ((X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G)).inv.app
                (f.toToposHom.inverseImage.obj W)) ≫
            (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).unitIso.inv.app
              ((X.localizationMorphism
                  (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj
                (f.toToposHom.inverseImage.obj W)) := by
  simp only [AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Category.assoc]
  simp

/-- **Stacks 04IF's pushforward square is the Beck–Chevalley mate of its inverse-image square**,
across the two vertical adjunctions `f⁻¹ ⊣ f_*` and `(f')⁻¹ ⊣ (f')_*` of the localization square.

This is the slice-level identity `MorphismOfTopoi.mateEquiv_inverseImageCompToOverIso_inv` of
Stacks 04H1 transported along the two identifications of the localizations with their slice
topoi. -/
theorem mateEquiv_inverseImageCompLocalizationIso_inv :
    mateEquiv f.toToposHom.adj (localizedToposMorphism f G).adj
        (TwoSquare.mk (Y.localizationMorphism G).toToposHom.inverseImage f.toToposHom.inverseImage
          (localizedToposMorphism f G).inverseImage
          (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage
          (f.inverseImageCompLocalizationIso G).inv) =
      TwoSquare.mk f.toToposHom.pushforward
        (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage
        (Y.localizationMorphism G).toToposHom.inverseImage
        (localizedToposMorphism f G).pushforward (f.localizationCompPushforwardIso G).inv :=
  Stacks.CategoryTheory.mateEquiv_transport f.toToposHom.adj (f.toToposHom.over G).adj
    (Y.localizationEquivalence G) (X.localizationEquivalence (f.toToposHom.inverseImage.obj G))
    (Y.localizationInverseImageIso G)
    (X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G))
    (TwoSquare.mk (toOver G) f.toToposHom.inverseImage (f.toToposHom.over G).inverseImage
      (toOver (f.toToposHom.inverseImage.obj G)) (f.toToposHom.inverseImageCompToOverIso G).inv)
    (TwoSquare.mk f.toToposHom.pushforward (toOver (f.toToposHom.inverseImage.obj G)) (toOver G)
      (f.toToposHom.over G).pushforward (f.toToposHom.toOverCompPushforwardIso G).inv)
    (f.toToposHom.mateEquiv_inverseImageCompToOverIso_inv G) _ _
    (f.inverseImageCompLocalizationIso_inv_app G) (f.localizationCompPushforwardIso_inv_app G)

/-- The structure map of the localized morphism of Stacks 04IF, unfolded into its four factors. -/
theorem localized_fSharp_eq :
    (f.localized G).fSharp =
      (Y.localizationInverseImageCommRingIso G).inv ≫
        (inverseImageCommRingFunctor.{v, v, v, max u' v, v, u'}
          (Y.localizationMorphism G).toToposHom).map f.fSharp ≫
        (f.localizedPushforwardCommRingIso G).inv.app X.O ≫
        (pushforwardCommRingFunctor.{v, v, v, max u v, v, max u' v}
          (localizedToposMorphism f G)).map
          (X.localizationInverseImageCommRingIso (f.toToposHom.inverseImage.obj G)).hom :=
  rfl

/-- The last two factors of the structure map of the localized morphism of Stacks 04IF, on
underlying sheaves of sets: the ring-level pushforward square followed by the identification of
the localized structure sheaf, which is the identity there. -/
theorem localized_fSharp_forget_last :
    (Y.localizedRingedTopos G).forgetRing.map
      ((f.localizedPushforwardCommRingIso G).inv.app X.O ≫
        (pushforwardCommRingFunctor.{v, v, v, max u v, v, max u' v}
          (localizedToposMorphism f G)).map
          (X.localizationInverseImageCommRingIso (f.toToposHom.inverseImage.obj G)).hom) =
      (f.localizationCompPushforwardIso G).inv.app (X.forgetRing.obj X.O) := by
  have e3 := f.localizedPushforwardCommRingIso_inv_forget G
  have e4 : (sheafCompose (Y.localizedRingedTopos G).J (forget CommRingCat.{v})).map
      ((pushforwardCommRingFunctor.{v, v, v, max u v, v, max u' v} (localizedToposMorphism f G)).map
        (X.localizationInverseImageCommRingIso (f.toToposHom.inverseImage.obj G)).hom) =
      (localizedToposMorphism f G).pushforward.map
        ((sheafCompose (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).J
            (forget CommRingCat.{v})).map
          (X.localizationInverseImageCommRingIso (f.toToposHom.inverseImage.obj G)).hom) :=
    underlyingRingSheaf_map_pullbackCommRingSheafMap.{v, v, v, max u' v, v, max u v}
      (Y.localizedRingedTopos G).J _
      (X.localizationInverseImageCommRingIso (f.toToposHom.inverseImage.obj G)).hom
  have hone : (sheafCompose (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).J
      (forget CommRingCat.{v})).map
      (X.localizationInverseImageCommRingIso (f.toToposHom.inverseImage.obj G)).hom =
      𝟙 ((X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj
        (X.forgetRing.obj X.O)) := rfl
  have hC := e4.trans ((congrArg (localizedToposMorphism f G).pushforward.map hone).trans
    ((localizedToposMorphism f G).pushforward.map_id _))
  exact ((sheafCompose (Y.localizedRingedTopos G).J (forget CommRingCat.{v})).map_comp _ _).trans
    ((congrArg₂ (· ≫ ·) e3 hC).trans
      (Category.comp_id (Y := (localizedToposMorphism f G).pushforward.obj
        ((X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj
          (X.forgetRing.obj X.O)))
        ((f.localizationCompPushforwardIso G).inv.app (X.forgetRing.obj X.O))))

/-- The last three factors of the structure map of the localized morphism of Stacks 04IF, on
underlying sheaves of sets. -/
theorem localized_fSharp_forget_tail :
    (Y.localizedRingedTopos G).forgetRing.map
      ((inverseImageCommRingFunctor.{v, v, v, max u' v, v, u'}
          (Y.localizationMorphism G).toToposHom).map f.fSharp ≫
        (f.localizedPushforwardCommRingIso G).inv.app X.O ≫
        (pushforwardCommRingFunctor.{v, v, v, max u v, v, max u' v}
          (localizedToposMorphism f G)).map
          (X.localizationInverseImageCommRingIso (f.toToposHom.inverseImage.obj G)).hom) =
      (Y.localizationMorphism G).toToposHom.inverseImage.map (Y.forgetRing.map f.fSharp) ≫
        (f.localizationCompPushforwardIso G).inv.app (X.forgetRing.obj X.O) :=
  ((sheafCompose (Y.localizedRingedTopos G).J (forget CommRingCat.{v})).map_comp _ _).trans
    (congrArg₂ (· ≫ ·)
      (underlyingRingSheaf_map_pullbackCommRingSheafMap.{v, v, v, max u' v, v, u'}
        (Y.localizedRingedTopos G).J _
        f.fSharp)
      (f.localized_fSharp_forget_last G))

end AlgebraicGeometry.RingedToposHom

end

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.AlgebraicGeometry.Recovery04IH.ToposRelocalization
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizationSquareMate
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RelocalizationBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposMorphismLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.StructureSheafComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Localizing a morphism of ringed topoi at a sheaf and a map to an inverse image

Let `(f, f♯) : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi, let `G` be a sheaf of
sets on `D`, let `F` be a sheaf of sets on `C` and let `s : F ⟶ f⁻¹G` be a morphism of sheaves.
Stacks 04J8 produces from these a morphism of ringed topoi

```
  (f_s, f_s♯) : (Sh(C)/F, O_F) ⟶ (Sh(D)/G, O'_G) ,
```

namely the composition of the localized morphism `(f', (f')♯)` of Stacks 04IF, which goes from
the localization at `f⁻¹G`, with the relocalization morphism of Stacks 04J4 along `s`; and it
asserts that the resulting square with the two localization morphisms `j_F` and `j_G` commutes
as a square of ringed topoi, as does the square comparing `f_s` and `f_{s'}` for compatible
`b : G' ⟶ G`, `a : F' ⟶ F` and `s' : F' ⟶ f⁻¹G'`.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso`: a comparison of the inverse
  images of two morphisms of ringed topoi which is compatible with the inverse-image form of
  their structure maps is a 2-isomorphism of ringed topoi.
* `AlgebraicGeometry.RingedToposHom.relocalized`: the morphism of ringed topoi `(f_s, f_s♯)`,
  defined as Stacks 04J8 defines it, as the composition of the morphism of Stacks 04IF with the
  relocalization morphism of Stacks 04J4 along `s`.
* `AlgebraicGeometry.RingedToposHom.localizedCompRelocalizationIso`: for `b : G' ⟶ G` on the
  target, the inverse image of the morphism `f'` of Stacks 04IF at `G` followed by that of the
  relocalization along `f⁻¹b` is the inverse image of the relocalization along `b` followed by
  that of `f'` at `G'`.

## Main results

* `AlgebraicGeometry.RingedToposHom.relocalizedInverseImageSquare`: the localization square of
  Stacks 04J8 commutes on inverse images.
* `AlgebraicGeometry.RingedToposHom.relocalizedToposSquare`: it commutes as a square of topoi.
* `AlgebraicGeometry.RingedToposHom.relocalizedRingedSquare`: it commutes as a square of ringed
  topoi.

## Implementation notes

`relocalized` is *defined* to be the composite the source specifies, so the factorization
`f_s = f' ∘ j` that Stacks 04J8 asserts holds by construction; that is faithful to the source,
whose proof of the factorization is that it is the definition. The source states the second
factor as the morphism `(j, j♯)` of Stacks 04J4 attached to `s : F ⟶ f⁻¹G`, which is
`AlgebraicGeometry.RingedTopos.relocalizationMorphism`.

**The relocalization contributes nothing to the inverse-image square.** The inverse image of a
relocalization is restriction along postcomposition of sections, and postcomposition with `s`
followed by the projection from the site of elements of `f⁻¹G` is the projection from the site
of elements of `F`; so `j_F⁻¹ = j_{f⁻¹G}⁻¹ ⋙ (j_s)⁻¹` on the nose
(`AlgebraicGeometry.RingedToposHom.localizationMorphism_inverseImage_eq_comp`). That is why
`relocalizedInverseImageSquare` is Stacks 04IF's inverse-image square
(`AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso`) whiskered by `(j_s)⁻¹` and
reassociated twice, with no new geometry, and why the structure map of the relocalization — the
identity on underlying sheaves of sets — drops out of the compatibility equation.

**Where the structure maps come from.** Commutativity of 04J8's square as a square of *ringed*
topoi is the structure-map compatibility of Stacks 04IF's own square, pasted with the
relocalization, and nothing else. That compatibility — the inverse-image form of `(f')♯` is the
restriction of the inverse-image form of `f♯` along 04IF's inverse-image square, read on
underlying sheaves of sets — is
`AlgebraicGeometry.RingedToposHom.localized_fSharpInverseImage_forget`;
it rests on the Beck–Chevalley comparison of 04IF's two squares, that its inverse-image square
is the mate of its identity `f'_* j_F⁻¹ = j_G⁻¹ f_*`.

The last assertion of Stacks 04J8, the commuting square comparing `f_s` with `f_{s'}` for
`b : G' ⟶ G`, `a : F' ⟶ F` and `s' : F' ⟶ f⁻¹G'` with `a ≫ s = s' ≫ f⁻¹b`, is not carried here;
it is carried on inverse images, as a square of topoi and as a square of ringed topoi by
`AlgebraicGeometry.RingedToposHom.relocalizedNaturalityInverseImageSquare`,
`…relocalizedNaturalityToposSquare` and `…relocalizedNaturalitySquare` in
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RelocalizedNaturalitySquare.lean`.
Already on inverse images it compares the localization of `f` at `G` with its localization at
`G'`, which is base change along `b` in the slice presentation; the identification of the inverse
image of a relocalization with base change is
`AlgebraicGeometry.RingedTopos.localizationInverseImageIso_eq_relocalization` in
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RelocalizationBaseChange.lean`.

What the square as one of *ringed* topoi needs beyond that is the compatibility of
`localizedCompRelocalizationIso` with 04IF's two comparisons, which is
`AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso_baseChange`; the structure maps
themselves are discharged by `localized_fSharpInverseImage_forget` at `G` and at `G'`.

Universes follow the localization: the morphisms of the sites and the sections of the
structure sheaves lie in one universe `v`, the objects of the two sites in universes of their
own, and the sites are essentially small for `v`; see
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/ToposLocalization.lean`.

## References

* [Stacks Project, Tag 04J8](https://stacks.math.columbia.edu/tag/04J8)
* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 04IV](https://stacks.math.columbia.edu/tag/04IV)
* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
* [Stacks Project, Tag 04H1](https://stacks.math.columbia.edu/tag/04H1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe v u u'

namespace AlgebraicGeometry.RingedToposHom

/-! ### 2-isomorphisms of ringed topoi from a comparison of inverse images

A 2-isomorphism of ringed topoi is an isomorphism of the direct images compatible with the
structure maps in their direct-image form. Both halves can be read off the inverse images
instead: an isomorphism of the inverse images conjugates to one of the direct images, and the
compatibility transposes to the same compatibility for the inverse-image form of the structure
maps. That is the form in which the squares below arrive. -/

section OfInverseImage

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {A : RingedTopos.{v₁, u₁, w₁}} {B : RingedTopos.{v₂, u₂, w₂}}
  [A.J.HasSheafCompose (forget RingCat.{w₁})]
  [B.J.HasSheafCompose (forget RingCat.{w₂})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]

/-- The structure map of a morphism of ringed topoi, on underlying sheaves of sets, is the
adjunct of its inverse-image form. This is
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv` read in the other
direction. -/
theorem forgetFSharp_eq_homEquiv (p : RingedToposHom A B) :
    forgetFSharp p =
      (p.toToposHom.adj.homEquiv (B.forgetRing.obj B.O) (A.forgetRing.obj A.O))
        (A.forgetRing.map p.fSharpInverseImage) :=
  ((congrArg (p.toToposHom.adj.homEquiv (B.forgetRing.obj B.O) (A.forgetRing.obj A.O))
      (fSharpInverseImage_forget_homEquiv p)).trans (Equiv.apply_symm_apply _ _)).symm

/-- **A 2-isomorphism of ringed topoi from a comparison of the inverse images.** Let
`p, q : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be morphisms of ringed topoi and `α : q⁻¹ ≅ p⁻¹` an
isomorphism of their inverse images whose value at the underlying sheaf of sets of `O_D` carries
the inverse-image form of the structure map of `p` to that of `q`. Then the conjugate
isomorphism `p_* ≅ q_*` is compatible with the two structure maps in their direct-image form,
so the pair is a 2-isomorphism of ringed topoi. -/
noncomputable def TwoIso.ofInverseImageIso {p q : RingedToposHom A B}
    (α : q.toToposHom.inverseImage ≅ p.toToposHom.inverseImage)
    (h : α.hom.app (B.forgetRing.obj B.O) ≫ A.forgetRing.map p.fSharpInverseImage =
      A.forgetRing.map q.fSharpInverseImage) :
    TwoIso p q where
  e := conjugateIsoEquiv p.toToposHom.adj q.toToposHom.adj α
  commutes := by
    have ht := Stacks.CategoryTheory.homEquiv_conjugate p.toToposHom.adj q.toToposHom.adj
      (conjugateEquiv p.toToposHom.adj q.toToposHom.adj α.hom)
      (A.forgetRing.map p.fSharpInverseImage)
    rw [Equiv.symm_apply_apply] at ht
    change forgetFSharp p ≫
      (conjugateEquiv p.toToposHom.adj q.toToposHom.adj α.hom).app
        (A.forgetRing.obj A.O) = forgetFSharp q
    exact (congrArg (fun z ↦ z ≫ (conjugateEquiv p.toToposHom.adj q.toToposHom.adj α.hom).app
          (A.forgetRing.obj A.O)) (forgetFSharp_eq_homEquiv p)).trans
      (ht.symm.trans
        ((congrArg (q.toToposHom.adj.homEquiv (B.forgetRing.obj B.O)
            (A.forgetRing.obj A.O)) h).trans
          (forgetFSharp_eq_homEquiv q).symm))

end OfInverseImage

/-! ### The morphism `(f_s, f_s♯)` and its localization square -/

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp

variable {X : RingedTopos.{v, u, v}} {Y : RingedTopos.{v, u', v}} [EssentiallySmall.{v} X.C]
  [EssentiallySmall.{v} Y.C] (f : RingedToposHom X Y) {G : Y.Topos} {F : X.Topos}
  (s : F ⟶ f.toToposHom.inverseImage.obj G)

/-- **Stacks 04J8.** The morphism of ringed topoi
`(f_s, f_s♯) : (Sh(C)/F, O_F) ⟶ (Sh(D)/G, O'_G)` attached to a morphism of ringed topoi
`(f, f♯)`, a sheaf `G` on the target, a sheaf `F` on the source and a morphism
`s : F ⟶ f⁻¹G`: the composition of the localized morphism of Stacks 04IF, from the localization
at `f⁻¹G`, with the relocalization morphism of Stacks 04J4 along `s`.

The factorization that Stacks 04J8 asserts is this definition. -/
@[stacks 04J8 "the morphism (f_s, f_s^sharp), and its factorization as the morphism of 04IF
  after the relocalization morphism of 04J4"]
noncomputable def relocalized :
    RingedToposHom (X.localizedRingedTopos F) (Y.localizedRingedTopos G) :=
  comp (X := X.localizedRingedTopos F)
    (Y := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G))
    (Z := Y.localizedRingedTopos G) (f.localized G) (X.relocalizationMorphism s)

/-- The morphism of topoi underlying `(f_s, f_s♯)` is the morphism of topoi of Stacks 04IF
composed with the relocalization morphism of topoi. -/
@[simp]
theorem relocalized_toToposHom :
    (f.relocalized s).toToposHom =
      (localizedToposMorphism f G).comp (X.relocalizationMorphismOfTopoi s) :=
  rfl

omit [EssentiallySmall.{v} Y.C] in
/-- Localizing at `F` has the same inverse image as localizing at `f⁻¹G` and relocalizing along
`s`, on the nose: postcomposition of sections with `s` followed by the projection from the site
of elements of `f⁻¹G` is the projection from the site of elements of `F`, and restriction along
a composite is the composite of the restrictions. -/
theorem localizationMorphism_inverseImage_eq_comp :
    (X.localizationMorphism F).toToposHom.inverseImage =
      ((X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.comp
        (X.relocalizationMorphismOfTopoi s)).inverseImage :=
  rfl

/-- **Stacks 04J8**, commutativity of the localization square on inverse images:
`f⁻¹ ⋙ j_F⁻¹ ≅ j_G⁻¹ ⋙ (f_s)⁻¹`.

Since `j_F⁻¹` is `j_{f⁻¹G}⁻¹` followed by the inverse image of the relocalization along `s` on
the nose, this is Stacks 04IF's inverse-image square whiskered by that relocalization. -/
@[stacks 04J8 "commutativity of the localization square, on inverse images"]
noncomputable def relocalizedInverseImageSquare :
    (comp (X := X.localizedRingedTopos F) (Y := X) (Z := Y) f
        (X.localizationMorphism F)).toToposHom.inverseImage ≅
      (comp (X := X.localizedRingedTopos F) (Y := Y.localizedRingedTopos G) (Z := Y)
        (Y.localizationMorphism G) (f.relocalized s)).toToposHom.inverseImage :=
  (Functor.associator f.toToposHom.inverseImage
      (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage
      (X.relocalizationMorphismOfTopoi s).inverseImage).symm ≪≫
    Functor.isoWhiskerRight (f.inverseImageCompLocalizationIso G)
      (X.relocalizationMorphismOfTopoi s).inverseImage ≪≫
    Functor.associator _ _ _

/-- The components of `relocalizedInverseImageSquare`: the two reassociations have identity
components, so the comparison is Stacks 04IF's square restricted along the relocalization. -/
theorem relocalizedInverseImageSquare_hom_app (H : Y.Topos) :
    (f.relocalizedInverseImageSquare s).hom.app H =
      (X.relocalizationMorphismOfTopoi s).inverseImage.map
        ((f.inverseImageCompLocalizationIso G).hom.app H) := by
  change 𝟙 _ ≫ (X.relocalizationMorphismOfTopoi s).inverseImage.map
      ((f.inverseImageCompLocalizationIso G).hom.app H) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- **Stacks 04J8**, commutativity of the localization square as a square of *topoi*: the
comparison of the two direct images conjugate to `relocalizedInverseImageSquare`.

This is the underlying morphism-of-topoi content of the square; its compatibility with the
structure sheaves is `relocalizedRingedSquare`. -/
@[stacks 04J8 "commutativity of the localization square, as a square of topoi"]
noncomputable def relocalizedToposSquare :
    (comp (X := X.localizedRingedTopos F) (Y := Y.localizedRingedTopos G) (Z := Y)
        (Y.localizationMorphism G) (f.relocalized s)).toToposHom.pushforward ≅
      (comp (X := X.localizedRingedTopos F) (Y := X) (Z := Y) f
        (X.localizationMorphism F)).toToposHom.pushforward :=
  conjugateIsoEquiv (comp (X := X.localizedRingedTopos F) (Y := Y.localizedRingedTopos G) (Z := Y)
      (Y.localizationMorphism G) (f.relocalized s)).toToposHom.adj
    (comp (X := X.localizedRingedTopos F) (Y := X) (Z := Y) f
      (X.localizationMorphism F)).toToposHom.adj (f.relocalizedInverseImageSquare s)

/-! ### The structure maps of the localization and relocalization morphisms

Both are the canonical identification of an inverse image of a structure sheaf with a
restriction, so both are the identity on underlying sheaves of sets. -/

/-- The inverse-image form of the structure map of the localization morphism is the identity on
underlying sheaves of sets. -/
theorem forgetRing_localizationMorphism_fSharpInverseImage (Z : RingedTopos.{v, u, v})
    [EssentiallySmall.{v} Z.C]
    (H : Z.Topos) :
    (Z.localizedRingedTopos H).forgetRing.map
        (Z.localizationMorphism H).fSharpInverseImage =
      𝟙 ((Z.localizedRingedTopos H).forgetRing.obj (Z.localizedRingedTopos H).O) :=
  (congrArg (Z.localizedRingedTopos H).forgetRing.map
      (Z.localization_fSharp_inverseImage H)).trans
    (restrictionCommRingIso_hom_forget (Z.elementTopology H) Z.J (Z.elementProjection H) Z.O)

/-- The inverse-image form of the structure map of the relocalization morphism is the identity
on underlying sheaves of sets. -/
theorem forgetRing_relocalizationMorphism_fSharpInverseImage (Z : RingedTopos.{v, u, v})
    [EssentiallySmall.{v} Z.C]
    {H K : Z.Topos} (a : H ⟶ K) :
    (Z.localizedRingedTopos H).forgetRing.map
        (Z.relocalizationMorphism a).fSharpInverseImage =
      𝟙 ((Z.localizedRingedTopos H).forgetRing.obj (Z.localizedRingedTopos H).O) :=
  (congrArg (Z.localizedRingedTopos H).forgetRing.map
      (Z.relocalization_fSharp_inverseImage a)).trans
    (restrictionCommRingIso_hom_forget (Z.elementTopology H) (Z.elementTopology K)
      (CostructuredArrow.map a.hom)
      (Z.localizedRingedTopos K).O)

/-! ### The localization square as a square of ringed topoi -/

/-- **Stacks 04J8**, commutativity of the localization square as a square of *ringed* topoi.

The structure-map compatibility of Stacks 04IF's own square is
`AlgebraicGeometry.RingedToposHom.localized_fSharpInverseImage_forget`: the inverse-image form of
`(f')♯` for the morphism `f'` of Stacks 04IF, read through 04IF's inverse-image square, is the
restriction of the inverse-image form of `f♯` to the site of elements of `f⁻¹G`. It is the one
thing beyond the inverse-image and pushforward squares of Stacks 04IF that commutativity of 04J8's
square as a square of ringed topoi needs; see the implementation notes of this file.

Given it, the square for `f_s` follows with no further geometry: the structure map of the
relocalization along `s` and that of the two localization morphisms are identities on
underlying sheaves of sets, and `j_F⁻¹` is `j_{f⁻¹G}⁻¹` followed by the inverse image of the
relocalization on the nose. -/
@[stacks 04J8 "commutativity of the localization square as a square of ringed topoi"]
noncomputable def relocalizedRingedSquare :
    TwoIso (A := X.localizedRingedTopos F) (B := Y)
      (comp (X := X.localizedRingedTopos F) (Y := Y.localizedRingedTopos G) (Z := Y)
          (Y.localizationMorphism G) (f.relocalized s))
      (comp (X := X.localizedRingedTopos F) (Y := X) (Z := Y) f
        (X.localizationMorphism F)) :=
  TwoIso.ofInverseImageIso (A := X.localizedRingedTopos F) (B := Y)
    (f.relocalizedInverseImageSquare s) (by
      have hjG := forgetRing_localizationMorphism_fSharpInverseImage Y G
      have hjF := forgetRing_localizationMorphism_fSharpInverseImage X F
      have hrs := forgetRing_relocalizationMorphism_fSharpInverseImage X s
      have hL : (f.relocalized s).toToposHom.inverseImage.map
            ((Y.localizedRingedTopos G).forgetRing.map
              (Y.localizationMorphism G).fSharpInverseImage) =
          𝟙 ((f.relocalized s).toToposHom.inverseImage.obj
            ((Y.localizedRingedTopos G).forgetRing.obj (Y.localizedRingedTopos G).O)) :=
        (congrArg (f.relocalized s).toToposHom.inverseImage.map hjG).trans
          ((f.relocalized s).toToposHom.inverseImage.map_id _)
      have hP : (X.localizedRingedTopos F).forgetRing.map
            (comp (X := X.localizedRingedTopos F) (Y := Y.localizedRingedTopos G) (Z := Y)
              (Y.localizationMorphism G) (f.relocalized s)).fSharpInverseImage =
          (X.localizedRingedTopos F).forgetRing.map (f.relocalized s).fSharpInverseImage :=
        (comp_fSharpInverseImage_forget (X := X.localizedRingedTopos F)
            (Y := Y.localizedRingedTopos G) (Z := Y) (Y.localizationMorphism G)
            (f.relocalized s)).trans
          ((congrArg (fun z ↦ z ≫ (X.localizedRingedTopos F).forgetRing.map
              (f.relocalized s).fSharpInverseImage) hL).trans (Category.id_comp _))
      have hFs : (X.localizedRingedTopos F).forgetRing.map (f.relocalized s).fSharpInverseImage =
          (X.relocalizationMorphismOfTopoi s).inverseImage.map
            ((X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).forgetRing.map
              (f.localized G).fSharpInverseImage) :=
        (comp_fSharpInverseImage_forget (X := X.localizedRingedTopos F)
            (Y := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G))
            (Z := Y.localizedRingedTopos G) (f.localized G)
            (X.relocalizationMorphism s)).trans
          ((congrArg (fun z ↦ (X.relocalizationMorphismOfTopoi s).inverseImage.map
              ((X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).forgetRing.map
                (f.localized G).fSharpInverseImage) ≫ z) hrs).trans (Category.comp_id _))
      have hQ : (X.localizedRingedTopos F).forgetRing.map
            (comp (X := X.localizedRingedTopos F) (Y := X) (Z := Y) f
              (X.localizationMorphism F)).fSharpInverseImage =
          (X.localizationMorphism F).toToposHom.inverseImage.map
            (X.forgetRing.map f.fSharpInverseImage) :=
        (comp_fSharpInverseImage_forget (X := X.localizedRingedTopos F) (Y := X) (Z := Y) f
            (X.localizationMorphism F)).trans
          ((congrArg (fun z ↦ (X.localizationMorphism F).toToposHom.inverseImage.map
              (X.forgetRing.map f.fSharpInverseImage) ≫ z) hjF).trans (Category.comp_id _))
      refine Eq.trans (congrArg (fun z ↦ (f.relocalizedInverseImageSquare s).hom.app
          (Y.forgetRing.obj Y.O) ≫ z) (hP.trans hFs)) (Eq.trans ?_ hQ.symm)
      refine Eq.trans (congrArg (fun z ↦ z ≫ (X.relocalizationMorphismOfTopoi s).inverseImage.map
          ((X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).forgetRing.map
            (f.localized G).fSharpInverseImage))
        (relocalizedInverseImageSquare_hom_app f s (Y.forgetRing.obj Y.O))) ?_
      exact (((X.relocalizationMorphismOfTopoi s).inverseImage.map_comp _ _).symm).trans
        (congrArg (X.relocalizationMorphismOfTopoi s).inverseImage.map
          (f.localized_fSharpInverseImage_forget G)))

/-! ### Changing the sheaf on the target -/

/-- **The two localized morphisms `f'` agree over a change of the sheaf on the target.** For
`b : G' ⟶ G` on the target, the inverse image of the morphism `f'` of Stacks 04IF at `G`,
followed by the inverse image of the relocalization of `X` along `f⁻¹b`, is the inverse image of
the relocalization of `Y` along `b` followed by the inverse image of `f'` at `G'`.

Read through the identifications of Stacks 04IE, the inverse image of `f'` is `Over.post f⁻¹`
and the inverse image of a relocalization is base change
(`AlgebraicGeometry.RingedTopos.relocalizationFibreIso` and
`AlgebraicGeometry.RingedTopos.relocalizationInverseImageSliceIso`, Stacks 04J4), so the
statement becomes the Beck-Chevalley isomorphism `CategoryTheory.Over.postPullbackIso` for the
left exact functor `f⁻¹`. -/
noncomputable def localizedCompRelocalizationIso {G G' : Y.Topos} (b : G' ⟶ G) :
    (f.localized G).toToposHom.inverseImage ⋙
        (X.relocalizationMorphism (f.toToposHom.inverseImage.map b)).toToposHom.inverseImage ≅
      (Y.relocalizationMorphism b).toToposHom.inverseImage ⋙
        (f.localized G').toToposHom.inverseImage :=
  haveI := f.toToposHom.preservesFiniteLimits
  Functor.isoWhiskerLeft
      ((Y.localizationEquivalence G).functor ⋙ Over.post f.toToposHom.inverseImage)
      (X.relocalizationFibreIso (f.toToposHom.inverseImage.map b)) ≪≫
    Functor.isoWhiskerLeft (Y.localizationEquivalence G).functor
      (Functor.isoWhiskerRight (Over.postPullbackIso f.toToposHom.inverseImage b).symm
        (X.localizationEquivalence (f.toToposHom.inverseImage.obj G')).inverse) ≪≫
    Functor.isoWhiskerRight (Y.relocalizationInverseImageSliceIso b).symm
      (Over.post f.toToposHom.inverseImage ⋙
        (X.localizationEquivalence (f.toToposHom.inverseImage.obj G')).inverse)

end AlgebraicGeometry.RingedToposHom

end

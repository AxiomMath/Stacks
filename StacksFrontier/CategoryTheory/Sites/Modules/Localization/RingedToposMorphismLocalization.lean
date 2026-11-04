module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageComposition
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.SliceEquivalence
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.OverPushforward
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
import StacksCore.Tactic.StacksAttribute

/-!
# Localization of a morphism of ringed topoi at a sheaf and its inverse image

Let `(f, f♯) : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi, let `G` be a sheaf of
sets on `D` and put `F = f⁻¹G`. Localizing the source at `F` and the target at `G` gives ringed
topoi `(Sh(C)/F, O_F)` and `(Sh(D)/G, O'_G)`, and `f` localizes to a morphism of ringed topoi
`(f', (f')♯) : (Sh(C)/F, O_F) ⟶ (Sh(D)/G, O'_G)` fitting in a square with the two localization
morphisms `j_F` and `j_G`. Its inverse image is characterized by
`(f')⁻¹(H ⟶ G) = (f⁻¹H ⟶ F)`, and `f'_* j_F⁻¹ = j_G⁻¹ f_*`.

The two localizations are the ringed topoi on the sites of elements of `F` and of `G`
(`AlgebraicGeometry.RingedTopos.localizedRingedTopos`), so `f'` is obtained by transporting the
slice-topos morphism `Over.post f⁻¹` of Stacks 04H1 across the identification of each
localization with its slice topos (Stacks 04IE). The structure map is the restriction
`j_G⁻¹(f♯)` of the structure map of `f`, read through the ring-level form of the identity
`f'_* j_F⁻¹ = j_G⁻¹ f_*` and through the identification `j⁻¹O ≅ O_F` of the inverse image of a
structure sheaf with the localized structure sheaf; this is the first of the two adjoint
descriptions the source gives.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.localizedToposMorphism`: the morphism of topoi
  `f' : Sh(C)/F ⟶ Sh(D)/G` on the two localizations.
* `AlgebraicGeometry.RingedToposHom.localized`: the localized morphism of ringed topoi
  `(f', (f')♯)`.

## Main results

* `AlgebraicGeometry.RingedToposHom.localizedInverseImageIso`: the inverse image of `f'`, read
  through the identifications with the slice topoi, is `Over.post f⁻¹`; this is the rule
  `(f')⁻¹(H ⟶ G) = (f⁻¹H ⟶ F)` which characterizes `f'`.
* `AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso`: the square commutes on
  inverse images, `f⁻¹ ⋙ j_F⁻¹ = j_G⁻¹ ⋙ (f')⁻¹`.
* `AlgebraicGeometry.RingedToposHom.localizationCompPushforwardIso` and
  `.localizedPushforwardCommRingIso`: the displayed identity `f'_* j_F⁻¹ = j_G⁻¹ f_*`, on
  sheaves of sets and on sheaves of commutative rings.
* `MorphismOfTopoi.inverseImageCompToOverIso_hom_app_comp_counit`: **the step the source
  omits** — the two descriptions the source gives of `(f')♯` are adjoint to each other — at the
  level of the slice topoi of Stacks 04H1. Equivalently: the comparison of inverse images in
  04H1's square is the mate of its comparison of direct images.
* `AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso_hom_app`,
  `.localizationCompPushforwardIso_inv_app`, `.localizedToposMorphism_adj_counit_app`: the three
  comparisons of this file read componentwise, as 04H1's data conjugated by the identifications
  of Stacks 04IE.
* `AlgebraicGeometry.RingedToposHom.localized_fSharp_forget`: the structure map of `f'`, on
  underlying sheaves of sets, is `j_G⁻¹(f♯)` followed by the comparison of direct images.
* `AlgebraicGeometry.RingedToposHom.localized_fSharpInverseImage_forget`: **the square of
  Stacks 04IF is a square of ringed topoi** — the comparison of inverse images carries the
  structure map of `f`, restricted to the site of elements of `f⁻¹G`, to the structure map of
  `f'`. This is the compatibility that
  `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` consumes.

## Implementation notes

The source states the sheaf `F` to be localized at as `f⁻¹G`, and that is how it appears below:
every declaration is about the localization of the source at `f.toToposHom.inverseImage.obj G`.
This is not a convenience but a necessity, since `MorphismOfTopoi.over` — Stacks 04H1, which
supplies the slice-level morphism and both halves of the commutative square — is defined only
for that sheaf.

Two things make the transport across the identifications with the slice topoi cheap. The
identification of the inverse image of the localization morphism with `toOver` is Stacks 04IE
part (1), already available as
`AlgebraicGeometry.RingedTopos.localizationInverseImageIso`; and transporting the commutative
ring operations along an isomorphism of finite-product-preserving functors of sheaves of sets is
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorIsoOfNatIso`, so the ring-level form of
`f'_* j_F⁻¹ = j_G⁻¹ f_*` needs no computation beyond composing that with the two comparisons of
iterated inverse images.

`Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor` and `.pushforwardCommRingFunctor`
leave the two sites, their morphisms and the sections implicit, to be recovered from the
morphism of topoi they are applied to. Inside the type of an isomorphism that recovery is
postponed past the point where the universe parameters are fixed, so the statement of
`localizedPushforwardCommRingIso` supplies them explicitly. For the same reason its proof names
the two topologies as the structure fields
`(_.localizedRingedTopos _).J`, the spelling under which the localized topos is the source of
the localization morphism, rather than as `AlgebraicGeometry.RingedTopos.elementTopology`.

**What is not carried.** The source also asserts that `f'_* j_F^* = j_G^* f_*` on sheaves of
modules. That is not proved here: it needs the module categories of the two localizations and
the comparison of their pullbacks, which is the content of Stacks 04IE part (2) for `f'`.

That the square commutes *as a square of ringed topoi* — that the comparison of inverse images
is compatible with the three structure maps — **is** proved here, as
`localized_fSharpInverseImage_forget`, and it is the analogue for an arbitrary sheaf `G` of
`AlgebraicGeometry.RingedSite.Hom.localizedRingedSquare` (Stacks 04J0 for `G = h_V^#`). The
proof of that one rests on a strict equality `f'_* j_U⁻¹ = j_V⁻¹ f_*` of functors coming from a
continuous functor of sites; for a general sheaf that identity is only the isomorphism
`localizationCompPushforwardIso` below, so here the compatibility is a computation rather than a
transcription, and the input it needs is the adjointness the source omits.

That adjointness is `MorphismOfTopoi.inverseImageCompToOverIso_hom_app_comp_counit`: 04H1's two
faces are mates of each other, which is the compatibility of the structure map of `f'` with the
inverse-image square at the slice topoi. It is transported to the two localizations by
`inverseImageCompLocalizationIso_hom_app_comp_counit`, using the three componentwise
descriptions `AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso_hom_app`,
`.localizationCompPushforwardIso_inv_app` and `.localizedToposMorphism_adj_counit_app`, each
exhibiting the comparison as 04H1's face conjugated by `RingedTopos.localizationInverseImageIso`
and by the unit or counit of `RingedTopos.localizationEquivalence`, together with
`CategoryTheory.Equivalence.unitIso_hom_app_comp_inverse_map_functor_map` and
`.functor_map_unitIso_hom_app_comp_counitIso`, which cancel those conjugations. What then turns
it into the ringed-topoi statement is `localized_fSharp_forget`, which reads the structure map
of `f'` on underlying sheaves of sets; the two structure maps are adjunct to their direct-image
forms, so matching them up is naturality of the comparison of inverse images at `f♯`.

The forgetting in `localized_fSharp_forget` is done one factor at a time, and each factor's
identity is applied by `congrArg` rather than by `rewrite` or `simp`. The direct image of
Stacks 04H1's slice morphism lands in chosen pullbacks, whose defining data the module system
does not expose, so the two spellings of the direct image of such a pullback — the iterated
inverse image and the inverse image of the composite — can be compared only through the
set-level object that both reduce to, never with each other. Every identity below therefore
names that object explicitly, and the two cancellations of an identity at the end of
`localized_fSharp_forget` name it as well.

Universes follow the localization: the morphisms of the sites and the sections of the
structure sheaves lie in one universe `v`, and the objects of the two sites in universes `u` and
`u'` of their own, the sites being essentially small for `v`. The localizations are then
`RingedTopos.{v, max u v, v}` and `RingedTopos.{v, max u' v, v}`; this is what lets the small
étale ringed topoi of algebraic spaces be localized.

## References

* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 04H1](https://stacks.math.columbia.edu/tag/04H1)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe v u u'

namespace MorphismOfTopoi

open MonoidalCategory CartesianMonoidalCategory

universe v₁ w₁ v₂ w₂

variable {E : Type w₁} [Category.{v₁} E] {D : Type w₂} [Category.{v₂} D]
  (f : MorphismOfTopoi E D) (G : D) [HasPullbacks D]
  [CartesianMonoidalCategory E] [CartesianMonoidalCategory D]

/-- The comparison of the two direct images in Stacks 04H1's square, read on the first
projection out of `j_F⁻¹K = K × F`.

The square `f'_* j_F⁻¹ = j_G⁻¹ f_*` is the comparison of two right adjoints of the strict
identity `(f')⁻¹ ∘ j_{F!} = j_{G!} ∘ f⁻¹`, so this is uniqueness of right adjoints
(`CategoryTheory.Adjunction.homEquiv_symm_rightAdjointUniq_hom_app`) with the two counits
written out. -/
theorem toOverCompPushforwardIso_inv_app_left_comp_fst (K : E) :
    f.inverseImage.map ((f.toOverCompPushforwardIso G).inv.app K).left ≫
        ((f.over G).adj.counit.app ((toOver (f.inverseImage.obj G)).obj K)).left ≫
          fst K (f.inverseImage.obj G) =
      f.inverseImage.map (fst (f.pushforward.obj K) G) ≫ f.adj.counit.app K := by
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    ((forgetAdjToOver G).comp f.adj)
    (Over.post_forget_eq_forget_comp f.inverseImage G ▸
      (f.over G).adj.comp (forgetAdjToOver (f.inverseImage.obj G))) K
  rw [Adjunction.homEquiv_counit] at h
  have h2 : (Over.forget G ⋙ f.inverseImage).map ((f.toOverCompPushforwardIso G).inv.app K) ≫
      ((f.over G).adj.comp (forgetAdjToOver (f.inverseImage.obj G))).counit.app K =
      ((forgetAdjToOver G).comp f.adj).counit.app K := h
  rw [Adjunction.comp_counit_app, Adjunction.comp_counit_app] at h2
  exact h2

/-- **The two faces of Stacks 04H1's square are adjoint to each other.** The comparison of
inverse images `inverseImageCompToOverIso` is the mate of the comparison of direct images
`toOverCompPushforwardIso`: transposing the latter at `K` and composing with the former recovers
`j_F⁻¹` of the counit of `f⁻¹ ⊣ f_*`.

This is the verification that Stacks 04IF omits — that the two descriptions it gives of the
structure map of the localized morphism are adjoint to each other — at the level of the slice
topoi. Both faces come from the strict identity
`Over.post f⁻¹ ⋙ Over.forget (f⁻¹G) = Over.forget G ⋙ f⁻¹`: the direct-image face is the
comparison of two right adjoints of it, the inverse-image face is the monoidal comparison of
`f⁻¹` with products, and the two are matched on the first projection by
`toOverCompPushforwardIso_inv_app_left_comp_fst` and `Functor.Monoidal.μ_fst`. On the second
projection both sides are the structure map of the slice, so there is nothing to check. -/
theorem inverseImageCompToOverIso_hom_app_comp_counit (K : E) :
    (f.inverseImageCompToOverIso G).hom.app (f.pushforward.obj K) ≫
        (f.over G).inverseImage.map ((f.toOverCompPushforwardIso G).inv.app K) ≫
          (f.over G).adj.counit.app ((toOver (f.inverseImage.obj G)).obj K) =
      (toOver (f.inverseImage.obj G)).map (f.adj.counit.app K) := by
  have := f.preservesFiniteLimits
  let _ : f.inverseImage.Monoidal := Functor.Monoidal.ofChosenFiniteProducts f.inverseImage
  refine Over.OverMorphism.ext (hom_ext _ _ ?_ ?_)
  · exact Eq.trans (Eq.trans (Category.assoc _ _ _)
      (congrArg (fun z =>
          (Functor.Monoidal.μIso f.inverseImage (f.pushforward.obj K) G).hom ≫ z)
        (Category.assoc _ _ _)))
      (Eq.trans (congrArg (fun z =>
            (Functor.Monoidal.μIso f.inverseImage (f.pushforward.obj K) G).hom ≫ z)
          (f.toOverCompPushforwardIso_inv_app_left_comp_fst G K))
        (Eq.trans (Functor.Monoidal.μ_fst_assoc f.inverseImage (f.pushforward.obj K) G
            (f.adj.counit.app K))
          (whiskerRight_fst (f.adj.counit.app K) (f.inverseImage.obj G)).symm))
  · exact (Over.w _).trans (Over.w _).symm

end MorphismOfTopoi

namespace CategoryTheory.Equivalence

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- Transporting a morphism along an equivalence and back gives the morphism again. -/
theorem unitIso_hom_app_comp_inverse_map_functor_map (e : C ≌ D) {A B : C} (g : A ⟶ B) :
    e.unitIso.hom.app A ≫ e.inverse.map (e.functor.map g) ≫ e.unitIso.inv.app B = g := by
  simp

/-- Transport of a three-step composite along an equivalence: if the composite agrees with the
image of `g` under the functor, then its image under the inverse, sandwiched between the unit
and its inverse, is `g`. -/
theorem unitIso_hom_app_comp_map₃ (e : C ≌ D) {A B : C} {Z₁ Z₂ : D}
    (n : e.functor.obj A ⟶ Z₁) (p : Z₁ ⟶ Z₂) (c : Z₂ ⟶ e.functor.obj B) (g : A ⟶ B)
    (h : n ≫ p ≫ c = e.functor.map g) :
    e.unitIso.hom.app A ≫ e.inverse.map n ≫ e.inverse.map p ≫ e.inverse.map c ≫
        e.unitIso.inv.app B = g := by
  rw [← e.inverse.map_comp_assoc, ← e.inverse.map_comp_assoc, Category.assoc, h]
  exact e.unitIso_hom_app_comp_inverse_map_functor_map g

/-- The transpose of the previous transport: the functor of an equivalence carries a morphism
assembled out of the unit and the inverse back to the morphism it came from. -/
theorem functor_map_unitIso_hom_app_comp_counitIso (e : C ≌ D) {A : C} {B : D}
    (m : e.functor.obj A ⟶ B) :
    e.functor.map (e.unitIso.hom.app A ≫ e.inverse.map m) ≫ e.counitIso.hom.app B = m := by
  simp

end CategoryTheory.Equivalence

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, v}} {Y : RingedTopos.{v, u', v}} [EssentiallySmall.{v} X.C]
  [EssentiallySmall.{v} Y.C] (f : RingedToposHom X Y) (G : Y.Topos)

/-- The **morphism of topoi underlying the localized morphism**: with `F = f⁻¹G`, the morphism
`f' : Sh(C)/F ⟶ Sh(D)/G` obtained from the slice-topos morphism of Stacks 04H1 by transporting
it across the identifications of the two localizations with their slice topoi. Its inverse image
and its direct image are the conjugates of `Over.post f⁻¹` and of its right adjoint. -/
noncomputable def localizedToposMorphism :
    MorphismOfTopoi (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).Topos
      (Y.localizedRingedTopos G).Topos where
  inverseImage := (Y.localizationEquivalence G).functor ⋙
    (f.toToposHom.over G).inverseImage ⋙
    (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).inverse
  pushforward := (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).functor ⋙
    (f.toToposHom.over G).pushforward ⋙ (Y.localizationEquivalence G).inverse
  adj := ((Y.localizationEquivalence G).toAdjunction.comp (f.toToposHom.over G).adj).comp
    (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).symm.toAdjunction
  preservesFiniteLimits :=
    haveI := (f.toToposHom.over G).preservesFiniteLimits
    haveI : PreservesFiniteLimits ((f.toToposHom.over G).inverseImage ⋙
        (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).inverse) :=
      comp_preservesFiniteLimits _ _
    comp_preservesFiniteLimits _ _

/-- **Stacks 04IF**, the rule characterizing `f'`: read through the identifications of the two
localizations with their slice topoi, the inverse image of `f'` is `Over.post f⁻¹`, that is
```
(f')⁻¹(H ⟶ G) = (f⁻¹H ⟶ f⁻¹G) .
```
-/
@[stacks 04IF "the characterization (f')^{-1}(H → G) = (f^{-1}H → F) of f'"]
noncomputable def localizedInverseImageIso :
    (localizedToposMorphism f G).inverseImage ⋙
        (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).functor ≅
      (Y.localizationEquivalence G).functor ⋙ Over.post f.toToposHom.inverseImage :=
  Functor.isoWhiskerLeft
      ((Y.localizationEquivalence G).functor ⋙ (f.toToposHom.over G).inverseImage)
      (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).counitIso ≪≫
    Functor.rightUnitor _

/-- **Stacks 04IF**, commutativity of the square on inverse images: `f⁻¹ ⋙ j_F⁻¹ = j_G⁻¹ ⋙
(f')⁻¹`. Concretely, the inverse image of a sheaf `H` on `D`, localized at `F`, is the inverse
image under `f'` of `H` localized at `G`; this is Stacks 04H1's version of the same square,
transported across the identifications of the localizations with their slice topoi. -/
@[stacks 04IF "commutativity of the square, on inverse images"]
noncomputable def inverseImageCompLocalizationIso :
    f.toToposHom.inverseImage ⋙
        (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage ≅
      (Y.localizationMorphism G).toToposHom.inverseImage ⋙
        (localizedToposMorphism f G).inverseImage :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (f.toToposHom.inverseImage ⋙
        (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage)
      (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).unitIso ≪≫
    Functor.isoWhiskerLeft f.toToposHom.inverseImage
      (Functor.isoWhiskerRight
        (X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G))
        (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).inverse) ≪≫
    Functor.isoWhiskerRight (f.toToposHom.inverseImageCompToOverIso G)
      (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).inverse ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
        (Y.localizationInverseImageIso G).symm (f.toToposHom.over G).inverseImage)
      (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).inverse

/-- **Stacks 04IF**: `f'_* j_F⁻¹ = j_G⁻¹ f_*`, on sheaves of sets.

This is Stacks 04H1's identity `f'_* ∘ toOver F = toOver G ∘ f_*` for the slice topoi, read
through the identification of the inverse image of each localization morphism with `toOver`
(Stacks 04IE part (1)) and through the two identifications of the localizations with their
slice topoi. -/
@[stacks 04IF "f'_* j_F^{-1} = j_G^{-1} f_*, on sheaves of sets"]
noncomputable def localizationCompPushforwardIso :
    (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage ⋙
        (localizedToposMorphism f G).pushforward ≅
      f.toToposHom.pushforward ⋙ (Y.localizationMorphism G).toToposHom.inverseImage :=
  Functor.isoWhiskerRight
      (X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G))
      ((f.toToposHom.over G).pushforward ⋙ (Y.localizationEquivalence G).inverse) ≪≫
    Functor.isoWhiskerRight (f.toToposHom.toOverCompPushforwardIso G)
      (Y.localizationEquivalence G).inverse ≪≫
    Functor.isoWhiskerLeft f.toToposHom.pushforward
      (Functor.isoWhiskerRight (Y.localizationInverseImageIso G).symm
        (Y.localizationEquivalence G).inverse) ≪≫
    Functor.isoWhiskerLeft (f.toToposHom.pushforward ⋙
      (Y.localizationMorphism G).toToposHom.inverseImage)
      (Y.localizationEquivalence G).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- **Stacks 04IF**: `f'_* j_F⁻¹ = j_G⁻¹ f_*`, on sheaves of commutative rings.

The inverse image and the direct image of sheaves of commutative rings along a morphism of topoi
are obtained by transporting the ring operations along the corresponding functor of sheaves of
sets, so this is the set-level identity `localizationCompPushforwardIso` transported, composed
with the two comparisons of an iterated inverse image with the inverse image of the composite. -/
noncomputable def localizedPushforwardCommRingIso :
    inverseImageCommRingFunctor.{v, v, v, max u v, v, u}
          (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom ⋙
        pushforwardCommRingFunctor.{v, v, v, max u v, v, max u' v}
          (localizedToposMorphism f G) ≅
      pushforwardCommRingFunctor.{v, v, v, u, v, u'} f.toToposHom ⋙
        inverseImageCommRingFunctor.{v, v, v, max u' v, v, u'}
          (Y.localizationMorphism G).toToposHom :=
  let source := pullbackCommRingSheafFunctorComp
    (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).J (Y.localizedRingedTopos G).J
    (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage
    (localizedToposMorphism f G).pushforward
  let transport := pullbackCommRingSheafFunctorIsoOfNatIso.{v, v, v, max u' v, v, u}
    (Y.localizedRingedTopos G).J
    (localizationCompPushforwardIso f G)
  let target := pullbackCommRingSheafFunctorComp Y.J (Y.localizedRingedTopos G).J
    f.toToposHom.pushforward (Y.localizationMorphism G).toToposHom.inverseImage
  source ≪≫ transport ≪≫ target.symm

/-- **Stacks 04IF.** The **localized morphism of ringed topoi**
`(f', (f')♯) : (Sh(C)/F, O_F) ⟶ (Sh(D)/G, O'_G)`, with `F = f⁻¹G`.

Its structure map is the restriction `j_G⁻¹(f♯)` of the structure map of `f`: the localized
structure sheaf `O'_G` is the inverse image `j_G⁻¹O'`, applying `j_G⁻¹` to `f♯ : O' ⟶ f_*O` lands
in `j_G⁻¹f_*O`, and that is `f'_*j_F⁻¹O = f'_*O_F` by
`localizedPushforwardCommRingIso`. -/
@[stacks 04IF "the localized morphism of ringed topoi (f', (f')^sharp)"]
noncomputable def localized :
    RingedToposHom (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G))
      (Y.localizedRingedTopos G) where
  toToposHom := localizedToposMorphism f G
  fSharp :=
    (Y.localizationInverseImageCommRingIso G).inv ≫
      (inverseImageCommRingFunctor (Y.localizationMorphism G).toToposHom).map f.fSharp ≫
      (localizedPushforwardCommRingIso f G).inv.app X.O ≫
      (pushforwardCommRingFunctor (localizedToposMorphism f G)).map
        (X.localizationInverseImageCommRingIso (f.toToposHom.inverseImage.obj G)).hom

/-- The morphism of topoi underlying the localized morphism of ringed topoi is
`localizedToposMorphism`. -/
@[simp]
theorem localized_toToposHom : (localized f G).toToposHom = localizedToposMorphism f G := rfl

/-- Stacks 04IF's comparison of inverse images, componentwise: the whiskerings with the
identifications of Stacks 04IE, read at a sheaf on the target. -/
theorem inverseImageCompLocalizationIso_hom_app (A : Y.Topos) :
    (f.inverseImageCompLocalizationIso G).hom.app A =
      (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).unitIso.hom.app
          ((X.localizationMorphism
            (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj
              (f.toToposHom.inverseImage.obj A)) ≫
        (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).inverse.map
          ((X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G)).hom.app
              (f.toToposHom.inverseImage.obj A) ≫
            (f.toToposHom.inverseImageCompToOverIso G).hom.app A ≫
              (f.toToposHom.over G).inverseImage.map
                ((Y.localizationInverseImageIso G).inv.app A)) := by
  simp only [inverseImageCompLocalizationIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app,
    Category.id_comp, CategoryTheory.Functor.map_comp]
  rfl

/-- Stacks 04IF's comparison of direct images, componentwise. -/
theorem localizationCompPushforwardIso_inv_app (K : X.Topos) :
    (localizationCompPushforwardIso f G).inv.app K =
      (Y.localizationEquivalence G).unitIso.hom.app
          ((Y.localizationMorphism G).toToposHom.inverseImage.obj
            (f.toToposHom.pushforward.obj K)) ≫
        (Y.localizationEquivalence G).inverse.map
          ((Y.localizationInverseImageIso G).hom.app (f.toToposHom.pushforward.obj K) ≫
            (f.toToposHom.toOverCompPushforwardIso G).inv.app K ≫
              (f.toToposHom.over G).pushforward.map
                ((X.localizationInverseImageIso
                  (f.toToposHom.inverseImage.obj G)).inv.app K)) := by
  simp only [localizationCompPushforwardIso]
  rfl

omit [EssentiallySmall.{v} X.C] [EssentiallySmall.{v} Y.C] in
/-- The counit of the localized morphism of topoi, componentwise: the counit of Stacks 04H1's
slice morphism, conjugated by the two identifications of Stacks 04IE. -/
theorem localizedToposMorphism_adj_counit_app
    (W : (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).Topos) :
    (localizedToposMorphism f G).adj.counit.app W =
      (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).inverse.map
          ((f.toToposHom.over G).inverseImage.map
              ((Y.localizationEquivalence G).counitIso.hom.app
                ((f.toToposHom.over G).pushforward.obj
                  ((X.localizationEquivalence
                    (f.toToposHom.inverseImage.obj G)).functor.obj W))) ≫
            (f.toToposHom.over G).adj.counit.app
              ((X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).functor.obj W)) ≫
        (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).unitIso.inv.app W := by
  simp only [localizedToposMorphism, Adjunction.comp_counit_app, Functor.comp_obj,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

/-- **Stacks 04IF**, the omitted adjointness, at the two localizations: the comparison of
inverse images of 04IF's square is the mate of its comparison of direct images.

Both comparisons are built by whiskering 04H1's two faces with the identifications of the two
localizations with their slice topoi (Stacks 04IE), so this is
`MorphismOfTopoi.inverseImageCompToOverIso_hom_app_comp_counit` with those identifications
cancelled: the two copies of Stacks 04IE at `G` cancel against each other, the two at `f⁻¹G`
cancel against the unit and the counit of the equivalence, and what is left is 04H1's
adjointness conjugated by the naturality of Stacks 04IE at `f⁻¹G`.

The proof is written without `rewrite`. The objects of the slice topos `Sh(D)/G` that the
direct image of Stacks 04H1's morphism lands in are chosen pullbacks, whose defining data the
module system does not expose, so the type-correctness check that `rewrite` performs on the
rewritten goal cannot be discharged; every step is therefore an explicit `Eq.trans` of a
`congrArg`, for which no such check arises. -/
theorem inverseImageCompLocalizationIso_hom_app_comp_counit (K : X.Topos) :
    (f.inverseImageCompLocalizationIso G).hom.app (f.toToposHom.pushforward.obj K) ≫
        (localizedToposMorphism f G).inverseImage.map
            ((localizationCompPushforwardIso f G).inv.app K) ≫
          (localizedToposMorphism f G).adj.counit.app
            ((X.localizationMorphism
              (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj K) =
      (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map
        (f.toToposHom.adj.counit.app K) := by
  have hmid : (Y.localizationEquivalence G).functor.map
          ((localizationCompPushforwardIso f G).inv.app K) ≫
        (Y.localizationEquivalence G).counitIso.hom.app
          ((f.toToposHom.over G).pushforward.obj
            ((X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).functor.obj
              ((X.localizationMorphism
                (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj K))) =
      (Y.localizationInverseImageIso G).hom.app (f.toToposHom.pushforward.obj K) ≫
        (f.toToposHom.toOverCompPushforwardIso G).inv.app K ≫
          (f.toToposHom.over G).pushforward.map
            ((X.localizationInverseImageIso
              (f.toToposHom.inverseImage.obj G)).inv.app K) :=
    Eq.trans (congrArg (fun z => (Y.localizationEquivalence G).functor.map z ≫ _)
        (localizationCompPushforwardIso_inv_app f G K))
      ((Y.localizationEquivalence G).functor_map_unitIso_hom_app_comp_counitIso _)
  have hnat := (X.localizationInverseImageIso
    (f.toToposHom.inverseImage.obj G)).hom.naturality (f.toToposHom.adj.counit.app K)
  have hslice := f.toToposHom.inverseImageCompToOverIso_hom_app_comp_counit G K
  have hmap : ∀ {a b c : Over G} (x : a ⟶ b) (y : b ⟶ c) (z : a ⟶ c), x ≫ y = z →
      (f.toToposHom.over G).inverseImage.map x ≫ (f.toToposHom.over G).inverseImage.map y =
        (f.toToposHom.over G).inverseImage.map z := fun x y z h =>
    ((f.toToposHom.over G).inverseImage.map_comp x y).symm.trans
      (congrArg (f.toToposHom.over G).inverseImage.map h)
  have hL : (localizedToposMorphism f G).inverseImage.map
        ((localizationCompPushforwardIso f G).inv.app K) =
      (X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).inverse.map
        ((f.toToposHom.over G).inverseImage.map
          ((Y.localizationEquivalence G).functor.map
            ((localizationCompPushforwardIso f G).inv.app K))) := rfl
  have hP : (f.toToposHom.over G).inverseImage.map
        ((Y.localizationEquivalence G).functor.map
          ((localizationCompPushforwardIso f G).inv.app K)) ≫
      (f.toToposHom.over G).inverseImage.map
        ((Y.localizationEquivalence G).counitIso.hom.app
          ((f.toToposHom.over G).pushforward.obj
            ((X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).functor.obj
              ((X.localizationMorphism
                (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj K)))) =
      (f.toToposHom.over G).inverseImage.map
        ((Y.localizationInverseImageIso G).hom.app (f.toToposHom.pushforward.obj K) ≫
          (f.toToposHom.toOverCompPushforwardIso G).inv.app K ≫
            (f.toToposHom.over G).pushforward.map
              ((X.localizationInverseImageIso
                (f.toToposHom.inverseImage.obj G)).inv.app K)) :=
    hmap _ _ _ hmid
  have hQ : (f.toToposHom.over G).inverseImage.map
        ((Y.localizationInverseImageIso G).inv.app (f.toToposHom.pushforward.obj K)) ≫
      (f.toToposHom.over G).inverseImage.map
        ((Y.localizationInverseImageIso G).hom.app (f.toToposHom.pushforward.obj K) ≫
          (f.toToposHom.toOverCompPushforwardIso G).inv.app K ≫
            (f.toToposHom.over G).pushforward.map
              ((X.localizationInverseImageIso
                (f.toToposHom.inverseImage.obj G)).inv.app K)) =
      (f.toToposHom.over G).inverseImage.map
        ((f.toToposHom.toOverCompPushforwardIso G).inv.app K ≫
          (f.toToposHom.over G).pushforward.map
            ((X.localizationInverseImageIso
              (f.toToposHom.inverseImage.obj G)).inv.app K)) :=
    hmap _ _ _ (Iso.inv_hom_id_app_assoc (Y.localizationInverseImageIso G) _ _)
  have hR : (f.toToposHom.over G).inverseImage.map
        ((f.toToposHom.toOverCompPushforwardIso G).inv.app K ≫
          (f.toToposHom.over G).pushforward.map
            ((X.localizationInverseImageIso
              (f.toToposHom.inverseImage.obj G)).inv.app K)) ≫
      (f.toToposHom.over G).adj.counit.app
        ((X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).functor.obj
          ((X.localizationMorphism
            (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj K)) =
      (f.toToposHom.over G).inverseImage.map
          ((f.toToposHom.toOverCompPushforwardIso G).inv.app K) ≫
        (f.toToposHom.over G).adj.counit.app
            ((toOver (f.toToposHom.inverseImage.obj G)).obj K) ≫
          (X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G)).inv.app K :=
    (congrArg (fun z => z ≫ (f.toToposHom.over G).adj.counit.app
          ((X.localizationEquivalence (f.toToposHom.inverseImage.obj G)).functor.obj
            ((X.localizationMorphism
              (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj K)))
        ((f.toToposHom.over G).inverseImage.map_comp _ _)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => (f.toToposHom.over G).inverseImage.map
            ((f.toToposHom.toOverCompPushforwardIso G).inv.app K) ≫ z)
          ((f.toToposHom.over G).adj.counit_naturality _)))
  refine Eq.trans (congrArg (fun z => z ≫ _ ≫ _)
    (inverseImageCompLocalizationIso_hom_app f G (f.toToposHom.pushforward.obj K))) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ z ≫ _) hL) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ z)
    (localizedToposMorphism_adj_counit_app f G
      ((X.localizationMorphism
        (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj K))) ?_
  simp only [Category.assoc]
  refine (X.localizationEquivalence
    (f.toToposHom.inverseImage.obj G)).unitIso_hom_app_comp_map₃ _ _ _ _ ?_
  simp only [Category.assoc]
  refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ _ ≫ z) (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ _ ≫ z ≫ _) hP) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ z) (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ z ≫ _) hQ) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ z) hR) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ z) (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ z) (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ z ≫ _) hslice) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ _) hnat.symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact Eq.trans (congrArg (fun z => _ ≫ z)
      ((X.localizationInverseImageIso (f.toToposHom.inverseImage.obj G)).hom_inv_id_app K))
    (Category.comp_id _)

/-! ### The structure map of the localized morphism -/

/-- Forgetting the ring operations, the identification of the inverse image of `O'` with the
structure sheaf of the localization of `Y` at `G` is the identity: both are the restriction of
the underlying sheaf of sets of `O'` to the site of elements of `G`. -/
theorem localizationInverseImageCommRingIso_inv_forget :
    (Y.localizedRingedTopos G).forgetRing.map (Y.localizationInverseImageCommRingIso G).inv =
      𝟙 ((Y.localizationMorphism G).toToposHom.inverseImage.obj (Y.forgetRing.obj Y.O)) :=
  restrictionCommRingIso_inv_forget.{v, v, max u' v, v, u'}
    (AlgebraicGeometry.RingedTopos.elementTopology Y G) Y.J
    (AlgebraicGeometry.RingedTopos.elementProjection Y G) Y.O

omit [EssentiallySmall.{v} X.C] in
/-- Forgetting the ring operations, the restriction `j_G⁻¹(f♯)` of the structure map of `f` is
`j_G⁻¹` of the underlying map of sheaves of sets of `f♯`. -/
theorem inverseImageCommRing_fSharp_forget :
    (Y.localizedRingedTopos G).forgetRing.map
        ((inverseImageCommRingFunctor (Y.localizationMorphism G).toToposHom).map f.fSharp) =
      (Y.localizationMorphism G).toToposHom.inverseImage.map (Y.forgetRing.map f.fSharp) :=
  underlyingRingSheaf_map_pullbackCommRingSheafMap.{v, v, v, max u' v, v, u'}
    (Y.localizedRingedTopos G).J _ f.fSharp

omit [EssentiallySmall.{v} Y.C] in
/-- Forgetting the ring operations, `f'_*` of the identification of the inverse image of `O`
with the structure sheaf of the localization of `X` at `f⁻¹G` is the identity. -/
theorem localizedPushforward_localizationInverseImageCommRingIso_forget :
    (Y.localizedRingedTopos G).forgetRing.map
        ((pushforwardCommRingFunctor (f.localizedToposMorphism G)).map
          (X.localizationInverseImageCommRingIso (f.toToposHom.inverseImage.obj G)).hom) =
      𝟙 ((f.localizedToposMorphism G).pushforward.obj
        ((X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj
          (X.forgetRing.obj X.O))) :=
  (underlyingRingSheaf_map_pullbackCommRingSheafMap.{v, v, v, max u' v, v, max u v}
      (Y.localizedRingedTopos G).J _
      (X.localizationInverseImageCommRingIso (f.toToposHom.inverseImage.obj G)).hom).trans
    ((congrArg (f.localizedToposMorphism G).pushforward.map
        (restrictionCommRingIso_hom_forget.{v, v, max u v, v, u}
          (AlgebraicGeometry.RingedTopos.elementTopology X (f.toToposHom.inverseImage.obj G))
          X.J
          (AlgebraicGeometry.RingedTopos.elementProjection X
            (f.toToposHom.inverseImage.obj G)) X.O)).trans
      ((f.localizedToposMorphism G).pushforward.map_id _))

omit [EssentiallySmall.{v} X.C] in
/-- Forgetting the ring operations, the comparison of the inverse image of `O` along `f_*` and
then `j_G⁻¹` with its inverse image along the composite is the identity. -/
theorem commRingComp_pushforwardLocalization_forget :
    (Y.localizedRingedTopos G).forgetRing.map
        ((pullbackCommRingSheafFunctorComp Y.J (Y.localizedRingedTopos G).J
          f.toToposHom.pushforward
          (Y.localizationMorphism G).toToposHom.inverseImage).hom.app X.O) =
      𝟙 ((Y.localizationMorphism G).toToposHom.inverseImage.obj
        (f.toToposHom.pushforward.obj (X.forgetRing.obj X.O))) :=
  forget_map_pullbackCommRingSheafComp_hom.{v, v, u, v, u', v, max u' v} Y.J
    (Y.localizedRingedTopos G).J f.toToposHom.pushforward
    (Y.localizationMorphism G).toToposHom.inverseImage X.O

/-- Forgetting the ring operations, the transport of the ring operations along
`localizationCompPushforwardIso` is that isomorphism itself. -/
theorem commRingTransport_localizationCompPushforward_inv_forget :
    (Y.localizedRingedTopos G).forgetRing.map
        ((pullbackCommRingSheafFunctorIsoOfNatIso (Y.localizedRingedTopos G).J
          (f.localizationCompPushforwardIso G)).inv.app X.O) =
      (f.localizationCompPushforwardIso G).inv.app (X.forgetRing.obj X.O) :=
  pullbackCommRingSheafMapOfNatTrans_forget.{v, v, v, max u' v, v, u} (Y.localizedRingedTopos G).J
    (f.localizationCompPushforwardIso G).inv X.O

omit [EssentiallySmall.{v} Y.C] in
/-- Forgetting the ring operations, the comparison of the inverse image of `O` along `j_F⁻¹` and
then `f'_*` with its inverse image along the composite is the identity.

The comparison is an isomorphism whose forward map is the identity on underlying sheaves of
sets, so its backward map is too; it is read off that way rather than by a cancellation, because
the two objects the backward map runs between are the two spellings of the direct image of a
chosen pullback and comparing them directly is beyond the elaborator. -/
theorem commRingComp_localizationPushforward_inv_forget :
    (Y.localizedRingedTopos G).forgetRing.map
        ((pullbackCommRingSheafFunctorComp
          (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).J
          (Y.localizedRingedTopos G).J
          (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage
          (f.localizedToposMorphism G).pushforward).inv.app X.O) =
      𝟙 ((f.localizedToposMorphism G).pushforward.obj
        ((X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj
          (X.forgetRing.obj X.O))) :=
  congrArg Iso.inv
    (Iso.ext (α := (Y.localizedRingedTopos G).forgetRing.mapIso
        ((pullbackCommRingSheafFunctorComp
          (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).J
          (Y.localizedRingedTopos G).J
          (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage
          (f.localizedToposMorphism G).pushforward).app X.O))
      (β := Iso.refl ((f.localizedToposMorphism G).pushforward.obj
        ((X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj
          (X.forgetRing.obj X.O))))
      (forget_map_pullbackCommRingSheafComp_hom.{v, v, u, v, max u v, v, max u' v}
        (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).J
        (Y.localizedRingedTopos G).J
        (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage
        (f.localizedToposMorphism G).pushforward X.O))

/-- Forgetting the ring operations, the ring-level form `localizedPushforwardCommRingIso` of
`f'_* j_F⁻¹ = j_G⁻¹ f_*` is its set-level form `localizationCompPushforwardIso`. The two
comparisons of iterated inverse images it is composed with contribute identities. -/
theorem localizedPushforwardCommRingIso_inv_forget :
    (Y.localizedRingedTopos G).forgetRing.map ((f.localizedPushforwardCommRingIso G).inv.app X.O) =
      (f.localizationCompPushforwardIso G).inv.app (X.forgetRing.obj X.O) := by
  refine Eq.trans (CategoryTheory.Functor.map_comp _ _ _) ?_
  refine Eq.trans (congrArg (fun z => z ≫ _) (CategoryTheory.Functor.map_comp _ _ _)) ?_
  refine Eq.trans (congrArg (fun z => (z ≫ _) ≫ _)
    (commRingComp_pushforwardLocalization_forget f G)) ?_
  refine Eq.trans (congrArg (fun z => (_ ≫ z) ≫ _)
    (commRingTransport_localizationCompPushforward_inv_forget f G)) ?_
  refine Eq.trans (congrArg (fun z => (_ ≫ _) ≫ z)
    (commRingComp_localizationPushforward_inv_forget f G)) ?_
  exact (Category.comp_id _).trans (Category.id_comp _)

/-- **Stacks 04IF**, the structure map of the localized morphism on underlying sheaves of sets:
`(f')♯` is the restriction `j_G⁻¹(f♯)` of the structure map of `f`, read through the comparison
`f'_* j_F⁻¹ = j_G⁻¹ f_*` of direct images.

This is the definition of `localized` with its four factors forgotten one at a time: the two
identifications of an inverse image of a structure sheaf with the localized structure sheaf are
identities on underlying sheaves of sets, the restriction of `f♯` is `j_G⁻¹` of the underlying
map of `f♯`, and the ring-level comparison of direct images is the set-level one. -/
theorem localized_fSharp_forget :
    (Y.localizedRingedTopos G).forgetRing.map (f.localized G).fSharp =
      (Y.localizationMorphism G).toToposHom.inverseImage.map (Y.forgetRing.map f.fSharp) ≫
        (f.localizationCompPushforwardIso G).inv.app (X.forgetRing.obj X.O) := by
  refine Eq.trans (CategoryTheory.Functor.map_comp _ _ _) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ z) (CategoryTheory.Functor.map_comp _ _ _)) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ z) (CategoryTheory.Functor.map_comp _ _ _)) ?_
  refine Eq.trans (congrArg (fun z => z ≫ _ ≫ _ ≫ _)
    (localizationInverseImageCommRingIso_inv_forget G)) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ z ≫ _ ≫ _)
    (inverseImageCommRing_fSharp_forget f G)) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ z ≫ _)
    (localizedPushforwardCommRingIso_inv_forget f G)) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ _ ≫ z)
    (localizedPushforward_localizationInverseImageCommRingIso_forget f G)) ?_
  refine Eq.trans (Category.id_comp
    (X := (Y.localizationMorphism G).toToposHom.inverseImage.obj (Y.forgetRing.obj Y.O)) _) ?_
  exact congrArg (fun z => _ ≫ z) (Category.comp_id
    (Y := (f.localizedToposMorphism G).pushforward.obj
      ((X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.obj
        (X.forgetRing.obj X.O))) _)

/-- **Stacks 04IF**: the square of Stacks 04IF is a square of *ringed* topoi — the comparison of
inverse images carries the structure map of `f` restricted to the site of elements of `f⁻¹G` to
the structure map of the localized morphism.

This is the compatibility that commutativity of 04IF's square as a square of ringed topoi needs,
in inverse-image form and on underlying sheaves of sets, and with it
`AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` turns 04IF's comparison of inverse
images into a 2-isomorphism of ringed topoi.

The proof is the adjointness the source omits. Both structure maps are adjunct to their
direct-image forms (`fSharpInverseImage_forget`), the direct-image form of `(f')♯` is `j_G⁻¹(f♯)`
followed by the comparison of direct images (`localized_fSharp_forget`), and
`inverseImageCompLocalizationIso_hom_app_comp_counit` says that 04IF's two comparisons are mates
of each other; naturality of the comparison of inverse images at `f♯` matches the two up. -/
@[stacks 04IF "commutativity of the square as a square of ringed topoi: the comparison of
  inverse images is compatible with the structure maps"]
theorem localized_fSharpInverseImage_forget :
    (f.inverseImageCompLocalizationIso G).hom.app (Y.forgetRing.obj Y.O) ≫
        (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).forgetRing.map
          (f.localized G).fSharpInverseImage =
      (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map
        (X.forgetRing.map f.fSharpInverseImage) := by
  have hL : (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).forgetRing.map
        (f.localized G).fSharpInverseImage =
      (f.localizedToposMorphism G).inverseImage.map
          ((Y.localizedRingedTopos G).forgetRing.map (f.localized G).fSharp) ≫
        (f.localizedToposMorphism G).adj.counit.app
          ((X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).forgetRing.obj
            (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).O) :=
    fSharpInverseImage_forget (f.localized G)
  have hR : X.forgetRing.map f.fSharpInverseImage =
      f.toToposHom.inverseImage.map (Y.forgetRing.map f.fSharp) ≫
        f.toToposHom.adj.counit.app (X.forgetRing.obj X.O) :=
    fSharpInverseImage_forget f
  have hkey := f.inverseImageCompLocalizationIso_hom_app_comp_counit G (X.forgetRing.obj X.O)
  have hnat := (f.inverseImageCompLocalizationIso G).hom.naturality (Y.forgetRing.map f.fSharp)
  refine Eq.trans (congrArg (fun z => (f.inverseImageCompLocalizationIso G).hom.app
      (Y.forgetRing.obj Y.O) ≫ z) hL) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ (f.localizedToposMorphism G).inverseImage.map z ≫ _)
    (localized_fSharp_forget f G)) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ z ≫ _)
    ((f.localizedToposMorphism G).inverseImage.map_comp _ _)) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ z) (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ _) hnat.symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => _ ≫ z) hkey) ?_
  refine Eq.trans
    (((X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map_comp
      _ _).symm) ?_
  exact congrArg
    (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map hR.symm

end AlgebraicGeometry.RingedToposHom

end

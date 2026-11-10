module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalizationInverseImage
public import StacksFrontier.CategoryTheory.Sites.Localization.ToposComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.InverseImageComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Morphism
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.SliceEquivalence
public import StacksFrontier.Deformation.ToposThickening.UniversalFirstOrder.ImageComposition

/-!
# Localizing a ringed site at an object and at its associated sheaf

Let `(C, J, O)` be a ringed site and `U` an object of `C`. Stacks 04IX localizes it at `U`,
giving the ringed site `(C/U, O|_U)` and a localization morphism of ringed topoi; Stacks 04IE
localizes the ringed *topos* `(Sh(C, J), O)` at a sheaf `F`, giving the site of elements of `F`
and its own localization morphism. Taking `F` to be the sheaf `h_U^#` associated to the
presheaf represented by `U` gives two localizations of the same ringed topos, and they agree.

This file supplies the comparison. The underlying topoi are identified by composing Stacks
00Y1's identification `Sh(C/U) ≌ Sh(C, J)/h_U^#` with Stacks 04IE's identification of the
localization at a sheaf with the slice topos; the inverse images are identified by Stacks 04IQ
together with 04IE's description of the inverse image of the localization at a sheaf; and the
structure sheaves are identified by transporting the ring operations along that identification
of inverse images.

## Main definitions

* `AlgebraicGeometry.RingedSite.representableSheaf`: the sheaf associated to the presheaf
  represented by `U`.
* `AlgebraicGeometry.RingedSite.localizationCommRingedToposHom`: the localization morphism at
  `U` of Stacks 04IX, read as a morphism of ringed topoi in the `CommRingCat`-valued
  presentation that `AlgebraicGeometry.RingedToposHom` takes.
* `AlgebraicGeometry.RingedSite.representableLocalizationEquivalence` and
  `.representableLocalizationToposMorphism`: the identification of the two localized topoi.
* `AlgebraicGeometry.RingedSite.representableLocalizationInverseImageIso`: the canonical
  comparison of the two inverse images.
* `AlgebraicGeometry.RingedSite.representableLocalizationStructureSheafIso`: the canonical
  comparison of the two structure sheaves.
* `AlgebraicGeometry.RingedSite.representableLocalizationRingedMorphism`: the identification of
  the two localized topoi, as a morphism of ringed topoi.
* `AlgebraicGeometry.RingedSite.representableLocalizationRingInverseImageIso`: the lift of the
  comparison of inverse images to sheaves of commutative rings.

## Main results

* `AlgebraicGeometry.RingedSite.representableLocalizationRingInverseImageIso_existsUnique`: the
  comparison of inverse images has exactly one lift to sheaves of commutative rings inducing
  it, so the lift is canonical rather than chosen.

## Implementation notes

The localization morphism of a ringed *site* is formalized as
`AlgebraicGeometry.RingedSite.localizationMorphism`, whose structure map is taken at the level
of sheaves of **rings**; the comparison here lives among morphisms of ringed *topoi*
(`AlgebraicGeometry.RingedToposHom`), whose structure map is taken at the level of sheaves of
**commutative rings**. `localizationCommRingedToposHom` is the same localization read in that
second presentation, assembled from the `CommRingCat`-valued structure maps
`AlgebraicGeometry.RingedSite.overCommRingFsharpAdjoint` and
`.overInverseImageCommRingFsharp`; it is not a second localization.

`toOver F` is taken for Mathlib's cartesian monoidal structure on `Sh(C, J)`
(`CartesianMonoidalCategory.fullSubcategory`) both in Stacks 04IQ's
`overPullbackCompSheafFunctorToOverIso` and in `RingedTopos.localizationInverseImageIso`, so the
two comparisons compose directly and no choice of products enters the statement.

The lift of the comparison of inverse images to sheaves of commutative rings is the
`Classical.choose` of `inverseImageCommRingIsoOfToposIso_existsUnique`, whose uniqueness clause
is `representableLocalizationRingInverseImageIso_existsUnique`; uniqueness is what makes it the
comparison rather than a choice.

Universes follow `RingedTopos.localizedRingedTopos`: site objects, site morphisms and sections
of `O` are all taken in one universe `u`, which is what Stacks 0791 needs in order to return a
sheaf equivalence.

## References

* [Stacks Project, Tag 04J3](https://stacks.math.columbia.edu/tag/04J3)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 04IQ](https://stacks.math.columbia.edu/tag/04IQ)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPushforward

universe w w' w'' v u v' u' v'' u''

section Forget

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [L.HasSheafCompose (forget RingCat.{w''})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [L.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [J.HasSheafCompose (forget CommRingCat.{w})] [K.HasSheafCompose (forget CommRingCat.{w'})]

omit [L.HasSheafCompose (forget RingCat.{w''})]
  [L.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})] in
/-- On underlying sheaves of sets, the inverse image along a morphism of topoi of a morphism of
sheaves of commutative rings is the inverse image of the underlying map of sheaves of sets. -/
theorem inverseImageCommRingFunctor_map_forget
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    {O O' : Sheaf K CommRingCat.{w'}} (a : O ⟶ O') :
    (sheafCompose J (forget CommRingCat.{w})).map ((inverseImageCommRingFunctor f).map a) =
      f.inverseImage.map ((sheafCompose K (forget CommRingCat.{w'})).map a) :=
  underlyingRingSheaf_map_pullbackCommRingSheafMap J _ a

omit [K.HasSheafCompose (forget CommRingCat.{w'})] in
/-- The comparison of the inverse image of sheaves of commutative rings along a composite of
morphisms of topoi with the iterated inverse image is the identity on underlying sheaves of
sets. -/
theorem inverseImageCommRingCompIso_inv_app_forget
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    (g : MorphismOfTopoi (Sheaf K (Type w')) (Sheaf L (Type w'')))
    (O : Sheaf L CommRingCat.{w''}) :
    (sheafCompose J (forget CommRingCat.{w})).map
        ((MorphismOfTopoi.inverseImageCommRingCompIso f g).inv.app O) = 𝟙 _ :=
  pullbackCommRingSheafCompIso_hom_forget J K f.inverseImage g.inverseImage O

end Forget

end Stacks.Sheaves.ToposPushforward

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- **Transporting the inverse unit of an equivalence along a comparison of its functor with a
third functor.** Let `E : A ≌ B`, let `L : A ⥤ D` and `G : B ⥤ D`, and let
`σ : E.functor ⋙ G ≅ L` identify `L` with `G` read through `E`. Then `L` applied to the inverse
unit `E⁻¹E T ⟶ T` is `σ` at `E⁻¹E T`, followed by `G` of the counit of `E` at `E T`, followed by
`σ` at `T`.

This is the general form of the step that converts a functor applied to a *morphism of `A`* into
a morphism of `B` read through `G`, and it is what makes two functors defined on opposite sides
of an equivalence comparable at all. The two ingredients are the naturality of `σ` and
`CategoryTheory.Equivalence.counit_app_functor`; nothing about sheaves or sites enters.

In the application `L` is a lower shriek, `G` is `Over.forget`, `E` is Stacks 00Y1's equivalence
and `σ` is its identification of the sheaf underlying `Φ_U T` with `j_{U!}T`, so the statement
says how a lower shriek applied to a morphism of `Sh(C/U)` is read in `Sh(C)/h_U^#`. Since every
comparison of inverse images in this family is whiskered with a unit or a counit of one of the
two equivalences of Stacks 04J3, the same lemma serves each of them. -/
theorem Equivalence.map_unitInv_of_comp_iso {A : Type u₁} [Category.{v₁} A] {B : Type u₂}
    [Category.{v₂} B] {D : Type u₃} [Category.{v₃} D] (E : A ≌ B) {G : B ⥤ D} {L : A ⥤ D}
    (σ : E.functor ⋙ G ≅ L) (T : A) :
    L.map (E.unitInv.app T) =
      σ.inv.app (E.inverse.obj (E.functor.obj T)) ≫
        G.map (E.counit.app (E.functor.obj T)) ≫ σ.hom.app T := by
  have hnat := σ.hom.naturality (E.unitInv.app T)
  have hfun : (E.functor ⋙ G).map (E.unitInv.app T) =
      G.map (E.counit.app (E.functor.obj T)) :=
    congrArg G.map (Equivalence.counit_app_functor E T).symm
  refine Eq.trans ?_ (congrArg (fun z =>
    σ.inv.app (E.inverse.obj (E.functor.obj T)) ≫ z ≫ σ.hom.app T) hfun)
  exact (Eq.trans
    (congrArg (fun z => σ.inv.app (E.inverse.obj (E.functor.obj T)) ≫ z) hnat)
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ L.map (E.unitInv.app T))
        (σ.inv_hom_id_app (E.inverse.obj (E.functor.obj T)))).trans
        (Category.id_comp _)))).symm

end CategoryTheory

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- The sheaf associated to the presheaf represented by `U`. -/
noncomputable abbrev representableSheaf : X.ringedTopos.Topos :=
  (presheafToSheaf X.J (Type u)).obj (yoneda.obj U)

/-- **The localization of a ringed site at an object, as a morphism of ringed topoi.** This is
the `AlgebraicGeometry.RingedSite.localizationMorphism` of Stacks 04IX, read in the
`CommRingCat`-valued presentation of the structure map that `AlgebraicGeometry.RingedToposHom`
takes: the morphism of topoi is restriction to the slice site, and the structure map is the
identification of the inverse image of `O` with its restriction. -/
@[sga "4 IV 11.2.1" "special case"]
noncomputable def localizationCommRingedToposHom :
    RingedToposHom (X.over U).ringedTopos X.ringedTopos where
  toToposHom := X.overMorphismOfTopoi U
  fSharp := X.overCommRingFsharpAdjoint U

/-- The structure map of the localization, in inverse-image form, is the identification of the
inverse image of `O` with its restriction to the slice site. -/
@[simp]
theorem localizationCommRingedToposHom_fSharpInverseImage :
    (X.localizationCommRingedToposHom U).fSharpInverseImage =
      X.overInverseImageCommRingFsharp U :=
  X.overCommRingFsharpAdjoint_inverseImage U

/-- **The identification of the two localized topoi**: sheaves on the slice site `C/U` are
sheaves on the site of elements of the sheaf `h_U^#`. It is the composite of Stacks 00Y1's
identification of `Sh(C/U)` with the slice topos and Stacks 04IE's identification of the
localization at a sheaf with the slice topos. -/
noncomputable def representableLocalizationEquivalence :
    (X.over U).ringedTopos.Topos ≌
      (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U)).Topos :=
  (CategoryTheory.OverShriek.sheafEquivalence (U := U) X.J).trans
    (RingedTopos.localizationEquivalence X.ringedTopos (representableSheaf X U)).symm

/-- The identification of the two localized topoi, read as a morphism of topoi: its inverse
image is the inverse of the equivalence, which is left exact because an equivalence is. -/
noncomputable def representableLocalizationToposMorphism :
    MorphismOfTopoi (X.over U).ringedTopos.Topos
      (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U)).Topos where
  pushforward := (representableLocalizationEquivalence X U).functor
  inverseImage := (representableLocalizationEquivalence X U).inverse
  adj := (representableLocalizationEquivalence X U).symm.toAdjunction
  preservesFiniteLimits :=
    haveI := (representableLocalizationEquivalence X U).toAdjunction.rightAdjoint_preservesLimits
    ⟨fun _ _ _ ↦ inferInstance⟩

/-- **The comparison of the two inverse images, in the direction of the slice topos.** Read
into the slice topos, the inverse image of the localization at `U` is the inverse image of the
localization at `h_U^#`: the first is "restrict to `C/U`, then view in the slice" by Stacks
04IQ, the second is "product with `h_U^#`" by Stacks 04IE, and both are taken for Mathlib's
cartesian monoidal structure on sheaves, so the two compose directly. -/
noncomputable def representableLocalizationForwardInverseImageIso :
    (X.localizationCommRingedToposHom U).toToposHom.inverseImage ⋙
        (CategoryTheory.OverShriek.sheafEquivalence (U := U) X.J).functor ≅
      (RingedTopos.localizationMorphism X.ringedTopos
          (representableSheaf X U)).toToposHom.inverseImage ⋙
        (RingedTopos.localizationEquivalence X.ringedTopos (representableSheaf X U)).functor :=
  CategoryTheory.OverShriek.overPullbackCompSheafFunctorToOverIso X.J ≪≫
    (RingedTopos.localizationInverseImageIso X.ringedTopos (representableSheaf X U)).symm

/-- Cancelling an isomorphism in `Over B`: if `e.hom.left ≫ c = d` then `e.inv.left ≫ d = c`. -/
private theorem inv_left_comp_eq_of_hom_left_comp_eq {C : Type*} [Category C] {B : C}
    {X Y : Over B} (e : X ≅ Y) {Z : C} {c : Y.left ⟶ Z} {d : X.left ⟶ Z}
    (h : e.hom.left ≫ c = d) : e.inv.left ≫ d = c := by
  rw [← h, ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]

/-- **Stacks 04IE's comparison of the inverse image with `toOver F`, read in the inverse
direction.** `AlgebraicGeometry.RingedTopos.forget_localizationInverseImageIso_hom_app` says
that the comparison, followed by the projection `G × F ⟶ G`, is the counit of the lower shriek;
this is the same statement for the inverse comparison, with the two projections exchanged.

The passage between them is `inv_left_comp_eq_of_hom_left_comp_eq`. -/
theorem _root_.AlgebraicGeometry.RingedTopos.forget_localizationInverseImageIso_inv_app
    (Z : RingedTopos.{u, u, u})
    (F G : Z.Topos) :
    ((Z.localizationInverseImageIso F).inv.app G).left ≫
        (Z.localizationShriekAdjunction F).counit.app G =
      (forgetAdjToOver F).counit.app G :=
  inv_left_comp_eq_of_hom_left_comp_eq ((Z.localizationInverseImageIso F).app G)
    (RingedTopos.forget_localizationInverseImageIso_hom_app Z F G)

/-- **Stacks 04J3's comparison of inverse images, read through the lower shriek.** The
comparison of the two inverse images in the direction of the slice topos, read through
`Over.forget` and followed by the lower shriek counit of the localization at `h_U^#`, is Stacks
00Y1's identification of `Φ_U ⋙ Over.forget` with `j_{U!}` followed by the lower shriek counit
of the localization at `U`.

This is the statement that connects the two lower shrieks the comparison of Stacks 04J3 sits
between — that of the slice site `C/U` and that of the localization of the ringed topos at
`h_U^#` — and it is what lets an equation built from one be compared with an equation built
from the other after transposing across `j_{U!}`.

Each of the two factors of `representableLocalizationForwardInverseImageIso` contributes one
step, and each step is already proved: Stacks 04IQ's comparison read through `Over.forget` and
followed by the first projection is Stacks 00Y1's identification followed by the slice-site
counit (`CategoryTheory.OverShriek.left_overPullbackCompSheafFunctorToOverIso_hom_app_comp_fst`);
and Stacks 04IE's comparison carries the projection to the localization counit
(`RingedTopos.forget_localizationInverseImageIso_inv_app`), whose right-hand side is that first
projection.

The step that replaces a factor *inside* the composite is taken by `rw` rather than by an
explicit `congrArg`: a `congrArg` against a hand-written `fun z => z ≫ _` has to have its own
spelling of the composite identified with the goal's, and that identification unfolds the body of
`localizationShriekAdjunction` — the equation is the same, and the proof is five times the
elaborator's budget. `rw` substitutes into the goal's own term, so no such identification
arises. -/
@[stacks 04J3 "part (2): the comparison of inverse images, read through the lower shriek"]
theorem left_representableLocalizationForwardInverseImageIso_hom_app_comp_counit
    (A : Sheaf X.J (Type u)) :
    ((representableLocalizationForwardInverseImageIso X U).hom.app A).left ≫
        (X.ringedTopos.localizationShriekAdjunction (representableSheaf X U)).counit.app A =
      (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J).hom.app
          ((X.J.overPullback (Type u) U).obj A) ≫
        ((Over.forget U).sheafAdjunctionContinuous (Type u) (X.J.over U) X.J).counit.app A := by
  have hleft : ((representableLocalizationForwardInverseImageIso X U).hom.app A).left =
      ((CategoryTheory.OverShriek.overPullbackCompSheafFunctorToOverIso X.J).hom.app A).left ≫
        ((RingedTopos.localizationInverseImageIso X.ringedTopos
          (representableSheaf X U)).inv.app A).left :=
    rfl
  refine Eq.trans ?_
    (CategoryTheory.OverShriek.left_overPullbackCompSheafFunctorToOverIso_hom_app_comp_fst
      (U := U) X.J A)
  rw [hleft]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (fun z =>
      ((CategoryTheory.OverShriek.overPullbackCompSheafFunctorToOverIso X.J).hom.app A).left ≫ z)
    ?_
  rw [RingedTopos.forget_localizationInverseImageIso_inv_app]
  rfl

/-- **The canonical comparison of the two inverse images**: the inverse image of the
localization at `h_U^#`, read through the identification of the two localized topoi, is the
inverse image of the localization at `U`. This is the previous comparison transported across
the unit of Stacks 00Y1's equivalence, so it is not an arbitrary isomorphism. -/
@[stacks 04J3 "part (2): canonical comparison of inverse images"]
noncomputable def representableLocalizationInverseImageIso :
    (RingedTopos.localizationMorphism X.ringedTopos
          (representableSheaf X U)).toToposHom.inverseImage ⋙
        (representableLocalizationEquivalence X U).inverse ≅
      (X.localizationCommRingedToposHom U).toToposHom.inverseImage :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (representableLocalizationForwardInverseImageIso X U).symm
      (CategoryTheory.OverShriek.sheafEquivalence (U := U) X.J).inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (CategoryTheory.OverShriek.sheafEquivalence (U := U) X.J).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- `left_representableLocalizationForwardInverseImageIso_hom_app_comp_counit` for the inverse
comparison: reading the inverse through `Over.forget` and following it by Stacks 00Y1's
identification and the slice-site counit gives the counit of the localization at `h_U^#`.

Obtained from the forward statement by `inv_left_comp_eq_of_hom_left_comp_eq`. -/
theorem left_representableLocalizationForwardInverseImageIso_inv_app_comp_counit
    (A : Sheaf X.J (Type u)) :
    ((representableLocalizationForwardInverseImageIso X U).inv.app A).left ≫
        (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J).hom.app
            ((X.J.overPullback (Type u) U).obj A) ≫
          ((Over.forget U).sheafAdjunctionContinuous (Type u) (X.J.over U) X.J).counit.app A =
      (X.ringedTopos.localizationShriekAdjunction (representableSheaf X U)).counit.app A := by
  exact inv_left_comp_eq_of_hom_left_comp_eq
    ((representableLocalizationForwardInverseImageIso X U).app A)
    (left_representableLocalizationForwardInverseImageIso_hom_app_comp_counit X U A)

/-- **The lower shriek of the inverse unit of Stacks 00Y1's equivalence.** Applying `j_{U!}` to
`Phi_U^{-1}Phi_U T ⟶ T` is Stacks 00Y1's identification of `j_{U!}Phi_U^{-1}` with `Over.forget`,
followed by its identification of the sheaf underlying `Phi_U T` with `j_{U!}T`.

This is the step that converts a lower shriek applied to a morphism of `Sh(C/U)` into a
morphism of `Sh(C)/h_U^#` read through `Over.forget`, which is what makes the two shrieks
comparable at all. Its ingredients are the naturality of
`CategoryTheory.OverShriek.sheafFunctorToOverForgetIso` and
`CategoryTheory.Equivalence.counit_app_functor`. -/
theorem shriek_sheafEquivalence_unitInv (T : Sheaf (X.J.over U) (Type u)) :
    ((Over.forget U).sheafPullback (Type u) (X.J.over U) X.J).map
        ((CategoryTheory.OverShriek.sheafEquivalence X.J).unitInv.app T) =
      (CategoryTheory.OverShriek.inverseCompShriekIso X.J).hom.app
          ((CategoryTheory.OverShriek.sheafEquivalence X.J).functor.obj T) ≫
        (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J).hom.app T :=
  Eq.trans
    (CategoryTheory.Equivalence.map_unitInv_of_comp_iso
      (CategoryTheory.OverShriek.sheafEquivalence X.J)
      (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J) T)
    (Eq.trans (Category.assoc _ _ _).symm
      (congrArg (fun z => z ≫
          (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J).hom.app T)
        (CategoryTheory.OverShriek.inverseCompShriekIso_hom_app X.J
          ((CategoryTheory.OverShriek.sheafEquivalence X.J).functor.obj T)).symm))

/-- **Stacks 04J3's comparison of inverse images, read through the lower shriek.** Applying
`j_{U!}` to the comparison and following it by the counit of `j_{U!} ⊣ j_U^{-1}` is Stacks 00Y1's
identification of `j_{U!}Phi_U^{-1}` with `Over.forget` followed by the counit of the lower
shriek of the localization at `h_U^#`.

This is the form of Stacks 04J3's comparison that an equation transposed across `j_{U!}`
consumes: on one side of such an equation the lower shriek is the slice site's, on the other it
is the localization's, and nothing but this lemma relates them. It is the comparison *after* the
cancellation of Stacks 00Y1's unit, so it applies to
`representableLocalizationInverseImageIso` itself rather than to the comparison in the slice
direction that it is built from.

The three steps are `shriek_sheafEquivalence_unitInv` for the cancelled unit, the naturality of
`CategoryTheory.OverShriek.inverseCompShriekIso`, and
`left_representableLocalizationForwardInverseImageIso_inv_app_comp_counit` for the comparison in
the slice direction.

The last of those is whiskered on by `CategoryTheory.whisker_eq` with the whiskering morphism left
to unification: written as a `congrArg` against an explicit `fun z => _ ≫ z`, the step alone takes
the whole of the elaborator's budget, because the lambda's spelling of the comparison has to be
identified with the goal's and that unfolds the body of `localizationShriekAdjunction`. -/
@[stacks 04J3 "part (2): the comparison of inverse images after the unit cancellation, read
  through the lower shriek"]
theorem shriek_representableLocalizationInverseImageIso_hom_app_comp_counit
    (A : Sheaf X.J (Type u)) :
    ((Over.forget U).sheafPullback (Type u) (X.J.over U) X.J).map
          ((representableLocalizationInverseImageIso X U).hom.app A) ≫
        ((Over.forget U).sheafAdjunctionContinuous (Type u) (X.J.over U) X.J).counit.app A =
      (CategoryTheory.OverShriek.inverseCompShriekIso X.J).hom.app
          ((X.ringedTopos.localizationEquivalence (representableSheaf X U)).functor.obj
            ((X.ringedTopos.localizationMorphism
              (representableSheaf X U)).toToposHom.inverseImage.obj A)) ≫
        (X.ringedTopos.localizationShriekAdjunction (representableSheaf X U)).counit.app A := by
  have hsplit : (representableLocalizationInverseImageIso X U).hom.app A =
      (CategoryTheory.OverShriek.sheafEquivalence X.J).inverse.map
          ((representableLocalizationForwardInverseImageIso X U).inv.app A) ≫
        (CategoryTheory.OverShriek.sheafEquivalence X.J).unitInv.app
          ((X.localizationCommRingedToposHom U).toToposHom.inverseImage.obj A) :=
    rfl
  refine Eq.trans (congrArg (fun z =>
      ((Over.forget U).sheafPullback (Type u) (X.J.over U) X.J).map z ≫
        ((Over.forget U).sheafAdjunctionContinuous (Type u) (X.J.over U) X.J).counit.app A)
    hsplit) ?_
  refine Eq.trans (congrArg (fun z => z ≫
      ((Over.forget U).sheafAdjunctionContinuous (Type u) (X.J.over U) X.J).counit.app A)
    (((Over.forget U).sheafPullback (Type u) (X.J.over U) X.J).map_comp
      ((CategoryTheory.OverShriek.sheafEquivalence X.J).inverse.map
        ((representableLocalizationForwardInverseImageIso X U).inv.app A))
      ((CategoryTheory.OverShriek.sheafEquivalence X.J).unitInv.app
        ((X.localizationCommRingedToposHom U).toToposHom.inverseImage.obj A)))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z =>
      ((Over.forget U).sheafPullback (Type u) (X.J.over U) X.J).map
        ((CategoryTheory.OverShriek.sheafEquivalence X.J).inverse.map
          ((representableLocalizationForwardInverseImageIso X U).inv.app A)) ≫ z)
    (Eq.trans (congrArg (fun z => z ≫
        ((Over.forget U).sheafAdjunctionContinuous (Type u) (X.J.over U) X.J).counit.app A)
      (X.shriek_sheafEquivalence_unitInv U
        ((X.localizationCommRingedToposHom U).toToposHom.inverseImage.obj A)))
      (Category.assoc _ _ _))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
      ((CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J).hom.app
          ((X.localizationCommRingedToposHom U).toToposHom.inverseImage.obj A) ≫
        ((Over.forget U).sheafAdjunctionContinuous (Type u) (X.J.over U) X.J).counit.app A))
    ((CategoryTheory.OverShriek.inverseCompShriekIso X.J).hom.naturality
      ((representableLocalizationForwardInverseImageIso X U).inv.app A))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _
    (X.left_representableLocalizationForwardInverseImageIso_inv_app_comp_counit U A)

/-- The composite of the localization at `h_U^#` with the identification of the two localized
topoi, as a morphism of topoi between sheaves of sets. -/
noncomputable abbrev compToposHom :
    MorphismOfTopoi (Sheaf (X.J.over U) (Type u)) (Sheaf X.J (Type u)) :=
  (RingedTopos.localizationMorphism X.ringedTopos (representableSheaf X U)).toToposHom.comp
    (representableLocalizationToposMorphism X U)

/-- The localization at `U`, as a morphism of topoi between sheaves of sets. -/
noncomputable abbrev siteToposHom :
    MorphismOfTopoi (Sheaf (X.J.over U) (Type u)) (Sheaf X.J (Type u)) :=
  (X.localizationCommRingedToposHom U).toToposHom

/-- The comparison of inverse images of sheaves of sets has exactly one lift to sheaves of
commutative rings inducing it. This is
`representableLocalizationRingInverseImageIso_existsUnique` with the composite taken at the
level of morphisms of topoi rather than of ringed topoi. -/
theorem ringInverseImageIsoCoreSpec :
    ∃! β : inverseImageCommRingFunctor.{u, u, u, u, u, u} (compToposHom X U) ≅
        inverseImageCommRingFunctor.{u, u, u, u, u, u} (siteToposHom X U),
      ∀ R : Sheaf X.J CommRingCat.{u},
        (sheafCompose (X.J.over U) (forget CommRingCat.{u})).map (β.hom.app R) =
          (representableLocalizationInverseImageIso X U).hom.app
            ((sheafCompose X.J (forget CommRingCat.{u})).obj R) :=
  inverseImageCommRingIsoOfToposIso_existsUnique (compToposHom X U) (siteToposHom X U)
    (representableLocalizationInverseImageIso X U)

/-- The unique lift to sheaves of commutative rings of the comparison of inverse images. -/
noncomputable def ringInverseImageIsoCore :
    inverseImageCommRingFunctor.{u, u, u, u, u, u} (compToposHom X U) ≅
      inverseImageCommRingFunctor.{u, u, u, u, u, u} (siteToposHom X U) :=
  Classical.choose (ringInverseImageIsoCoreSpec X U)

/-- The lift of the comparison of inverse images induces the comparison itself on underlying
sheaves of sets. This is the characterisation that makes the lift canonical. -/
theorem ringInverseImageIsoCore_hom_forget (R : Sheaf X.J CommRingCat.{u}) :
    (sheafCompose (X.J.over U) (forget CommRingCat.{u})).map
        ((ringInverseImageIsoCore X U).hom.app R) =
      (representableLocalizationInverseImageIso X U).hom.app
        ((sheafCompose X.J (forget CommRingCat.{u})).obj R) :=
  (Classical.choose_spec (ringInverseImageIsoCoreSpec X U)).1 R

/-- **The canonical comparison of the two structure sheaves.** Read through the identification
of the two localized topoi, the structure sheaf of the localization at `h_U^#` is the structure
sheaf `O|_U` of the localization at `U`: the inverse image of the former along the
identification is the inverse image of `O` along the composite, which the lift above identifies
with the inverse image of `O` along the localization at `U`, which is `O|_U`. -/
@[stacks 04J3 "part (1): canonical structure-sheaf comparison"]
noncomputable def representableLocalizationStructureSheafIso :
    (inverseImageCommRingFunctor (representableLocalizationToposMorphism X U)).obj
        (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U)).O ≅
      (X.over U).ringedTopos.O :=
  (inverseImageCommRingFunctor (representableLocalizationToposMorphism X U)).mapIso
      (RingedTopos.localizationInverseImageCommRingIso X.ringedTopos
        (representableSheaf X U)).symm ≪≫
    ((MorphismOfTopoi.inverseImageCommRingCompIso
        (representableLocalizationToposMorphism X U)
        (RingedTopos.localizationMorphism X.ringedTopos
          (representableSheaf X U)).toToposHom).app X.O).symm ≪≫
    (ringInverseImageIsoCore X U).app X.O ≪≫ X.overInverseImageCommRingIso U

/-- The identification of the inverse image of `O` with the structure sheaf of the localization
at a sheaf is the identity on underlying sheaves of sets. -/
theorem localizationInverseImageCommRingIso_hom_forget :
    (sheafCompose (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U)).J
        (forget CommRingCat.{u})).map
      (RingedTopos.localizationInverseImageCommRingIso X.ringedTopos
        (representableSheaf X U)).hom = 𝟙 _ :=
  rfl

/-- The inverse identification is also the identity on underlying sheaves of sets. -/
theorem localizationInverseImageCommRingIso_inv_forget :
    (sheafCompose (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U)).J
        (forget CommRingCat.{u})).map
      (RingedTopos.localizationInverseImageCommRingIso X.ringedTopos
        (representableSheaf X U)).inv = 𝟙 _ :=
  rfl

/-- **The identification of the two localized topoi, as a morphism of ringed topoi.** Its
structure map is the adjunct of the comparison of structure sheaves. -/
noncomputable def representableLocalizationRingedMorphism :
    RingedToposHom (X.over U).ringedTopos
      (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U)) where
  toToposHom := representableLocalizationToposMorphism X U
  fSharp := (commRingImageAdjunction (representableLocalizationToposMorphism X U)).homEquiv _ _
    (representableLocalizationStructureSheafIso X U).hom

/-- The structure map of the identification, in inverse-image form, is the comparison of
structure sheaves. -/
theorem representableLocalizationRingedMorphism_fSharpInverseImage :
    (representableLocalizationRingedMorphism X U).fSharpInverseImage =
      (representableLocalizationStructureSheafIso X U).hom := by
  change ((commRingImageAdjunction (representableLocalizationToposMorphism X U)).homEquiv
      _ _).symm ((commRingImageAdjunction (representableLocalizationToposMorphism X U)).homEquiv
        _ _ (representableLocalizationStructureSheafIso X U).hom) = _
  rw [Equiv.symm_apply_apply]

/-- **The comparison of inverse images lifts uniquely to sheaves of commutative rings.** For
the composite of the localization at `h_U^#` with the identification of the two localized
topoi, and for the localization at `U`, there is exactly one isomorphism of their inverse
images of sheaves of commutative rings whose underlying map of sheaves of sets is the canonical
comparison. -/
@[stacks 04J3 "part (2): canonical comparison on ring sheaves"]
theorem representableLocalizationRingInverseImageIso_existsUnique :
    ∃! β : inverseImageCommRingFunctor.{u, u, u, u, u, u}
        ((RingedTopos.localizationMorphism X.ringedTopos (representableSheaf X U)).comp
          (representableLocalizationRingedMorphism X U)).toToposHom ≅
        inverseImageCommRingFunctor.{u, u, u, u, u, u}
          (X.localizationCommRingedToposHom U).toToposHom,
      ∀ R : Sheaf X.J CommRingCat.{u},
        (sheafCompose (X.J.over U) (forget CommRingCat.{u})).map (β.hom.app R) =
          (representableLocalizationInverseImageIso X U).hom.app
            ((sheafCompose X.J (forget CommRingCat.{u})).obj R) :=
  ringInverseImageIsoCoreSpec X U

/-- The canonical comparison of the inverse images of sheaves of commutative rings. -/
noncomputable def representableLocalizationRingInverseImageIso :
    inverseImageCommRingFunctor.{u, u, u, u, u, u}
        ((RingedTopos.localizationMorphism X.ringedTopos (representableSheaf X U)).comp
          (representableLocalizationRingedMorphism X U)).toToposHom ≅
      inverseImageCommRingFunctor.{u, u, u, u, u, u}
        (X.localizationCommRingedToposHom U).toToposHom :=
  Classical.choose (representableLocalizationRingInverseImageIso_existsUnique X U)

end AlgebraicGeometry.RingedSite

end

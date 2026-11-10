module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RelocalizedMorphismComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RepresentableRelocalization

/-!
# The two relocalization triangles of a ringed site agree as triangles of ringed topoi

Let `(C, J, O)` be a ringed site and `f : V ⟶ U` a morphism of `C`. There are two relocalization
triangles over `(Sh(C, J), O)`:

* the one of Stacks 04IY, built from the localizations of the ringed *site* at `V` and at `U`,
  whose upper edge is restriction along `Over.map f`;
* the one of Stacks 04J4, built from the localizations of the ringed *topos* at the sheaves
  `h_V^#` and `h_U^#`, whose upper edge is the localization of `(Sh(C)/h_U^#, O_{h_U^#})` at the
  object `h_V^#/h_U^#`.

Stacks 04J5 says that these two triangles agree via the identifications of Stacks 04J3. This file
proves it, with the two upper edges identified as morphisms of *ringed* topoi.

## Main definitions

* `AlgebraicGeometry.RingedSite.representableRelocalizationToposMorphism`: the identification of
  `Sh(C/V)` with the topos of the localization at `h_V^#/h_U^#`, as a morphism of topoi.
* `AlgebraicGeometry.RingedSite.representableRelocalizationRingInverseImageIso`: the lift to
  sheaves of commutative rings of the comparison of the two inverse images.
* `AlgebraicGeometry.RingedSite.representableRelocalizationStructureSheafIso`: the canonical
  comparison of the two structure sheaves.
* `AlgebraicGeometry.RingedSite.representableRelocalizationRingedMorphism`: the identification
  of the two topoi, as a morphism of ringed topoi.
* `AlgebraicGeometry.RingedSite.representableRelocalizationSheafMapInverseImageIso`: the
  comparison of the two descriptions Stacks 04J4 gives of the upper edge of its triangle — the
  relocalization along `h_f^#` and the localization at the object `h_V^#/h_U^#` — on inverse
  images.
* `AlgebraicGeometry.RingedSite.representableRelocalizationSheafMapCompInverseImageIso`:
  **Stacks 04J5** on inverse images, in the sheaf-morphism description of that upper edge.

## Main results

* `AlgebraicGeometry.RingedSite.representableRelocalizationRingInverseImageIso_existsUnique`:
  the comparison of the two inverse images has exactly one lift to sheaves of commutative rings
  inducing it.
* `AlgebraicGeometry.RingedSite.representableRelocalizationTwoIso`: **Stacks 04J5** on the upper
  edges, as a 2-isomorphism of morphisms of ringed topoi.
* `AlgebraicGeometry.RingedSite.representableRelocalizationTriangleCompare`: **Stacks 04J5** on
  the triangles: the relocalization triangle of Stacks 04J4 at a representable sheaf, read
  through the identifications of Stacks 04J3, is the relocalization triangle of Stacks 04IY.

## References

* [Stacks Project, Tag 04J5](https://stacks.math.columbia.edu/tag/04J5)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 04IY](https://stacks.math.columbia.edu/tag/04IY)
* [Stacks Project, Tag 04J3](https://stacks.math.columbia.edu/tag/04J3)
* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open AlgebraicGeometry.RingedToposHom

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
  [J.HasSheafCompose (forget CommRingCat.{w})]

/-- The comparison of the inverse image along a composite of morphisms of topoi with the
iterated inverse image is the identity on underlying sheaves of sets. -/
theorem inverseImageCommRingCompIso_hom_app_forget
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    (g : MorphismOfTopoi (Sheaf K (Type w')) (Sheaf L (Type w'')))
    (O : Sheaf L CommRingCat.{w''}) :
    (sheafCompose J (forget CommRingCat.{w})).map
        ((MorphismOfTopoi.inverseImageCommRingCompIso f g).hom.app O) = 𝟙 _ := by
  have h : (sheafCompose J (forget CommRingCat.{w})).map
      ((MorphismOfTopoi.inverseImageCommRingCompIso f g).hom.app O ≫
        (MorphismOfTopoi.inverseImageCommRingCompIso f g).inv.app O) = 𝟙 _ := by
    rw [Iso.hom_inv_id_app]
    exact CategoryTheory.Functor.map_id _ _
  rw [Functor.map_comp, inverseImageCommRingCompIso_inv_app_forget] at h
  exact (Category.comp_id _).symm.trans h

/-- The comparison of the inverse image along a composite with the iterated inverse image
disappears from a composite on underlying sheaves of sets. -/
theorem forget_map_inverseImageCommRingCompIso_hom_app_comp
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    (g : MorphismOfTopoi (Sheaf K (Type w')) (Sheaf L (Type w'')))
    (O : Sheaf L CommRingCat.{w''}) {B : Sheaf J CommRingCat.{w}}
    (b : (inverseImageCommRingFunctor f).obj ((inverseImageCommRingFunctor g).obj O) ⟶ B) :
    (sheafCompose J (forget CommRingCat.{w})).map
        ((MorphismOfTopoi.inverseImageCommRingCompIso f g).hom.app O ≫ b) =
      (sheafCompose J (forget CommRingCat.{w})).map b := by
  rw [Functor.map_comp, inverseImageCommRingCompIso_hom_app_forget]
  exact Category.id_comp _

end Forget

end Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedTopos

universe u

variable (X : RingedTopos.{u, u, u}) (F : X.Topos)

/-- The identification of the inverse image of the structure sheaf with the structure sheaf of
the localization at `F` is the identity on underlying sheaves of sets: both are the restriction
of the underlying sheaf of sets of `O` to the site of elements of `F`. -/
theorem localizationInverseImageCommRingIso_hom_forget :
    (localizedRingedTopos X F).forgetRing.map (localizationInverseImageCommRingIso X F).hom =
      𝟙 ((localizationToposMorphism X F).inverseImage.obj (X.forgetRing.obj X.O)) :=
  Stacks.Sheaves.ToposPullback.restrictionCommRingIso_hom_forget (elementTopology X F) X.J
    (elementProjection X F) X.O

/-- The inverse identification is also the identity on underlying sheaves of sets. -/
theorem localizationInverseImageCommRingIso_inv_forget :
    (localizedRingedTopos X F).forgetRing.map (localizationInverseImageCommRingIso X F).inv =
      𝟙 ((localizationToposMorphism X F).inverseImage.obj (X.forgetRing.obj X.O)) :=
  Stacks.Sheaves.ToposPullback.restrictionCommRingIso_inv_forget (elementTopology X F) X.J
    (elementProjection X F) X.O

end AlgebraicGeometry.RingedTopos

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u}) {U V : X.C} (f : V ⟶ U)

/-- The localization of the ringed topos of `X` at the sheaf `h_U^#` associated to the presheaf
represented by `U`. -/
noncomputable abbrev representableLocalizedRingedTopos (U : X.C) : RingedTopos.{u, u, u} :=
  RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U)

/-- The localization of `(Sh(C)/h_U^#, O_{h_U^#})` at the object `h_V^#/h_U^#`: the upper corner
of the relocalization triangle of Stacks 04J4 at the morphism `f : V ⟶ U`. -/
noncomputable abbrev representableRelocalizedRingedTopos : RingedTopos.{u, u, u} :=
  RingedTopos.localizedRingedTopos (representableLocalizedRingedTopos X U)
    (representableRelocalizationObject X f)

/-- The upper edge of the relocalization triangle of Stacks 04J4 at `f`, as a morphism of
topoi: the localization of `(Sh(C)/h_U^#, O_{h_U^#})` at the object `h_V^#/h_U^#`. -/
noncomputable abbrev representableRelocalizationToposLocalization :
    MorphismOfTopoi (representableRelocalizedRingedTopos X f).Topos
      (representableLocalizedRingedTopos X U).Topos :=
  RingedTopos.localizationToposMorphism (representableLocalizedRingedTopos X U)
    (representableRelocalizationObject X f)

/-- **The identification of the localization at `h_V^#/h_U^#` with `Sh(C/V)`, as a morphism of
topoi.** Its inverse image is the equivalence of
`AlgebraicGeometry.RingedSite.representableRelocalizationEquivalence`. -/
noncomputable def representableRelocalizationToposMorphism :
    MorphismOfTopoi (ringedTopos (X.over V)).Topos (representableRelocalizedRingedTopos X f).Topos
    where
  pushforward := (representableRelocalizationEquivalence X f).inverse
  inverseImage := (representableRelocalizationEquivalence X f).functor
  adj := (representableRelocalizationEquivalence X f).toAdjunction
  preservesFiniteLimits :=
    haveI := Adjunction.rightAdjoint_preservesLimits
      (representableRelocalizationEquivalence X f).symm.toAdjunction
    ⟨fun _ _ _ ↦ inferInstance⟩

/-- The localization at `h_V^#/h_U^#` followed by the identification of the two topoi, as a
morphism of topoi between sheaves of sets. -/
noncomputable abbrev representableRelocalizationCompToposHom :
    MorphismOfTopoi (Sheaf (X.J.over V) (Type u))
      (representableLocalizedRingedTopos X U).Topos :=
  (representableRelocalizationToposLocalization X f).comp
    (representableRelocalizationToposMorphism X f)

/-- The relocalization of the ringed site along `f` followed by the identification of Stacks
04J3 at `U`, as a morphism of topoi between sheaves of sets. -/
noncomputable abbrev representableRelocalizationSiteToposHom :
    MorphismOfTopoi (Sheaf (X.J.over V) (Type u))
      (representableLocalizedRingedTopos X U).Topos :=
  (representableLocalizationToposMorphism X U).comp (X.overMapMorphismOfTopoi f)

/-- **The comparison of the inverse images of the two composites.** Stacks 04J5 compares the
inverse image of the localization at `h_V^#/h_U^#` with that of the relocalization of the ringed
site *after restricting along the identification of Stacks 04J3 at `U`*; whiskering that
comparison with the inverse of the identification at `U` and cancelling its counit turns it into
a comparison of the two composites out of `Sh(C/V)`. -/
noncomputable def representableRelocalizationCompInverseImageIso :
    (representableRelocalizationCompToposHom X f).inverseImage ≅
      (representableRelocalizationSiteToposHom X f).inverseImage :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (X.representableLocalizationEquivalence U).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (X.representableLocalizationEquivalence U).inverse
      (representableRelocalizationInverseImageIso X f)

/-- **The comparison of inverse images lifts uniquely to sheaves of commutative rings.** For the
localization at `h_V^#/h_U^#` composed with the identification of the two topoi, and for the
relocalization of the ringed site composed with the identification of Stacks 04J3 at `U`, there
is exactly one isomorphism of their inverse images of sheaves of commutative rings whose
underlying map of sheaves of sets is the canonical comparison. -/
theorem representableRelocalizationRingInverseImageIso_existsUnique :
    ∃! β : inverseImageCommRingFunctor.{u, u, u, u, u, u}
        (representableRelocalizationCompToposHom X f) ≅
        inverseImageCommRingFunctor.{u, u, u, u, u, u}
          (representableRelocalizationSiteToposHom X f),
      ∀ R : Sheaf (representableLocalizedRingedTopos X U).J CommRingCat.{u},
        (sheafCompose (X.J.over V) (forget CommRingCat.{u})).map (β.hom.app R) =
          (representableRelocalizationCompInverseImageIso X f).hom.app
            ((sheafCompose (representableLocalizedRingedTopos X U).J
              (forget CommRingCat.{u})).obj R) :=
  inverseImageCommRingIsoOfToposIso_existsUnique (representableRelocalizationCompToposHom X f)
    (representableRelocalizationSiteToposHom X f)
    (representableRelocalizationCompInverseImageIso X f)

/-- The unique lift to sheaves of commutative rings of the comparison of inverse images. -/
noncomputable def representableRelocalizationRingInverseImageIso :
    inverseImageCommRingFunctor.{u, u, u, u, u, u}
        (representableRelocalizationCompToposHom X f) ≅
      inverseImageCommRingFunctor.{u, u, u, u, u, u}
        (representableRelocalizationSiteToposHom X f) :=
  Classical.choose (representableRelocalizationRingInverseImageIso_existsUnique X f)

/-- The lift of the comparison of inverse images induces the comparison itself on underlying
sheaves of sets. -/
theorem representableRelocalizationRingInverseImageIso_hom_forget
    (R : Sheaf (representableLocalizedRingedTopos X U).J CommRingCat.{u}) :
    (sheafCompose (X.J.over V) (forget CommRingCat.{u})).map
        ((representableRelocalizationRingInverseImageIso X f).hom.app R) =
      (representableRelocalizationCompInverseImageIso X f).hom.app
        ((sheafCompose (representableLocalizedRingedTopos X U).J
          (forget CommRingCat.{u})).obj R) :=
  (Classical.choose_spec (representableRelocalizationRingInverseImageIso_existsUnique X f)).1 R

/-- **The inverse image of `O_{h_U^#}` along the relocalization of the ringed site is `O|_V`.**
The identification of Stacks 04J3 at `U` carries `O_{h_U^#}` to `O|_U`, and restriction along
`Over.map f` carries `O|_U` to `O|_V`. -/
noncomputable def representableRelocalizationSiteStructureIso :
    (inverseImageCommRingFunctor (representableRelocalizationSiteToposHom X f)).obj
        (representableLocalizedRingedTopos X U).O ≅
      (X.over V).ringedTopos.O :=
  (MorphismOfTopoi.inverseImageCommRingCompIso (X.overMapMorphismOfTopoi f)
      (representableLocalizationToposMorphism X U)).app
      (representableLocalizedRingedTopos X U).O ≪≫
    (inverseImageCommRingFunctor (X.overMapMorphismOfTopoi f)).mapIso
      (representableLocalizationStructureSheafIso X U) ≪≫
    X.overMapInverseImageCommRingIso f

/-- The comparison of Stacks 04J3 at `U`, evaluated at `O`, restricted along `Over.map f`, with
its endpoints spelled as the underlying sheaves of sets of the two inverse images of
`O_{h_U^#}`. -/
noncomputable def representableRelocalizationStructureComparison :
    (sheafCompose (X.J.over V) (forget CommRingCat.{u})).obj
        ((inverseImageCommRingFunctor (representableRelocalizationSiteToposHom X f)).obj
          (representableLocalizedRingedTopos X U).O) ⟶
      (sheafCompose (X.J.over V) (forget CommRingCat.{u})).obj (X.over V).ringedTopos.O :=
  (X.overMapMorphismOfTopoi f).inverseImage.map (structureSheafInverseImageComparison X U)

/-- On underlying sheaves of sets, the inverse image of `O_{h_U^#}` is identified with `O|_V` by
the restriction along `Over.map f` of the comparison of Stacks 04J3 at `U`. -/
theorem representableRelocalizationSiteStructureIso_hom_forget :
    (sheafCompose (X.J.over V) (forget CommRingCat.{u})).map
        (representableRelocalizationSiteStructureIso X f).hom =
      representableRelocalizationStructureComparison X f := by
  refine (forget_map_inverseImageCommRingCompIso_hom_app_comp (X.overMapMorphismOfTopoi f)
    (representableLocalizationToposMorphism X U)
    (representableLocalizedRingedTopos X U).O _).trans ?_
  refine (forget_map_inverseImageCommRing_map_comp (X.overMapMorphismOfTopoi f)
    (representableLocalizationStructureSheafIso X U).hom _).trans ?_
  rw [representableLocalizationStructureSheafIso_hom_forget_eq,
    X.overMapInverseImageCommRingIso_forget f]
  exact Category.comp_id _

/-- The comparison of the two inverse images, evaluated at `O_{h_U^#}`, as an isomorphism of
sheaves of sets. -/
noncomputable def representableRelocalizationRingComparisonApp :
    (sheafCompose (X.J.over V) (forget CommRingCat.{u})).obj
        ((inverseImageCommRingFunctor (representableRelocalizationCompToposHom X f)).obj
          (representableLocalizedRingedTopos X U).O) ≅
      (sheafCompose (X.J.over V) (forget CommRingCat.{u})).obj
        ((inverseImageCommRingFunctor (representableRelocalizationSiteToposHom X f)).obj
          (representableLocalizedRingedTopos X U).O) :=
  (representableRelocalizationCompInverseImageIso X f).app
    ((sheafCompose (representableLocalizedRingedTopos X U).J (forget CommRingCat.{u})).obj
      (representableLocalizedRingedTopos X U).O)

/-- The lift to sheaves of commutative rings of the comparison of inverse images, evaluated at
`O_{h_U^#}`, induces the comparison itself. -/
theorem representableRelocalizationRingInverseImageIso_hom_app_structureSheaf_forget :
    (sheafCompose (X.J.over V) (forget CommRingCat.{u})).map
        ((representableRelocalizationRingInverseImageIso X f).hom.app
          (representableLocalizedRingedTopos X U).O) =
      (representableRelocalizationRingComparisonApp X f).hom :=
  representableRelocalizationRingInverseImageIso_hom_forget X f
    (representableLocalizedRingedTopos X U).O

/-- **The canonical comparison of the two structure sheaves.** Read through the identification of
`Sh(C/V)` with the topos of the localization at `h_V^#/h_U^#`, the structure sheaf of that
localization is the structure sheaf `O|_V` of the localization of the ringed site at `V`. -/
noncomputable def representableRelocalizationStructureSheafIso :
    (inverseImageCommRingFunctor (representableRelocalizationToposMorphism X f)).obj
        (representableRelocalizedRingedTopos X f).O ≅
      (X.over V).ringedTopos.O :=
  (inverseImageCommRingFunctor (representableRelocalizationToposMorphism X f)).mapIso
      (RingedTopos.localizationInverseImageCommRingIso
        (representableLocalizedRingedTopos X U)
        (representableRelocalizationObject X f)).symm ≪≫
    ((MorphismOfTopoi.inverseImageCommRingCompIso
        (representableRelocalizationToposMorphism X f)
        (representableRelocalizationToposLocalization X f)).app
      (representableLocalizedRingedTopos X U).O).symm ≪≫
    (representableRelocalizationRingInverseImageIso X f).app
        (representableLocalizedRingedTopos X U).O ≪≫
    representableRelocalizationSiteStructureIso X f

/-- The inverse image along the identification of the two topoi of the identification of the
inverse image of `O_{h_U^#}` with the structure sheaf of the localization at `h_V^#/h_U^#` is the
identity on underlying sheaves of sets. -/
theorem inverseImage_map_relocalizedInverseImageCommRingIso_inv_forget :
    (representableRelocalizationToposMorphism X f).inverseImage.map
        ((representableRelocalizedRingedTopos X f).forgetRing.map
          (RingedTopos.localizationInverseImageCommRingIso
            (representableLocalizedRingedTopos X U)
            (representableRelocalizationObject X f)).inv) =
      𝟙 _ :=
  by
  rw [RingedTopos.localizationInverseImageCommRingIso_inv_forget]
  exact CategoryTheory.Functor.map_id _ _

/-- The first two factors of the comparison of structure sheaves are the identity on underlying
sheaves of sets, so they drop out of any composite. -/
theorem forget_map_representableRelocalizationStructureSheafIso_prefix_comp
    {B : Sheaf (X.J.over V) CommRingCat.{u}}
    (b : (inverseImageCommRingFunctor (representableRelocalizationCompToposHom X f)).obj
        (representableLocalizedRingedTopos X U).O ⟶ B) :
    (sheafCompose (X.J.over V) (forget CommRingCat.{u})).map
        ((inverseImageCommRingFunctor (representableRelocalizationToposMorphism X f)).map
            (RingedTopos.localizationInverseImageCommRingIso
              (representableLocalizedRingedTopos X U)
              (representableRelocalizationObject X f)).inv ≫
          ((MorphismOfTopoi.inverseImageCommRingCompIso
                (representableRelocalizationToposMorphism X f)
                (representableRelocalizationToposLocalization X f)).inv.app
              (representableLocalizedRingedTopos X U).O ≫ b)) =
      (sheafCompose (X.J.over V) (forget CommRingCat.{u})).map b := by
  refine (forget_map_inverseImageCommRing_map_comp
    (representableRelocalizationToposMorphism X f)
    (RingedTopos.localizationInverseImageCommRingIso
      (representableLocalizedRingedTopos X U)
      (representableRelocalizationObject X f)).inv _).trans ?_
  rw [inverseImage_map_relocalizedInverseImageCommRingIso_inv_forget]
  refine (Category.id_comp _).trans ?_
  exact forget_map_inverseImageCommRingCompIso_inv_app_comp
    (representableRelocalizationToposMorphism X f)
    (representableRelocalizationToposLocalization X f)
    (representableLocalizedRingedTopos X U).O b

/-- **The comparison of the two structure sheaves induces the comparison of the two inverse
images on underlying sheaves of sets.** -/
theorem representableRelocalizationStructureSheafIso_hom_forget :
    (sheafCompose (X.J.over V) (forget CommRingCat.{u})).map
        (representableRelocalizationStructureSheafIso X f).hom =
      (representableRelocalizationRingComparisonApp X f).hom ≫
        representableRelocalizationStructureComparison X f := by
  refine (forget_map_representableRelocalizationStructureSheafIso_prefix_comp X f
    ((representableRelocalizationRingInverseImageIso X f).hom.app _ ≫
      (representableRelocalizationSiteStructureIso X f).hom)).trans ?_
  rw [CategoryTheory.Functor.map_comp,
    representableRelocalizationRingInverseImageIso_hom_app_structureSheaf_forget,
    representableRelocalizationSiteStructureIso_hom_forget]

/-- **The identification of the localization at `h_V^#/h_U^#` with `Sh(C/V)`, as a morphism of
ringed topoi.** Its structure map is the adjunct of the comparison of structure sheaves. -/
noncomputable def representableRelocalizationRingedMorphism :
    RingedToposHom (ringedTopos (X.over V)) (representableRelocalizedRingedTopos X f) where
  toToposHom := representableRelocalizationToposMorphism X f
  fSharp := (commRingImageAdjunction (representableRelocalizationToposMorphism X f)).homEquiv _ _
    (representableRelocalizationStructureSheafIso X f).hom

/-- The structure map of the identification, in inverse-image form, is the comparison of
structure sheaves. -/
theorem representableRelocalizationRingedMorphism_fSharpInverseImage :
    (representableRelocalizationRingedMorphism X f).fSharpInverseImage =
      (representableRelocalizationStructureSheafIso X f).hom := by
  change ((commRingImageAdjunction (representableRelocalizationToposMorphism X f)).homEquiv
      _ _).symm ((commRingImageAdjunction
        (representableRelocalizationToposMorphism X f)).homEquiv _ _
          (representableRelocalizationStructureSheafIso X f).hom) = _
  rw [Equiv.symm_apply_apply]

/-- The inverse image along the identification of the two topoi of the structure map of the
localization at `h_V^#/h_U^#` is the identity on underlying sheaves of sets. -/
theorem inverseImage_map_relocalizedLocalization_fSharpInverseImage_forget :
    (representableRelocalizationToposMorphism X f).inverseImage.map
        ((representableRelocalizedRingedTopos X f).forgetRing.map
          (RingedTopos.localizationMorphism (representableLocalizedRingedTopos X U)
            (representableRelocalizationObject X f)).fSharpInverseImage) = 𝟙 _ :=
  (congrArg (fun z ↦ (representableRelocalizationToposMorphism X f).inverseImage.map
        ((representableRelocalizedRingedTopos X f).forgetRing.map z))
      (RingedTopos.localization_fSharp_inverseImage
        (representableLocalizedRingedTopos X U)
        (representableRelocalizationObject X f))).trans
    ((congrArg (fun z ↦ (representableRelocalizationToposMorphism X f).inverseImage.map z)
        (RingedTopos.localizationInverseImageCommRingIso_hom_forget
          (representableLocalizedRingedTopos X U)
          (representableRelocalizationObject X f))).trans
      (CategoryTheory.Functor.map_id _ _))

/-- The structure map of the localization at `h_V^#/h_U^#` composed with the identification of
the two topoi is, on underlying sheaves of sets, the comparison of the two inverse images
followed by the comparison of Stacks 04J3 at `U` restricted along `Over.map f`. -/
theorem comp_representableRelocalizationRingedMorphism_fSharpInverseImage_forget :
    (ringedTopos (X.over V)).forgetRing.map
        ((RingedTopos.localizationMorphism (representableLocalizedRingedTopos X U)
            (representableRelocalizationObject X f)).comp
          (representableRelocalizationRingedMorphism X f)).fSharpInverseImage =
      (representableRelocalizationRingComparisonApp X f).hom ≫
        representableRelocalizationStructureComparison X f := by
  refine (RingedToposHom.comp_fSharpInverseImage_forget
    (RingedTopos.localizationMorphism (representableLocalizedRingedTopos X U)
      (representableRelocalizationObject X f))
    (representableRelocalizationRingedMorphism X f)).trans ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫ (ringedTopos (X.over V)).forgetRing.map
      (representableRelocalizationRingedMorphism X f).fSharpInverseImage)
    (inverseImage_map_relocalizedLocalization_fSharpInverseImage_forget X f)) ?_
  refine (Category.id_comp _).trans ?_
  refine Eq.trans (congrArg (fun z ↦ (ringedTopos (X.over V)).forgetRing.map z)
    (representableRelocalizationRingedMorphism_fSharpInverseImage X f)) ?_
  exact representableRelocalizationStructureSheafIso_hom_forget X f

/-- The structure map of the relocalization of the ringed site composed with the identification
of Stacks 04J3 at `U` is, on underlying sheaves of sets, the comparison of Stacks 04J3 at `U`
restricted along `Over.map f`: the relocalization contributes the identity. -/
theorem comp_representableLocalizationRingedMorphism_relocalization_fSharpInverseImage_forget :
    (ringedTopos (X.over V)).forgetRing.map
        ((representableLocalizationRingedMorphism X U).comp
          (X.relocalizationRingedToposHom f)).fSharpInverseImage =
      representableRelocalizationStructureComparison X f := by
  refine (RingedToposHom.comp_fSharpInverseImage_forget
    (representableLocalizationRingedMorphism X U) (X.relocalizationRingedToposHom f)).trans ?_
  rw [X.forgetRing_relocalizationRingedToposHom_fSharpInverseImage f]
  refine (Category.comp_id _).trans ?_
  rw [representableLocalizationRingedMorphism_fSharpInverseImage]
  exact congrArg (fun z ↦ (X.overMapMorphismOfTopoi f).inverseImage.map z)
    (representableLocalizationStructureSheafIso_hom_forget_eq X U)

/-- **The two upper edges agree**, as a 2-isomorphism of morphisms of ringed topoi: the
localization of `(Sh(C)/h_U^#, O_{h_U^#})` at the object `h_V^#/h_U^#`, read through the
identification of the localization at `h_V^#/h_U^#` with `Sh(C/V)`, *is* the relocalization of
the ringed site along `f : V ⟶ U`, read through the identification of Stacks 04J3 at `U`. -/
@[stacks 04J5 "the diagrams of 04IY and 04J4 agree via the identifications of 04J3, as a \
2-isomorphism of morphisms of ringed topoi"]
noncomputable def representableRelocalizationTwoIso :
    TwoIso (A := ringedTopos (X.over V)) (B := representableLocalizedRingedTopos X U)
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over V))
        (Y := representableRelocalizedRingedTopos X f)
        (Z := representableLocalizedRingedTopos X U)
        (RingedTopos.localizationMorphism (representableLocalizedRingedTopos X U)
          (representableRelocalizationObject X f))
        (representableRelocalizationRingedMorphism X f))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over V))
        (Y := ringedTopos (X.over U)) (Z := representableLocalizedRingedTopos X U)
        (representableLocalizationRingedMorphism X U) (X.relocalizationRingedToposHom f)) :=
  RingedToposHom.TwoIso.ofInverseImageIso (A := ringedTopos (X.over V))
    (B := representableLocalizedRingedTopos X U)
    (p := AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over V))
      (Y := representableRelocalizedRingedTopos X f)
      (Z := representableLocalizedRingedTopos X U)
      (RingedTopos.localizationMorphism (representableLocalizedRingedTopos X U)
        (representableRelocalizationObject X f))
      (representableRelocalizationRingedMorphism X f))
    (q := AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over V))
      (Y := ringedTopos (X.over U)) (Z := representableLocalizedRingedTopos X U)
      (representableLocalizationRingedMorphism X U) (X.relocalizationRingedToposHom f))
    (representableRelocalizationCompInverseImageIso X f).symm
    ((congrArg (fun z ↦ (representableRelocalizationRingComparisonApp X f).inv ≫ z)
        (comp_representableRelocalizationRingedMorphism_fSharpInverseImage_forget X f)).trans
      (((representableRelocalizationRingComparisonApp X f).inv_hom_id_assoc _).trans
        (comp_representableLocalizationRingedMorphism_relocalization_fSharpInverseImage_forget
          X f).symm))

/-- **The two relocalization triangles agree**: the relocalization triangle of Stacks 04J4 at the
morphism `h_f^# : h_V^# ⟶ h_U^#` of representable sheaves, read through the identifications of
Stacks 04J3 at `U` and the identification of the localization at `h_V^#/h_U^#` with `Sh(C/V)`,
*is* the relocalization triangle of Stacks 04IY along `f : V ⟶ U`. -/
@[stacks 04J5 "the triangle of 04J4 at a representable is the triangle of 04IY, via the \
identifications of 04J3"]
noncomputable def representableRelocalizationTriangleCompare :
    TwoIso (A := ringedTopos (X.over V)) (B := ringedTopos X)
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over V))
        (Y := representableLocalizedRingedTopos X U) (Z := ringedTopos X)
        (RingedTopos.localizationMorphism X.ringedTopos (representableSheaf X U))
        (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over V))
          (Y := representableRelocalizedRingedTopos X f)
          (Z := representableLocalizedRingedTopos X U)
          (RingedTopos.localizationMorphism (representableLocalizedRingedTopos X U)
            (representableRelocalizationObject X f))
          (representableRelocalizationRingedMorphism X f)))
      (X.localizationRingedToposHom V) :=
  ((representableRelocalizationTwoIso X f).whiskerRight
        (RingedTopos.localizationMorphism X.ringedTopos (representableSheaf X U))).trans
    ((TwoIso.associator (X.relocalizationRingedToposHom f)
          (representableLocalizationRingedMorphism X U)
          (RingedTopos.localizationMorphism X.ringedTopos (representableSheaf X U))).trans
      ((TwoIso.whiskerLeft (X.relocalizationRingedToposHom f)
          (localizationTwoIso X U)).trans (relocalizationTriangle X f).symm))


/-! ### The two descriptions of the upper edge of Stacks 04J4's triangle

Stacks 04J4 describes the upper edge of its relocalization triangle in two ways: as the
relocalization morphism along the morphism `h_f^# : h_V^# ⟶ h_U^#` of sheaves, and as the
localization of `(Sh(C)/h_U^#, O_{h_U^#})` at the object `h_V^#/h_U^#`. Everything above is
stated for the second description. The two have the same inverse image, both being base change
along `h_f^#` read through the identifications of Stacks 04IE. -/

/-- The inverse image of the relocalization morphism of Stacks 04J4 along `h_f^#`, read through
the identification of Stacks 04J3 at `V`, is base change along `h_f^#` followed by Stacks 00Y1's
identification of `Sh(C)/h_V^#` with `Sh(C/V)`. -/
noncomputable def representableRelocalizationSheafMapPullbackIso :
    (RingedTopos.relocalizationMorphism X.ringedTopos
          (representableSheafMap X f)).toToposHom.inverseImage ⋙
        (X.representableLocalizationEquivalence V).inverse ≅
      ((representableSliceEquivalence X U).functor ⋙
          Over.pullback (representableSheafMap X f)) ⋙
        (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (RingedTopos.relocalizationInverseImageSliceIso X.ringedTopos (representableSheafMap X f))
      (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse

/-- The inverse image of the localization at the object `h_V^#/h_U^#`, read through the
identification of that localization with `Sh(C/V)`, is the same base change along `h_f^#`
followed by Stacks 00Y1's identification. -/
noncomputable def representableRelocalizationObjectPullbackIso :
    (representableRelocalizationToposLocalization X f).inverseImage ⋙
        (representableRelocalizationEquivalence X f).functor ≅
      ((representableSliceEquivalence X U).functor ⋙
          Over.pullback (representableSheafMap X f)) ⋙
        (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse :=
  Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        (RingedTopos.localizationInverseImageIso (representableLocalizedRingedTopos X U)
          (representableRelocalizationObject X f))
        (representableRelocalizationSliceEquivalence X f).functor) _ ≪≫
    Functor.isoWhiskerRight (representableRelocalizationStarIso X f) _

/-- **The two descriptions of the upper edge of Stacks 04J4's triangle have the same inverse
image**, read through the identification of Stacks 04J3 at `V` on the one side and through the
identification of the localization at `h_V^#/h_U^#` with `Sh(C/V)` on the other. Both are base
change along `h_f^#`. -/
noncomputable def representableRelocalizationSheafMapInverseImageIso :
    (RingedTopos.relocalizationMorphism X.ringedTopos
          (representableSheafMap X f)).toToposHom.inverseImage ⋙
        (X.representableLocalizationEquivalence V).inverse ≅
      (representableRelocalizationToposLocalization X f).inverseImage ⋙
        (representableRelocalizationEquivalence X f).functor :=
  representableRelocalizationSheafMapPullbackIso X f ≪≫
    (representableRelocalizationObjectPullbackIso X f).symm

/-- **Stacks 04J5 on inverse images, in the sheaf-morphism description of Stacks 04J4's upper
edge.** The relocalization morphism of Stacks 04J4 along `h_f^#`, preceded by the identification
of Stacks 04J3 at `V`, has the same inverse image as the relocalization of the ringed site along
`f`, preceded by the identification of Stacks 04J3 at `U`. -/
noncomputable def representableRelocalizationSheafMapCompInverseImageIso :
    (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over V))
        (Y := representableLocalizedRingedTopos X V)
        (Z := representableLocalizedRingedTopos X U)
        (RingedTopos.relocalizationMorphism X.ringedTopos (representableSheafMap X f))
        (representableLocalizationRingedMorphism X V)).toToposHom.inverseImage ≅
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over V))
        (Y := ringedTopos (X.over U)) (Z := representableLocalizedRingedTopos X U)
        (representableLocalizationRingedMorphism X U)
        (X.relocalizationRingedToposHom f)).toToposHom.inverseImage :=
  representableRelocalizationSheafMapInverseImageIso X f ≪≫
    representableRelocalizationCompInverseImageIso X f

end AlgebraicGeometry.RingedSite

end

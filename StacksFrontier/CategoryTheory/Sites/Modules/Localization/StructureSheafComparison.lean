module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RepresentableLocalization

/-!
# The two localizations of a ringed topos at a representable sheaf agree

Stacks 04IX localizes a ringed site `(C, J, O)` at an object `U`, and Stacks 04IE localizes the
ringed topos `(Sh(C, J), O)` at a sheaf `F`. Taking `F` to be the sheaf `h_U^#` associated to
the presheaf represented by `U` gives two localizations of the same ringed topos. The module
`StacksFrontier.CategoryTheory.Sites.Modules.Localization.RepresentableLocalization` identifies
their
underlying topoi, their inverse images and their structure sheaves; this module proves the last
compatibility of Stacks 04J3, that the two localization morphisms have the same structure map
under that identification.

The proof is a computation on underlying sheaves of sets: the comparison of structure sheaves is
a composite of four isomorphisms, three of which are the identity after forgetting the ring
operations, and the fourth is the canonical comparison of inverse images.

## Main results

* `AlgebraicGeometry.RingedSite.representableLocalizationStructureSheafIso_hom_forget`: the
  comparison of the two structure sheaves induces the canonical comparison of the two inverse
  images on underlying sheaves of sets.
* `AlgebraicGeometry.RingedSite.representableLocalizationMorphism_compare`: the two
  localization morphisms have the same structure map under the canonical comparison of their
  inverse images of sheaves of commutative rings.

## Implementation notes

Both statements are equalities between morphisms whose source and target have two definitionally
equal but syntactically different spellings — `(F ⋙ G).obj A` against `G.obj (F.obj A)`, and the
structure map of a composite of morphisms of ringed topoi against the composite of the structure
maps. Rewriting across such a spelling makes the target ill-typed at the `implicit` transparency
level that `rw` and `simp` use, after which no further rewrite fires. Every statement here
therefore names its endpoints: `compInverseImageComparison`, `overStructureComparison`,
`structureSheafInverseImageComparison` and `ringInverseImageComparisonApp` are the four
comparison morphisms *given the result type they are used at*, and the calculus lemmas
`forget_map_inverseImageCommRing_map_comp` and
`forget_map_inverseImageCommRingCompIso_inv_app_comp` are stated with the
second factor at the type it has on underlying sheaves of sets. With the spellings fixed, each
step is a rewrite with a homogeneous equation, and the remaining definitional identifications are
discharged by `exact`, which works at the default transparency level.

## References

* [Stacks Project, Tag 04J3](https://stacks.math.columbia.edu/tag/04J3)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
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

/-- Forgetting the ring operations in a composite whose first factor is an inverse image of a
morphism of sheaves of commutative rings. The second factor is given the result type it has on
underlying sheaves of sets, so that no later step has to retype it. -/
theorem forget_map_inverseImageCommRing_map_comp
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    {O O' : Sheaf K CommRingCat.{w'}} (a : O ⟶ O') {B : Sheaf J CommRingCat.{w}}
    (b : (inverseImageCommRingFunctor f).obj O' ⟶ B) :
    (sheafCompose J (forget CommRingCat.{w})).map ((inverseImageCommRingFunctor f).map a ≫ b) =
      f.inverseImage.map ((sheafCompose K (forget CommRingCat.{w'})).map a) ≫
        ((sheafCompose J (forget CommRingCat.{w})).map b :
          f.inverseImage.obj ((sheafCompose K (forget CommRingCat.{w'})).obj O') ⟶
            (sheafCompose J (forget CommRingCat.{w})).obj B) := by
  rw [Functor.map_comp, inverseImageCommRingFunctor_map_forget]
  rfl

omit [K.HasSheafCompose (forget CommRingCat.{w'})] in
/-- The comparison of the inverse image along a composite with the iterated inverse image
disappears from a composite on underlying sheaves of sets. -/
theorem forget_map_inverseImageCommRingCompIso_inv_app_comp
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    (g : MorphismOfTopoi (Sheaf K (Type w')) (Sheaf L (Type w'')))
    (O : Sheaf L CommRingCat.{w''}) {B : Sheaf J CommRingCat.{w}}
    (b : (inverseImageCommRingFunctor (g.comp f)).obj O ⟶ B) :
    (sheafCompose J (forget CommRingCat.{w})).map
        ((MorphismOfTopoi.inverseImageCommRingCompIso f g).inv.app O ≫ b) =
      (sheafCompose J (forget CommRingCat.{w})).map b := by
  rw [Functor.map_comp, inverseImageCommRingCompIso_inv_app_forget]
  exact Category.id_comp _

end Forget

end Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- The inverse image, along the identification of the two localized topoi, of the
identification of the inverse image of `O` with the localized structure sheaf is the identity on
underlying sheaves of sets. -/
theorem inverseImage_map_localizationInverseImageCommRingIso_hom_forget :
    (representableLocalizationToposMorphism X U).inverseImage.map
        ((sheafCompose (RingedTopos.localizedRingedTopos X.ringedTopos
            (representableSheaf X U)).J (forget CommRingCat.{u})).map
          (RingedTopos.localizationInverseImageCommRingIso X.ringedTopos
            (representableSheaf X U)).hom) =
      𝟙 _ := by
  rw [localizationInverseImageCommRingIso_hom_forget]
  exact CategoryTheory.Functor.map_id _ _

/-- The same for the inverse identification. -/
theorem inverseImage_map_localizationInverseImageCommRingIso_inv_forget :
    (representableLocalizationToposMorphism X U).inverseImage.map
        ((sheafCompose (RingedTopos.localizedRingedTopos X.ringedTopos
            (representableSheaf X U)).J (forget CommRingCat.{u})).map
          (RingedTopos.localizationInverseImageCommRingIso X.ringedTopos
            (representableSheaf X U)).inv) =
      𝟙 _ := by
  rw [localizationInverseImageCommRingIso_inv_forget]
  exact CategoryTheory.Functor.map_id _ _

/-- The comparison of the iterated inverse image with the inverse image along the composite,
with its codomain spelled as the inverse image along `compToposHom`. -/
noncomputable def compInverseImageComparison :
    (inverseImageCommRingFunctor (representableLocalizationToposMorphism X U)).obj
        ((inverseImageCommRingFunctor (RingedTopos.localizationToposMorphism X.ringedTopos
          (representableSheaf X U))).obj X.O) ⟶
      (inverseImageCommRingFunctor (compToposHom X U)).obj X.O :=
  (MorphismOfTopoi.inverseImageCommRingCompIso (representableLocalizationToposMorphism X U)
    (RingedTopos.localizationToposMorphism X.ringedTopos (representableSheaf X U))).inv.app X.O

/-- The comparison of the inverse image of `O` along the localization at `U` with the
restriction `O|_U`, with its domain spelled as the inverse image along `siteToposHom`. -/
noncomputable def overStructureComparison :
    (inverseImageCommRingFunctor (siteToposHom X U)).obj X.O ⟶ (X.over U).ringedTopos.O :=
  (X.overInverseImageCommRingIso U).hom

/-- The comparison of the inverse image of `O` with its restriction is the identity on
underlying sheaves of sets. -/
theorem overStructureComparison_forget :
    (sheafCompose (X.J.over U) (forget CommRingCat.{u})).map (overStructureComparison X U) =
      𝟙 _ :=
  X.overInverseImageCommRingIso_hom_forget U

/-- The comparison of the two inverse images, evaluated at `O`, with its endpoints spelled as
the underlying sheaves of sets of the two structure sheaves. -/
noncomputable def structureSheafInverseImageComparison :
    (sheafCompose (X.J.over U) (forget CommRingCat.{u})).obj
        ((inverseImageCommRingFunctor (representableLocalizationToposMorphism X U)).obj
          (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U)).O) ⟶
      (sheafCompose (X.J.over U) (forget CommRingCat.{u})).obj (X.over U).ringedTopos.O :=
  (representableLocalizationInverseImageIso X U).hom.app
    ((sheafCompose X.J (forget CommRingCat.{u})).obj X.O)

/-- The lift to sheaves of commutative rings of the comparison of inverse images, evaluated at
`O`, induces the comparison itself. -/
theorem ringInverseImageIsoCore_hom_app_structureSheaf_forget :
    (sheafCompose (X.J.over U) (forget CommRingCat.{u})).map
        ((ringInverseImageIsoCore X U).hom.app X.O) =
      structureSheafInverseImageComparison X U :=
  ringInverseImageIsoCore_hom_forget X U X.O

/-- The first two factors of the comparison of structure sheaves are the identity on underlying
sheaves of sets, so they drop out of any composite. -/
theorem forget_map_structureSheafIso_prefix_comp
    {B : Sheaf (X.J.over U) CommRingCat.{u}}
    (b : (inverseImageCommRingFunctor (compToposHom X U)).obj X.O ⟶ B) :
    (sheafCompose (X.J.over U) (forget CommRingCat.{u})).map
        ((inverseImageCommRingFunctor (representableLocalizationToposMorphism X U)).map
            (RingedTopos.localizationInverseImageCommRingIso X.ringedTopos
              (representableSheaf X U)).inv ≫ compInverseImageComparison X U ≫ b) =
      (sheafCompose (X.J.over U) (forget CommRingCat.{u})).map b := by
  refine (forget_map_inverseImageCommRing_map_comp
    (representableLocalizationToposMorphism X U)
    (RingedTopos.localizationInverseImageCommRingIso X.ringedTopos
      (representableSheaf X U)).inv (compInverseImageComparison X U ≫ b)).trans ?_
  rw [inverseImage_map_localizationInverseImageCommRingIso_inv_forget]
  refine (Category.id_comp _).trans ?_
  exact forget_map_inverseImageCommRingCompIso_inv_app_comp
    (representableLocalizationToposMorphism X U)
    (RingedTopos.localizationToposMorphism X.ringedTopos (representableSheaf X U)) X.O b

/-- **The comparison of the two structure sheaves induces the canonical comparison of the two
inverse images**, in the spelling of `structureSheafInverseImageComparison`. -/
theorem representableLocalizationStructureSheafIso_hom_forget_eq :
    (sheafCompose (X.J.over U) (forget CommRingCat.{u})).map
        (representableLocalizationStructureSheafIso X U).hom =
      structureSheafInverseImageComparison X U := by
  have key : (sheafCompose (X.J.over U) (forget CommRingCat.{u})).map
        ((inverseImageCommRingFunctor (representableLocalizationToposMorphism X U)).map
            (RingedTopos.localizationInverseImageCommRingIso X.ringedTopos
              (representableSheaf X U)).inv ≫
          compInverseImageComparison X U ≫
            (ringInverseImageIsoCore X U).hom.app X.O ≫ overStructureComparison X U) =
      structureSheafInverseImageComparison X U := by
    refine (forget_map_structureSheafIso_prefix_comp X U _).trans ?_
    rw [Functor.map_comp, ringInverseImageIsoCore_hom_app_structureSheaf_forget,
      overStructureComparison_forget]
    exact Category.comp_id _
  exact key

/-- **The comparison of the two structure sheaves induces the canonical comparison of the two
inverse images.** -/
theorem representableLocalizationStructureSheafIso_hom_forget :
    (sheafCompose (X.J.over U) (forget CommRingCat.{u})).map
        (representableLocalizationStructureSheafIso X U).hom =
      (representableLocalizationInverseImageIso X U).hom.app
        ((sheafCompose X.J (forget CommRingCat.{u})).obj X.O) :=
  representableLocalizationStructureSheafIso_hom_forget_eq X U

/-- The comparison of the two inverse images, evaluated at `O`, as an isomorphism, with its
endpoints spelled as the inverse images of sheaves of commutative rings. -/
noncomputable def ringInverseImageComparisonApp :
    (sheafCompose (X.J.over U) (forget CommRingCat.{u})).obj
        ((inverseImageCommRingFunctor (compToposHom X U)).obj X.O) ≅
      (sheafCompose (X.J.over U) (forget CommRingCat.{u})).obj
        ((inverseImageCommRingFunctor (siteToposHom X U)).obj X.O) :=
  (representableLocalizationInverseImageIso X U).app
    ((sheafCompose X.J (forget CommRingCat.{u})).obj X.O)

/-- The two spellings of the comparison of inverse images at `O` agree. -/
theorem structureSheafInverseImageComparison_eq :
    structureSheafInverseImageComparison X U = (ringInverseImageComparisonApp X U).hom := rfl

/-- The lift to sheaves of commutative rings of the comparison of inverse images induces, at
`O`, the comparison itself as an isomorphism. -/
theorem ringInverseImageIsoCore_mapIso_app_eq :
    (sheafCompose (X.J.over U) (forget CommRingCat.{u})).mapIso
        ((ringInverseImageIsoCore X U).app X.O) =
      ringInverseImageComparisonApp X U :=
  Iso.ext (ringInverseImageIsoCore_hom_forget X U X.O)

/-- The inverse of the canonical comparison of inverse images of sheaves of commutative rings
induces, at `O`, the inverse of the comparison of inverse images of sheaves of sets. -/
theorem representableLocalizationRingInverseImageIso_inv_app_forget :
    (sheafCompose (X.J.over U) (forget CommRingCat.{u})).map
        ((representableLocalizationRingInverseImageIso X U).inv.app X.O) =
      (ringInverseImageComparisonApp X U).inv :=
  congrArg Iso.inv (ringInverseImageIsoCore_mapIso_app_eq X U)

/-- The inverse image, along the identification of the two localized topoi, of the structure map
of the localization at `h_U^#` is the identity on underlying sheaves of sets. -/
theorem inverseImage_map_localization_fSharpInverseImage_forget :
    (representableLocalizationRingedMorphism X U).toToposHom.inverseImage.map
        ((RingedTopos.localizedRingedTopos X.ringedTopos
            (representableSheaf X U)).forgetRing.map
          (RingedTopos.localizationMorphism X.ringedTopos
            (representableSheaf X U)).fSharpInverseImage) =
      𝟙 _ := by
  rw [RingedTopos.localization_fSharp_inverseImage]
  exact inverseImage_map_localizationInverseImageCommRingIso_hom_forget X U

/-- The structure map of the localization at `U`, read as a morphism of ringed topoi, is the
identity on underlying sheaves of sets. -/
theorem localizationCommRingedToposHom_fSharpInverseImage_forget :
    (sheafCompose (X.J.over U) (forget CommRingCat.{u})).map
        (X.localizationCommRingedToposHom U).fSharpInverseImage = 𝟙 _ := by
  rw [localizationCommRingedToposHom_fSharpInverseImage]
  exact X.overInverseImageCommRingFsharp_forget U

/-- The structure map of the composite of the localization at `h_U^#` with the identification of
the two localized topoi is, on underlying sheaves of sets, the comparison of inverse images. -/
theorem comp_representableLocalizationRingedMorphism_fSharpInverseImage_forget :
    (sheafCompose (X.J.over U) (forget CommRingCat.{u})).map
        ((RingedTopos.localizationMorphism X.ringedTopos (representableSheaf X U)).comp
          (representableLocalizationRingedMorphism X U)).fSharpInverseImage =
      (ringInverseImageComparisonApp X U).hom := by
  refine (RingedToposHom.comp_fSharpInverseImage_forget
    (RingedTopos.localizationMorphism X.ringedTopos (representableSheaf X U))
    (representableLocalizationRingedMorphism X U)).trans ?_
  rw [inverseImage_map_localization_fSharpInverseImage_forget]
  refine (Category.id_comp _).trans ?_
  rw [representableLocalizationRingedMorphism_fSharpInverseImage]
  exact (representableLocalizationStructureSheafIso_hom_forget_eq X U).trans
    (structureSheafInverseImageComparison_eq X U)

/-- **The two localizations have the same structure map**, under the canonical comparison of
their inverse images of sheaves of commutative rings. This is the last compatibility of Stacks
04J3: the identification of the two localized ringed topoi is compatible with their structure
maps, so it is an identification of localizations and not merely of topoi. -/
@[stacks 04J3 "part (2): compatibility of localization structure maps"]
theorem representableLocalizationMorphism_compare :
    (representableLocalizationRingInverseImageIso X U).inv.app X.O ≫
        ((RingedTopos.localizationMorphism X.ringedTopos (representableSheaf X U)).comp
          (representableLocalizationRingedMorphism X U)).fSharpInverseImage =
      (X.localizationCommRingedToposHom U).fSharpInverseImage := by
  refine (sheafCompose (X.J.over U) (forget CommRingCat.{u})).map_injective ?_
  rw [Functor.map_comp, representableLocalizationRingInverseImageIso_inv_app_forget,
    comp_representableLocalizationRingedMorphism_fSharpInverseImage_forget,
    localizationCommRingedToposHom_fSharpInverseImage_forget]
  exact (ringInverseImageComparisonApp X U).inv_hom_id

end AlgebraicGeometry.RingedSite

end

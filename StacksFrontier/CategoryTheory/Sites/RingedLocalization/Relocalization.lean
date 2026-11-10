module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Morphism
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizationTriangle
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Relocalization of a ringed site, as a morphism of ringed topoi

Let `(C, O)` be a ringed site and `f : V ⟶ U` a morphism of `C`. Localizing at `U` and at `V`
gives two ringed sites `(C/U, O|_U)` and `(C/V, O|_V)`, and the functor `Over.map f : C/V ⥤ C/U`
is continuous and cocontinuous for the localized topologies. It therefore induces a morphism of
topoi `Sh(C/V) ⟶ Sh(C/U)` whose inverse image is restriction along `Over.map f`; and because
the structure sheaf of the localization at `V` *is* the restriction of `O`, the inverse image
of `O|_U` under that morphism is `O|_V`, so the morphism of topoi carries a canonical structure
map and is a morphism of ringed topoi.

This is the *relocalization* morphism. Under the canonical equivalence `(C/U)/(V/U) ≌ C/V` it
is the localization morphism of `(C/U, O|_U)` at the object `V/U`, which is what the source
uses it for.

## Main definitions

* `AlgebraicGeometry.RingedSite.overMapMorphismOfTopoi`: the morphism of topoi
  `Sh(C/V) ⟶ Sh(C/U)` induced by `Over.map f`.
* `AlgebraicGeometry.RingedSite.overMapInverseImageRingIso`: the identification of the
  canonical inverse image of `O|_U` along that morphism with `O|_V`, as sheaves of rings.
* `AlgebraicGeometry.RingedSite.overMapInverseImageFsharp` and `.overMapFsharpAdjoint`: the
  structure map of the relocalization, in inverse-image and in direct-image form.
* `AlgebraicGeometry.RingedSite.relocalizationMorphism`: the relocalization morphism of ringed
  topoi.
* `AlgebraicGeometry.RingedSite.canonicalRelocalizationComparison`: the canonical comparison of
  the two direct images in the relocalization triangle.
* `AlgebraicGeometry.RingedSite.overMapInverseImageCommRingIso` and
  `.overMapCommRingFsharpAdjoint`: the identification of the inverse image of `O|_U` with `O|_V`
  and the resulting structure map, at the level of sheaves of *commutative* rings.
* `AlgebraicGeometry.RingedSite.localizationRingedToposHom` and
  `.relocalizationRingedToposHom`: the localization and the relocalization read as morphisms of
  ringed topoi in the sense of Stacks 01D3 part (2), so that they can be composed.
* `AlgebraicGeometry.RingedSite.overMapInverseImageCompIso` and
  `.relocalizationCompComparison`: the comparison of the two inverse images, and of the two direct
  images, for relocalizing along a composite `f ≫ c`.

## Main results

* `AlgebraicGeometry.RingedSite.overMapInverseImageRingIso_ringSheafMap` and
  `.overMapInverseImageFsharp_ringSheafMap`: the identification and the structure map are the
  identity on underlying sheaves of sets.
* `AlgebraicGeometry.RingedSite.overMap_inverseImage_iteratedSlice`: after transporting along
  the equivalence `(C/U)/(V/U) ≌ C/V`, the inverse image of the relocalization is the inverse
  image of the localization of `(C/U, O|_U)` at `V/U`.
* `AlgebraicGeometry.RingedSite.iteratedSlice_structureSheaf`: the same equivalence carries
  `O|_V` to the structure sheaf of that localization.
* `AlgebraicGeometry.RingedSite.localizationMorphism_comp_relocalizationMorphism`: the
  comparison of the two direct images commutes with the two structure-sheaf maps — the
  relocalization triangle commutes as a triangle of morphisms of *ringed* topoi.
* `AlgebraicGeometry.RingedSite.unit_relocalizationCompComparison_hom_app`: the comparison of the
  two direct images for a composite `f ≫ c` commutes with the structure-sheaf maps, which are all
  units; with `overMapInverseImageCompIso_hom_app_structureSheaf` this is functoriality of
  relocalization as a triangle of morphisms of ringed topoi.
* `AlgebraicGeometry.RingedSite.forgetRing_localizationRingedToposHom_fSharp`,
  `.forgetRing_relocalizationRingedToposHom_fSharp` and `.forgetRing_comp_fSharp`: on
  underlying sheaves of sets, the structure maps of the localization, of the relocalization and
  of their composite are the units of `π⁻¹ ⊣ π_*`, of `j⁻¹ ⊣ j_*` and of the composite
  adjunction.

## Implementation notes

The identification of the inverse image with the restriction is
`Stacks.Sheaves.ToposPullback.restrictionRingIso` at `Over.map f`, followed by Mathlib's
`CategoryTheory.Sheaf.pushforwardOverMapIso`, which says that restricting `O|_U` along
`Over.map f` is `O|_V`. Both are the identity on underlying sheaves of sets, the first because
the inverse image along a restriction functor has the sections of the original sheaf on the
nose, the second because `Over.map f ⋙ Over.forget U = Over.forget V`. So, exactly as for
`AlgebraicGeometry.RingedSite.localizationMorphism`, the structure map of the relocalization
is an isomorphism and is the identity in that sense.

For `relocalizationMorphism` both forms of the structure map are taken at the level of sheaves of
**rings**, which is what `Stacks.Sheaves.RingedToposModules.RingedToposHom.fSharp` asks for; the
direct-image form is the adjunct of the inverse-image form under
`Stacks.Sheaves.ToposPushforward.ringImageAdjunction`, and the adjunctness field holds on
sections by definition, for the reason recorded for the localization morphism. The same two
objects are also supplied at the level of sheaves of **commutative** rings
(`overMapInverseImageCommRingIso`, `overMapCommRingFsharpAdjoint`), built from
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso` and
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`, exactly as
`StacksFrontier/CategoryTheory/Sites/Localization/RingedSiteLocalizationInverseImage.lean` supplies
both levels for the localization; the triangle is stated at the commutative level, for the
reason below.

Two structures in this development are called a morphism of ringed topoi, and the triangle needs
*both*. `relocalizationMorphism` is valued in the four-field
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, which works at the `RingCat` level and is
what the pullback of sheaves of modules is constructed over. The commutativity of the triangle,
however, is a statement about a *composite* of morphisms of ringed topoi, and composition —
Stacks 01D3 part (3), `AlgebraicGeometry.RingedToposHom.comp` — exists only for the canonical
two-field structure `AlgebraicGeometry.RingedToposHom` of Stacks 01D3 part (2), whose structure
map lives at the `CommRingCat` level, which is also the level that
`AlgebraicGeometry.RingedTopos.forgetRing` forgets from. `localizationRingedToposHom` and
`relocalizationRingedToposHom` are therefore the same two geometric morphisms presented as that
structure; their underlying morphisms of topoi are the same objects on the nose
(`localizationRingedToposHom_toToposHom`, `relocalizationRingedToposHom_toToposHom`), so
`canonicalRelocalizationComparison` applies to them unchanged. As
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposHom.lean` records, the two structures
are not interchangeable and must not be consolidated.

The proof of commutativity is the uniqueness of right adjoints. All three structure maps are, on
underlying sheaves of sets, units of the respective adjunctions — because all three
inverse-image forms are the identity there — so the triangle reduces to
`CategoryTheory.Adjunction.unit_rightAdjointUniq_hom_app`. The passage from the direct-image
form of the structure map to the inverse-image form at the `CommRingCat` level is
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`; it is not an equation that
holds on sections by definition — the `CommRingCat`-level adjunction is obtained by restriction
along a fully faithful inclusion, so the ring structure on its unit is transported through chosen
limits — which is why the unit identifications are proved from it rather than by `rfl`, and why
the passage from an adjunct that is the identity to the unit is isolated in the
sheaf-free `CategoryTheory.Adjunction.unit_app_eq_of_homEquiv_symm_eq_id` below.

The structure-sheaf universe is `max u v w`, forced by `overMorphismOfTopoi`, and the two
slice sites keep the object universe `max u v` and the morphism universe `v` of
`AlgebraicGeometry.RingedSite.over`. The `HasSheafCompose` hypotheses that the topos-level ring
image needs are discharged by instance search at this universe rather than assumed.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 04IY](https://stacks.math.columbia.edu/tag/04IY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u v w

namespace CategoryTheory.Adjunction

/-- A morphism `u : A ⟶ G(F(A))` is the unit of `F ⊣ G` at `A` as soon as its adjunct
`F(A) ⟶ F(A)` is the identity.

Stated separately from its two uses below because the two sides of the adjunction bijection are
spelled very differently there: fixing the two objects once, in a statement with no sheaves in
it, keeps both uses inside the default elaboration budget. -/
theorem unit_app_eq_of_homEquiv_symm_eq_id {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (A : C) (u : A ⟶ G.obj (F.obj A))
    (hu : (adj.homEquiv A (F.obj A)).symm u = 𝟙 (F.obj A)) :
    u = adj.unit.app A :=
  ((Equiv.symm_apply_eq _).mp hu).trans (adj.homEquiv_id A)

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max u v w}) {U V : X.C} (f : V ⟶ U)

/-- The morphism of topoi `Sh(C/V) ⟶ Sh(C/U)` induced by `Over.map f`. Its inverse image is
restriction along `Over.map f` and its direct image is the right adjoint of that
restriction. -/
noncomputable def overMapMorphismOfTopoi :
    MorphismOfTopoi (Sheaf (X.J.over V) (Type (max u v w)))
      (Sheaf (X.J.over U) (Type (max u v w))) where
  inverseImage := (Over.map f).sheafPushforwardContinuous _ (X.J.over V) (X.J.over U)
  pushforward := (Over.map f).sheafPushforwardCocontinuous _ (X.J.over V) (X.J.over U)
  adj := (Over.map f).sheafAdjunctionCocontinuous _ (X.J.over V) (X.J.over U)
  preservesFiniteLimits := inferInstance

/-- The canonical inverse image of the structure sheaf of the localization at `U`, along the
relocalization morphism of topoi, is the structure sheaf of the localization at `V`.

It is the comparison of the inverse image with restriction along `Over.map f`, followed by the
identification of the restriction of `O|_U` with `O|_V`. -/
noncomputable def overMapInverseImageRingIso :
    (inverseImageRingFunctor (X.overMapMorphismOfTopoi f)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) ≅
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).O) :=
  (restrictionRingIso (X.J.over V) (X.J.over U) (Over.map f)
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).trans
    ((sheafCompose (X.J.over V) (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).mapIso
      (X.O.pushforwardOverMapIso f))

/-- The identification of the inverse image with the structure sheaf of the localization at `V`
is the identity on underlying sheaves of sets. -/
@[simp]
theorem overMapInverseImageRingIso_ringSheafMap :
    (sheafCompose (X.J.over V) (forget RingCat.{max u v w})).map
        (X.overMapInverseImageRingIso f).hom =
      𝟙 ((sheafCompose (X.J.over V) (forget RingCat.{max u v w})).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).O)) :=
  rfl

/-- The structure map of the relocalization, with the canonical ring inverse image of the
structure sheaf of the localization at `U` as its domain. -/
noncomputable def overMapInverseImageFsharp :
    (inverseImageRingFunctor (X.overMapMorphismOfTopoi f)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).O) :=
  (X.overMapInverseImageRingIso f).hom

/-- The structure map of the relocalization is the identity after forgetting the ring
operations. -/
@[simp]
theorem overMapInverseImageFsharp_ringSheafMap :
    (sheafCompose (X.J.over V) (forget RingCat.{max u v w})).map
        (X.overMapInverseImageFsharp f) =
      𝟙 ((sheafCompose (X.J.over V) (forget RingCat.{max u v w})).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).O)) :=
  rfl

/-- The structure map of the relocalization in direct-image form, the adjunct of
`overMapInverseImageFsharp` under the adjunction `j⁻¹ ⊣ j_*` on sheaves of rings. -/
noncomputable def overMapFsharpAdjoint :
    (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) ⟶
      (pushforwardRingFunctor (X.overMapMorphismOfTopoi f)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).O) :=
  (ringImageAdjunction (X.overMapMorphismOfTopoi f)).homEquiv _ _
    (X.overMapInverseImageFsharp f)

/-- The ring adjunction recovers the inverse-image form of the relocalization structure map
from its direct-image form. -/
@[simp]
theorem overMapFsharpAdjoint_inverseImage :
    ((ringImageAdjunction (X.overMapMorphismOfTopoi f)).homEquiv _ _).symm
        (X.overMapFsharpAdjoint f) = X.overMapInverseImageFsharp f :=
  ((ringImageAdjunction (X.overMapMorphismOfTopoi f)).homEquiv _ _).symm_apply_apply _

/-- The two forms of the relocalization structure map are adjunct on underlying sheaves of
sets: the direct-image form is the adjunct of the inverse-image form under `j⁻¹ ⊣ j_*`. -/
theorem ringSheafMap_overMapFsharpAdjoint :
    (sheafCompose (X.J.over U) (forget RingCat.{max u v w})).map (X.overMapFsharpAdjoint f) =
      (X.overMapMorphismOfTopoi f).adj.homEquiv _ _
        ((sheafCompose (X.J.over V) (forget RingCat.{max u v w})).map
          (X.overMapInverseImageFsharp f)) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- **Stacks 04IY.** The relocalization morphism of ringed topoi attached to a morphism
`f : V ⟶ U` of a ringed site: the morphism of topoi is restriction along `Over.map f`, and the
structure map is the identification of the inverse image of `O|_U` with `O|_V`. -/
noncomputable def relocalizationMorphism :
    Stacks.Sheaves.RingedToposModules.RingedToposHom (ringedTopos (X.over V))
      (ringedTopos (X.over U)) where
  toToposHom := X.overMapMorphismOfTopoi f
  fSharp := X.overMapFsharpAdjoint f
  fSharpInverseImage := X.overMapInverseImageFsharp f
  fSharp_adjunct := X.ringSheafMap_overMapFsharpAdjoint f

/-- The morphism of topoi underlying the relocalization morphism is restriction along
`Over.map f`. -/
@[simp]
theorem relocalizationMorphism_toToposHom :
    (X.relocalizationMorphism f).toToposHom = X.overMapMorphismOfTopoi f :=
  rfl

/-- The direct-image structure map of the relocalization morphism is `overMapFsharpAdjoint f`. -/
@[simp]
theorem relocalizationMorphism_fSharp :
    (X.relocalizationMorphism f).fSharp = X.overMapFsharpAdjoint f :=
  rfl

/-- The structure map of the relocalization, in inverse-image form, is the comparison of the
inverse image of `O|_U` with its restriction along `Over.map f`, followed by the canonical
change-of-slice identification of that restriction with `O|_V`. -/
@[simp]
theorem relocalizationMorphism_fSharpInverseImage :
    (X.relocalizationMorphism f).fSharpInverseImage =
      (restrictionRingIso (X.J.over V) (X.J.over U) (Over.map f)
          (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).hom ≫
        (sheafCompose (X.J.over V)
            (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).map
          (X.O.pushforwardOverMapIso f).hom :=
  rfl

/-- The forward functor `(C/U)/(V/U) ⥤ C/V` of the iterated-slice equivalence is continuous
for the localized topologies.

Mathlib has this instance, but states its target topology as `J.over (Over.mk f).left`;
instance search cannot recover `Over.mk f` from `V`, so the statement at `J.over V` has to be
registered separately. -/
@[sga "3 IV 4.5.1" "partial"]
instance isContinuous_iteratedSliceForward_overMk :
    (Over.iteratedSliceForward (Over.mk f)).IsContinuous
      ((X.J.over U).over (Over.mk f)) (X.J.over V) :=
  CategoryTheory.instIsContinuousOverLeftIteratedSliceForwardOver _

/-- **Stacks 04IY.** After transporting sheaves through the canonical equivalence
`(C/U)/(V/U) ≌ C/V`, the inverse image of the relocalization at `f : V ⟶ U` is the inverse
image of the localization of `(C/U, O|_U)` at the object `V/U`. -/
theorem overMap_inverseImage_iteratedSlice :
    (X.overMapMorphismOfTopoi f).inverseImage ⋙
        (Over.iteratedSliceForward (Over.mk f)).sheafPushforwardContinuous
          (Type (max u v w)) ((X.J.over U).over (Over.mk f)) (X.J.over V) =
      ((X.over U).overMorphismOfTopoi (Over.mk f)).inverseImage := by
  have hfe : Over.iteratedSliceForward (Over.mk f) ⋙ Over.map f = Over.forget (Over.mk f) :=
    map_eq_forget_iteratedSlice (f := f)
  have : (Over.iteratedSliceForward (Over.mk f) ⋙ Over.map f).IsContinuous
      ((X.J.over U).over (Over.mk f)) (X.J.over U) := by
    rw [hfe]; infer_instance
  change (Over.iteratedSliceForward (Over.mk f) ⋙ Over.map f).sheafPushforwardContinuous
      (Type (max u v w)) ((X.J.over U).over (Over.mk f)) (X.J.over U) = _
  congr 1

/-- **Stacks 04IY.** The comparison between the two direct images in the relocalization
triangle: localizing at `V` and localizing at `U` followed by relocalizing along `f` have the
same inverse image, by `inverseImage_eq`, so their direct images are canonically isomorphic by
uniqueness of right adjoints.

The two paths have *different chosen* direct images — `sheafPushforwardCocontinuous` is a chosen
right adjoint — so commutativity of the triangle is this comparison and not an equality. -/
noncomputable def canonicalRelocalizationComparison :
    (X.localizationMorphism V).toToposHom.pushforward ≅
      (MorphismOfTopoi.comp (X.localizationMorphism U).toToposHom
        (X.relocalizationMorphism f).toToposHom).pushforward :=
  Adjunction.rightAdjointUniq
    ((X.localizationMorphism V).toToposHom.adj.ofNatIsoLeft
      (eqToIso (inverseImage_eq X.J f (Type (max u v w)))))
    (MorphismOfTopoi.comp (X.localizationMorphism U).toToposHom
      (X.relocalizationMorphism f).toToposHom).adj

/-- **Stacks 04IY.** The equivalence `(C/U)/(V/U) ≌ C/V` carries the structure sheaf of the
localization at `V` to the structure sheaf of the localization of `(C/U, O|_U)` at `V/U`: both
evaluate at a further slice object as `O` on its underlying object of `C`. -/
theorem iteratedSlice_structureSheaf :
    ((Over.iteratedSliceForward (Over.mk f)).sheafPushforwardContinuous
        CommRingCat.{max u v w} ((X.J.over U).over (Over.mk f)) (X.J.over V)).obj
          (X.over V).O =
      ((X.over U).over (Over.mk f)).O :=
  rfl

/-! ### The triangle as a triangle of morphisms of ringed topoi

Commutativity of the relocalization triangle compares the structure map of the localization at
`V` with the structure map of the composite of the localization at `U` and the relocalization
along `f`. Composition of morphisms of ringed topoi is Stacks 01D3 part (3), which is available
for the canonical two-field structure of part (2), so the two geometric morphisms are presented
once more in that form. -/

/-- The canonical inverse image of the structure sheaf of the localization at `U` along the
relocalization morphism of topoi is the structure sheaf of the localization at `V`, as sheaves
of **commutative** rings.

This is `overMapInverseImageRingIso` one level up: the comparison of the inverse image with
restriction along `Over.map f`, followed by the identification of the restriction of `O|_U`
with `O|_V`. -/
noncomputable def overMapInverseImageCommRingIso :
    (inverseImageCommRingFunctor (X.overMapMorphismOfTopoi f)).obj (X.over U).O ≅
      (X.over V).O :=
  (restrictionCommRingIso (X.J.over V) (X.J.over U) (Over.map f) (X.over U).O).trans
    (X.O.pushforwardOverMapIso f)

/-- The identification of the inverse image of `O|_U` with `O|_V` is the identity on underlying
sheaves of sets. -/
@[simp]
theorem overMapInverseImageCommRingIso_forget :
    (sheafCompose (X.J.over V) (forget CommRingCat.{max u v w})).map
        (X.overMapInverseImageCommRingIso f).hom =
      𝟙 ((sheafCompose (X.J.over V) (forget CommRingCat.{max u v w})).obj (X.over V).O) :=
  rfl

/-- The structure map of the relocalization in direct-image form, at the level of sheaves of
commutative rings: the adjunct of `overMapInverseImageCommRingIso` under the adjunction
`j⁻¹ ⊣ j_*` for sheaves of commutative rings. -/
noncomputable def overMapCommRingFsharpAdjoint :
    (X.over U).O ⟶
      (pushforwardCommRingFunctor (X.overMapMorphismOfTopoi f)).obj (X.over V).O :=
  (commRingImageAdjunction (X.overMapMorphismOfTopoi f)).homEquiv _ _
    (X.overMapInverseImageCommRingIso f).hom

/-- **Stacks 04IX.** The localization morphism at `T`, read as a morphism of ringed topoi in
the sense of Stacks 01D3 part (2): the same morphism of topoi as `localizationMorphism`, with
the `CommRingCat`-level direct-image form of its structure map. -/
noncomputable def localizationRingedToposHom (T : X.C) :
    AlgebraicGeometry.RingedToposHom (ringedTopos (X.over T)) (ringedTopos X) where
  toToposHom := X.overMorphismOfTopoi T
  fSharp := X.overCommRingFsharpAdjoint T

/-- **Stacks 04IY.** The relocalization morphism along `f`, read as a morphism of ringed topoi
in the sense of Stacks 01D3 part (2): the same morphism of topoi as `relocalizationMorphism`,
with the `CommRingCat`-level direct-image form of its structure map. -/
noncomputable def relocalizationRingedToposHom :
    AlgebraicGeometry.RingedToposHom (ringedTopos (X.over V)) (ringedTopos (X.over U)) where
  toToposHom := X.overMapMorphismOfTopoi f
  fSharp := X.overMapCommRingFsharpAdjoint f

/-- The two presentations of the localization have the same underlying morphism of topoi. -/
@[simp]
theorem localizationRingedToposHom_toToposHom (T : X.C) :
    (X.localizationRingedToposHom T).toToposHom = X.overMorphismOfTopoi T :=
  rfl

/-- The two presentations of the relocalization have the same underlying morphism of topoi. -/
@[simp]
theorem relocalizationRingedToposHom_toToposHom :
    (X.relocalizationRingedToposHom f).toToposHom = X.overMapMorphismOfTopoi f :=
  rfl

/-- The inverse-image form of the structure map of the localization is the identity on
underlying sheaves of sets. -/
theorem forgetRing_localizationRingedToposHom_fSharpInverseImage (T : X.C) :
    (ringedTopos (X.over T)).forgetRing.map
        (X.localizationRingedToposHom T).fSharpInverseImage =
      𝟙 ((ringedTopos (X.over T)).forgetRing.obj (X.over T).O) :=
  (congrArg (fun φ ↦ (sheafCompose (X.J.over T) (forget CommRingCat.{max u v w})).map φ)
      (((commRingImageAdjunction (X.overMorphismOfTopoi T)).homEquiv _ _).symm_apply_apply
        (X.overInverseImageCommRingFsharp T))).trans
    (X.overInverseImageCommRingFsharp_forget T)

/-- The inverse-image form of the structure map of the relocalization is the identity on
underlying sheaves of sets. -/
theorem forgetRing_relocalizationRingedToposHom_fSharpInverseImage :
    (ringedTopos (X.over V)).forgetRing.map
        (X.relocalizationRingedToposHom f).fSharpInverseImage =
      𝟙 ((ringedTopos (X.over V)).forgetRing.obj (X.over V).O) :=
  (congrArg (fun φ ↦ (sheafCompose (X.J.over V) (forget CommRingCat.{max u v w})).map φ)
      (((commRingImageAdjunction (X.overMapMorphismOfTopoi f)).homEquiv _ _).symm_apply_apply
        (X.overMapInverseImageCommRingIso f).hom)).trans
    (X.overMapInverseImageCommRingIso_forget f)

/-- On underlying sheaves of sets, the structure map of the localization at `T` is the unit of
`π⁻¹ ⊣ π_*` at the structure sheaf: its inverse-image form is the identity, and the two forms
are adjunct. -/
theorem forgetRing_localizationRingedToposHom_fSharp (T : X.C) :
    (ringedTopos X).forgetRing.map (X.localizationRingedToposHom T).fSharp =
      (X.overMorphismOfTopoi T).adj.unit.app ((ringedTopos X).forgetRing.obj X.O) :=
  Adjunction.unit_app_eq_of_homEquiv_symm_eq_id _ _ _
    ((AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv
        (X.localizationRingedToposHom T)).symm.trans
      (X.forgetRing_localizationRingedToposHom_fSharpInverseImage T))

/-- On underlying sheaves of sets, the structure map of the relocalization along `f` is the unit
of `j⁻¹ ⊣ j_*` at the structure sheaf of the localization at `U`. -/
theorem forgetRing_relocalizationRingedToposHom_fSharp :
    (ringedTopos (X.over U)).forgetRing.map (X.relocalizationRingedToposHom f).fSharp =
      (X.overMapMorphismOfTopoi f).adj.unit.app
        ((ringedTopos (X.over U)).forgetRing.obj (X.over U).O) :=
  Adjunction.unit_app_eq_of_homEquiv_symm_eq_id _ _ _
    ((AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv
        (X.relocalizationRingedToposHom f)).symm.trans
      (X.forgetRing_relocalizationRingedToposHom_fSharpInverseImage f))

/-- On underlying sheaves of sets, the structure map of the composite of the localization at `U`
and the relocalization along `f` is the unit of the composite adjunction. -/
theorem forgetRing_comp_fSharp :
    (ringedTopos X).forgetRing.map
        ((X.localizationRingedToposHom U).comp (X.relocalizationRingedToposHom f)).fSharp =
      ((X.overMorphismOfTopoi U).adj.comp (X.overMapMorphismOfTopoi f).adj).unit.app
        ((ringedTopos X).forgetRing.obj X.O) := by
  have hcf := AlgebraicGeometry.RingedToposHom.comp_fSharp_forget
    (X.localizationRingedToposHom U) (X.relocalizationRingedToposHom f)
  rw [hcf, X.forgetRing_localizationRingedToposHom_fSharp U,
    X.forgetRing_relocalizationRingedToposHom_fSharp f]
  exact (Adjunction.comp_unit_app _ _ _).symm

/-- The comparison of the two direct images, as the uniqueness isomorphism of the two right
adjoints of the common inverse image. Stated so that the two adjunctions it is formed from are
named rather than recovered by unfolding. -/
theorem canonicalRelocalizationComparison_eq :
    X.canonicalRelocalizationComparison f =
      Adjunction.rightAdjointUniq
        ((X.localizationMorphism V).toToposHom.adj.ofNatIsoLeft
          (eqToIso (inverseImage_eq X.J f (Type (max u v w)))))
        (MorphismOfTopoi.comp (X.localizationMorphism U).toToposHom
          (X.relocalizationMorphism f).toToposHom).adj :=
  rfl

/-- Transporting `π⁻¹ ⊣ π_*` along the equality `inverseImage_eq` of its left adjoint with the
composite inverse image does not change its unit at the structure sheaf: the transporting
isomorphism has identity components. -/
theorem localizationAdjunction_ofNatIsoLeft_unit_app :
    ((X.localizationMorphism V).toToposHom.adj.ofNatIsoLeft
          (eqToIso (inverseImage_eq X.J f (Type (max u v w))))).unit.app
        ((ringedTopos X).forgetRing.obj X.O) =
      (X.overMorphismOfTopoi V).adj.unit.app ((ringedTopos X).forgetRing.obj X.O) :=
  (congrArg
    (fun m ↦ (X.overMorphismOfTopoi V).adj.unit.app ((ringedTopos X).forgetRing.obj X.O) ≫ m)
    ((X.overMorphismOfTopoi V).pushforward.map_id
      ((X.overMorphismOfTopoi V).inverseImage.obj
        ((ringedTopos X).forgetRing.obj X.O)))).trans (Category.comp_id _)

/-- The unit of `π⁻¹ ⊣ π_*` for the localization at `V`, followed by the comparison of the two
direct images, is the unit of the composite adjunction. This is uniqueness of right adjoints,
evaluated at the underlying sheaf of sets of the structure sheaf. -/
theorem unit_canonicalRelocalizationComparison_hom_app :
    (X.overMorphismOfTopoi V).adj.unit.app ((ringedTopos X).forgetRing.obj X.O) ≫
        (X.canonicalRelocalizationComparison f).hom.app
          ((ringedTopos (X.over V)).forgetRing.obj (X.over V).O) =
      ((X.overMorphismOfTopoi U).adj.comp (X.overMapMorphismOfTopoi f).adj).unit.app
        ((ringedTopos X).forgetRing.obj X.O) := by
  rw [X.canonicalRelocalizationComparison_eq f,
    ← X.localizationAdjunction_ofNatIsoLeft_unit_app f]
  exact Adjunction.unit_rightAdjointUniq_hom_app _ _ _

/-- **Stacks 04IY.** The canonical comparison of the two paths from `Sh(C/V)` to `Sh(C)`
commutes with their structure-sheaf maps: the relocalization triangle commutes as a triangle of
morphisms of ringed topoi, the two direct images being identified by
`canonicalRelocalizationComparison`. -/
theorem localizationMorphism_comp_relocalizationMorphism :
    (ringedTopos X).forgetRing.map (X.localizationRingedToposHom V).fSharp ≫
        (X.canonicalRelocalizationComparison f).hom.app
          ((ringedTopos (X.over V)).forgetRing.obj (X.over V).O) =
      (ringedTopos X).forgetRing.map
        ((X.localizationRingedToposHom U).comp (X.relocalizationRingedToposHom f)).fSharp := by
  rw [X.forgetRing_localizationRingedToposHom_fSharp V, X.forgetRing_comp_fSharp f]
  exact X.unit_canonicalRelocalizationComparison_hom_app f

/-! ### Functoriality of relocalization

Relocalizing along `f : V ⟶ U` and then along `c : U ⟶ T` is relocalizing along `f ≫ c`. On the
underlying sites the two functors `Over.map f ⋙ Over.map c` and `Over.map (f ≫ c)` agree up to
`CategoryTheory.Over.mapComp`, so the two inverse images are identified by
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` and the two direct images by uniqueness
of right adjoints. The comparison of the inverse images is the *identity* at the structure sheaf
— its component there is restriction of `O` along a morphism of `C/T` lying over an identity of
`C` — which is what makes the comparison of the direct images compatible with the three structure
maps, all three of which are units. -/

section Comp

variable {T : X.C} (c : U ⟶ T)

/-- Relocalizing along `f : V ⟶ U` and then along `c : U ⟶ T` has the same inverse image as
relocalizing along `f ≫ c`: the two underlying functors agree up to `Over.mapComp`, and
restriction along a composite is the composite of the restrictions. -/
noncomputable def overMapInverseImageCompIso :
    (X.overMapMorphismOfTopoi c).inverseImage ⋙ (X.overMapMorphismOfTopoi f).inverseImage ≅
      (X.overMapMorphismOfTopoi (f ≫ c)).inverseImage :=
  Functor.sheafPushforwardContinuousComp' (Over.mapComp f c).symm
    (Type (max u v w)) (X.J.over V) (X.J.over U) (X.J.over T)

/-- At the structure sheaf of the localization at `T` the comparison of the two inverse images is
the identity: its component there is restriction of `O` along a morphism of `C/T` whose underlying
morphism of `C` is an identity. -/
theorem overMapInverseImageCompIso_hom_app_structureSheaf :
    (X.overMapInverseImageCompIso f c).hom.app
        ((ringedTopos (X.over T)).forgetRing.obj (X.over T).O) = 𝟙 _ := by
  refine Sheaf.hom_ext ?_
  ext Y
  simp only [overMapInverseImageCompIso,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.symm_inv]
  have hl : ((Over.mapComp f c).hom.app (Opposite.unop Y)).left = 𝟙 _ := rfl
  have h1 : ((ringedTopos (X.over T)).forgetRing.obj (X.over T).O).obj.map
        ((Over.mapComp f c).hom.app (Opposite.unop Y)).op =
      (forget CommRingCat.{max u v w}).map (X.O.obj.map
        (((Over.mapComp f c).hom.app (Opposite.unop Y)).left).op) := rfl
  rw [h1, hl]
  simp
  rfl

/-- The comparison of the two inverse images read backwards is the identity at the structure
sheaf, since its inverse is. -/
theorem overMapInverseImageCompIso_inv_app_structureSheaf :
    (X.overMapInverseImageCompIso f c).inv.app
        ((ringedTopos (X.over T)).forgetRing.obj (X.over T).O) = 𝟙 _ := by
  have h := (X.overMapInverseImageCompIso f c).hom_inv_id_app
    ((ringedTopos (X.over T)).forgetRing.obj (X.over T).O)
  rw [X.overMapInverseImageCompIso_hom_app_structureSheaf f c] at h
  exact (Category.id_comp _).symm.trans h

/-- The comparison of the two direct images for functoriality of relocalization: relocalizing
along `f ≫ c`, and relocalizing along `f` and then along `c`, have the same inverse image, so
their direct images are canonically isomorphic by uniqueness of right adjoints. -/
noncomputable def relocalizationCompComparison :
    (X.overMapMorphismOfTopoi (f ≫ c)).pushforward ≅
      (MorphismOfTopoi.comp (X.overMapMorphismOfTopoi c)
        (X.overMapMorphismOfTopoi f)).pushforward :=
  Adjunction.rightAdjointUniq
    ((X.overMapMorphismOfTopoi (f ≫ c)).adj.ofNatIsoLeft
      (X.overMapInverseImageCompIso f c).symm)
    (MorphismOfTopoi.comp (X.overMapMorphismOfTopoi c) (X.overMapMorphismOfTopoi f)).adj

/-- Transporting the relocalization adjunction along the comparison of the two inverse images
does not change its unit at the structure sheaf: the comparison is the identity there. -/
theorem relocalizationAdjunction_ofNatIsoLeft_unit_app :
    ((X.overMapMorphismOfTopoi (f ≫ c)).adj.ofNatIsoLeft
          (X.overMapInverseImageCompIso f c).symm).unit.app
        ((ringedTopos (X.over T)).forgetRing.obj (X.over T).O) =
      (X.overMapMorphismOfTopoi (f ≫ c)).adj.unit.app
        ((ringedTopos (X.over T)).forgetRing.obj (X.over T).O) :=
  (congrArg (fun m ↦ (X.overMapMorphismOfTopoi (f ≫ c)).adj.unit.app
        ((ringedTopos (X.over T)).forgetRing.obj (X.over T).O) ≫ m)
    ((congrArg (X.overMapMorphismOfTopoi (f ≫ c)).pushforward.map
        (X.overMapInverseImageCompIso_inv_app_structureSheaf f c)).trans
      ((X.overMapMorphismOfTopoi (f ≫ c)).pushforward.map_id _))).trans (Category.comp_id _)

/-- On underlying sheaves of sets, the structure map of the composite of the relocalizations
along `f` and along `c` is the unit of the composite adjunction. -/
theorem forgetRing_relocalizationComp_fSharp :
    (ringedTopos (X.over T)).forgetRing.map
        ((X.relocalizationRingedToposHom c).comp (X.relocalizationRingedToposHom f)).fSharp =
      ((X.overMapMorphismOfTopoi c).adj.comp (X.overMapMorphismOfTopoi f).adj).unit.app
        ((ringedTopos (X.over T)).forgetRing.obj (X.over T).O) := by
  have hcf := AlgebraicGeometry.RingedToposHom.comp_fSharp_forget
    (X.relocalizationRingedToposHom c) (X.relocalizationRingedToposHom f)
  rw [hcf, X.forgetRing_relocalizationRingedToposHom_fSharp c,
    X.forgetRing_relocalizationRingedToposHom_fSharp f]
  exact (Adjunction.comp_unit_app _ _ _).symm

/-- The comparison of the two direct images commutes with the structure-sheaf maps: the unit of
the relocalization along `f ≫ c`, followed by the comparison, is the unit of the composite
adjunction. This is uniqueness of right adjoints, read at the structure sheaf. -/
theorem unit_relocalizationCompComparison_hom_app :
    (X.overMapMorphismOfTopoi (f ≫ c)).adj.unit.app
          ((ringedTopos (X.over T)).forgetRing.obj (X.over T).O) ≫
        (X.relocalizationCompComparison f c).hom.app
          ((ringedTopos (X.over V)).forgetRing.obj (X.over V).O) =
      ((X.overMapMorphismOfTopoi c).adj.comp (X.overMapMorphismOfTopoi f).adj).unit.app
        ((ringedTopos (X.over T)).forgetRing.obj (X.over T).O) := by
  rw [← X.relocalizationAdjunction_ofNatIsoLeft_unit_app f c]
  exact Adjunction.unit_rightAdjointUniq_hom_app _ _ _

end Comp

end AlgebraicGeometry.RingedSite

end

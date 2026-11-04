module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQcqsPushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleObjRestrict
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenInclusion
public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovariance

/-!
# The small étale direct image along an open immersion of an associated sheaf

Let `j : X' ⟶ X` be a morphism of a big étale site whose underlying morphism of schemes `r` is a
quasi-compact open immersion, and let `𝓕` be a quasi-coherent `𝒪_X`-module.  On abelian sheaves
of the small étale site of `X`, restriction `j^{-1}` to `X'` is left adjoint to the direct image
`j_*`, and Descent, Lemma 071N in degree zero together with the compatibility of `𝓕 ↦ 𝓕^a` with
restriction to `X'` give an isomorphism

`(r_* r^* 𝓕)^a ≅ j_* j^{-1} (𝓕^a)`.

This file produces such an isomorphism which moreover carries the associated sheaf of the unit
`𝓕 ⟶ r_* r^* 𝓕` to the unit `𝓕^a ⟶ j_* j^{-1}(𝓕^a)`.  That compatibility is what the comparison
of the Zariski and étale sequences of Stacks 0A45, in the proof of Stacks 0A46, needs in degree
zero.

## Main definitions

* `CategoryTheory.Adjunction.isoOfIsIsoMap`: for `L ⊣ R` and `f : A ⟶ B` with `L f` and the
  counit at `L A` invertible, an isomorphism `B ≅ R (L A)` corrected by an automorphism of
  `R (L A)` so that `f` followed by it is the unit.
* `AlgebraicGeometry.SmallEtale.pushforwardAssociatedSheafIsoOfQcqs`: Lemma 071N in degree zero
  on abelian sheaves, for a quasi-compact quasi-separated morphism.
* `AlgebraicGeometry.SmallEtale.openRestrictionAssociatedSheafIso`: `(r^*𝓕)^a ≅ j^{-1}(𝓕^a)`.
* `AlgebraicGeometry.SmallEtale.openPushforwardRestrictionAssociatedSheafIso`:
  `(r_* r^* 𝓕)^a ≅ j_* j^{-1} (𝓕^a)`.

## Main results

* `AlgebraicGeometry.SmallEtale.associatedSheaf_map_unit_comp_openPushforwardRestrictionIso_hom`:
  that isomorphism carries the unit to the unit.
* `AlgebraicGeometry.SmallEtale.isIso_openAdjunctionAb_counit_app`: the counit of
  `j^{-1} ⊣ j_*` is an isomorphism.

## Implementation notes

The isomorphism with the unit property is not obtained by checking that the composite of the
identifications of degree zero commutes with the units, but by correcting it:
`j^{-1}` applied to the associated sheaf of the unit is an isomorphism (it is `(r^*` of the unit
`)^a`, and `r^*` of the unit is inverse to the counit of `r^* ⊣ r_*`, which is invertible for an
open immersion), so the adjoint transpose of the unit followed by any isomorphism
`(r_* r^* 𝓕)^a ≅ j_* j^{-1} (𝓕^a)` is an automorphism of `j^{-1}(𝓕^a)`, and composing with its
inverse gives the unit.

## References

* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
* [Stacks Project, Tag 0A46](https://stacks.math.columbia.edu/tag/0A46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {L : C ⥤ D} {R : D ⥤ C}

/-- An isomorphism `B ≅ R (L A)`, corrected by an automorphism of `R (L A)` so that a given
morphism `f : A ⟶ B` followed by it is the unit of `L ⊣ R` at `A`.  This needs `L f` and the
counit at `L A` to be isomorphisms: the adjoint transpose of `f` followed by the given
isomorphism is then an automorphism of `L A`, and its inverse is the correction. -/
def isoOfIsIsoMap (adj : L ⊣ R) {A B : C} (f : A ⟶ B) (e : B ≅ R.obj (L.obj A))
    [IsIso (L.map f)] [IsIso (adj.counit.app (L.obj A))] : B ≅ R.obj (L.obj A) :=
  haveI : IsIso (L.map (f ≫ e.hom) ≫ adj.counit.app (L.obj A)) := by
    rw [L.map_comp]; infer_instance
  e ≪≫ R.mapIso (asIso (L.map (f ≫ e.hom) ≫ adj.counit.app (L.obj A))).symm

/-- **The corrected isomorphism carries `f` to the unit.** -/
@[reassoc]
theorem hom_isoOfIsIsoMap (adj : L ⊣ R) {A B : C} (f : A ⟶ B) (e : B ≅ R.obj (L.obj A))
    [IsIso (L.map f)] [IsIso (adj.counit.app (L.obj A))] :
    f ≫ (adj.isoOfIsIsoMap f e).hom = adj.unit.app A := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_counit, homEquiv_counit, left_triangle_components]
  simp only [isoOfIsIsoMap, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv,
    Functor.map_comp, Category.assoc, counit_naturality]
  simp only [← Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

/-- For an open immersion `r`, the counit `r^* r_* M ⟶ M` is an isomorphism: `r^*` is restriction
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`), whose counit is invertible. -/
instance isIso_pullbackPushforwardAdjunction_counit_app_of_isOpenImmersion {X Y : Scheme.{u}}
    (r : X ⟶ Y) [IsOpenImmersion r] (M : X.Modules) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction r).counit.app M) := by
  have h := Adjunction.leftAdjointUniq_hom_app_counit (Scheme.Modules.restrictAdjunction r)
    (Scheme.Modules.pullbackPushforwardAdjunction r) M
  have : IsIso (((Scheme.Modules.restrictAdjunction r).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction r)).hom.app
        ((Scheme.Modules.pushforward r).obj M) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction r).counit.app M) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left (((Scheme.Modules.restrictAdjunction r).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction r)).hom.app
        ((Scheme.Modules.pushforward r).obj M))
    ((Scheme.Modules.pullbackPushforwardAdjunction r).counit.app M)

/-- For an open immersion `r`, the pullback of the unit `F ⟶ r_* r^* F` is an isomorphism, by
the triangle identity and invertibility of the counit. -/
instance isIso_pullback_map_unit_app_of_isOpenImmersion {X Y : Scheme.{u}}
    (r : X ⟶ Y) [IsOpenImmersion r] (F : Y.Modules) :
    IsIso ((Scheme.Modules.pullback r).map
      ((Scheme.Modules.pullbackPushforwardAdjunction r).unit.app F)) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction r).left_triangle_components F
  have : IsIso ((Scheme.Modules.pullback r).map
        ((Scheme.Modules.pullbackPushforwardAdjunction r).unit.app F) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction r).counit.app
        ((Scheme.Modules.pullback r).obj F)) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Scheme.Modules.pullbackPushforwardAdjunction r).counit.app
      ((Scheme.Modules.pullback r).obj F))

end AlgebraicGeometry

namespace AlgebraicGeometry.SmallEtale

open Stacks.PresheafOfModules

section Abelian

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- `𝓕 ↦ 𝓕^a`, read as an abelian sheaf on the small étale site. -/
abbrev associatedSheaf (X : B.Scheme) :
    X.obj.Modules ⥤ Sheaf (topology B X.obj X.property) AddCommGrpCat.{u} :=
  associatedModule B X.obj X.property ⋙ SheafOfModules.toSheaf (structureSheaf B X.obj X.property)

/-- **Descent, Lemma 071N in degree zero, on abelian sheaves**: `f_{small,*}(𝓕^a) ≅ (r_*𝓕)^a`
for `r` quasi-compact and quasi-separated, where `f_{small,*}` is the direct image of abelian
sheaves along small étale base change.  It is the abelian sheaf underlying
`AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIsoOfQcqs`. -/
def pushforwardAssociatedSheafIsoOfQcqs
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] :
    ((smallEtaleBaseChange B a).sheafPushforwardContinuous AddCommGrpCat.{u}
        (topology B Y.obj Y.property) (topology B X.obj X.property)).obj
        ((associatedSheaf B X).obj 𝓕) ≅
      (associatedSheaf B Y).obj ((Scheme.Modules.pushforward (schemeHom B a)).obj 𝓕) :=
  (SheafOfModules.toSheaf (structureSheaf B Y.obj Y.property)).mapIso
    (pushforwardAssociatedModuleIsoOfQcqs B a 𝓕)

end Abelian

section OpenImmersion

variable (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)]

/-- Restriction of abelian sheaves along the open immersion `j`, `j^{-1}`: the direct image along
post-composition with `j`, so that sections over an object `W` of `X'_étale` are sections over
`W` viewed over `X`. -/
abbrev openRestrictionAb :
    Sheaf (topology B X.obj X.property) AddCommGrpCat.{u} ⥤
      Sheaf (topology B X'.obj X'.property) AddCommGrpCat.{u} :=
  (openPostcompose B j).sheafPushforwardContinuous AddCommGrpCat.{u}
    (topology B X'.obj X'.property) (topology B X.obj X.property)

/-- The direct image of abelian sheaves along `j`, `j_*`. -/
abbrev openPushforwardAb :
    Sheaf (topology B X'.obj X'.property) AddCommGrpCat.{u} ⥤
      Sheaf (topology B X.obj X.property) AddCommGrpCat.{u} :=
  (smallEtaleBaseChange B j).sheafPushforwardContinuous AddCommGrpCat.{u}
    (topology B X.obj X.property) (topology B X'.obj X'.property)

/-- `j^{-1} ⊣ j_*` on abelian sheaves, induced by post-composition with `j` being left adjoint to
base change along `j`. -/
abbrev openAdjunctionAb : openRestrictionAb B j ⊣ openPushforwardAb B j :=
  Adjunction.sheafPushforwardContinuous (openPostcomposeAdjunction B j)
    (topology B X'.obj X'.property) (topology B X.obj X.property)

/-- The counit `j^{-1} j_* K ⟶ K` is an isomorphism, post-composition with an open immersion
being fully faithful. -/
instance isIso_openAdjunctionAb_counit_app
    (K : Sheaf (topology B X'.obj X'.property) AddCommGrpCat.{u}) :
    IsIso ((openAdjunctionAb B j).counit.app K) := by
  have h : ∀ W : (SmallEtale B X'.obj X'.property)ᵒᵖ,
      IsIso (((openAdjunctionAb B j).counit.app K).hom.app W) := by
    intro W
    dsimp [openAdjunctionAb, Adjunction.sheafPushforwardContinuous, Adjunction.whiskerLeft]
    simp only [Category.id_comp, Category.comp_id]
    have : IsIso (openPostcomposeAdjunction B j).unit :=
      Adjunction.unit_isIso_of_L_fully_faithful _
    have : IsIso ((openPostcomposeAdjunction B j).op.counit.app W) :=
      inferInstanceAs (IsIso ((openPostcomposeAdjunction B j).unit.app W.unop).op)
    exact Functor.map_isIso K.obj _
  have : IsIso ((openAdjunctionAb B j).counit.app K).hom := NatIso.isIso_of_isIso_app _
  exact (isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)).1 this

/-- **The associated module commutes with restriction to an open**, on abelian sheaves:
`(r^*𝓕)^a ≅ j^{-1}(𝓕^a)`, naturally in `𝓕`.  This is
`AlgebraicGeometry.SmallEtale.associatedModuleObjRestrictIso` at the object of `X_étale` given by
`j`, the crossover restriction being restriction along post-composition with `j`
(`AlgebraicGeometry.SmallEtale.objRestrictPostIso`). -/
def openRestrictionAssociatedSheafIso :
    Scheme.Modules.pullback (schemeHom B j) ⋙ associatedSheaf B X' ≅
      associatedSheaf B X ⋙ openRestrictionAb B j :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (associatedModuleObjRestrictIso B X.obj X.property (openSiteObject B j))
      (SheafOfModules.toSheaf (structureSheaf B X'.obj X'.property)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (associatedModule B X.obj X.property)
      (Functor.isoWhiskerRight (objRestrictPostIso B X.obj X.property (openSiteObject B j))
        (SheafOfModules.toSheaf (structureSheaf B X'.obj X'.property)) ≪≫
        Iso.refl (SheafOfModules.toSheaf (structureSheaf B X.obj X.property) ⋙
          openRestrictionAb B j)) ≪≫
    (Functor.associator _ _ _).symm

/-- `j^{-1}` of the associated sheaf of the unit `𝓕 ⟶ r_* r^* 𝓕` is an isomorphism, being
`(r^* (unit))^a` by `AlgebraicGeometry.SmallEtale.openRestrictionAssociatedSheafIso`. -/
instance isIso_openRestrictionAb_map_associatedSheaf_map_unit (𝓕 : X.obj.Modules) :
    IsIso ((openRestrictionAb B j).map ((associatedSheaf B X).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B j)).unit.app 𝓕))) :=
  (NatIso.isIso_map_iff (openRestrictionAssociatedSheafIso B j)
    ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B j)).unit.app 𝓕)).1
    (Functor.map_isIso (associatedSheaf B X') _)

/-- **Descent, Lemma 071N in degree zero for an open immersion, compatibly with the units.**
For a quasi-compact open immersion `j` with underlying morphism of schemes `r` and a
quasi-coherent `𝒪_X`-module `𝓕`, an isomorphism `(r_* r^* 𝓕)^a ≅ j_* j^{-1} (𝓕^a)` of abelian
sheaves on `X_étale` which carries the associated sheaf of the unit `𝓕 ⟶ r_* r^* 𝓕` to the unit
`𝓕^a ⟶ j_* j^{-1} 𝓕^a`
(`AlgebraicGeometry.SmallEtale.associatedSheaf_map_unit_comp_openPushforwardRestrictionIso_hom`).

It is the isomorphism `(r_* r^* 𝓕)^a ≅ j_*((r^* 𝓕)^a) ≅ j_* j^{-1}(𝓕^a)` of
`AlgebraicGeometry.SmallEtale.pushforwardAssociatedSheafIsoOfQcqs` and
`AlgebraicGeometry.SmallEtale.openRestrictionAssociatedSheafIso`, corrected by an automorphism
of `j_* j^{-1}(𝓕^a)` (`CategoryTheory.Adjunction.isoOfIsIsoMap`). -/
def openPushforwardRestrictionAssociatedSheafIso [QuasiCompact (schemeHom B j)]
    (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] :
    (associatedSheaf B X).obj ((Scheme.Modules.pushforward (schemeHom B j)).obj
        ((Scheme.Modules.pullback (schemeHom B j)).obj 𝓕)) ≅
      (openPushforwardAb B j).obj ((openRestrictionAb B j).obj ((associatedSheaf B X).obj 𝓕)) :=
  (openAdjunctionAb B j).isoOfIsIsoMap
    ((associatedSheaf B X).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B j)).unit.app 𝓕))
    ((pushforwardAssociatedSheafIsoOfQcqs B j
        ((Scheme.Modules.pullback (schemeHom B j)).obj 𝓕)).symm ≪≫
      (openPushforwardAb B j).mapIso ((openRestrictionAssociatedSheafIso B j).app 𝓕))

/-- **The isomorphism `(r_* r^* 𝓕)^a ≅ j_* j^{-1} (𝓕^a)` carries the unit to the unit.** -/
@[reassoc]
theorem associatedSheaf_map_unit_comp_openPushforwardRestrictionIso_hom
    [QuasiCompact (schemeHom B j)] (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] :
    (associatedSheaf B X).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B j)).unit.app 𝓕) ≫
      (openPushforwardRestrictionAssociatedSheafIso B j 𝓕).hom =
      (openAdjunctionAb B j).unit.app ((associatedSheaf B X).obj 𝓕) :=
  (openAdjunctionAb B j).hom_isoOfIsIsoMap _ _

end OpenImmersion

end AlgebraicGeometry.SmallEtale

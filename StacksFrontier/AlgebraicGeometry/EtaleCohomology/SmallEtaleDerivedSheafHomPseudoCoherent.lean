module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelMonoidal
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.PseudoCoherentHomComparisonLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackOfInternalHom
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSheafHomPerfect
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08JP, case (1): `ε^*` and `RSheafHom` out of a pseudo-coherent object

Let `S` be a scheme and `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` the morphism of ringed sites of
Stacks 08H7, read on the `Type u` model of the small étale site
(`AlgebraicGeometry.SmallEtale.toZariskiSmallModelHom`). Case (1) of Stacks 08JP asserts that for
`E` pseudo-coherent and `F` bounded below in `D(𝒪_S)` the canonical map
`ε^* RSheafHom(E, F) ⟶ RSheafHom(ε^*E, ε^*F)` is an isomorphism.

The argument is local on `S`, as in the source: the general statement
`AlgebraicGeometry.RingedSite.isIso_homComparisonMonoidal_of_isPseudoCoherent` reduces the
question, for a monoidal t-exact functor which is compatible with restriction to slices, to the
members of a covering on which `E` is approximated by a strictly perfect complex. This file
supplies its hypotheses at `ε`, and reads the result for the canonical map of Stacks 08JF
through `isIso_derivedPullbackSheafHomMap_iff_isIso_homComparisonMonoidal`.

## Main results

* `CategoryTheory.Over.isIso_forgetAdjStar_unit_of_subsingleton`: an object admitting at most one
  morphism from every object is subterminal.
* `AlgebraicGeometry.SmallEtale.isZero_over_pullbackTopos_toZariskiSmallModelHom`: if an
  `𝒪_S`-module vanishes on an open `W` of `S`, its pullback to the model vanishes on the image of
  `W`.
* `SmallEtale.isIso_homComparisonMonoidal_derivedPullbackSmallModel_of_isPseudoCoherent`: the
  comparison of the monoidal functor `ε^*` with `RSheafHom` is invertible at `E` pseudo-coherent
  and `F` bounded below.
* `AlgebraicGeometry.SmallEtale.isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent`:
  **Stacks 08JP, case (1)**: the canonical map of Stacks 08JF at `ε` is an isomorphism for `E`
  pseudo-coherent and `F` bounded below.

## Implementation notes

The site of the model is the field `(smallModelRingedTopos B S hS).C`, whose category structure
is the `RingedTopos` field and not the instance of `SmallModel`; slices of sheaves of modules on
the model are therefore taken at objects spelled in `(smallModelRingedTopos B S hS).C`.

## References

* [Stacks Project, Tag 08JP](https://stacks.math.columbia.edu/tag/08JP)
* [Stacks Project, Tag 08H2](https://stacks.math.columbia.edu/tag/08H2)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  AlgebraicGeometry.Scheme.zariskiRingedTopos

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal

/-- **An object admitting at most one morphism from every object is subterminal**: the unit
`V ⟶ U × V` of `Over.forget U ⊣ Over.star U` is an isomorphism over `U`, its inverse being the
second projection. -/
theorem CategoryTheory.Over.isIso_forgetAdjStar_unit_of_subsingleton {C : Type*} [Category C]
    [HasBinaryProducts C] (U : C) [∀ Z : C, Subsingleton (Z ⟶ U)] :
    IsIso (Over.forgetAdjStar U).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro W
  have : IsIso ((Over.forget U).map ((Over.forgetAdjStar U).unit.app W)) := by
    rw [Over.forget_map, Over.forgetAdjStar_unit_app_left]
    refine ⟨(prod.snd : U ⨯ W.left ⟶ W.left), prod.lift_snd _ _, ?_⟩
    show prod.snd ≫ prod.lift W.hom (𝟙 W.left) = 𝟙 (U ⨯ W.left)
    exact prod.hom_ext (Subsingleton.elim _ _) (by simp)
  exact isIso_of_reflects_iso _ (Over.forget U)

namespace AlgebraicGeometry.SmallEtale

/-- There is at most one morphism from an object of the model into the image of an open of `S`:
morphisms into the image of an object under the comparison correspond to morphisms of the small
étale site into that object, and an open immersion is a monomorphism. -/
instance subsingleton_hom_opensToSmallModel (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (Z : SmallModel.{u} (SmallEtale B S hS)) (W : S.Opens) :
    Subsingleton (Z ⟶ (opensToSmallModel B S hS).obj W) :=
  ((smallModelEquiv B S hS).symm.toAdjunction.homEquiv Z _).symm.subsingleton

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Transport to the model preserves vanishing on a slice**: if a sheaf of modules on the small
étale site vanishes on the slice over `X`, its transport to the model vanishes on the slice over
the image of `X`. The sections of the transport over `T ⟶ X'` are those of the sheaf over the
corresponding object of the small étale site, which maps to `X`. -/
theorem isZero_over_modelModulesEquiv_functor_obj
    (G : _root_.SheafOfModules.{u} (structureSheaf B S hS)) (X : SmallEtale B S hS)
    (h : IsZero (G.over X)) :
    IsZero (((modelModulesEquiv B S hS).functor.obj G).over
      (show (smallModelRingedTopos B S hS).C from (smallModelEquiv B S hS).functor.obj X)) := by
  refine Stacks.SheafOfModules.isZero_of_forall_subsingleton_sections _ fun V => ?_
  exact ModuleCat.subsingleton_of_isZero (Functor.map_isZero (SheafOfModules.evaluation _
    (Opposite.op (Over.mk ((smallModelEquiv B S hS).inverse.map V.unop.hom ≫
      (smallModelEquiv B S hS).unitIso.inv.app X)))) h)

/-- **`ε^*` on the model preserves vanishing on the image of an open**: if an `𝒪_S`-module
vanishes on an open `W`, its pullback to the model vanishes on the image of `W`. On the small
étale site, `(𝓕^a)|_{W_étale}` is the associated module of `𝓕|_W`
(`AlgebraicGeometry.SmallEtale.associatedModuleOverObjIso`), and `ε^*` on the model is `𝓕^a`
transported to the model. -/
theorem isZero_over_pullbackTopos_toZariskiSmallModelHom (W : S.Opens)
    (F : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O))
    (h : IsZero (F.over W)) :
    IsZero (((toZariskiSmallModelHom B S hS).pullbackTopos.obj F).over
      ((toZariskiSmallModelHom B S hS).u.obj W)) := by
  have h1 : IsZero (((associatedModule B S hS).obj F).over ((opensToSmallEtale B S hS).obj W)) :=
    (Functor.map_isZero (SheafOfModules.pullback.{u} (sliceStructureMap B S hS W)) h).of_iso
      (associatedModuleOverObjIso B S hS W F).symm
  refine (isZero_over_modelModulesEquiv_functor_obj B S hS _ _ h1).of_iso ?_
  exact (SheafOfModules.overFunctor _ _).mapIso ((pullbackToposIsoAssociatedModel B S hS).app F)

/-- **`ε^*` commutes with `RSheafHom` out of a pseudo-coherent object into a bounded below one**,
for the comparison `AlgebraicGeometry.RingedSite.homComparisonMonoidal` of the monoidal functor
`ε^*` on the model: this is
`AlgebraicGeometry.RingedSite.isIso_homComparisonMonoidal_of_isPseudoCoherent` at `ε`, whose
hypotheses hold because `ε^*` is exact (Stacks 08H8), the images of the opens of `S` cover the
final object (Stacks 08H2), opens of `S` and their images are subterminal, and `ε^*` preserves
vanishing on an open (`isZero_over_pullbackTopos_toZariskiSmallModelHom`). -/
theorem isIso_homComparisonMonoidal_derivedPullbackSmallModel_of_isPseudoCoherent
    (E M : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)))
    (hE : S.zariskiRingedSite.IsPseudoCoherent E) (a : ℤ) (hM : M.IsGE a) :
    letI : (Stacks.Sheaves.DerivedPullback.pullbackToposMapDerived.{u}
      (toZariskiSmallModelHom B S hS)).Monoidal := derivedPullbackSmallModelMonoidal B S hS
    IsIso (RingedSite.homComparisonMonoidal (X := S.zariskiRingedSite)
      (Y := (smallModelRingedTopos B S hS).toRingedSite)
      (Stacks.Sheaves.DerivedPullback.pullbackToposMapDerived.{u} (toZariskiSmallModelHom B S hS))
      E M) := by
  let : (Stacks.Sheaves.DerivedPullback.pullbackToposMapDerived.{u}
      (toZariskiSmallModelHom B S hS)).Monoidal := derivedPullbackSmallModelMonoidal B S hS
  have : ∀ W : S.zariskiRingedSite.C, HasBinaryProducts (S.zariskiRingedSite.over W).C :=
    fun W => inferInstanceAs (HasBinaryProducts (Over W))
  have : HasBinaryProducts (SmallModel.{u} (SmallEtale B S hS)) :=
    Adjunction.hasLimitsOfShape_of_equivalence (smallModelEquiv B S hS).inverse
  have : HasBinaryProducts (smallModelRingedTopos B S hS).toRingedSite.C :=
    inferInstanceAs (HasBinaryProducts (SmallModel.{u} (SmallEtale B S hS)))
  have : (toZariskiSmallModelHom B S hS).u.IsContinuous S.zariskiRingedSite.J
      (smallModelRingedTopos B S hS).toRingedSite.J :=
    isContinuous_opensToSmallModel B S hS
  have : ∀ W : S.zariskiRingedSite.C,
      IsIso (Over.forgetAdjStar ((toZariskiSmallModelHom B S hS).u.obj W)).unit := fun W =>
    Over.isIso_forgetAdjStar_unit_of_subsingleton (C := SmallModel.{u} (SmallEtale B S hS))
      ((opensToSmallModel B S hS).obj W)
  refine RingedSite.isIso_homComparisonMonoidal_of_isPseudoCoherent
    (X := S.zariskiRingedSite) (Y := (smallModelRingedTopos B S hS).toRingedSite)
    (toZariskiSmallModelHom B S hS).u ?_ _
    (fun K n h => Functor.isLE_mapDerivedCategory_obj
      (toZariskiSmallModelHom B S hS).pullbackTopos K n h)
    (fun K n h => Functor.isGE_mapDerivedCategory_obj
      (toZariskiSmallModelHom B S hS).pullbackTopos K n h)
    (fun g j h => Functor.isIso_homologyMap_mapDerivedCategory_map
      (toZariskiSmallModelHom B S hS).pullbackTopos g j h) ?_ E M hE a hM
  · have : PreservesFiniteLimits ((toZariskiSmallModelHom B S hS).u.sheafPullback (Type u)
        S.zariskiRingedSite.J (smallModelRingedTopos B S hS).toRingedSite.J) :=
      (isMorphismOfSites_toZariskiSmallModelHom_u B S hS).preservesFiniteLimits
    exact GrothendieckTopology.coversTop_obj_of_preservesTerminal_sheafPullback _
      S.zariskiRingedSite.J (smallModelRingedTopos B S hS).toRingedSite.J
  · intro W K hK
    rw [DerivedCategory.isZero_iff_forall_isZero_homology] at hK ⊢
    intro n
    have h1 := (hK n).of_iso
      ((RingedSite.sliceDerivedRestrictionHomologyIso S.zariskiRingedSite W n).app K).symm
    refine (isZero_over_pullbackTopos_toZariskiSmallModelHom B S hS W _ h1).of_iso ?_
    exact (RingedSite.sliceDerivedRestrictionHomologyIso
        (smallModelRingedTopos B S hS).toRingedSite ((toZariskiSmallModelHom B S hS).u.obj W)
        n).app _ ≪≫ (SheafOfModules.overFunctor _ _).mapIso
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (toZariskiSmallModelHom B S hS).pullbackTopos n).app K)

/-- **Stacks 08JP, case (1): `ε^*` commutes with `RSheafHom` out of a pseudo-coherent object into
a bounded below one.** Let `S` be a scheme and `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` the morphism of
ringed sites of Stacks 08H7, read on the model of the small étale site. For `E` pseudo-coherent
and `F` in `D^+(𝒪_S)`, the canonical map `ε^* RSheafHom(E, F) ⟶ RSheafHom(ε^* E, ε^* F)` of
Stacks 08JF, `AlgebraicGeometry.RingedToposSiteHom.derivedPullbackSheafHomMap`, is an
isomorphism.

The only hypotheses are the two of the source: pseudo-coherence of `E` and boundedness below of
`F`. By `isIso_derivedPullbackSheafHomMap_iff_isIso_homComparisonMonoidal` it is enough that the
comparison of the monoidal functor `ε^*` is invertible at `E` and `F`, which is
`isIso_homComparisonMonoidal_derivedPullbackSmallModel_of_isPseudoCoherent`. -/
@[stacks 08JP "case (1): E pseudo-coherent, F bounded below"]
theorem isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent
    (E F : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O)))
    (hE : S.zariskiRingedSite.IsPseudoCoherent E) (hF : ∃ a : ℤ, F.IsGE a) :
    IsIso (RingedToposSiteHom.derivedPullbackSheafHomMap (toZariskiSmallModelHom B S hS)
      (isMorphismOfSites_toZariskiSmallModelHom_u B S hS) E F) := by
  obtain ⟨a, ha⟩ := hF
  exact (isIso_derivedPullbackSheafHomMap_iff_isIso_homComparisonMonoidal S B hS E F).2
    (isIso_homComparisonMonoidal_derivedPullbackSmallModel_of_isPseudoCoherent B S hS E F hE a ha)

end AlgebraicGeometry.SmallEtale

end

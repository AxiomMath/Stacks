module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelEtaleBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleBaseChangeMate
public import StacksFrontier.CategoryTheory.Adjunction.MateEquivalenceConjugation
public import StacksFrontier.CategoryTheory.Sites.Modules.PushforwardPushforwardAdjMate

/-!
# Étale base change on the spaces-étale models

Consider a cartesian square of algebraic spaces
```
  Y' --j'--> W'
  |h         |g
  v          v
  Y  --j-->  W
```
with `j` (hence `j'`) étale. This file proves that the base change morphism
`g_* ⋙ j^* ⟶ j'^* ⋙ h_*` of modules on the spaces-étale models
(`AlgebraicGeometry.Space.spacesEtaleModelPushforwardBaseChange`) is invertible, and hence, by
`AlgebraicGeometry.Space.isIso_spacesEtaleModelDerivedPushforwardBaseChange`, so is the derived
base change morphism `Rg_* ⋙ Lj^* ⟶ Lj'^* ⋙ Rh_*`.

By `AlgebraicGeometry.Space.isIso_spacesEtaleModelPushforwardBaseChange_iff` the underived
statement is the invertibility of a mate along the adjunctions of restriction along
postcomposition with the direct images. Those adjunctions are restrictions along the adjunctions
postcomposition ⊣ base change of the small models, so the mate is computed on the sites
(`SheafOfModules.isIso_mateEquiv_symm_pushforwardPushforwardAdj`): on sections it is restriction
along the mate of the square of base changes
(`AlgebraicGeometry.Space.conjugateEquiv_spacesEtaleModelPullbackSquare_app_val_app`). On the
small models that mate is the spaces-étale Beck–Chevalley isomorphism conjugated by the
equivalences with the small models
(`AlgebraicGeometry.Space.isIso_mateEquiv_symm_smallModelBaseChangeSquare`).

## Main definitions

* `AlgebraicGeometry.Space.smallModelBaseChangeSquare`: the 2-cell `u_j ⋙ u_h ⟶ u_g ⋙ u_{j'}` of
  base changes on the small models around a commutative square.

## Main results

* `AlgebraicGeometry.Space.isIso_spacesEtaleModelPushforwardBaseChange_of_isPullback`: étale base
  change for modules on the models.
* `AlgebraicGeometry.Space.isIso_spacesEtaleModelDerivedPushforwardBaseChange_of_isPullback`:
  étale base change for the derived direct image on the models.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Space

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- On sections, the conjugate of the identification of inverse images along equal morphisms is
restriction along the identification of the base changes. -/
theorem conjugateEquiv_spacesEtaleModelPullbackCongr_hom_app_val_app
    {X Y : AlgebraicSpaces B S hS} {k₁ k₂ : X ⟶ Y} (hk : k₁ = k₂)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS X).O))
    (V : (SmallModel.{u} (SpacesEtale B S hS Y))ᵒᵖ) (x) :
    ((conjugateEquiv (spacesEtaleModelHom B S hS k₂).pullbackPushforwardAdjunctionTopos
        (spacesEtaleModelHom B S hS k₁).pullbackPushforwardAdjunctionTopos
        (spacesEtaleModelPullbackCongr B S hS hk).hom).app N).val.app V x =
      N.val.map ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.map
        ((eqToHom (congrArg (fun m : X ⟶ Y => (spacesBaseChange B S hS m).functor) hk)).app
          ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.obj V.unop))).op x := by
  subst hk
  simp only [spacesEtaleModelPullbackCongr, eqToHom_refl, NatTrans.id_app, Iso.refl_hom,
    conjugateEquiv_id]
  show _ =
    N.val.presheaf.map ((equivSmallModel.{u} (SpacesEtale B S hS X)).functor.map (𝟙 _)).op x
  rw [CategoryTheory.Functor.map_id, op_id]
  exact (ConcreteCategory.congr_hom (N.val.presheaf.map_id _) x).symm

variable {W W' Y Y' : AlgebraicSpaces B S hS} (g : W' ⟶ W) (h : Y' ⟶ Y) (j : Y ⟶ W)
  (j' : Y' ⟶ W') (comm : h ≫ j = j' ≫ g)

/-- The 2-cell `u_j ⋙ u_h ⟶ u_g ⋙ u_{j'}` of base changes on the small models around a
commutative square: the comparison `AlgebraicGeometry.Space.spacesBaseChangeCompSquare` of the two
composites of spaces-étale base change, conjugated by the equivalences with the small models. -/
def smallModelBaseChangeSquare :
    TwoSquare (smallModelBaseChange B S hS j) (smallModelBaseChange B S hS g)
      (smallModelBaseChange B S hS h) (smallModelBaseChange B S hS j') :=
  Equivalence.twoSquareConjRight (equivSmallModel.{u} (SpacesEtale B S hS Y))
    (equivSmallModel.{u} (SpacesEtale B S hS W)) (equivSmallModel.{u} (SpacesEtale B S hS Y'))
    (equivSmallModel.{u} (SpacesEtale B S hS W'))
    (TwoSquare.mk _ _ _ _ (spacesBaseChangeCompSquare B S hS j' h g j comm.symm))

/-- The components of `AlgebraicGeometry.Space.smallModelBaseChangeSquare` are those of the
composition isomorphisms of base change on the small models around the square. -/
theorem smallModelBaseChangeSquare_app (V : SmallModel.{u} (SpacesEtale B S hS W)) :
    (smallModelBaseChangeSquare B S hS g h j j' comm).natTrans.app V =
      (smallModelBaseChangeComp B S hS h j).hom.app V ≫
        (equivSmallModel.{u} (SpacesEtale B S hS Y')).functor.map
          ((eqToHom (congrArg (fun m : Y' ⟶ W => (spacesBaseChange B S hS m).functor) comm)).app
            ((equivSmallModel.{u} (SpacesEtale B S hS W)).inverse.obj V)) ≫
        (smallModelBaseChangeComp B S hS j' g).inv.app V := by
  simp [smallModelBaseChangeSquare, Equivalence.twoSquareConjRight, spacesBaseChangeCompSquare,
    smallModelBaseChangeComp]

/-- **On sections, the conjugate square of direct images is restriction along the square of base
changes**: the conjugate `j'_* ⋙ g_* ⟶ h_* ⋙ j_*` of
`AlgebraicGeometry.Space.spacesEtaleModelPullbackSquare` is, on the sections over `V`, restriction
along the component at `V` of `AlgebraicGeometry.Space.smallModelBaseChangeSquare`. -/
theorem conjugateEquiv_spacesEtaleModelPullbackSquare_app_val_app
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS Y').O))
    (V : (SmallModel.{u} (SpacesEtale B S hS W))ᵒᵖ) (x) :
    ((conjugateEquiv ((spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos.comp
        (spacesEtaleModelHom B S hS j').pullbackPushforwardAdjunctionTopos)
      ((spacesEtaleModelHom B S hS j).pullbackPushforwardAdjunctionTopos.comp
        (spacesEtaleModelHom B S hS h).pullbackPushforwardAdjunctionTopos)
      (spacesEtaleModelPullbackSquare B S hS g h j j' comm).natTrans).app N).val.app V x =
      N.val.map ((smallModelBaseChangeSquare B S hS g h j j' comm).natTrans.app V.unop).op x := by
  rw [conjugateEquiv_spacesEtaleModelPullbackSquare]
  show ((spacesEtaleModelPushforwardComp B S hS h j).inv.app N).val.app V
    (((conjugateEquiv (spacesEtaleModelHom B S hS (j' ≫ g)).pullbackPushforwardAdjunctionTopos
        (spacesEtaleModelHom B S hS (h ≫ j)).pullbackPushforwardAdjunctionTopos
        (spacesEtaleModelPullbackCongr B S hS comm).hom).app N).val.app V
      (((spacesEtaleModelPushforwardComp B S hS j' g).hom.app N).val.app V x)) = _
  refine (congrArg (fun y => ((spacesEtaleModelPushforwardComp B S hS h j).inv.app N).val.app V y)
    (conjugateEquiv_spacesEtaleModelPullbackCongr_hom_app_val_app B S hS comm N V _)).trans ?_
  let P : (SmallModel.{u} (SpacesEtale B S hS Y'))ᵒᵖ ⥤ AddCommGrpCat.{u} := N.val.presheaf
  show P.map ((smallModelBaseChangeComp B S hS h j).hom.app V.unop).op
    (P.map ((equivSmallModel.{u} (SpacesEtale B S hS Y')).functor.map
        ((eqToHom (congrArg (fun m : Y' ⟶ W => (spacesBaseChange B S hS m).functor) comm)).app
          ((equivSmallModel.{u} (SpacesEtale B S hS W)).inverse.obj V.unop))).op
      (P.map ((smallModelBaseChangeComp B S hS j' g).inv.app V.unop).op x)) =
    P.map ((smallModelBaseChangeSquare B S hS g h j j' comm).natTrans.app V.unop).op x
  have key : P.map ((smallModelBaseChangeComp B S hS j' g).inv.app V.unop).op ≫
      P.map ((equivSmallModel.{u} (SpacesEtale B S hS Y')).functor.map
        ((eqToHom (congrArg (fun m : Y' ⟶ W => (spacesBaseChange B S hS m).functor) comm)).app
          ((equivSmallModel.{u} (SpacesEtale B S hS W)).inverse.obj V.unop))).op ≫
      P.map ((smallModelBaseChangeComp B S hS h j).hom.app V.unop).op =
      P.map ((smallModelBaseChangeSquare B S hS g h j j' comm).natTrans.app V.unop).op := by
    rw [← P.map_comp, ← P.map_comp, smallModelBaseChangeSquare_app]
    simp only [op_comp, Category.assoc]
  exact ConcreteCategory.congr_hom key x

/-- **Beck–Chevalley on the small models**: for a cartesian square with étale horizontal arrows,
the mate `u_h ⋙ P_{j'} ⟶ P_j ⋙ u_g` of `AlgebraicGeometry.Space.smallModelBaseChangeSquare`
along postcomposition ⊣ base change is invertible. It is the spaces-étale Beck–Chevalley
isomorphism `AlgebraicGeometry.Space.spacesEtaleBaseChangeSquare` conjugated by the equivalences
with the small models (`AlgebraicGeometry.Space.mateEquiv_spacesEtaleBaseChangeSquare` and
`CategoryTheory.Equivalence.mateEquiv_twoSquareConjLeft`). -/
theorem isIso_mateEquiv_symm_smallModelBaseChangeSquare (hj : IsEtale B S hS j.hom)
    (hj' : IsEtale B S hS j'.hom) (sq : IsPullback j' h g j) :
    IsIso ((mateEquiv (smallModelPostcompAdjunction B S hS j hj)
      (smallModelPostcompAdjunction B S hS j' hj')).symm
        (smallModelBaseChangeSquare B S hS g h j j' comm)).natTrans := by
  have e1 : (mateEquiv (spacesEtalePostcompBaseChangeAdjunction B S hS j hj)
      (spacesEtalePostcompBaseChangeAdjunction B S hS j' hj')).symm
        (TwoSquare.mk _ _ _ _ (spacesBaseChangeCompSquare B S hS j' h g j comm.symm)) =
      TwoSquare.mk _ _ _ _ (spacesEtaleBaseChangeSquare B S hS j' h g j sq hj).hom := by
    rw [Equiv.symm_apply_eq]
    exact (mateEquiv_spacesEtaleBaseChangeSquare B S hS j' h g j sq hj).symm
  have e2 : (mateEquiv (smallModelPostcompAdjunction B S hS j hj)
      (smallModelPostcompAdjunction B S hS j' hj')).symm
        (smallModelBaseChangeSquare B S hS g h j j' comm) =
      Equivalence.twoSquareConjLeft (equivSmallModel.{u} (SpacesEtale B S hS Y))
        (equivSmallModel.{u} (SpacesEtale B S hS W)) (equivSmallModel.{u} (SpacesEtale B S hS Y'))
        (equivSmallModel.{u} (SpacesEtale B S hS W'))
        ((mateEquiv (spacesEtalePostcompBaseChangeAdjunction B S hS j hj)
          (spacesEtalePostcompBaseChangeAdjunction B S hS j' hj')).symm
            (TwoSquare.mk _ _ _ _ (spacesBaseChangeCompSquare B S hS j' h g j comm.symm))) := by
    rw [Equiv.symm_apply_eq]
    refine Eq.trans ?_ (Equivalence.mateEquiv_twoSquareConjLeft _ _ _ _
      (spacesEtalePostcompBaseChangeAdjunction B S hS j hj)
      (spacesEtalePostcompBaseChangeAdjunction B S hS j' hj') _).symm
    rw [Equiv.apply_symm_apply]
    rfl
  rw [e2, e1]
  infer_instance

/-- **Étale base change for modules on the spaces-étale models (Stacks 03LR, part (1)).** For a
cartesian square of algebraic spaces with étale horizontal arrows `j`, `j'`, the base change
morphism `g_* ⋙ j^* ⟶ j'^* ⋙ h_*` of modules on the models is invertible. -/
theorem isIso_spacesEtaleModelPushforwardBaseChange_of_isPullback (hj : IsEtale B S hS j.hom)
    (hj' : IsEtale B S hS j'.hom) (sq : IsPullback j' h g j) :
    IsIso (spacesEtaleModelPushforwardBaseChange B S hS g h j j' comm).natTrans := by
  rw [isIso_spacesEtaleModelPushforwardBaseChange_iff B S hS g h j j' comm hj hj']
  refine SheafOfModules.isIso_mateEquiv_symm_pushforwardPushforwardAdj
    (ha := (spacesEtaleModelHom B S hS g).isContinuous)
    (hb := (spacesEtaleModelHom B S hS h).isContinuous)
    (hq := (spacesEtaleModelHom B S hS j).isContinuous)
    (hq' := (spacesEtaleModelHom B S hS j').isContinuous)
    (hσ := isIso_mateEquiv_symm_smallModelBaseChangeSquare B S hS g h j j' comm hj hj' sq)
    (smallModelPostcompAdjunction B S hS j hj) (smallModelPostcompAdjunction B S hS j' hj')
    (smallModelPostcompSharp B S hS j hj) (spacesEtaleModelHom B S hS j).fSharpRing
    (NatTrans.ext (funext fun V => RingCat.hom_ext (RingHom.ext fun s =>
      (Shrink.ringEquiv _).injective (smallModelPostcomp_H₁_apply B S hS j hj V s))))
    (smallModelPostcomp_H₂ B S hS j hj)
    (smallModelPostcompSharp B S hS j' hj') (spacesEtaleModelHom B S hS j').fSharpRing
    (NatTrans.ext (funext fun V => RingCat.hom_ext (RingHom.ext fun s =>
      (Shrink.ringEquiv _).injective (smallModelPostcomp_H₁_apply B S hS j' hj' V s))))
    (smallModelPostcomp_H₂ B S hS j' hj')
    (spacesEtaleModelHom B S hS g).fSharpRing (spacesEtaleModelHom B S hS h).fSharpRing
    (conjugateEquiv ((spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos.comp
        (spacesEtaleModelHom B S hS j').pullbackPushforwardAdjunctionTopos)
      ((spacesEtaleModelHom B S hS j).pullbackPushforwardAdjunctionTopos.comp
        (spacesEtaleModelHom B S hS h).pullbackPushforwardAdjunctionTopos)
      (spacesEtaleModelPullbackSquare B S hS g h j j' comm).natTrans)
    (smallModelBaseChangeSquare B S hS g h j j' comm)
    ?_
  intro N V x
  exact conjugateEquiv_spacesEtaleModelPullbackSquare_app_val_app B S hS g h j j' comm N V x

/-- **Étale base change for the derived direct image on the spaces-étale models.**
For a cartesian square of algebraic spaces with étale horizontal arrows `j`, `j'`, the derived
base change morphism `Rg_* ⋙ Lj^* ⟶ Lj'^* ⋙ Rh_*` on the models is invertible. -/
theorem isIso_spacesEtaleModelDerivedPushforwardBaseChange_of_isPullback
    (hj : IsEtale B S hS j.hom) (hj' : IsEtale B S hS j'.hom) (sq : IsPullback j' h g j) :
    IsIso (spacesEtaleModelDerivedPushforwardBaseChange B S hS g h j j' comm).natTrans :=
  have := isIso_spacesEtaleModelPushforwardBaseChange_of_isPullback B S hS g h j j' comm hj hj' sq
  isIso_spacesEtaleModelDerivedPushforwardBaseChange B S hS g h j j' comm hj hj'

end AlgebraicGeometry.Space

end

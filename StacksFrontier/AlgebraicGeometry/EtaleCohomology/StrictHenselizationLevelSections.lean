module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationStalkColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleSectionsPullbackRestriction

/-!
# The levels of the neighbourhood system and sections over the base changes

Let `f : X ⟶ S`, `s` a geometric point of `S`, `U` an open subscheme containing the image of `s`,
and `a` a member of the directed system of affine étale neighbourhoods `N_a` of `s` over `U`. The
level `Y_a = Z_a ×_U X_U` of `AlgebraicGeometry.etaleNeighborhoodDirectedBaseChange` is the base
change `X ×_S N_a` over `X`, so restricting along that identification is an isomorphism

`F(X ×_S N_a) ≅ Γ(Y_a, (Y_a ⟶ X)⁻¹F)`

for an abelian sheaf `F` on `X_étale`. The legs of the limit cone
`AlgebraicGeometry.strictHenselizationDirectedLimitCone` followed by that identification are the
lifts `AlgebraicGeometry.sectionsLift` along which
`AlgebraicGeometry.strictHenselizationSectionsCocone` restricts.

## Main definitions

* `AlgebraicGeometry.levelToSource` — the étale projection `Y_a ⟶ X`.
* `AlgebraicGeometry.levelToBaseChange` — the isomorphism `Y_a ⟶ X ×_S N_a` over `X`.
* `AlgebraicGeometry.levelSections` — the restriction `F(X ×_S N_a) ⟶ Γ(Y_a, (Y_a ⟶ X)⁻¹F)`.

## Main results

* `AlgebraicGeometry.isIso_levelSections` — it is an isomorphism.
* `AlgebraicGeometry.strictHenselizationDirectedLimitCone_π_levelToBaseChange` — the legs of the
  limit cone are the lifts of the cocone of restrictions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (U : S.Opens) (hU : s.hom (closedPoint s.residueField) ∈ U) {X : Scheme.{u}} (f : X ⟶ S)
  (a : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ)

/-- The étale neighbourhood of `s` in the small étale site of `S` at a member of the directed
system. -/
abbrev directedNeighborhood : S.Etale :=
  ((etaleNeighborhoodDirectedNeighborhoods B S hS s U hU).obj a).1

/-- Its structure morphism to `S` factors through `U` as the structure morphism of `Z_a`. -/
theorem directedNeighborhood_hom :
    (directedNeighborhood B S hS s U hU a).hom =
      ((etaleNeighborhoodDirectedSystem B S hS s U hU).obj a).hom ≫ U.ι :=
  (etaleNeighborhoodToOpen_ι B S hS s U _).symm

/-- The projection `Y_a = Z_a ×_U X_U ⟶ X_U ⟶ X` of a level to `X`. -/
abbrev levelToSource : (etaleNeighborhoodDirectedBaseChange B S hS s U hU f).obj a ⟶ X :=
  pullback.snd ((etaleNeighborhoodDirectedSystem B S hS s U hU).obj a).hom
      (sourceOverOpen S U f).hom ≫ pullback.fst f U.ι

/-- The projection `Y_a ⟶ X` of a level is étale. -/
instance : Etale (levelToSource B S hS s U hU f a) := inferInstance

/-- The identification `Y_a ⟶ X ×_S N_a` of the level with the base change of `f` to the
neighbourhood, over `X`. -/
def levelToBaseChange :
    (etaleNeighborhoodDirectedBaseChange B S hS s U hU f).obj a ⟶
      ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj
        (directedNeighborhood B S hS s U hU a)).left :=
  pullback.lift (pullback.fst ((etaleNeighborhoodDirectedSystem B S hS s U hU).obj a).hom
      (sourceOverOpen S U f).hom) (levelToSource B S hS s U hU f a) (by
    rw [directedNeighborhood_hom]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.ι) pullback.condition).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (pullback.condition (f := f) (g := U.ι)).symm).trans (Category.assoc _ _ _).symm))))

/-- The identification `Y_a ⟶ X ×_S N_a` is a morphism over `X`. -/
@[reassoc (attr := simp)]
theorem levelToBaseChange_hom :
    levelToBaseChange B S hS s U hU f a ≫
        ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj
          (directedNeighborhood B S hS s U hU a)).hom =
      levelToSource B S hS s U hU f a :=
  pullback.lift_snd _ _ _

/-- The identification `Y_a ⟶ X ×_S N_a` followed by the projection to `N_a` is the projection
`Z_a ×_U X_U ⟶ Z_a`. -/
@[reassoc (attr := simp)]
theorem levelToBaseChange_fst :
    levelToBaseChange B S hS s U hU f a ≫
        pullback.fst (directedNeighborhood B S hS s U hU a).hom f =
      pullback.fst ((etaleNeighborhoodDirectedSystem B S hS s U hU).obj a).hom
        (sourceOverOpen S U f).hom :=
  pullback.lift_fst _ _ _

/-- The level `Z_a ×_U X_U` is a pullback of `f` along the neighbourhood `N_a ⟶ S`, by pasting the
two cartesian squares. -/
theorem isPullback_level :
    IsPullback (pullback.fst ((etaleNeighborhoodDirectedSystem B S hS s U hU).obj a).hom
        (sourceOverOpen S U f).hom) (levelToSource B S hS s U hU f a)
      (directedNeighborhood B S hS s U hU a).hom f := by
  rw [directedNeighborhood_hom]
  exact ((IsPullback.of_hasPullback ((etaleNeighborhoodDirectedSystem B S hS s U hU).obj a).hom
    (sourceOverOpen S U f).hom).flip.paste_horiz (IsPullback.of_hasPullback f U.ι)).flip

/-- The identification `Y_a ⟶ X ×_S N_a` is an isomorphism. -/
instance isIso_levelToBaseChange : IsIso (levelToBaseChange B S hS s U hU f a) := by
  have h := isPullback_level B S hS s U hU f a
  rw [show levelToBaseChange B S hS s U hU f a = h.isoPullback.hom from pullback.hom_ext
    ((levelToBaseChange_fst B S hS s U hU f a).trans h.isoPullback_hom_fst.symm)
    ((levelToBaseChange_hom B S hS s U hU f a).trans h.isoPullback_hom_snd.symm)]
  exact Iso.isIso_hom _

/-- **The legs of the limit cone are the lifts of the cocone of restrictions**: the leg
`X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ Y_a` followed by `Y_a ≅ X ×_S N_a` is the morphism induced by the
canonical lift `Spec(𝒪^{sh}_{S,s}) ⟶ N_a` and the projection to `X`. -/
theorem strictHenselizationDirectedLimitCone_π_levelToBaseChange :
    (strictHenselizationDirectedLimitCone B S hS s U hU f).π.app a ≫
        levelToBaseChange B S hS s U hU f a =
      sectionsLift B hS f s (strictHenselizationBaseChangeToSource B hS f s)
        (strictHenselizationBaseChangeToStrictHenselization B hS f s) pullback.condition
        (directedNeighborhood B S hS s U hU a)
        ((etaleNeighborhoodDirectedNeighborhoods B S hS s U hU).obj a).2 := by
  let e := etaleNeighborhoodDirectedBaseChangeConePtIso B S hS s U hU f
  let π := (strictHenselizationDirectedLimitCone B S hS s U hU f).π.app a
  let coneLeg := (strictHenselizationCone B S hS s).π.app
    ((etaleNeighborhoodAffineInclusion B S hS s).obj
      ((etaleNeighborhoodDirectedFunctor B S hS s U hU).obj a).1)
  have he :
      e.inv ≫ pullback.fst _ _ = strictHenselizationBaseChangeToStrictHenselization B hS f s :=
    (Iso.inv_comp_eq e).mpr
      (etaleNeighborhoodDirectedBaseChangeConePtIso_hom_toStrictHenselization B S hS s U hU f).symm
  have hπ : π ≫ pullback.fst ((etaleNeighborhoodDirectedSystem B S hS s U hU).obj a).hom
      (sourceOverOpen S U f).hom = (e.inv ≫ pullback.fst _ _) ≫ coneLeg := by
    simp only [π, Over.pullback, Cone.extend_π, Functor.const_obj_obj, Functor.mapCone_π_app,
      Over.forget_map, NatTrans.comp_app, Category.assoc, Functor.const_map_app, Over.homMk_left]
    exact congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans ((congrArg (π ≫ ·)
      (levelToBaseChange_fst B S hS s U hU f a)).trans (hπ.trans ?_))
    refine (congrArg (· ≫ coneLeg) he).trans ?_
    refine (congrArg (strictHenselizationBaseChangeToStrictHenselization B hS f s ≫ ·)
      (strictHenselizationCone_π_app_eq_neighborhoodLift B S hS s _)).trans ?_
    exact (sectionsLift_fst B hS f s _ _ _ _ _).symm
  · refine (Category.assoc _ _ _).trans ((congrArg (π ≫ ·)
      (levelToBaseChange_hom B S hS s U hU f a)).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst f U.ι)
      (strictHenselizationDirectedLimitCone_π_snd B S hS s U hU f a)).trans
        ((strictHenselizationToSourceOverOpen_fst B S hS s U hU f).trans ?_))
    exact (sectionsLift_hom B hS f s _ _ _ _ _).symm

/-- **Sections over the base change are global sections over the level**: the restriction
`F(X ×_S N_a) ⟶ Γ(Y_a, (Y_a ⟶ X)⁻¹F)` along `Y_a ≅ X ×_S N_a`. -/
abbrev levelSections (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    ((smallEtalePushforwardAb f).obj F).obj.obj (op (directedNeighborhood B S hS s U hU a)) ⟶
      (Sheaf.Γ (smallEtaleTopology ((etaleNeighborhoodDirectedBaseChange B S hS s U hU f).obj a))
        Ab.{u + 1}).obj ((smallEtalePullbackAb (levelToSource B S hS s U hU f a)).obj F) :=
  (smallEtaleSectionsPullbackAb (levelToSource B S hS s U hU f a)
    ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj (directedNeighborhood B S hS s U hU a))
    (levelToBaseChange B S hS s U hU f a) (levelToBaseChange_hom B S hS s U hU f a)).app F

/-- The restriction `F(X ×_S N_a) ⟶ Γ(Y_a, (Y_a ⟶ X)⁻¹F)` is an isomorphism. -/
instance isIso_levelSections (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    IsIso (levelSections B S hS s U hU f a F) :=
  isIso_smallEtaleSectionsPullbackAb_app_of_isIso _ _ _ _ inferInstance F

end AlgebraicGeometry

end

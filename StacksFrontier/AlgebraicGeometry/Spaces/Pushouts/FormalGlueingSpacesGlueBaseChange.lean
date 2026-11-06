module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesHomSheafAffineBase

/-!
# Base change of glueing triples along a cartesian morphism of situations

Let `D'` be a formal glueing situation lying over `D` along `q : X' ⟶ X` through cartesian
squares on `Y`, `U` and `V`, compatibly with the restrictions of the two morphisms glued along
(the shape `AlgebraicGeometry.Space.FormalGlueingSituation.baseChangeAlong` produces). A glueing
triple `G = (G_U, G_Y, G_U|_V ≅ G_Y|_V)` for `D` base changes to the triple
`(G_U ×_U U', G_Y ×_Y Y', can)` for `D'`. This module builds it.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingBaseChange`: the base-changed triple.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.affineLegs_glueingBaseChange`: base change
  preserves affine legs.

## References

* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullback_presheaf_FormalGlueingSpacesGlueBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (Limits.functorCategoryHasLimitsOfShape :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).has_limit _

/-- A cartesian morphism of formal glueing situations: `D'` lies over `D` along `q` through
cartesian squares on `Y`, `U` and `V`, compatible with the restrictions of `f` and `f'`. -/
structure CartesianMap (D D' : FormalGlueingSituation B S hS) where
  /-- The map of ambient spaces. -/
  q : D'.X ⟶ D.X
  /-- The map of the spaces glued along. -/
  gY : D'.Y ⟶ D.Y
  /-- The map of the open parts. -/
  gU : D'.U.toFunctor ⟶ D.U.toFunctor
  /-- The map of the overlaps. -/
  gV : D'.V.toFunctor ⟶ D.V.toFunctor
  /-- `Y' = Y ×_X X'`. -/
  hYsq : IsPullback gY D'.f D.f q
  /-- `U' = U ×_X X'`. -/
  hUsq : IsPullback gU D'.U.ι D.U.ι q
  /-- `V' = V ×_Y Y'`. -/
  hVsq : IsPullback gV D'.V.ι D.V.ι gY
  /-- The restrictions of `f'` and `f` to the open parts are compatible. -/
  hW : D'.U.fromPreimage D'.f ≫ gU = gV ≫ D.U.fromPreimage D.f

/-- The base change of a situation along any morphism of its ambient space
(`AlgebraicGeometry.Space.FormalGlueingSituation.baseChangeAlong`) is a cartesian morphism of
situations. -/
noncomputable def CartesianMap.baseChangeAlong (D : FormalGlueingSituation B S hS)
    {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X') (g : X' ⟶ D.X) :
    CartesianMap D (D.baseChangeAlong hX' g) where
  q := g
  gY := pullback.fst D.f g
  gU := D.U.mapOfEqPreimage g (baseChangeAlong_U_eq D hX' g)
  gV := D.V.mapOfEqPreimage (pullback.fst D.f g) (baseChangeAlong_V_eq D hX' g)
  hYsq := IsPullback.of_hasPullback D.f g
  hUsq := Subfunctor.isPullback_mapOfEqPreimage D.U g (baseChangeAlong_U_eq D hX' g)
  hVsq := Subfunctor.isPullback_mapOfEqPreimage D.V (pullback.fst D.f g)
    (baseChangeAlong_V_eq D hX' g)
  hW := Subfunctor.mapOfEqPreimage_comm D.U (IsPullback.of_hasPullback D.f g)
    (baseChangeAlong_U_eq D hX' g) (baseChangeAlong_V_eq D hX' g)

variable {D D' : FormalGlueingSituation B S hS} (c : CartesianMap D D')

/-- The overlap square `V' = U' ×_U V` of a cartesian morphism of situations. -/
theorem CartesianMap.hWsq :
    IsPullback (D'.U.fromPreimage D'.f) c.gV c.gU (D.U.fromPreimage D.f) := by
  refine IsPullback.of_right ?_ c.hW c.hUsq.flip
  rw [Subfunctor.fromPreimage_ι, Subfunctor.fromPreimage_ι]
  exact c.hVsq.flip.paste_horiz c.hYsq.flip

variable (G : glueingData D)

/-- Base change of the overlap `A ×_Y V` along `V' ⟶ V` computes `(A ×_Y Y') ×_{Y'} V'`, when
`V' ⟶ Y'` lies over `V ⟶ Y`. -/
private theorem isPullback_lift_pullback_snd {C : Type*} [Category C] [HasPullbacks C]
    {A Y Y' V V' : C} {p : A ⟶ Y} {g : Y' ⟶ Y} {i : V ⟶ Y} {j : V' ⟶ Y'} {k : V' ⟶ V}
    (hk : j ≫ g = k ≫ i) {w} :
    IsPullback (pullback.lift (pullback.fst (pullback.snd p g) j ≫ pullback.fst p g)
      (pullback.snd (pullback.snd p g) j ≫ k) w) (pullback.snd (pullback.snd p g) j)
      (pullback.snd p i) k := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p i)
  rw [pullback.lift_fst, ← hk]
  exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)

/-- The overlap of the left leg of the base-changed triple, `(G_U ×_U U') ×_{U'} V'`, is the base
change along `V' ⟶ V` of the overlap `G_U ×_U V` of `G`. -/
theorem CartesianMap.isPullback_left :
    IsPullback
      (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ c.gV) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc, Category.assoc, c.hW]) :
        pullback (pullback.snd G.obj.left.hom c.gU) (D'.U.fromPreimage D'.f) ⟶
          pullback G.obj.left.hom (D.U.fromPreimage D.f))
      (pullback.snd _ _) (pullback.snd _ _) c.gV :=
  isPullback_lift_pullback_snd c.hW

/-- The overlap of the right leg of the base-changed triple, `(G_Y ×_Y Y') ×_{Y'} V'`, is the
base change along `V' ⟶ V` of the overlap `G_Y ×_Y V` of `G`. -/
theorem CartesianMap.isPullback_right :
    IsPullback
      (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ c.gV) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc, Category.assoc, c.hVsq.w]) :
        pullback (pullback.snd G.obj.right.hom c.gY) D'.V.ι ⟶
          pullback G.obj.right.hom D.V.ι)
      (pullback.snd _ _) (pullback.snd _ _) c.gV :=
  isPullback_lift_pullback_snd c.hVsq.w.symm

/-- The overlap of the left leg of the base-changed triple, read through the identification of
`G`, is also the base change of the overlap `G_Y ×_Y V`. -/
theorem CartesianMap.isPullback_left_comp :
    IsPullback
      (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ c.gV) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc, Category.assoc, c.hW]) ≫ G.obj.hom.left :
        pullback (pullback.snd G.obj.left.hom c.gU) (D'.U.fromPreimage D'.f) ⟶
          pullback G.obj.right.hom D.V.ι)
      (pullback.snd _ _) (pullback.snd _ _) c.gV := by
  have : IsIso G.obj.hom := G.property.1
  have : IsIso G.obj.hom.left := Functor.map_isIso (Over.forget _) G.obj.hom
  have hsq : IsPullback G.obj.hom.left (pullback.snd _ _) (pullback.snd _ _)
      (𝟙 D.V.toFunctor) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w G.obj.hom⟩
  have h := (c.isPullback_left G).paste_horiz hsq
  rwa [Category.comp_id] at h

/-- The identification of the overlaps of the base-changed triple: the base change along
`V' ⟶ V` of the identification of `G`. -/
noncomputable def CartesianMap.overlapIso :
    pullback (pullback.snd G.obj.left.hom c.gU) (D'.U.fromPreimage D'.f) ≅
      pullback (pullback.snd G.obj.right.hom c.gY) D'.V.ι :=
  IsPullback.isoIsPullback _ _ (c.isPullback_left_comp G) (c.isPullback_right G)

/-- The identification `overlapIso` commutes with the projections to `V'`. -/
theorem CartesianMap.overlapIso_hom_snd :
    (c.overlapIso G).hom ≫ pullback.snd _ _ = pullback.snd _ _ :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- **The base change of a glueing triple along a cartesian morphism of situations**,
`(G_U ×_U U', G_Y ×_Y Y', can)`. -/
noncomputable def glueingBaseChange : glueingData D' :=
  ⟨⟨(Over.pullback c.gU).obj G.obj.left, (Over.pullback c.gY).obj G.obj.right,
      Over.homMk (c.overlapIso G).hom (c.overlapIso_hom_snd G)⟩,
    ⟨by
      have : IsIso ((Over.forget _).map
          (Over.homMk (c.overlapIso G).hom (c.overlapIso_hom_snd G) :
            (Over.pullback (D'.U.fromPreimage D'.f)).obj ((Over.pullback c.gU).obj G.obj.left) ⟶
              (Over.pullback D'.V.ι).obj ((Over.pullback c.gY).obj G.obj.right))) :=
        (inferInstance : IsIso (c.overlapIso G).hom)
      exact isIso_of_reflects_iso _ (Over.forget _),
     isAlgebraicSpace_pullback B S hS _ _ G.property.2.1 (isOpenSubspace_U D').1
       (isOpenSubspace_U D).1,
     isAlgebraicSpace_pullback B S hS _ _ G.property.2.2 D'.algebraicSpace_Y
       D.algebraicSpace_Y⟩⟩

/-- Base change preserves affine legs. -/
theorem affineLegs_glueingBaseChange (hG : affineLegs D G) :
    affineLegs D' (glueingBaseChange c G) :=
  ⟨isAffineHom_of_isPullback (IsPullback.of_hasPullback _ _) hG.1,
    isAffineHom_of_isPullback (IsPullback.of_hasPullback _ _)
      (isAffineHom_of_isPullback (IsPullback.of_hasPullback _ _) hG.1),
    isAffineHom_of_isPullback (IsPullback.of_hasPullback _ _) hG.2.2⟩

end AlgebraicGeometry.Space.FormalGlueingSituation

end

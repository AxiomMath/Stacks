module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialSurjectivity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictionModulesAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.CategoryTheory.Adjunction.MateCompatibility
public import StacksFrontier.CategoryTheory.Sites.Localization.RestrictionSquareMate
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackTopos
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# Pullback of sheaves of modules commutes with restriction along a Guitart exact square

Let `f : X ⟶ Y` and `f' : X' ⟶ Y'` be morphisms of ringed sites given by `u : Y ⥤ X` and
`u' : Y' ⥤ X'`, let `jX : X' ⥤ X` and `jY : Y' ⥤ Y` be continuous and cocontinuous functors with
`𝒪_{X'} ≅ jX^{-1}𝒪_X` and `𝒪_{Y'} ≅ jY^{-1}𝒪_Y`, and let `w : u' ⋙ jX ⟶ jY ⋙ u` be a Guitart exact
`2`-square compatible with the structure maps of `f` and `f'`. Restriction of
sheaves of modules along `jX`, `jY` commutes with the direct images, and the Beck–Chevalley mate
`jY^*(G) ⟶ ...`, that is `f'^*(G|_{Y'}) ⟶ (f^*G)|_{X'}`, of that square is invertible.
Consequently the unit `G ⟶ f_*f^*G`, restricted to `Y'`, is invertible exactly when the unit of
`f'` at `G|_{Y'}` is.

This is the generic form of the slice case
`AlgebraicGeometry.RingedSite.Hom.isIso_localizedPullbackMate`, where `jX`, `jY` are the
localization functors and `w` is the identity.

## Main definitions

* `AlgebraicGeometry.RingedSite.restrictRestrictionSquarePullbackMate`: the ringed site
  `(C', J', j^{-1}𝒪)` of a continuous functor `j : C' ⥤ C`, and
  `restrictModulesAlongRestrictRestrictionSquarePullbackMate`,
  `restrictModulesAdjunctionRestrictionSquarePullbackMate`: restriction of sheaves of modules
  along `j`, left adjoint to the direct image with the unit and counit of sheaves of sets.
* `AlgebraicGeometry.RingedSite.Hom.restrictPushforwardSquareRestrictionSquarePullbackMate`:
  restriction to `Y'` of a direct image along `f` is the direct image along `f'` of the
  restriction to `X'`, through `w`.

## References

* [Stacks Project, Tag 0FN1](https://stacks.math.columbia.edu/tag/0FN1)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
  Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.RingedSite

variable (Z : RingedSite.{u, u, u}) {C' : Type u} [Category.{u} C'] (J' : GrothendieckTopology C')
  (j : C' ⥤ Z.C) [j.IsContinuous J' Z.J]

/-- The ringed site `(C', J', j^{-1}𝒪)` of a continuous functor `j : (C', J') ⥤ (Z.C, Z.J)`. -/
abbrev restrictRestrictionSquarePullbackMate : RingedSite.{u, u, u} where
  C := C'
  J := J'
  O := (j.sheafPushforwardContinuous CommRingCat.{u} J' Z.J).obj Z.O

/-- Restriction of sheaves of modules along a continuous functor `j`. -/
noncomputable abbrev restrictModulesAlongRestrictRestrictionSquarePullbackMate :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) ⥤
      SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J')
        (Z.restrictRestrictionSquarePullbackMate J' j).O)) :=
  restrictionModules J' Z.J j ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))

/-- Restriction of sheaves of modules along a continuous and cocontinuous functor is left
adjoint to the direct image, with the unit and counit of sheaves of sets. -/
noncomputable abbrev restrictModulesAdjunctionRestrictionSquarePullbackMate
    [j.IsCocontinuous J' Z.J] :=
  restrictionModulesAdjunction J' Z.J j (j.sheafAdjunctionCocontinuous (Type u) J' Z.J)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  {CX' : Type u} [Category.{u} CX'] (JX' : GrothendieckTopology CX')
  {CY' : Type u} [Category.{u} CY'] (JY' : GrothendieckTopology CY')
  (jX : CX' ⥤ X.C) (jY : CY' ⥤ Y.C) [jX.IsContinuous JX' X.J] [jY.IsContinuous JY' Y.J]
  (f' : RingedSite.Hom (X.restrictRestrictionSquarePullbackMate JX' jX)
    (Y.restrictRestrictionSquarePullbackMate JY' jY)) (w : TwoSquare f'.u jY jX f.u)
  (hw : ∀ V : CY'ᵒᵖ, f.fsharp.hom.app (jY.op.obj V) ≫ X.O.obj.map (w.app V.unop).op =
    f'.fsharp.hom.app V)

omit [jX.IsContinuous JX' X.J] in
/-- The functor of a morphism of ringed sites between restricted ringed sites is continuous for
the given topologies. -/
instance Hom.isContinuous_restrict_restrictionSquarePullbackMate : f'.u.IsContinuous JY' JX' :=
  f'.isContinuous

/-- The underlying sheaf of sets of `(f_*M)|_{Y'}`. -/
noncomputable abbrev Hom.restrictPushforwardSheafRestrictionSquarePullbackMate
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    Sheaf JY' (Type u) :=
  (jY.sheafPushforwardContinuous (Type u) JY' Y.J).obj
    (f.ringedToposHom.toToposHom.pushforward.obj
      (Sheaf.moduleSheaf.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M))

/-- The underlying sheaf of sets of `f'_*(M|_{X'})`. -/
noncomputable abbrev Hom.pushforwardRestrictSheafRestrictionSquarePullbackMate
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    Sheaf JY' (Type u) :=
  f'.ringedToposHom.toToposHom.pushforward.obj
    ((jX.sheafPushforwardContinuous (Type u) JX' X.J).obj
      (Sheaf.moduleSheaf.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M))

/-- The comparison of underlying sheaves of sets `(f_*M)|_{Y'} ⟶ f'_*(M|_{X'})`: restriction
along the components of `w`. -/
noncomputable abbrev Hom.restrictPushforwardSheafMapRestrictionSquarePullbackMate
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    f.restrictPushforwardSheafRestrictionSquarePullbackMate JY' jY M ⟶
      f'.pushforwardRestrictSheafRestrictionSquarePullbackMate JX' JY' jX jY M :=
  (Stacks.Sites.CocontinuousExchange.restrictionTwoSquareRestrictionSquareMate (Type u) JY' JX' Y.J
    X.J w).app
    (Sheaf.moduleSheaf.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M)

/-- The comparison of underlying sheaves of sets, on a section: restriction along the
component of `w`. -/
theorem Hom.sectionsFunctor_map_restrictPushforwardSheafMap_restrictionSquarePullbackMate
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) (V : CY'ᵒᵖ)
    (x : M.val.obj (f.u.op.obj (jY.op.obj V))) :
    (Sheaf.sectionsFunctor JY' V).map
      (f.restrictPushforwardSheafMapRestrictionSquarePullbackMate JX' JY' jX jY f' w M) x =
      M.val.map (w.app V.unop).op x :=
  rfl

include hw in
/-- **Stacks 03CF (d) along a square.** The restriction to `Y'` of a direct image along `f` maps
to the direct image along `f'` of the restriction to `X'`, through the components of `w`; the
map is linear because the structure maps of `f` and `f'` agree through `w`. -/
noncomputable def Hom.restrictPushforwardSquareAppRestrictionSquarePullbackMate
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Y.restrictModulesAlongRestrictRestrictionSquarePullbackMate JY' jY).obj
      ((RingedToposHom.pushforwardModules f.ringedToposHom).obj M) ⟶
      (RingedToposHom.pushforwardModules f'.ringedToposHom).obj
        ((X.restrictModulesAlongRestrictRestrictionSquarePullbackMate JX' jX).obj M) :=
  ofSheafHom.{u, u, u}
    (f.restrictPushforwardSheafMapRestrictionSquarePullbackMate JX' JY' jX jY f' w M)
    (fun V x y => by
      have h1 := f.ringedToposHom.pushforwardModules_add M (Opposite.op (jY.obj V.unop)) x y
      have h1' := Sheaf.app_moduleAddObj ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M
        (f.sectionsComparison (Opposite.op (jY.obj V.unop))) x y
      have h2 := f'.ringedToposHom.pushforwardModules_add
        ((X.restrictModulesAlongRestrictRestrictionSquarePullbackMate JX' jX).obj M) V
        ((Sheaf.sectionsFunctor JY' V).map
          (f.restrictPushforwardSheafMapRestrictionSquarePullbackMate JX' JY' jX jY f' w M) x)
        ((Sheaf.sectionsFunctor JY' V).map
          (f.restrictPushforwardSheafMapRestrictionSquarePullbackMate JX' JY' jX jY f' w M) y)
      have h2' := Sheaf.app_moduleAddObj _
        ((X.restrictModulesAlongRestrictRestrictionSquarePullbackMate JX' jX).obj M)
        (f'.sectionsComparison V)
        ((Sheaf.sectionsFunctor JY' V).map
          (f.restrictPushforwardSheafMapRestrictionSquarePullbackMate JX' JY' jX jY f' w M) x)
        ((Sheaf.sectionsFunctor JY' V).map
          (f.restrictPushforwardSheafMapRestrictionSquarePullbackMate JX' JY' jX jY f' w M) y)
      refine (congrArg (M.val.map (w.app V.unop).op) (h1.trans h1')).trans ?_
      exact (LinearMap.map_add (M.val.map (w.app V.unop).op).hom
        (x : M.val.obj (Opposite.op (f.u.obj (jY.obj V.unop))))
        (y : M.val.obj (Opposite.op (f.u.obj (jY.obj V.unop))))).trans (h2.trans h2').symm)
    (fun V r x => by
      have e1 := (f.ringedToposHom.pushforwardModules_smul M
        (Opposite.op (jY.obj V.unop)) r x).trans
        (Sheaf.app_moduleSMulObj ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M
          (f.sectionsComparison (Opposite.op (jY.obj V.unop))) _ x)
      have e2 :=
        (f'.ringedToposHom.pushforwardModules_smul
        ((X.restrictModulesAlongRestrictRestrictionSquarePullbackMate JX' jX).obj M) V r
        ((Sheaf.sectionsFunctor JY' V).map
          (f.restrictPushforwardSheafMapRestrictionSquarePullbackMate JX' JY' jX jY f' w M)
            x)).trans
        (Sheaf.app_moduleSMulObj _
          ((X.restrictModulesAlongRestrictRestrictionSquarePullbackMate JX' jX).obj M)
            (f'.sectionsComparison V) _
          ((Sheaf.sectionsFunctor JY' V).map
            (f.restrictPushforwardSheafMapRestrictionSquarePullbackMate JX' JY' jX jY f' w M) x))
      refine (congrArg (M.val.map (w.app V.unop).op) e1).trans ?_
      refine (M.val.map_smul (w.app V.unop).op _ x).trans ?_
      refine Eq.trans ?_ e2.symm
      exact congrArg (· • M.val.map (w.app V.unop).op x)
        (ConcreteCategory.congr_hom (hw V) r))

include hw in
/-- **Stacks 03CF (d) along a square**, as a `2`-square of functors: restricting a direct image
along `f` to `Y'` maps to the direct image along `f'` of the restriction to `X'`. -/
noncomputable def Hom.restrictPushforwardSquareRestrictionSquarePullbackMate :
    TwoSquare (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} f.ringedToposHom)
      (X.restrictModulesAlongRestrictRestrictionSquarePullbackMate JX' jX)
        (Y.restrictModulesAlongRestrictRestrictionSquarePullbackMate JY' jY)
      (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} f'.ringedToposHom) :=
  TwoSquare.mk _ _ _ _
    { app := fun M => f.restrictPushforwardSquareAppRestrictionSquarePullbackMate JX' JY' jX jY f'
        w hw M
      naturality := fun M M' φ => by
        refine hom_ext_moduleSheafFunctor (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := JY')
          (Y.restrictRestrictionSquarePullbackMate JY' jY).O)) ?_
        exact Sheaf.hom_ext_sections (J := JY') fun V x ↦
          (ConcreteCategory.congr_hom (φ.val.naturality (w.app V.unop).op) x).symm }

/-- The underlying morphism of sheaves of sets of the square is restriction along `w`. -/
theorem Hom.moduleSheafFunctor_map_restrictPushforwardSquare_app_restrictionSquarePullbackMate
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Sheaf.moduleSheafFunctor
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := JY')
        (Y.restrictRestrictionSquarePullbackMate JY' jY).O))).map
        ((f.restrictPushforwardSquareRestrictionSquarePullbackMate JX' JY' jX jY f' w hw).app M) =
      f.restrictPushforwardSheafMapRestrictionSquarePullbackMate JX' JY' jX jY f' w M :=
  moduleSheafFunctor_map_ofSheafHom.{u, u, u} _ _ _

/-- The square of modules, read over the inverse-image ring, is restriction along `w` on
underlying sheaves of sets. -/
theorem Hom.moduleSheaf_restrictScalars_restrictPushforwardSquare_heq_restrictionSquarePullbackMate
    [jY.IsCocontinuous JY' Y.J]
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Sheaf.moduleSheafFunctor.{u, u, u} (inverseImageRingSheaf.{u, u, u, u, u, u}
        (restrictionMorphism.{u, u, u, u, u} JY' Y.J jY
          (jY.sheafAdjunctionCocontinuous (Type u) JY' Y.J))
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).map
      ((SheafOfModules.restrictScalars (restrictionRingIso.{u} JY' Y.J jY
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).hom).map
          ((f.restrictPushforwardSquareRestrictionSquarePullbackMate JX' JY' jX jY f' w hw).app
            M)) ≍
      f.restrictPushforwardSheafMapRestrictionSquarePullbackMate JX' JY' jX jY f' w M :=
  (conj_eqToHom_iff_heq _ _ rfl rfl).mp (Sheaf.hom_ext_sections fun _ _ ↦ rfl)

namespace Hom

/-- The direct image along `f'`, read over the inverse-image rings, is the direct image of
sheaves of sets on underlying morphisms. -/
theorem
    moduleSheafFunctor_map_restrictScalars_map_pushforwardModules_map_heq_cocontinuousLocalizedMate
    [jX.IsCocontinuous JX' X.J] [jY.IsCocontinuous JY' Y.J]
    {N N' : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := JX')
        (X.restrictRestrictionSquarePullbackMate JX' jX).O))} (c : N ⟶ N') :
    (Sheaf.moduleSheafFunctor.{u, u, u} (inverseImageRingSheaf.{u, u, u, u, u, u}
        (restrictionMorphism.{u, u, u, u, u} JY' Y.J jY
          (jY.sheafAdjunctionCocontinuous (Type u) JY' Y.J))
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).map
      ((SheafOfModules.restrictScalars (restrictionRingIso.{u} JY' Y.J jY
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).hom).map
          ((RingedToposHom.pushforwardModules.{u, u, u, u, u, u} f'.ringedToposHom).map c)) ≍
      f'.ringedToposHom.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor.{u, u, u} (inverseImageRingSheaf.{u, u, u, u, u, u}
          (restrictionMorphism.{u, u, u, u, u} JX' X.J jX
            (jX.sheafAdjunctionCocontinuous (Type u) JX' X.J))
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))).map
          ((SheafOfModules.restrictScalars (restrictionRingIso.{u} JX' X.J jX
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).hom).map c)) :=
  (conj_eqToHom_iff_heq _ _ rfl rfl).mp (Sheaf.hom_ext_sections fun _ _ ↦ rfl)

end Hom

section Mate

variable [jX.IsCocontinuous JX' X.J] [jY.IsCocontinuous JY' Y.J]

/-- The mate of the square of sheaves of modules under the two restriction adjunctions: a
comparison `jX_* ⋙ f_* ⟶ f'_* ⋙ jY_*` of direct images. -/
noncomputable def Hom.restrictPushforwardSquareMateRestrictionSquarePullbackMate :=
  mateEquiv (X.restrictModulesAdjunctionRestrictionSquarePullbackMate JX' jX)
    (Y.restrictModulesAdjunctionRestrictionSquarePullbackMate JY' jY)
    (f.restrictPushforwardSquareRestrictionSquarePullbackMate JX' JY' jX jY f' w hw)

/-- The source of the iterated mate, on underlying sheaves of sets. -/
theorem Hom.moduleSheaf_restrictPushforwardSquareMate_source_restrictionSquarePullbackMate
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := JX')
        (X.restrictRestrictionSquarePullbackMate JX' jX).O))) :
    (Sheaf.moduleSheafFunctor.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).obj
        (((SheafOfModules.restrictScalars (restrictionRingIso.{u} JX' X.J jX
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).hom ⋙
          directImageModules (restrictionMorphism JX' X.J jX
            (jX.sheafAdjunctionCocontinuous (Type u) JX' X.J))
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) ⋙
          RingedToposHom.pushforwardModules.{u, u, u, u, u, u} f.ringedToposHom).obj N) =
      (f.u.sheafPushforwardContinuous (Type u) Y.J X.J).obj
        ((jX.sheafPushforwardCocontinuous (Type u) JX' X.J).obj
          ((Sheaf.moduleSheafFunctor.{u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := JX')
              (X.restrictRestrictionSquarePullbackMate JX' jX).O))).obj N)) :=
  rfl

omit [jY.IsCocontinuous JY' Y.J] in
/-- The direct image along `jX` of a sheaf of modules, on underlying sheaves of sets. -/
theorem moduleSheaf_restrictModulesAdjunction_rightAdjoint_obj_restrictionSquarePullbackMate
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := JX')
        (X.restrictRestrictionSquarePullbackMate JX' jX).O))) :
    Sheaf.moduleSheaf.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))
        ((SheafOfModules.restrictScalars (restrictionRingIso.{u} JX' X.J jX
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).hom ⋙
          directImageModules (restrictionMorphism JX' X.J jX
            (jX.sheafAdjunctionCocontinuous (Type u) JX' X.J))
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).obj N) =
      (jX.sheafPushforwardCocontinuous (Type u) JX' X.J).obj
        ((Sheaf.moduleSheafFunctor.{u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := JX')
            (X.restrictRestrictionSquarePullbackMate JX' jX).O))).obj N) :=
  rfl

omit [jX.IsCocontinuous JX' X.J] [jY.IsCocontinuous JY' Y.J] in
/-- The target of the iterated mate, on underlying sheaves of sets, before the direct image along
`jY`. -/
theorem Hom.moduleSheaf_restrictPushforwardSquareMate_target_restrictionSquarePullbackMate
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := JX')
        (X.restrictRestrictionSquarePullbackMate JX' jX).O))) :
    (Sheaf.moduleSheafFunctor.{u, u, u} (pullbackRingSheaf.{u, u, u, u, u, u} JY'
        (jY.sheafPushforwardContinuous (Type u) JY' Y.J)
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).obj
        ((SheafOfModules.restrictScalars (restrictionRingIso.{u} JY' Y.J jY
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).hom).obj
          ((RingedToposHom.pushforwardModules.{u, u, u, u, u, u} f'.ringedToposHom).obj N)) =
      (f'.u.sheafPushforwardContinuous (Type u) JY' JX').obj
        ((Sheaf.moduleSheafFunctor.{u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := JX')
            (X.restrictRestrictionSquarePullbackMate JX' jX).O))).obj N) :=
  rfl

open Hom in
/-- The direct image along `f'` of the counit of restriction to `X'` is, on underlying sheaves
of sets, the direct image of the counit of sheaves of sets. -/
theorem Hom.moduleSheaf_restrictScalars_pushforwardModules_map_counit_heq_cocontinuousLocalizedMate
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := JX')
        (X.restrictRestrictionSquarePullbackMate JX' jX).O))) :
    (Sheaf.moduleSheafFunctor.{u, u, u} (inverseImageRingSheaf.{u, u, u, u, u, u}
        (restrictionMorphism.{u, u, u, u, u} JY' Y.J jY
          (jY.sheafAdjunctionCocontinuous (Type u) JY' Y.J))
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).map
      ((SheafOfModules.restrictScalars (restrictionRingIso.{u} JY' Y.J jY
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).hom).map
          ((RingedToposHom.pushforwardModules.{u, u, u, u, u, u} f'.ringedToposHom).map
            ((X.restrictModulesAdjunctionRestrictionSquarePullbackMate JX' jX).counit.app N))) ≍
      (f'.u.sheafPushforwardContinuous (Type u) JY' JX').map
        ((jX.sheafAdjunctionCocontinuous (Type u) JX' X.J).counit.app
          ((Sheaf.moduleSheafFunctor.{u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := JX')
              (X.restrictRestrictionSquarePullbackMate JX' jX).O))).obj N)) := by
  refine
    (moduleSheafFunctor_map_restrictScalars_map_pushforwardModules_map_heq_cocontinuousLocalizedMate
      JX' JY' jX jY f' _).trans ?_
  refine (heq_of_eq (f'.ringedToposHom.toToposHom.pushforward.congr_map
    (moduleSheafFunctor_map_restrictionModulesAdjunction_counit_app JX' X.J jX
      (jX.sheafAdjunctionCocontinuous (Type u) JX' X.J)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) N))).trans ?_
  heq_congr

/-- **The iterated mate of the square of sheaves of modules is that of sheaves of sets.** -/
theorem
    Hom.moduleSheafFunctor_map_mateEquiv_restrictPushforwardSquare_app_restrictionSquarePullbackMate
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := JX')
        (X.restrictRestrictionSquarePullbackMate JX' jX).O))) :
    (Sheaf.moduleSheafFunctor.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
        ((f.restrictPushforwardSquareMateRestrictionSquarePullbackMate JX' JY' jX jY f' w hw).app
          N) =
      eqToHom (f.moduleSheaf_restrictPushforwardSquareMate_source_restrictionSquarePullbackMate JX'
          jX N) ≫
        (mateEquiv (jX.sheafAdjunctionCocontinuous (Type u) JX' X.J)
          (jY.sheafAdjunctionCocontinuous (Type u) JY' Y.J)
          (Stacks.Sites.CocontinuousExchange.restrictionTwoSquareRestrictionSquareMate (Type u) JY'
            JX' Y.J X.J w)).app
            ((Sheaf.moduleSheafFunctor.{u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := JX')
                (X.restrictRestrictionSquarePullbackMate JX' jX).O))).obj N) ≫
        eqToHom (congrArg (jY.sheafPushforwardCocontinuous (Type u) JY' Y.J).obj
          (Hom.moduleSheaf_restrictPushforwardSquareMate_target_restrictionSquarePullbackMate JX'
            JY' jX jY f' N).symm) := by
  have h1 := Stacks.CategoryTheory.mateEquiv_app_eq_homEquiv
    (X.restrictModulesAdjunctionRestrictionSquarePullbackMate JX' jX)
      (Y.restrictModulesAdjunctionRestrictionSquarePullbackMate JY' jY)
    (f.restrictPushforwardSquareRestrictionSquarePullbackMate JX' JY' jX jY f' w hw) N
  rw [Adjunction.homEquiv_unit] at h1
  have h2 := (Sheaf.moduleSheafFunctor.{u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).congr_map h1
  rw [Functor.map_comp, moduleSheafFunctor_map_restrictionModulesAdjunction_unit_app,
    Functor.comp_map (SheafOfModules.restrictScalars _),
    moduleSheafFunctor_map_restrictionModulesRightAdjoint_map] at h2
  have hs := (Stacks.CategoryTheory.mateEquiv_app_eq_homEquiv
    (jX.sheafAdjunctionCocontinuous (Type u) JX' X.J)
    (jY.sheafAdjunctionCocontinuous (Type u) JY' Y.J)
    (Stacks.Sites.CocontinuousExchange.restrictionTwoSquareRestrictionSquareMate (Type u) JY' JX'
      Y.J X.J w)
    ((Sheaf.moduleSheafFunctor.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := JX')
        (X.restrictRestrictionSquarePullbackMate JX' jX).O))).obj N)).trans
    ((jY.sheafAdjunctionCocontinuous (Type u) JY' Y.J).homEquiv_unit _ _ _)
  rw [hs]
  refine h2.trans (Stacks.CategoryTheory.unit_comp_map_eq_eqToHom
    (jY.sheafAdjunctionCocontinuous (Type u) JY' Y.J)
    (f.moduleSheaf_restrictPushforwardSquareMate_source_restrictionSquarePullbackMate JX' jX N)
    (Hom.moduleSheaf_restrictPushforwardSquareMate_target_restrictionSquarePullbackMate JX' JY' jX
      jY f' N) _ _ ?_)
  rw [Functor.map_comp, Functor.map_comp]
  refine heq_comp ?e1 ?e2 ?e3
    ((f.moduleSheaf_restrictScalars_restrictPushforwardSquare_heq_restrictionSquarePullbackMate
      JX' JY' jX jY f' w hw _).trans (congr_arg_heq (fun A ↦
        (Stacks.Sites.CocontinuousExchange.restrictionTwoSquareRestrictionSquareMate (Type u)
          JY' JX' Y.J X.J w).app A)
        (moduleSheaf_restrictModulesAdjunction_rightAdjoint_obj_restrictionSquarePullbackMate JX'
          jX N)))
    (Hom.moduleSheaf_restrictScalars_pushforwardModules_map_counit_heq_cocontinuousLocalizedMate
      JX' JY' jX jY f' N)
  all_goals exact eq_of_heq (by heq_congr)

end Mate

section Invertibility

variable [jX.IsCocontinuous JX' X.J] [jY.IsCocontinuous JY' Y.J] [w.GuitartExact]

/-- The underlying morphism of sheaves of sets of the iterated mate is invertible: it is the
exchange of Stacks 0FN1 for the Guitart exact square `w`. -/
theorem
    Hom.isIso_moduleSheafFunctor_map_restrictPushforwardSquareMate_app_restrictionSquarePullbackMate
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := JX')
        (X.restrictRestrictionSquarePullbackMate JX' jX).O))) :
    IsIso ((Sheaf.moduleSheafFunctor.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
      ((f.restrictPushforwardSquareMateRestrictionSquarePullbackMate JX' JY' jX jY f' w hw).app
        N)) := by
  have hs :=
    Stacks.Sites.CocontinuousExchange.isIso_mateEquiv_restrictionTwoSquare_restrictionSquareMate
      (Type u) JY' JX' Y.J X.J w
  rw [f.moduleSheafFunctor_map_mateEquiv_restrictPushforwardSquare_app_restrictionSquarePullbackMate
    JX' JY' jX jY f' w hw N]
  have hm : IsIso ((mateEquiv (jX.sheafAdjunctionCocontinuous (Type u) JX' X.J)
      (jY.sheafAdjunctionCocontinuous (Type u) JY' Y.J)
      (Stacks.Sites.CocontinuousExchange.restrictionTwoSquareRestrictionSquareMate (Type u)
        JY' JX' Y.J X.J w)).app
        ((Sheaf.moduleSheafFunctor.{u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := JX')
            (X.restrictRestrictionSquarePullbackMate JX' jX).O))).obj N)) :=
    NatIso.isIso_app_of_isIso _ _
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hm (Iso.isIso_hom (eqToIso
    (congrArg (jY.sheafPushforwardCocontinuous (Type u) JY' Y.J).obj
      (Hom.moduleSheaf_restrictPushforwardSquareMate_target_restrictionSquarePullbackMate JX' JY'
        jX jY f' N).symm))))

/-- **The iterated mate of the square of sheaves of modules is invertible.** -/
theorem Hom.isIso_restrictPushforwardSquareMate_restrictionSquarePullbackMate :
    IsIso (f.restrictPushforwardSquareMateRestrictionSquarePullbackMate JX' JY' jX jY f' w
      hw) := by
  have hN : ∀ N, IsIso ((f.restrictPushforwardSquareMateRestrictionSquarePullbackMate JX' JY' jX jY
      f' w hw).app N) :=
    fun N => Stacks.Sheaves.PushforwardEssentialImage.isIso_of_isIso_moduleSheafFunctor_map
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))
        ((f.restrictPushforwardSquareMateRestrictionSquarePullbackMate JX' JY' jX jY f' w hw).app
          N) <|
      f.isIso_moduleSheafFunctor_map_restrictPushforwardSquareMate_app_restrictionSquarePullbackMate
        JX' JY' jX jY f' w hw N
  exact NatIso.isIso_of_isIso_app _

variable [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify JX' AddCommGrpCat.{u}] [JX'.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The Beck–Chevalley comparison along the square** `f'^*(G|_{Y'}) ⟶ (f^*G)|_{X'}` of sheaves
of modules: the mate of `restrictPushforwardSquareRestrictionSquarePullbackMate` under the
adjunctions `f^* ⊣ f_*` and `f'^* ⊣ f'_*`. -/
noncomputable def Hom.restrictPullbackMateRestrictionSquarePullbackMate :
    TwoSquare (Y.restrictModulesAlongRestrictRestrictionSquarePullbackMate JY' jY)
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u, u, u}
        f.ringedToposHom.toModulesHom)
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u, u, u}
        f'.ringedToposHom.toModulesHom)
      (X.restrictModulesAlongRestrictRestrictionSquarePullbackMate JX' jX) :=
  (mateEquiv (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} f.ringedToposHom)
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} f'.ringedToposHom)).symm
      (f.restrictPushforwardSquareRestrictionSquarePullbackMate JX' JY' jX jY f' w hw)

/-- **Pullback of sheaves of modules commutes with restriction along a Guitart exact square**:
the comparison `f'^*(G|_{Y'}) ⟶ (f^*G)|_{X'}` is an isomorphism, being conjugate to the iterated
mate of the square of direct images. -/
theorem Hom.isIso_restrictPullbackMate_restrictionSquarePullbackMate :
    IsIso (f.restrictPullbackMateRestrictionSquarePullbackMate JX' JY' jX jY f' w hw) := by
  have h := iterated_mateEquiv_conjugateEquiv
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} f.ringedToposHom)
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} f'.ringedToposHom)
    (Y.restrictModulesAdjunctionRestrictionSquarePullbackMate JY' jY)
      (X.restrictModulesAdjunctionRestrictionSquarePullbackMate JX' jX)
    (f.restrictPullbackMateRestrictionSquarePullbackMate JX' JY' jX jY f' w hw)
  have e : mateEquiv
      (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} f.ringedToposHom)
      (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} f'.ringedToposHom)
      (f.restrictPullbackMateRestrictionSquarePullbackMate JX' JY' jX jY f' w hw) =
        f.restrictPushforwardSquareRestrictionSquarePullbackMate JX' JY' jX jY f' w hw :=
    Equiv.apply_symm_apply _ _
  have h' :
    (f.restrictPushforwardSquareMateRestrictionSquarePullbackMate JX' JY' jX jY f' w hw) =
      conjugateEquiv
        ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} f.ringedToposHom).comp
          (X.restrictModulesAdjunctionRestrictionSquarePullbackMate JX' jX))
        ((Y.restrictModulesAdjunctionRestrictionSquarePullbackMate JY' jY).comp
          (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} f'.ringedToposHom))
        (f.restrictPullbackMateRestrictionSquarePullbackMate JX' JY' jX jY f' w hw) :=
    (congrArg (mateEquiv (X.restrictModulesAdjunctionRestrictionSquarePullbackMate JX' jX)
      (Y.restrictModulesAdjunctionRestrictionSquarePullbackMate JY' jY)) e).symm.trans h
  have hi :=
    f.isIso_restrictPushforwardSquareMate_restrictionSquarePullbackMate JX' JY' jX jY f' w hw
  rw [h'] at hi
  exact conjugateEquiv_of_iso
    ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} f.ringedToposHom).comp
      (X.restrictModulesAdjunctionRestrictionSquarePullbackMate JX' jX))
    ((Y.restrictModulesAdjunctionRestrictionSquarePullbackMate JY' jY).comp
      (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} f'.ringedToposHom))
    (f.restrictPullbackMateRestrictionSquarePullbackMate JX' JY' jX jY f' w hw)

omit [jX.IsCocontinuous JX' X.J] [jY.IsCocontinuous JY' Y.J] [w.GuitartExact] in
/-- **The restricted unit factors through the unit of `f'`**: restricting the unit
`G ⟶ f_*f^*G` to `Y'` and comparing `(f_*f^*G)|_{Y'}` with `f'_*((f^*G)|_{X'})` is the unit
`G|_{Y'} ⟶ f'_*f'^*(G|_{Y'})` followed by the direct image of the Beck–Chevalley comparison. -/
theorem Hom.restrictModules_map_unit_comp_restrictionSquarePullbackMate
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :
    (Y.restrictModulesAlongRestrictRestrictionSquarePullbackMate JY' jY).map
        ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
          f.ringedToposHom).unit.app G) ≫
      (f.restrictPushforwardSquareRestrictionSquarePullbackMate JX' JY' jX jY f' w hw).app _ =
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
        f'.ringedToposHom).unit.app
          ((Y.restrictModulesAlongRestrictRestrictionSquarePullbackMate JY' jY).obj G) ≫
      (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} f'.ringedToposHom).map
        ((f.restrictPullbackMateRestrictionSquarePullbackMate JX' JY' jX jY f' w hw).app G) :=
  unit_mateEquiv_symm _ _
    (f.restrictPushforwardSquareRestrictionSquarePullbackMate JX' JY' jX jY f' w hw) G

omit [jX.IsCocontinuous JX' X.J] [jY.IsCocontinuous JY' Y.J] [w.GuitartExact]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify JX' AddCommGrpCat.{u}] [JX'.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The square of direct images is invertible when `w` is. -/
theorem Hom.isIso_restrictPushforwardSquare_app_restrictionSquarePullbackMate [IsIso w]
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    IsIso
      ((f.restrictPushforwardSquareRestrictionSquarePullbackMate JX' JY' jX jY f' w hw).app M) := by
  refine Stacks.Sheaves.PushforwardEssentialImage.isIso_of_isIso_moduleSheafFunctor_map
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := JY')
      (Y.restrictRestrictionSquarePullbackMate JY' jY).O)) _ ?_
  rw [f.moduleSheafFunctor_map_restrictPushforwardSquare_app_restrictionSquarePullbackMate JX' JY'
    jX jY f' w hw M]
  have := Functor.isContinuous_comp f'.u jX JY' JX' X.J
  have := Functor.isContinuous_comp jY f.u JY' Y.J X.J
  exact inferInstanceAs (IsIso ((Functor.sheafPushforwardContinuousIso (asIso w) (Type u)
    JY' X.J).inv.app
      (Sheaf.moduleSheaf.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M)))

include hw in
/-- **The restricted unit is invertible if and only if the unit of `f'` is**, for a Guitart exact
invertible square `w`. -/
theorem Hom.isIso_restrictModules_map_unit_iff_restrictionSquarePullbackMate [IsIso w]
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :
    IsIso ((Y.restrictModulesAlongRestrictRestrictionSquarePullbackMate JY' jY).map
        ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
          f.ringedToposHom).unit.app G)) ↔
      IsIso ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
        f'.ringedToposHom).unit.app
          ((Y.restrictModulesAlongRestrictRestrictionSquarePullbackMate JY' jY).obj G)) := by
  have := f.isIso_restrictPullbackMate_restrictionSquarePullbackMate JX' JY' jX jY f' w hw
  have : IsIso
      ((f.restrictPullbackMateRestrictionSquarePullbackMate JX' JY' jX jY f' w hw).app G) :=
    inferInstanceAs (IsIso
      ((f.restrictPullbackMateRestrictionSquarePullbackMate JX' JY' jX jY f' w hw).app G))
  have := f.isIso_restrictPushforwardSquare_app_restrictionSquarePullbackMate JX' JY' jX jY f' w hw
    ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u, u, u}
      f.ringedToposHom.toModulesHom).obj G)
  rw [← isIso_comp_right_iff _
    ((f.restrictPushforwardSquareRestrictionSquarePullbackMate JX' JY' jX jY f' w hw).app _),
    f.restrictModules_map_unit_comp_restrictionSquarePullbackMate JX' JY' jX jY f' w hw G,
    isIso_comp_right_iff]

end Invertibility

end AlgebraicGeometry.RingedSite

end

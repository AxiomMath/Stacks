module

public import StacksFrontier.CategoryTheory.Adjunction.MateCompatibility
public import StacksFrontier.CategoryTheory.IsIsoOfEqIsoHom
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.CocontinuousMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizedPullbackMate
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The base change map of sheaves of modules for a localization

Let `F : (Sh(X), O_X) ⟶ (Sh(Y), O_Y)` and `F' : (Sh(X/V), O_X|_V) ⟶ (Sh(Y/W), O_Y|_W)` be
morphisms of ringed topoi and `e : F_* ⋙ j_W^{-1} ⟶ j_V^{-1} ⋙ F'_*` a transformation of sheaves of
sets carrying the structure map of `F`, restricted to `Y/W`, to that of `F'`. Then `e` is, at
the underlying sheaf of every sheaf of `O_X`-modules `M`, a map of sheaves of `O_Y|_W`-modules
`(F_*M)|_W ⟶ F'_*(M|_V)`. This is the case of the localization `F'` at `V` of a morphism given by
a cocontinuous functor, with `e` the base change map of Stacks 03EG.

## Main definitions

* `AlgebraicGeometry.RingedSite.baseChangeModulesAppCocontinuousLocalizedMate`: the base change map
  of sheaves of modules `(F_*M)|_W ⟶ F'_*(M|_V)` induced by a base change map of sheaves of sets
  compatible with the structure maps.
* `AlgebraicGeometry.RingedSite.baseChangeModulesCocontinuousLocalizedMate`: these maps as a
  base change square of sheaves of modules.
* `AlgebraicGeometry.RingedSite.baseChangePullbackMateCocontinuousLocalizedMate`: its mate
  `F'^*(G|_W) ⟶ (F^*G)|_V` under the adjunctions `F^* ⊣ F_*` and `F'^* ⊣ F'_*`.

## Main results

* `AlgebraicGeometry.RingedSite.moduleAddObj_overRestrictionModules_cocontinuousLocalizedMate` and
  `AlgebraicGeometry.RingedSite.moduleSMulObj_overRestrictionModules_cocontinuousLocalizedMate`:
  the module operations of a restriction to a slice.
* `AlgebraicGeometry.RingedSite.isIso_baseChangePullbackMate_cocontinuousLocalizedMate`: the mate
  `F'^*(G|_W) ⟶ (F^*G)|_V` is invertible when the mate of `e` under the localization adjunctions
  of sheaves of sets is.

## References

* [Stacks Project, Tag 03EG](https://stacks.math.columbia.edu/tag/03EG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
  Stacks.Sheaves.ToposPushforward

universe u

/-- Images under a functor of heterogeneously equal morphisms between equal objects are
heterogeneously equal. -/
theorem CategoryTheory.Functor.map_heq_of_heq_cocontinuousLocalizedMate
    {C D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D) {a b a' b' : C} (ha : a = a') (hb : b = b') {f : a ⟶ b} {g : a' ⟶ b'}
    (h : f ≍ g) : G.map f ≍ G.map g := by
  subst ha hb
  rw [eq_of_heq h]

namespace AlgebraicGeometry.RingedSite

section OverOperations

variable (Z : RingedSite.{u, u, u}) (W : Z.C)
  (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)))
  (P : Sheaf (Z.J.over W) (Type u) ⥤ Type u) [PreservesFiniteProducts P]

/-- The addition of a module transported along `j_W^{-1} ⋙ P` is the addition of its restriction
to the slice transported along `P`. -/
theorem moduleAddObj_overRestrictionModules_cocontinuousLocalizedMate
    (a b : P.obj (Sheaf.moduleSheaf.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Z.J.over W)) (Z.O.over W)))
      ((Z.overRestrictionModules W).obj M))) :
    Sheaf.moduleAddObj ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) M
        ((Z.overMorphismOfTopoi W).inverseImage ⋙ P)
        a b =
      Sheaf.moduleAddObj ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Z.J.over W)) (Z.O.over W)))
        ((Z.overRestrictionModules W).obj M) P a b :=
  moduleAddObj_restrictionModules (Z.J.over W) Z.J (Over.forget W)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) M
    P a b

/-- The scalar action of a module transported along `j_W^{-1} ⋙ P` is the action of its
restriction to the slice transported along `P`. -/
theorem moduleSMulObj_overRestrictionModules_cocontinuousLocalizedMate
    (r : P.obj (Sheaf.ringSheaf.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Z.J.over W)) (Z.O.over W)))))
    (a : P.obj (Sheaf.moduleSheaf.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Z.J.over W)) (Z.O.over W)))
      ((Z.overRestrictionModules W).obj M))) :
    Sheaf.moduleSMulObj ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) M
        ((Z.overMorphismOfTopoi W).inverseImage ⋙ P)
        r a =
      Sheaf.moduleSMulObj
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Z.J.over W)) (Z.O.over W)))
        ((Z.overRestrictionModules W).obj M) P r a :=
  moduleSMulObj_restrictionModules (Z.J.over W) Z.J (Over.forget W)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) M
    P r a

/-- A morphism of sheaves of modules on a slice, read over the inverse-image ring, has the same
underlying morphism of sheaves of sets. -/
theorem moduleSheafFunctor_map_restrictScalars_map_heq_cocontinuousLocalizedMate
    {N N' : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Z.J.over W)) (Z.O.over W)))} (k : N ⟶ N') :
    (Sheaf.moduleSheafFunctor.{u, u, u} (inverseImageRingSheaf.{u, u, u, u, u, u}
        (restrictionMorphism.{u, u, u, u, u} (Z.J.over W) Z.J (Over.forget W)
          ((Over.forget W).sheafAdjunctionCocontinuous (Type u) (Z.J.over W) Z.J))
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)))).map
      ((SheafOfModules.restrictScalars (restrictionRingIso.{u} (Z.J.over W) Z.J (Over.forget W)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))).hom).map k) ≍
      (Sheaf.moduleSheafFunctor.{u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Z.J.over W)) (Z.O.over W)))).map k :=
  (conj_eqToHom_iff_heq _ _ rfl rfl).mp (Sheaf.hom_ext_sections fun _ _ ↦ rfl)

end OverOperations

section Generic

variable {X Y : RingedSite.{u, u, u}} (V : X.C) (W : Y.C)
  (F : RingedToposHom (ringedTopos X) (ringedTopos Y))
  (F' : RingedToposHom (ringedTopos (X.over V)) (ringedTopos (Y.over W)))
  (e : F.toToposHom.pushforward ⋙ (Y.overMorphismOfTopoi W).inverseImage ⟶
    (X.overMorphismOfTopoi V).inverseImage ⋙ F'.toToposHom.pushforward)
  (hfs : RingedToposHom.forgetFSharp F' =
    (Y.overMorphismOfTopoi W).inverseImage.map (RingedToposHom.forgetFSharp F) ≫
      e.app ((sheafCompose X.J (forget CommRingCat.{u})).obj X.O))

include hfs in
/-- The compatibility of `e` with the structure maps of `F` and `F'`, as maps into the direct
images of the ring sheaves. -/
theorem baseChange_fSharpRing_cocontinuousLocalizedMate :
    (sheafCompose (Y.J.over W) (forget RingCat.{u})).map F'.fSharpRing ≫
        (pushforwardRingSheafIso F'.toToposHom
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))).hom =
      (Y.overMorphismOfTopoi W).inverseImage.map
          ((sheafCompose Y.J (forget RingCat.{u})).map F.fSharpRing ≫
            (pushforwardRingSheafIso F.toToposHom
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).hom) ≫
        e.app (Sheaf.ringSheaf.{u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :=
  (Category.comp_id _).trans (hfs.trans (congrArg (· ≫ _)
    (congrArg (Y.overMorphismOfTopoi W).inverseImage.map (Category.comp_id _).symm)))

/-- The base change map `e` at the underlying sheaf of sets of a module `M`: a morphism of sheaves
of sets from the underlying sheaf of `(F_*M)|_W` to that of `F'_*(M|_V)`. -/
noncomputable abbrev baseChangeSheafHomCocontinuousLocalizedMate
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Y.overMorphismOfTopoi W).inverseImage.obj (F.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M)) ⟶
      F'.toToposHom.pushforward.obj ((X.overMorphismOfTopoi V).inverseImage.obj
        (Sheaf.moduleSheaf.{u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M)) :=
  e.app (Sheaf.moduleSheaf.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M)

include hfs in
/-- **The base change map of sheaves of modules** `(F_*M)|_W ⟶ F'_*(M|_V)` induced by a base
change map `e` of sheaves of sets compatible with the structure maps. -/
noncomputable def baseChangeModulesAppCocontinuousLocalizedMate
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Y.overRestrictionModules W).obj ((RingedToposHom.pushforwardModules F).obj M) ⟶
      (RingedToposHom.pushforwardModules F').obj ((X.overRestrictionModules V).obj M) :=
  ofSheafHom.{u, u, u} (baseChangeSheafHomCocontinuousLocalizedMate V W F F' e M)
    (fun Z x y ↦ by
      have h1 : x + y = Sheaf.moduleAddObj
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M
          (F.toToposHom.pushforward ⋙
            Sheaf.sectionsFunctor Y.J (Opposite.op (Opposite.unop Z).left)) x y :=
        F.pushforwardModules_add M (Opposite.op (Opposite.unop Z).left) x y
      have key := Sheaf.moduleAddObj_naturality
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M
        (Functor.whiskerRight e (Sheaf.sectionsFunctor (Y.J.over W) Z)) x y
      have h2 := F'.pushforwardModules_add ((X.overRestrictionModules V).obj M) Z
        ((Sheaf.sectionsFunctor (Y.J.over W) Z).map
          (baseChangeSheafHomCocontinuousLocalizedMate V W F F' e M) x)
        ((Sheaf.sectionsFunctor (Y.J.over W) Z).map
          (baseChangeSheafHomCocontinuousLocalizedMate V W F F' e M) y)
      have h3 := moduleAddObj_overRestrictionModules_cocontinuousLocalizedMate X V M
        (F'.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor (Y.J.over W) Z)
        ((Sheaf.sectionsFunctor (Y.J.over W) Z).map
          (baseChangeSheafHomCocontinuousLocalizedMate V W F F' e M) x)
        ((Sheaf.sectionsFunctor (Y.J.over W) Z).map
          (baseChangeSheafHomCocontinuousLocalizedMate V W F F' e M) y)
      exact (congrArg _ h1).trans (key.trans (h3.trans h2.symm)))
    (fun Z r x ↦ by
      have h1 := F.pushforwardModules_smul_pushforward M (Opposite.op (Opposite.unop Z).left) r x
      have key := Sheaf.moduleSMulObj_naturality
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M
        (Functor.whiskerRight e (Sheaf.sectionsFunctor (Y.J.over W) Z))
        ((Sheaf.sectionsFunctor Y.J (Opposite.op (Opposite.unop Z).left)).map
          ((sheafCompose Y.J (forget RingCat.{u})).map F.fSharpRing ≫
            (pushforwardRingSheafIso F.toToposHom
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).hom) r) x
      have h2 := F'.pushforwardModules_smul_pushforward ((X.overRestrictionModules V).obj M) Z r
        ((Sheaf.sectionsFunctor (Y.J.over W) Z).map
          (baseChangeSheafHomCocontinuousLocalizedMate V W F F' e M) x)
      have h3 := moduleSMulObj_overRestrictionModules_cocontinuousLocalizedMate X V M
        (F'.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor (Y.J.over W) Z)
        ((Sheaf.sectionsFunctor (Y.J.over W) Z).map ((sheafCompose (Y.J.over W)
          (forget RingCat.{u})).map F'.fSharpRing ≫
            (pushforwardRingSheafIso F'.toToposHom
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))).hom) r)
        ((Sheaf.sectionsFunctor (Y.J.over W) Z).map
          (baseChangeSheafHomCocontinuousLocalizedMate V W F F' e M) x)
      have hr := congrArg (fun s ↦ Sheaf.moduleSMulObj
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M
        ((X.overMorphismOfTopoi V).inverseImage ⋙ F'.toToposHom.pushforward ⋙
            Sheaf.sectionsFunctor (Y.J.over W) Z)
        ((Sheaf.sectionsFunctor (Y.J.over W) Z).map s r)
        ((Sheaf.sectionsFunctor (Y.J.over W) Z).map
          (baseChangeSheafHomCocontinuousLocalizedMate V W F F' e M) x))
        (baseChange_fSharpRing_cocontinuousLocalizedMate V W F F' e hfs)
      exact (congrArg _ h1).trans (key.trans (hr.symm.trans (h3.trans h2.symm))))

include hfs in
/-- The base change map is natural on sections. -/
theorem baseChangeModulesApp_naturality_cocontinuousLocalizedMate
    {M N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))}
    (g : M ⟶ N) :
    (Y.overRestrictionModules W).map ((RingedToposHom.pushforwardModules F).map g) ≫
        baseChangeModulesAppCocontinuousLocalizedMate V W F F' e hfs N =
      baseChangeModulesAppCocontinuousLocalizedMate V W F F' e hfs M ≫
        (RingedToposHom.pushforwardModules F').map ((X.overRestrictionModules V).map g) := by
  refine hom_ext_moduleSheafFunctor
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := (Y.J.over W)) (Y.O.over W))) ?_
  refine Sheaf.hom_ext_sections (J := Y.J.over W) fun Z x => ?_
  exact congrArg (fun t => (Sheaf.sectionsFunctor (Y.J.over W) Z).map t x)
    (e.naturality ((Sheaf.moduleSheafFunctor.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map g))

include hfs in
/-- **The base change square of sheaves of modules**: restricting a direct image along `F` to
`Y/W` maps to the direct image along `F'` of the restriction to `X/V`. -/
noncomputable def baseChangeModulesCocontinuousLocalizedMate :
    TwoSquare (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} F)
      (X.overRestrictionModules V) (Y.overRestrictionModules W)
      (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} F') :=
  TwoSquare.mk _ _ _ _
    { app := fun M ↦ baseChangeModulesAppCocontinuousLocalizedMate V W F F' e hfs M
      naturality := fun _ _ g ↦
        baseChangeModulesApp_naturality_cocontinuousLocalizedMate V W F F' e hfs g }

include hfs in
/-- The underlying morphism of sheaves of sets of the base change square is `e`. -/
theorem moduleSheafFunctor_map_baseChangeModules_app_cocontinuousLocalizedMate
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Sheaf.moduleSheafFunctor.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Y.J.over W)) (Y.O.over W)))).map
        ((baseChangeModulesCocontinuousLocalizedMate V W F F' e hfs).app M) =
      baseChangeSheafHomCocontinuousLocalizedMate V W F F' e M :=
  moduleSheafFunctor_map_ofSheafHom.{u, u, u} _ _ _

include hfs in
/-- The base change square of modules, read over the inverse-image ring, is `e` on underlying
sheaves of sets. -/
theorem
    moduleSheafFunctor_map_restrictScalars_map_baseChangeModules_app_heq_cocontinuousLocalizedMate
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Sheaf.moduleSheafFunctor.{u, u, u} (inverseImageRingSheaf.{u, u, u, u, u, u}
        (restrictionMorphism.{u, u, u, u, u} (Y.J.over W) Y.J (Over.forget W)
          ((Over.forget W).sheafAdjunctionCocontinuous (Type u) (Y.J.over W) Y.J))
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).map
      ((SheafOfModules.restrictScalars (restrictionRingIso.{u} (Y.J.over W) Y.J (Over.forget W)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).hom).map
          ((baseChangeModulesCocontinuousLocalizedMate V W F F' e hfs).app M)) ≍
      baseChangeSheafHomCocontinuousLocalizedMate V W F F' e M :=
  (conj_eqToHom_iff_heq _ _ rfl rfl).mp (Sheaf.hom_ext_sections fun _ _ ↦ rfl)

/-- The underlying sheaf of sets of a direct image of modules along `F` is the direct image of
the underlying sheaf of sets. -/
theorem moduleSheaf_pushforwardModules_obj_cocontinuousLocalizedMate
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Sheaf.moduleSheafFunctor.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).obj
      ((RingedToposHom.pushforwardModules.{u, u, u, u, u, u} F).obj M) =
    F.toToposHom.pushforward.obj
      ((Sheaf.moduleSheafFunctor.{u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).obj M) := rfl

/-- The underlying sheaf of sets of the direct image of modules along `j_V` is the direct image
of the underlying sheaf of sets. -/
theorem moduleSheaf_overRestrictionModules_rightAdjoint_obj_cocontinuousLocalizedMate
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))) :
    (Sheaf.moduleSheafFunctor.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).obj
      ((SheafOfModules.restrictScalars (restrictionRingIso.{u} (X.J.over V) X.J
          (Over.forget V) ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).hom ⋙
        directImageModules (restrictionMorphism (X.J.over V) X.J (Over.forget V)
          ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (X.J.over V) X.J))
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).obj N) =
    ((Over.forget V).sheafPushforwardCocontinuous (Type u) (X.J.over V) X.J).obj
          ((Sheaf.moduleSheafFunctor.{u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))).obj N) :=
  rfl

/-- The underlying sheaf of sets of a direct image of modules along `F'`, read over the
inverse-image ring, is the direct image of the underlying sheaf of sets. -/
theorem moduleSheaf_restrictScalars_pushforwardModules_obj_cocontinuousLocalizedMate
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))) :
    (Sheaf.moduleSheafFunctor.{u, u, u} (inverseImageRingSheaf.{u, u, u, u, u, u}
        (restrictionMorphism.{u, u, u, u, u} (Y.J.over W) Y.J (Over.forget W)
          ((Over.forget W).sheafAdjunctionCocontinuous (Type u) (Y.J.over W) Y.J))
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).obj
      ((SheafOfModules.restrictScalars (restrictionRingIso.{u} (Y.J.over W) Y.J (Over.forget W)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).hom).obj
          ((RingedToposHom.pushforwardModules.{u, u, u, u, u, u} F').obj N)) =
    F'.toToposHom.pushforward.obj ((Sheaf.moduleSheafFunctor.{u, u, u}
      (inverseImageRingSheaf.{u, u, u, u, u, u}
          (restrictionMorphism.{u, u, u, u, u} (X.J.over V) X.J (Over.forget V)
            ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (X.J.over V) X.J))
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))).obj
        ((SheafOfModules.restrictScalars (restrictionRingIso.{u} (X.J.over V) X.J
          (Over.forget V)
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).hom).obj N)) := rfl

/-- The direct image along `F'`, read over the inverse-image rings, is the direct image of
sheaves of sets on underlying morphisms. -/
theorem
    moduleSheafFunctor_map_restrictScalars_map_pushforwardModules_map_heq_cocontinuousLocalizedMate
    {N N' : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))} (c : N ⟶ N') :
    (Sheaf.moduleSheafFunctor.{u, u, u} (inverseImageRingSheaf.{u, u, u, u, u, u}
        (restrictionMorphism.{u, u, u, u, u} (Y.J.over W) Y.J (Over.forget W)
          ((Over.forget W).sheafAdjunctionCocontinuous (Type u) (Y.J.over W) Y.J))
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).map
      ((SheafOfModules.restrictScalars (restrictionRingIso.{u} (Y.J.over W) Y.J (Over.forget W)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).hom).map
          ((RingedToposHom.pushforwardModules.{u, u, u, u, u, u} F').map c)) ≍
      F'.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor.{u, u, u} (inverseImageRingSheaf.{u, u, u, u, u, u}
          (restrictionMorphism.{u, u, u, u, u} (X.J.over V) X.J (Over.forget V)
            ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (X.J.over V) X.J))
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))).map
        ((SheafOfModules.restrictScalars (restrictionRingIso.{u} (X.J.over V) X.J
          (Over.forget V) ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).hom).map c)) :=
  (moduleSheafFunctor_map_restrictScalars_map_heq_cocontinuousLocalizedMate Y W
      ((RingedToposHom.pushforwardModules.{u, u, u, u, u, u} F').map c)).trans
    ((heq_of_eq (RingedToposHom.moduleSheafFunctor_map_pushforwardModules_map F' c)).trans
      (F'.toToposHom.pushforward.map_heq_of_heq_cocontinuousLocalizedMate rfl rfl
        (moduleSheafFunctor_map_restrictScalars_map_heq_cocontinuousLocalizedMate X V c).symm))

/-- The direct image along `F'` of the counit of restriction to the slice is, on underlying
sheaves of sets, the direct image of the counit of sheaves of sets. -/
theorem moduleSheafFunctor_map_restrictScalars_map_pushforwardModules_map_counit_heq_cocontinuousLocalizedMate
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))) :
    (Sheaf.moduleSheafFunctor.{u, u, u} (inverseImageRingSheaf.{u, u, u, u, u, u}
        (restrictionMorphism.{u, u, u, u, u} (Y.J.over W) Y.J (Over.forget W)
          ((Over.forget W).sheafAdjunctionCocontinuous (Type u) (Y.J.over W) Y.J))
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).map
      ((SheafOfModules.restrictScalars (restrictionRingIso.{u} (Y.J.over W) Y.J (Over.forget W)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).hom).map
          ((RingedToposHom.pushforwardModules.{u, u, u, u, u, u} F').map
            ((X.overRestrictionModulesAdjunction V).counit.app N))) ≍
      F'.toToposHom.pushforward.map
        (((Over.forget V).sheafAdjunctionCocontinuous (Type u) (X.J.over V) X.J).counit.app
          ((Sheaf.moduleSheafFunctor.{u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (J := (X.J.over V)) (X.O.over V)))).obj N)) := by
  refine
    (moduleSheafFunctor_map_restrictScalars_map_pushforwardModules_map_heq_cocontinuousLocalizedMate
      V W F' _).trans ?_
  refine (heq_of_eq (F'.toToposHom.pushforward.congr_map
    (moduleSheafFunctor_map_restrictionModulesAdjunction_counit_app (X.J.over V) X.J
      (Over.forget V)
      ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (X.J.over V) X.J)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) N))).trans ?_
  heq_congr

/-- The mate of the base change square of modules under the two localization adjunctions: a
comparison `j_{V,*} ⋙ F_* ⟶ F'_* ⋙ j_{W,*}` of direct images. -/
noncomputable def baseChangeModulesMateCocontinuousLocalizedMate :
    TwoSquare (SheafOfModules.restrictScalars (restrictionRingIso.{u} (X.J.over V) X.J
          (Over.forget V) ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).hom ⋙
        directImageModules (restrictionMorphism (X.J.over V) X.J (Over.forget V)
          ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (X.J.over V) X.J))
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))
      (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} F')
      (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} F)
      (SheafOfModules.restrictScalars (restrictionRingIso.{u} (Y.J.over W) Y.J
          (Over.forget W) ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).hom ⋙
        directImageModules (restrictionMorphism (Y.J.over W) Y.J (Over.forget W)
          ((Over.forget W).sheafAdjunctionCocontinuous (Type u) (Y.J.over W) Y.J))
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :=
  mateEquiv (X.overRestrictionModulesAdjunction V) (Y.overRestrictionModulesAdjunction W)
    (baseChangeModulesCocontinuousLocalizedMate V W F F' e hfs)

/-- The source of the mate of the base change square, on underlying sheaves of sets. -/
theorem moduleSheaf_baseChangeModulesMate_source_cocontinuousLocalizedMate
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))) :
    (Sheaf.moduleSheafFunctor.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).obj
      (((SheafOfModules.restrictScalars (restrictionRingIso.{u} (X.J.over V) X.J
          (Over.forget V) ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).hom ⋙
        directImageModules (restrictionMorphism (X.J.over V) X.J (Over.forget V)
          ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (X.J.over V) X.J))
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) ⋙
        RingedToposHom.pushforwardModules.{u, u, u, u, u, u} F).obj N) =
      F.toToposHom.pushforward.obj
        (((Over.forget V).sheafPushforwardCocontinuous (Type u) (X.J.over V) X.J).obj
          ((Sheaf.moduleSheafFunctor.{u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))).obj N)) :=
  (moduleSheaf_pushforwardModules_obj_cocontinuousLocalizedMate F _).trans
    (congrArg F.toToposHom.pushforward.obj
      (moduleSheaf_overRestrictionModules_rightAdjoint_obj_cocontinuousLocalizedMate V N))

/-- The target of the mate of the base change square, on underlying sheaves of sets, before the
direct image along the slice. -/
theorem moduleSheaf_baseChangeModulesMate_target_cocontinuousLocalizedMate
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))) :
    (Sheaf.moduleSheafFunctor.{u, u, u} (pullbackRingSheaf.{u, u, u, u, u, u} (Y.J.over W)
        ((Over.forget W).sheafPushforwardContinuous (Type u) (Y.J.over W) Y.J)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).obj
        ((SheafOfModules.restrictScalars (restrictionRingIso.{u} (Y.J.over W) Y.J (Over.forget W)
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).hom).obj
          ((RingedToposHom.pushforwardModules.{u, u, u, u, u, u} F').obj N)) =
      F'.toToposHom.pushforward.obj ((Sheaf.moduleSheafFunctor.{u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))).obj N) := rfl

include hfs in
/-- **The mate of the base change square of modules is that of sheaves of sets**, up to the
identifications of underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_baseChangeModulesMate_app_cocontinuousLocalizedMate
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))) :
    (Sheaf.moduleSheafFunctor.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
        ((baseChangeModulesMateCocontinuousLocalizedMate V W F F' e hfs).app N) =
      eqToHom (moduleSheaf_baseChangeModulesMate_source_cocontinuousLocalizedMate V F N) ≫
        (mateEquiv ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (X.J.over V) X.J)
          ((Over.forget W).sheafAdjunctionCocontinuous (Type u) (Y.J.over W) Y.J) e).app
          ((Sheaf.moduleSheafFunctor.{u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))).obj N) ≫
        eqToHom (congrArg ((Over.forget W).sheafPushforwardCocontinuous (Type u) (Y.J.over W)
          Y.J).obj
          (moduleSheaf_baseChangeModulesMate_target_cocontinuousLocalizedMate V W F' N).symm) := by
  have h1 := Stacks.CategoryTheory.mateEquiv_app_eq_homEquiv
    (X.overRestrictionModulesAdjunction V)
    (Y.overRestrictionModulesAdjunction W)
    (baseChangeModulesCocontinuousLocalizedMate V W F F' e hfs) N
  rw [Adjunction.homEquiv_unit] at h1
  have h2 := (Sheaf.moduleSheafFunctor.{u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).congr_map h1
  rw [Functor.map_comp, moduleSheafFunctor_map_restrictionModulesAdjunction_unit_app,
    Functor.comp_map (SheafOfModules.restrictScalars _),
    moduleSheafFunctor_map_restrictionModulesRightAdjoint_map] at h2
  have hs := (Stacks.CategoryTheory.mateEquiv_app_eq_homEquiv
    ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (X.J.over V) X.J)
    ((Over.forget W).sheafAdjunctionCocontinuous (Type u) (Y.J.over W) Y.J) e
    ((Sheaf.moduleSheafFunctor.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))).obj N)).trans
    (((Over.forget W).sheafAdjunctionCocontinuous (Type u) (Y.J.over W) Y.J).homEquiv_unit _ _ _)
  rw [hs]
  refine h2.trans (Stacks.CategoryTheory.unit_comp_map_eq_eqToHom
    ((Over.forget W).sheafAdjunctionCocontinuous (Type u) (Y.J.over W) Y.J)
    (moduleSheaf_baseChangeModulesMate_source_cocontinuousLocalizedMate V F N)
    (moduleSheaf_baseChangeModulesMate_target_cocontinuousLocalizedMate V W F' N) _ _ ?_)
  rw [Functor.map_comp, Functor.map_comp]
  refine heq_comp ?e1 ?e2 ?e3
    ((moduleSheafFunctor_map_restrictScalars_map_baseChangeModules_app_heq_cocontinuousLocalizedMate
      V W F F' e hfs _).trans (by heq_congr))
    (moduleSheafFunctor_map_restrictScalars_map_pushforwardModules_map_counit_heq_cocontinuousLocalizedMate
      V W F' N)
  all_goals exact eq_of_heq (by heq_congr)

include hfs in
/-- The underlying morphism of sheaves of sets of the mate of the base change square is
invertible when the mate of `e` under the localization adjunctions of sheaves of sets is. -/
theorem isIso_moduleSheafFunctor_map_baseChangeModulesMate_app_cocontinuousLocalizedMate
    (hs : IsIso (mateEquiv ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (X.J.over V) X.J)
      ((Over.forget W).sheafAdjunctionCocontinuous (Type u) (Y.J.over W) Y.J) e).natTrans)
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))) :
    IsIso ((Sheaf.moduleSheafFunctor.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
      ((baseChangeModulesMateCocontinuousLocalizedMate V W F F' e hfs).app N)) := by
  have : IsIso ((mateEquiv ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (X.J.over V)
      X.J) ((Over.forget W).sheafAdjunctionCocontinuous (Type u) (Y.J.over W) Y.J) e).app
        ((Sheaf.moduleSheafFunctor.{u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over V)) (X.O.over V)))).obj N)) :=
    NatIso.isIso_app_of_isIso _ _
  have h₁ :
      IsIso (eqToHom (moduleSheaf_baseChangeModulesMate_source_cocontinuousLocalizedMate V F N)) :=
    inferInstance
  have h₃ : IsIso (eqToHom (congrArg ((Over.forget W).sheafPushforwardCocontinuous (Type u)
      (Y.J.over W) Y.J).obj
      (moduleSheaf_baseChangeModulesMate_target_cocontinuousLocalizedMate V W F' N).symm)) :=
    inferInstance
  rw [moduleSheafFunctor_map_baseChangeModulesMate_app_cocontinuousLocalizedMate V W F F' e hfs N]
  exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' this h₃)

include hfs in
/-- **The mate of the base change square of sheaves of modules is invertible** when the mate of
`e` under the localization adjunctions of sheaves of sets is. -/
theorem isIso_baseChangeModulesMate_cocontinuousLocalizedMate
    (hs : IsIso (mateEquiv ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (X.J.over V) X.J)
      ((Over.forget W).sheafAdjunctionCocontinuous (Type u) (Y.J.over W) Y.J) e).natTrans) :
    IsIso (baseChangeModulesMateCocontinuousLocalizedMate V W F F' e hfs).natTrans := by
  have hN : ∀ N,
      IsIso ((baseChangeModulesMateCocontinuousLocalizedMate V W F F' e hfs).natTrans.app N) :=
    fun N ↦
      Stacks.Sheaves.PushforwardEssentialImage.isIso_of_isIso_moduleSheafFunctor_map
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))
        ((baseChangeModulesMateCocontinuousLocalizedMate V W F F' e hfs).app N)
        (isIso_moduleSheafFunctor_map_baseChangeModulesMate_app_cocontinuousLocalizedMate V W F F'
          e hfs hs N)
  exact NatIso.isIso_of_isIso_app _

section Pullback

variable [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [(X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

include hfs in
/-- **The base change mate of sheaves of modules.** The comparison `F'^*(G|_W) ⟶ (F^*G)|_V`:
the mate of the base change square under the two adjunctions `F^* ⊣ F_*` and `F'^* ⊣ F'_*`. -/
noncomputable def baseChangePullbackMateCocontinuousLocalizedMate :
    TwoSquare (Y.overRestrictionModules W)
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u, u, u}
        F.toModulesHom)
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u, u, u}
        F'.toModulesHom)
      (X.overRestrictionModules V) :=
  (mateEquiv (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} F)
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} F')).symm
      (baseChangeModulesCocontinuousLocalizedMate V W F F' e hfs)

omit [HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [(X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
include hfs in
/-- **The base change mate of sheaves of modules is invertible** when the mate of `e` under the
localization adjunctions of sheaves of sets is. -/
theorem isIso_baseChangePullbackMate_cocontinuousLocalizedMate
    (hs : IsIso (mateEquiv ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (X.J.over V) X.J)
      ((Over.forget W).sheafAdjunctionCocontinuous (Type u) (Y.J.over W) Y.J) e).natTrans) :
    IsIso (baseChangePullbackMateCocontinuousLocalizedMate V W F F' e hfs).natTrans := by
  have h := iterated_mateEquiv_conjugateEquiv
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} F)
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} F')
    (Y.overRestrictionModulesAdjunction W) (X.overRestrictionModulesAdjunction V)
    (baseChangePullbackMateCocontinuousLocalizedMate V W F F' e hfs)
  have e' : mateEquiv
      (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} F)
      (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} F')
      (baseChangePullbackMateCocontinuousLocalizedMate V W F F' e hfs) =
        baseChangeModulesCocontinuousLocalizedMate V W F F' e hfs :=
    Equiv.apply_symm_apply _ _
  have h' : (baseChangeModulesMateCocontinuousLocalizedMate V W F F' e hfs).natTrans =
      conjugateEquiv
        ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} F).comp
          (X.overRestrictionModulesAdjunction V))
        ((Y.overRestrictionModulesAdjunction W).comp
          (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} F'))
        (baseChangePullbackMateCocontinuousLocalizedMate V W F F' e hfs) :=
    (congrArg (mateEquiv (X.overRestrictionModulesAdjunction V)
      (Y.overRestrictionModulesAdjunction W)) e').symm.trans h
  have hi := isIso_baseChangeModulesMate_cocontinuousLocalizedMate V W F F' e hfs hs
  rw [h'] at hi
  exact @conjugateEquiv_of_iso _ _ _ _ _ _ _ _
    ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} F).comp
      (X.overRestrictionModulesAdjunction V))
    ((Y.overRestrictionModulesAdjunction W).comp
      (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} F'))
    (baseChangePullbackMateCocontinuousLocalizedMate V W F F' e hfs) hi

end Pullback

end Generic

end AlgebraicGeometry.RingedSite

module

public import StacksFrontier.CategoryTheory.Adjunction.MateCompatibility
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictionModulesAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialSurjectivity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizedMorphism
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The localization mate of a morphism of ringed sites is invertible

Let `f : X ⟶ Y` be a morphism of ringed sites given by `u : Y.C ⥤ X.C`, let `V` be an object of
`Y.C` and let `f' : X/u(V) ⟶ Y/V` be the localized morphism of Stacks 04J0. Restriction of
sheaves of modules to the slices commutes with the direct images on the nose (Stacks 03CF (d)),
and the Beck–Chevalley mate `j_V^* ⋙ f'^* ⟶ f^* ⋙ j_{u(V)}^*` of that identity is invertible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
  Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.RingedToposHom

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {A : RingedTopos.{v₁, u₁, w₁}} {B : RingedTopos.{v₂, u₂, w₂}}
  [A.J.HasSheafCompose (forget RingCat.{w₁})] [B.J.HasSheafCompose (forget RingCat.{w₂})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [A.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]

/-- The scalar action on the sections of a direct image of a sheaf of modules, with the scalar
carried along the structure map into the direct image of the underlying sheaf of sets. -/
theorem pushforwardModules_smul_pushforward (f : RingedToposHom A B)
    (F : SheafOfModules.{w₁} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := A.J) A.O))) (Z : B.Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor B.J Z).obj
      (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := B.J) B.O))))
    (x : (Sheaf.sectionsFunctor B.J Z).obj
      (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := B.J) B.O))
        ((pushforwardModules f).obj F))) :
    r • x =
      Sheaf.moduleSMulObj ((Stacks.SheafOfModules.Tensor.ringSheaf (J := A.J) A.O)) F
        (f.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor B.J Z)
        ((Sheaf.sectionsFunctor B.J Z).map
          ((sheafCompose B.J (forget RingCat.{w₂})).map f.fSharpRing ≫
            (pushforwardRingSheafIso f.toToposHom
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := A.J) A.O))).hom) r) x :=
  f.pushforwardModules_smul F Z r x

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.RingedSite

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

/-- Restriction of sheaves of modules on a ringed site to the slice over an object. -/
noncomputable abbrev overRestrictionModules (Z : RingedSite.{u, u, u}) (W : Z.C) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) ⥤
      SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Z.J.over W)) (Z.O.over W))) :=
  restrictionModules (Z.J.over W) Z.J (Over.forget W)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))

/-- Restriction of sheaves of modules to a slice is left adjoint to the direct image, with the
unit and counit of sheaves of sets. -/
noncomputable abbrev overRestrictionModulesAdjunction (Z : RingedSite.{u, u, u}) (W : Z.C) :=
  restrictionModulesAdjunction (Z.J.over W) Z.J (Over.forget W)
    ((Over.forget W).sheafAdjunctionCocontinuous (Type u) (Z.J.over W) Z.J)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))

/-- A sheaf of modules on a slice and its restriction of scalars to the inverse-image ring have
the same underlying sheaf of sets. -/
theorem moduleSheaf_restrictScalars_restrictionRingIso {Z : RingedSite.{u, u, u}} (W : Z.C)
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Z.J.over W)) (Z.O.over W)))) :
    Sheaf.moduleSheaf.{u, u, u} (pullbackRingSheaf.{u, u, u, u, u, u} (Z.J.over W)
      ((Over.forget W).sheafPushforwardContinuous (Type u) (Z.J.over W) Z.J)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)))
      ((SheafOfModules.restrictScalars (restrictionRingIso.{u} (Z.J.over W) Z.J (Over.forget W)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))).hom).obj N) =
    Sheaf.moduleSheaf.{u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Z.J.over W)) (Z.O.over W))) N := rfl

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)

/-- The underlying sheaf of sets of `f'_*(M|_{u(V)})`, which is also that of `(f_*M)|_V`. -/
noncomputable abbrev Hom.localizedPushforwardSheaf
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    Sheaf (Y.J.over V) (Type u) :=
  (f.localized V).ringedToposHom.toToposHom.pushforward.obj
    ((X.overMorphismOfTopoi (f.u.obj V)).inverseImage.obj
      (Sheaf.moduleSheaf.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M))

/-- The structure map of the localized morphism, on underlying sheaves of sets, is the
restriction of the structure map of `f`. -/
theorem Hom.forget_map_localized_fSharpRing :
    (sheafCompose (Y.J.over V) (forget RingCat.{u})).map
        (f.localized V).ringedToposHom.fSharpRing =
      (Y.J.overPullback (Type u) V).map
        ((sheafCompose Y.J (forget RingCat.{u})).map f.ringedToposHom.fSharpRing) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- **Stacks 03CF (d) for sheaves of modules.** The restriction to `Y/V` of a direct image
along `f` is the direct image along `f'` of the restriction to `X/u(V)`; the comparison is the
identity on underlying sheaves of sets. -/
noncomputable def Hom.localizedPushforwardSquareApp
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Y.overRestrictionModules V).obj ((RingedToposHom.pushforwardModules
        f.ringedToposHom).obj M) ⟶
      (RingedToposHom.pushforwardModules (f.localized V).ringedToposHom).obj
        ((X.overRestrictionModules (f.u.obj V)).obj M) :=
  ofSheafHom.{u, u, u} (𝟙 (f.localizedPushforwardSheaf V M))
    (fun Z x y => by
      have h1 : x + y = Sheaf.moduleAddObj
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M
          (f.ringedToposHom.toToposHom.pushforward ⋙
            Sheaf.sectionsFunctor Y.J (Opposite.op (Opposite.unop Z).left)) x y :=
        f.ringedToposHom.pushforwardModules_add M (Opposite.op (Opposite.unop Z).left) x y
      have h2 := (f.localized V).ringedToposHom.pushforwardModules_add
        ((X.overRestrictionModules (f.u.obj V)).obj M) Z
        ((Sheaf.sectionsFunctor (Y.J.over V) Z).map (𝟙 (f.localizedPushforwardSheaf V M)) x)
        ((Sheaf.sectionsFunctor (Y.J.over V) Z).map (𝟙 (f.localizedPushforwardSheaf V M)) y)
      have h3 := moduleAddObj_restrictionModules (X.J.over (f.u.obj V)) X.J
        (Over.forget (f.u.obj V)) ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M
        ((f.localized V).ringedToposHom.toToposHom.pushforward ⋙
          Sheaf.sectionsFunctor (Y.J.over V) Z)
        ((Sheaf.sectionsFunctor (Y.J.over V) Z).map (𝟙 (f.localizedPushforwardSheaf V M)) x)
        ((Sheaf.sectionsFunctor (Y.J.over V) Z).map (𝟙 (f.localizedPushforwardSheaf V M)) y)
      exact h1.trans (h3.trans h2.symm))
    (fun Z r x => by
      have h1 := f.ringedToposHom.pushforwardModules_smul_pushforward M
        (Opposite.op (Opposite.unop Z).left) r x
      have h2 := (f.localized V).ringedToposHom.pushforwardModules_smul_pushforward
        ((X.overRestrictionModules (f.u.obj V)).obj M) Z r
        ((Sheaf.sectionsFunctor (Y.J.over V) Z).map (𝟙 (f.localizedPushforwardSheaf V M)) x)
      have h3 := moduleSMulObj_restrictionModules (X.J.over (f.u.obj V)) X.J
        (Over.forget (f.u.obj V)) ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M
        ((f.localized V).ringedToposHom.toToposHom.pushforward ⋙
          Sheaf.sectionsFunctor (Y.J.over V) Z)
        ((Sheaf.sectionsFunctor (Y.J.over V) Z).map ((sheafCompose (Y.J.over V)
          (forget RingCat.{u})).map (f.localized V).ringedToposHom.fSharpRing ≫
            (pushforwardRingSheafIso (f.localized V).ringedToposHom.toToposHom
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over (f.u.obj V)))
                (X.O.over (f.u.obj V))))).hom) r)
        ((Sheaf.sectionsFunctor (Y.J.over V) Z).map (𝟙 (f.localizedPushforwardSheaf V M)) x)
      have hr := congrArg (fun s => Sheaf.moduleSMulObj
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M
        ((X.overMorphismOfTopoi (f.u.obj V)).inverseImage ⋙
          (f.localized V).ringedToposHom.toToposHom.pushforward ⋙
            Sheaf.sectionsFunctor (Y.J.over V) Z)
        ((Sheaf.sectionsFunctor (Y.J.over V) Z).map (s ≫
            (pushforwardRingSheafIso (f.localized V).ringedToposHom.toToposHom
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over (f.u.obj V)))
                (X.O.over (f.u.obj V))))).hom) r)
        ((Sheaf.sectionsFunctor (Y.J.over V) Z).map (𝟙 (f.localizedPushforwardSheaf V M)) x))
        (f.forget_map_localized_fSharpRing V)
      have e1 := h1.trans hr.symm
      have e2 := h3.trans h2.symm
      exact e1.trans e2)

/-- **Stacks 03CF (d) for sheaves of modules**, as a square of functors: restricting a direct
image along `f` to `Y/V` is taking the direct image along `f'` of the restriction to `X/u(V)`. -/
noncomputable def Hom.localizedPushforwardSquare :
    TwoSquare (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} f.ringedToposHom)
      (X.overRestrictionModules (f.u.obj V)) (Y.overRestrictionModules V)
      (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} (f.localized V).ringedToposHom) :=
  TwoSquare.mk _ _ _ _
    { app := fun M => f.localizedPushforwardSquareApp V M
      naturality := fun _ _ _ => by
        refine hom_ext_moduleSheafFunctor
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := (Y.J.over V)) (Y.O.over V)))
          ?_
        exact Sheaf.hom_ext_sections (J := Y.J.over V) fun _ _ ↦ rfl }

/-- The underlying morphism of sheaves of sets of the square is the identity. -/
theorem Hom.moduleSheafFunctor_map_localizedPushforwardSquare_app
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Sheaf.moduleSheafFunctor
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (Y.J.over V)) (Y.O.over V)))).map
        ((f.localizedPushforwardSquare V).app M) = 𝟙 (f.localizedPushforwardSheaf V M) :=
  moduleSheafFunctor_map_ofSheafHom.{u, u, u} _ _ _

/-- The square of modules, read over the inverse-image ring, is the identity on underlying sheaves
of sets. -/
theorem Hom.moduleSheafFunctor_map_restrictScalars_map_localizedPushforwardSquare_app_heq
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Sheaf.moduleSheafFunctor.{u, u, u} (inverseImageRingSheaf.{u, u, u, u, u, u}
      (restrictionMorphism.{u, u, u, u, u} (Y.J.over V) Y.J (Over.forget V)
        ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (Y.J.over V) Y.J))
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).map
      ((SheafOfModules.restrictScalars (restrictionRingIso.{u} (Y.J.over V) Y.J (Over.forget V)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).hom).map
          ((f.localizedPushforwardSquare V).app M)) ≍
      𝟙 (f.localizedPushforwardSheaf V M) :=
  (conj_eqToHom_iff_heq _ _ rfl rfl).mp (Sheaf.hom_ext_sections fun _ _ ↦ rfl)

/-- The direct image along the localized morphism, read over the inverse-image rings, is the
direct image of sheaves of sets on underlying morphisms. -/
theorem Hom.moduleSheafFunctor_map_restrictScalars_map_localized_pushforwardModules_map_heq
    {N N' : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over (f.u.obj V)))
        (X.O.over (f.u.obj V))))}
    (c : N ⟶ N') :
    (Sheaf.moduleSheafFunctor.{u, u, u} (inverseImageRingSheaf.{u, u, u, u, u, u}
      (restrictionMorphism.{u, u, u, u, u} (Y.J.over V) Y.J (Over.forget V)
        ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (Y.J.over V) Y.J))
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).map
      ((SheafOfModules.restrictScalars (restrictionRingIso.{u} (Y.J.over V) Y.J (Over.forget V)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).hom).map
          ((RingedToposHom.pushforwardModules.{u, u, u, u, u, u}
            (f.localized V).ringedToposHom).map c)) ≍
      (f.localized V).ringedToposHom.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor.{u, u, u} (inverseImageRingSheaf.{u, u, u, u, u, u}
          (restrictionMorphism.{u, u, u, u, u} (X.J.over (f.u.obj V)) X.J (Over.forget (f.u.obj V))
            ((Over.forget (f.u.obj V)).sheafAdjunctionCocontinuous (Type u) (X.J.over (f.u.obj V))
              X.J))
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))).map
        ((SheafOfModules.restrictScalars (restrictionRingIso.{u} (X.J.over (f.u.obj V)) X.J
          (Over.forget (f.u.obj V))
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).hom).map c)) :=
  (conj_eqToHom_iff_heq _ _ rfl rfl).mp (Sheaf.hom_ext_sections fun _ _ ↦ rfl)

/-- The mate of a square of right adjoints is invertible iff its mate back along the outer
adjunctions is, by `iterated_mateEquiv_conjugateEquiv`. -/
private theorem isIso_mateEquiv_iff_isIso_mateEquiv_symm {A B C D : Type*} [Category A]
    [Category B] [Category C] [Category D] {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : F₁ ⊣ U₁) (adj₄ : F₂ ⊣ U₂)
    (β : TwoSquare R₁ F₂ F₁ R₂) :
    IsIso (mateEquiv adj₄ adj₃ β).natTrans ↔ IsIso ((mateEquiv adj₁ adj₂).symm β).natTrans := by
  obtain ⟨α, rfl⟩ := (mateEquiv adj₁ adj₂).surjective β
  rw [Equiv.symm_apply_apply, iterated_mateEquiv_conjugateEquiv]
  exact ⟨fun h => conjugateEquiv_of_iso (adj₁.comp adj₄) (adj₃.comp adj₂) α,
    fun h => conjugateEquiv_iso (adj₁.comp adj₄) (adj₃.comp adj₂) α⟩

/-- **The iterated mate of the localization square, on sheaves of sets, is invertible.** The
mate of Stacks 03CF (d) under `f^{-1} ⊣ f_*` and `f'^{-1} ⊣ f'_*` is clause (b), an isomorphism;
its further mate under the two localization adjunctions is its conjugate, hence invertible. -/
theorem Hom.isIso_mateEquiv_localizationAdj_eqToHom :
    IsIso (mateEquiv ((Over.forget (f.u.obj V)).sheafAdjunctionCocontinuous (Type u)
      (X.J.over (f.u.obj V)) X.J)
      ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (Y.J.over V) Y.J)
      (eqToHom (sheafPushforwardContinuous_overPost_eq Y.J X.J f.u V (Type u)).symm)).natTrans := by
  refine (isIso_mateEquiv_iff_isIso_mateEquiv_symm
    (f.u.sheafAdjunctionContinuous (Type u) Y.J X.J)
    ((Over.post (X := V) f.u).sheafAdjunctionContinuous (Type u) (Y.J.over V)
      (X.J.over (f.u.obj V)))
    ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (Y.J.over V) Y.J)
    ((Over.forget (f.u.obj V)).sheafAdjunctionCocontinuous (Type u) (X.J.over (f.u.obj V)) X.J)
    (eqToHom (sheafPushforwardContinuous_overPost_eq Y.J X.J f.u V (Type u)).symm)).2 ?_
  exact CategoryTheory.SliceTopos.isIso_overPullbackCompSheafPullbackOverPostMate Y.J X.J f.u V
    f.isMorphismOfSites

/-- The mate of the localization square of sheaves of modules under the two localization
adjunctions: a comparison `j_{u(V),*} ⋙ f_* ⟶ f'_* ⋙ j_{V,*}` of direct images. -/
noncomputable def Hom.localizedPushforwardSquareMate :=
  mateEquiv (X.overRestrictionModulesAdjunction (f.u.obj V))
    (Y.overRestrictionModulesAdjunction V) (f.localizedPushforwardSquare V)

/-- The source of the iterated mate of the localization square, on underlying sheaves of
sets. -/
theorem Hom.moduleSheaf_localizedPushforwardSquareMate_source
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over (f.u.obj V)))
        (X.O.over (f.u.obj V))))) :
    (Sheaf.moduleSheafFunctor.{u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).obj
        (((SheafOfModules.restrictScalars (restrictionRingIso.{u}
          (X.J.over (f.u.obj V)) X.J (Over.forget (f.u.obj V))
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).hom ⋙
        directImageModules (restrictionMorphism (X.J.over (f.u.obj V)) X.J (Over.forget (f.u.obj V))
        ((Over.forget (f.u.obj V)).sheafAdjunctionCocontinuous (Type u) (X.J.over (f.u.obj V)) X.J))
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) ⋙
        RingedToposHom.pushforwardModules.{u, u, u, u, u, u} f.ringedToposHom).obj N) =
      (f.u.sheafPushforwardContinuous (Type u) Y.J X.J).obj
        (((Over.forget (f.u.obj V)).sheafPushforwardCocontinuous (Type u) (X.J.over (f.u.obj V))
          X.J).obj ((Sheaf.moduleSheafFunctor.{u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over (f.u.obj V)))
            (X.O.over (f.u.obj V))))).obj N)) := rfl

/-- The target of the iterated mate of the localization square, on underlying sheaves of
sets, before the direct image along the slice. -/
theorem Hom.moduleSheaf_localizedPushforwardSquareMate_target
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over (f.u.obj V)))
        (X.O.over (f.u.obj V))))) :
    ((Sheaf.moduleSheafFunctor.{u, u, u} (pullbackRingSheaf.{u, u, u, u, u, u} (Y.J.over V)
        ((Over.forget V).sheafPushforwardContinuous (Type u) (Y.J.over V) Y.J)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).obj
        ((SheafOfModules.restrictScalars (restrictionRingIso.{u} (Y.J.over V) Y.J (Over.forget V)
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).hom).obj
          ((RingedToposHom.pushforwardModules.{u, u, u, u, u, u}
            (f.localized V).ringedToposHom).obj N))) =
      ((Over.post (X := V) f.u).sheafPushforwardContinuous (Type u) (Y.J.over V)
          (X.J.over (f.u.obj V))).obj ((Sheaf.moduleSheafFunctor.{u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over (f.u.obj V)))
            (X.O.over (f.u.obj V))))).obj N) := rfl

/-- The direct image along the localized morphism of the counit of restriction to the slice is,
on underlying sheaves of sets, the direct image of the counit of sheaves of sets. -/
theorem Hom.moduleSheafFunctor_map_restrictScalars_map_localized_pushforwardModules_map_counit_heq
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over (f.u.obj V)))
        (X.O.over (f.u.obj V))))) :
    (Sheaf.moduleSheafFunctor.{u, u, u} (inverseImageRingSheaf.{u, u, u, u, u, u}
        (restrictionMorphism.{u, u, u, u, u} (Y.J.over V) Y.J (Over.forget V)
          ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (Y.J.over V) Y.J))
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).map
      ((SheafOfModules.restrictScalars (restrictionRingIso.{u} (Y.J.over V) Y.J (Over.forget V)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).hom).map
          ((RingedToposHom.pushforwardModules.{u, u, u, u, u, u} (f.localized V).ringedToposHom).map
            ((X.overRestrictionModulesAdjunction (f.u.obj V)).counit.app N))) ≍
      ((Over.post (X := V) f.u).sheafPushforwardContinuous (Type u) (Y.J.over V)
          (X.J.over (f.u.obj V))).map
        (((Over.forget (f.u.obj V)).sheafAdjunctionCocontinuous (Type u) (X.J.over (f.u.obj V))
          X.J).counit.app ((Sheaf.moduleSheafFunctor.{u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over (f.u.obj V)))
              (X.O.over (f.u.obj V))))).obj N)) := by
  refine
    (f.moduleSheafFunctor_map_restrictScalars_map_localized_pushforwardModules_map_heq V _).trans ?_
  refine (heq_of_eq ((f.localized V).ringedToposHom.toToposHom.pushforward.congr_map
    (moduleSheafFunctor_map_restrictionModulesAdjunction_counit_app (X.J.over (f.u.obj V)) X.J
      (Over.forget (f.u.obj V))
      ((Over.forget (f.u.obj V)).sheafAdjunctionCocontinuous (Type u) (X.J.over (f.u.obj V)) X.J)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) N))).trans ?_
  heq_congr

/-- **The iterated mate of the localization square of sheaves of modules is that of sheaves of
sets.** Its underlying morphism of sheaves of sets is the iterated mate of Stacks 03CF (d), up
to the identifications of underlying sheaves of sets: the two localization adjunctions of
modules have the units and counits of sheaves of sets, and the square of modules is the
identity on underlying sheaves of sets. -/
theorem Hom.moduleSheafFunctor_map_mateEquiv_localizedPushforwardSquare_app
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over (f.u.obj V)))
        (X.O.over (f.u.obj V))))) :
    (Sheaf.moduleSheafFunctor.{u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
        ((f.localizedPushforwardSquareMate V).app N) =
      eqToHom (f.moduleSheaf_localizedPushforwardSquareMate_source V N) ≫
        (mateEquiv
          ((Over.forget (f.u.obj V)).sheafAdjunctionCocontinuous (Type u) (X.J.over (f.u.obj V))
            X.J)
          ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (Y.J.over V) Y.J)
          (eqToHom (sheafPushforwardContinuous_overPost_eq Y.J X.J f.u V (Type u)).symm)).app
          ((Sheaf.moduleSheafFunctor.{u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over (f.u.obj V)))
              (X.O.over (f.u.obj V))))).obj N) ≫
        eqToHom (congrArg
          ((Over.forget V).sheafPushforwardCocontinuous (Type u) (Y.J.over V) Y.J).obj
          (f.moduleSheaf_localizedPushforwardSquareMate_target V N).symm) := by
  have h1 := Stacks.CategoryTheory.mateEquiv_app_eq_homEquiv
    (X.overRestrictionModulesAdjunction (f.u.obj V))
    (Y.overRestrictionModulesAdjunction V) (f.localizedPushforwardSquare V) N
  rw [Adjunction.homEquiv_unit] at h1
  have h2 := (Sheaf.moduleSheafFunctor.{u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).congr_map h1
  rw [Functor.map_comp, moduleSheafFunctor_map_restrictionModulesAdjunction_unit_app,
    Functor.comp_map (SheafOfModules.restrictScalars _),
    moduleSheafFunctor_map_restrictionModulesRightAdjoint_map] at h2
  have hs := (Stacks.CategoryTheory.mateEquiv_app_eq_homEquiv
      ((Over.forget (f.u.obj V)).sheafAdjunctionCocontinuous (Type u) (X.J.over (f.u.obj V)) X.J)
      ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (Y.J.over V) Y.J)
      (eqToHom (sheafPushforwardContinuous_overPost_eq Y.J X.J f.u V (Type u)).symm)
      ((Sheaf.moduleSheafFunctor.{u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over (f.u.obj V)))
          (X.O.over (f.u.obj V))))).obj N)).trans
    (((Over.forget V).sheafAdjunctionCocontinuous (Type u) (Y.J.over V) Y.J).homEquiv_unit _ _ _)
  rw [hs]
  refine h2.trans (Stacks.CategoryTheory.unit_comp_map_eq_eqToHom
    ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (Y.J.over V) Y.J)
    (f.moduleSheaf_localizedPushforwardSquareMate_source V N)
    (f.moduleSheaf_localizedPushforwardSquareMate_target V N) _ _ ?_)
  rw [Functor.map_comp, Functor.map_comp, eqToHom_app]
  refine heq_comp ?e1 ?e2 ?e3
    ((f.moduleSheafFunctor_map_restrictScalars_map_localizedPushforwardSquare_app_heq V _).trans
      (eqToHom_heq_id_dom _ _ _).symm)
    (f.moduleSheafFunctor_map_restrictScalars_map_localized_pushforwardModules_map_counit_heq V N)
  case e1 => exact eq_of_heq (by heq_congr)
  case e2 => exact eq_of_heq (by heq_congr)
  case e3 => exact eq_of_heq (by heq_congr)

/-- The underlying morphism of sheaves of sets of the iterated mate of the localization square
is invertible. -/
theorem Hom.isIso_moduleSheafFunctor_map_localizedPushforwardSquareMate_app
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (X.J.over (f.u.obj V)))
        (X.O.over (f.u.obj V))))) :
    IsIso ((Sheaf.moduleSheafFunctor.{u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
      ((f.localizedPushforwardSquareMate V).app N)) := by
  have hs := f.isIso_mateEquiv_localizationAdj_eqToHom V
  rw [f.moduleSheafFunctor_map_mateEquiv_localizedPushforwardSquare_app V N]
  exact IsIso.comp_isIso'
    (Iso.isIso_hom (eqToIso (f.moduleSheaf_localizedPushforwardSquareMate_source V N)))
    (IsIso.comp_isIso' (NatIso.isIso_app_of_isIso _ _)
      (Iso.isIso_hom (eqToIso (congrArg ((Over.forget V).sheafPushforwardCocontinuous (Type u)
        (Y.J.over V) Y.J).obj (f.moduleSheaf_localizedPushforwardSquareMate_target V N).symm))))

/-- **The iterated mate of the localization square of sheaves of modules is invertible**, since
its underlying morphism of sheaves of sets is the iterated mate of Stacks 03CF (d). -/
theorem Hom.isIso_localizedPushforwardSquareMate :
    IsIso (f.localizedPushforwardSquareMate V).natTrans := by
  have hN : ∀ N, IsIso ((f.localizedPushforwardSquareMate V).natTrans.app N) := fun N =>
    Stacks.Sheaves.PushforwardEssentialImage.isIso_of_isIso_moduleSheafFunctor_map
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))
      ((f.localizedPushforwardSquareMate V).app N)
      (f.isIso_moduleSheafFunctor_map_localizedPushforwardSquareMate_app V N)
  exact NatIso.isIso_of_isIso_app _

variable [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over (f.u.obj V)) AddCommGrpCat.{u}]
  [(X.J.over (f.u.obj V)).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The localization mate of a morphism of ringed sites.** The Beck–Chevalley comparison
`(f')^*(G|_V) ⟶ (f^*G)|_{u(V)}` of sheaves of modules: the mate of the identity
`(f_*M)|_V = f'_*(M|_{u(V)})` under the two adjunctions `f^* ⊣ f_*` and `f'^* ⊣ f'_*`. -/
noncomputable def Hom.localizedPullbackMate :
    TwoSquare (Y.overRestrictionModules V)
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u, u, u}
        f.ringedToposHom.toModulesHom)
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u, u, u}
        ((f.localized V).ringedToposHom).toModulesHom)
      (X.overRestrictionModules (f.u.obj V)) :=
  (mateEquiv (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} f.ringedToposHom)
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
      (f.localized V).ringedToposHom)).symm
      (f.localizedPushforwardSquare V)

omit [HasWeakSheafify (X.J.over (f.u.obj V)) AddCommGrpCat.{u}]
  [(X.J.over (f.u.obj V)).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The localization mate of a morphism of ringed sites is invertible**: the Beck–Chevalley
comparison `(f')^*(G|_V) ⟶ (f^*G)|_{u(V)}` is an isomorphism, being conjugate to the iterated
mate of Stacks 03CF (d). -/
theorem Hom.isIso_localizedPullbackMate : IsIso (f.localizedPullbackMate V).natTrans := by
  exact (isIso_mateEquiv_iff_isIso_mateEquiv_symm
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} f.ringedToposHom)
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} (f.localized V).ringedToposHom)
    (Y.overRestrictionModulesAdjunction V) (X.overRestrictionModulesAdjunction (f.u.obj V))
    (f.localizedPushforwardSquare V)).1 (f.isIso_localizedPushforwardSquareMate V)

end AlgebraicGeometry.RingedSite

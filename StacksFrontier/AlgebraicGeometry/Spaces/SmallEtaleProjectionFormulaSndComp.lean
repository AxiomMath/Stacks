module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaSnd
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorComp
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMapSndComp

/-!
# The projection formula with the counit in the second factor, along a composite of spaces

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces, the projection formula map
`K ⊗^𝐋 R(f ≫ g)_*W ⟶ R(f ≫ g)_*(L(f ≫ g)^*K ⊗^𝐋 W)`
(`AlgebraicGeometry.Space.smallEtaleProjectionFormulaMapSnd`) is the one of `g` at `(K, Rf_*W)`
followed by `Rg_*` of the one of `f` at `(Lg^*K, W)`, through the composition isomorphism
`Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of [Stacks, Tag 0D6D] and its conjugate
`Rf_* ⋙ Rg_* ⟶ R(f ≫ g)_*` on the right adjoints. This is
`Stacks.ProjectionFormula.adjunctionTensorMapSnd_comp_conjugateEquiv`, whose compatibility input is
[Stacks, Tag 07A4] along a composite
(`AlgebraicGeometry.Space.smallEtaleDerivedPullbackTensorIso_comp`).

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedPushforwardCompConjugate`: the conjugate
  `Rf_* ⋙ Rg_* ⟶ R(f ≫ g)_*`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleProjectionFormulaMapSnd_comp`, and
  `AlgebraicGeometry.Space.smallEtaleProjectionFormulaSndNatTrans_comp` as an equality of natural
  transformations, from the abstract
  `Stacks.ProjectionFormula.adjunctionTensorMapSnd_comp_conjugateEquiv_natTrans`, and along an
  equation `f ≫ g = q` (`smallEtaleProjectionFormulaSndNatTrans_comp_of_eq`).
* `AlgebraicGeometry.Space.smallEtaleProjectionFormulaSndNatTrans_naturality`: naturality in the
  second argument.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Prod

universe u

namespace Stacks.ProjectionFormula

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {F : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} F]
  {Lp : C ⥤ D} {Rp : D ⥤ C} (ap : Lp ⊣ Rp) {Li : D ⥤ F} {Ri : F ⥤ D} (ai : Li ⊣ Ri)
  {Lq : C ⥤ F} {Rq : F ⥤ C} (aq : Lq ⊣ Rq) (γ : Lp ⋙ Li ≅ Lq)
  (FC : C ⥤ C ⥤ C) (FD : D ⥤ D ⥤ D) (FF : F ⥤ F ⥤ F)
  (μp : Functor.uncurry.obj FC ⋙ Lp ⟶ Lp.prod Lp ⋙ Functor.uncurry.obj FD)
  (μi : Functor.uncurry.obj FD ⋙ Li ⟶ Li.prod Li ⋙ Functor.uncurry.obj FF)
  (μq : Functor.uncurry.obj FC ⋙ Lq ⟶ Lq.prod Lq ⋙ Functor.uncurry.obj FF)

/-- **`adjunctionTensorMapSnd_comp_conjugateEquiv` as an equality of natural transformations** in
the first factor, for curried bifunctors: `αp`, `αi`, `αq` are any natural transformations whose
components are the projection formula maps. -/
theorem adjunctionTensorMapSnd_comp_conjugateEquiv_natTrans
    (hμ : ∀ H G : C, γ.hom.app ((Functor.uncurry.obj FC).obj (H, G)) ≫ μq.app (H, G) =
      Li.map (μp.app (H, G)) ≫ μi.app (Lp.obj H, Lp.obj G) ≫
        (Functor.uncurry.obj FF).map (γ.hom.app H ×ₘ γ.hom.app G)) (Z : F)
    (αp : FC.flip.obj (Rp.obj (Ri.obj Z)) ⟶ Lp ⋙ FD.flip.obj (Ri.obj Z) ⋙ Rp)
    (hαp : ∀ H, αp.app H = adjunctionTensorMapSnd ap (Functor.uncurry.obj FC)
      (Functor.uncurry.obj FD) μp H (Ri.obj Z))
    (αi : FD.flip.obj (Ri.obj Z) ⟶ Li ⋙ FF.flip.obj Z ⋙ Ri)
    (hαi : ∀ H, αi.app H = adjunctionTensorMapSnd ai (Functor.uncurry.obj FD)
      (Functor.uncurry.obj FF) μi H Z)
    (αq : FC.flip.obj (Rq.obj Z) ⟶ Lq ⋙ FF.flip.obj Z ⋙ Rq)
    (hαq : ∀ H, αq.app H = adjunctionTensorMapSnd aq (Functor.uncurry.obj FC)
      (Functor.uncurry.obj FF) μq H Z) :
    FC.flip.map ((conjugateEquiv (ap.comp ai) aq γ.inv).app Z) ≫ αq =
      αp ≫ Functor.whiskerRight (Functor.whiskerLeft Lp αi ≫
          Functor.whiskerRight γ.hom (FF.flip.obj Z ⋙ Ri)) Rp ≫
        Functor.whiskerLeft (Lq ⋙ FF.flip.obj Z) (conjugateEquiv (ap.comp ai) aq γ.inv) := by
  ext H
  have h := adjunctionTensorMapSnd_comp_conjugateEquiv ap ai aq γ (Functor.uncurry.obj FC)
    (Functor.uncurry.obj FD) (Functor.uncurry.obj FF) μp μi μq hμ H Z
  simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc] at h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.flip_map_app, Functor.comp_obj, Functor.flip_obj_obj,
    Functor.map_comp, Category.assoc, hαp, hαi, hαq]
  exact h

end Stacks.ProjectionFormula

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **`Rf_* ⋙ Rg_* ⟶ R(f ≫ g)_*`**: the conjugate, under the composite adjunction
`Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*` and `L(f ≫ g)^* ⊣ R(f ≫ g)_*`, of the inverse of the composition
isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*`. -/
def smallEtaleDerivedPushforwardCompConjugate :=
  conjugateEquiv ((smallEtaleDerivedModuleAdjunction B S hS g).comp
      (smallEtaleDerivedModuleAdjunction B S hS f))
    (smallEtaleDerivedModuleAdjunction B S hS (f ≫ g))
    (smallEtaleDerivedModulePullbackCompIso B S hS f g).inv

/-- **The projection formula map along a composite of algebraic spaces.** For `K ∈ D(𝒪_Z)` and
`W ∈ D(𝒪_X)`, `K ⊗^𝐋 c_W` followed by the projection formula map of `f ≫ g` is the projection
formula map of `g` at `(K, Rf_*W)`, then `Rg_*` of that of `f` at `(Lg^*K, W)` and of the
composition isomorphism in the first factor, then `c`, where `c` is
`smallEtaleDerivedPushforwardCompConjugate`. -/
theorem smallEtaleProjectionFormulaMapSnd_comp
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (W : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    ((smallEtaleDerivedTensor B S hS Z).obj K).map
        ((smallEtaleDerivedPushforwardCompConjugate f g).app W) ≫
      smallEtaleProjectionFormulaMapSnd (f ≫ g) K W =
    smallEtaleProjectionFormulaMapSnd g K
        ((Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS f)).obj W) ≫
      (Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS g)).map
        (smallEtaleProjectionFormulaMapSnd f
            ((smallEtaleDerivedModulePullback B S hS g).obj K) W ≫
          (Stacks.Cohomology.DerivedPushforward.derivedPushforward
            (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS _)
            (smallEtaleRingedToposHom B S hS f)).map
            (((smallEtaleDerivedTensor B S hS X).flip.obj W).map
              ((smallEtaleDerivedModulePullbackCompIso B S hS f g).hom.app K))) ≫
      (smallEtaleDerivedPushforwardCompConjugate f g).app
        (((smallEtaleDerivedTensor B S hS X).obj
          ((smallEtaleDerivedModulePullback B S hS (f ≫ g)).obj K)).obj W) := by
  have h := Stacks.ProjectionFormula.adjunctionTensorMapSnd_comp_conjugateEquiv
    (smallEtaleDerivedModuleAdjunction B S hS g) (smallEtaleDerivedModuleAdjunction B S hS f)
    (smallEtaleDerivedModuleAdjunction B S hS (f ≫ g))
    (smallEtaleDerivedModulePullbackCompIso B S hS f g)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Z))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleDerivedPullbackTensorIso g).hom (smallEtaleDerivedPullbackTensorIso f).hom
    (smallEtaleDerivedPullbackTensorIso (f ≫ g)).hom
    (fun H G => NatTrans.congr_app (smallEtaleDerivedPullbackTensorIso_comp f g) (H, G)) K W
  simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, Category.comp_id] at h
  exact h

/-- **`smallEtaleProjectionFormulaMapSnd_comp` as an equality of natural transformations** in the
first factor `K`, for a fixed `W ∈ D(𝒪_X)`. -/
theorem smallEtaleProjectionFormulaSndNatTrans_comp
    (W : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedTensor B S hS Z).flip.map
        ((smallEtaleDerivedPushforwardCompConjugate f g).app W) ≫
      smallEtaleProjectionFormulaSndNatTrans (f ≫ g) W =
    smallEtaleProjectionFormulaSndNatTrans g
        ((derivedModulePushforward B S hS f).obj W) ≫
      Functor.whiskerRight
        (Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS g)
            (smallEtaleProjectionFormulaSndNatTrans f W) ≫
          Functor.whiskerRight (smallEtaleDerivedModulePullbackCompIso B S hS f g).hom
            ((smallEtaleDerivedTensor B S hS X).flip.obj W ⋙
              derivedModulePushforward B S hS f))
        (derivedModulePushforward B S hS g) ≫
      Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS (f ≫ g) ⋙
          (smallEtaleDerivedTensor B S hS X).flip.obj W)
        (smallEtaleDerivedPushforwardCompConjugate f g) :=
  Stacks.ProjectionFormula.adjunctionTensorMapSnd_comp_conjugateEquiv_natTrans
    (smallEtaleDerivedModuleAdjunction B S hS g) (smallEtaleDerivedModuleAdjunction B S hS f)
    (smallEtaleDerivedModuleAdjunction B S hS (f ≫ g))
    (smallEtaleDerivedModulePullbackCompIso B S hS f g)
    (smallEtaleDerivedTensor B S hS Z) (smallEtaleDerivedTensor B S hS Y)
    (smallEtaleDerivedTensor B S hS X)
    (smallEtaleDerivedPullbackTensorIso g).hom (smallEtaleDerivedPullbackTensorIso f).hom
    (smallEtaleDerivedPullbackTensorIso (f ≫ g)).hom
    (fun H G => NatTrans.congr_app (smallEtaleDerivedPullbackTensorIso_comp f g) (H, G)) W
    _ (fun _ => rfl) _ (fun _ => rfl) _ (fun _ => rfl)

/-- **The Snd projection formula is natural in its second argument**: for `u : W₁ ⟶ W₂` in
`D(𝒪_X)`, `- ⊗^𝐋 Rf_*u` followed by the projection formula at `W₂` is the projection formula at
`W₁` followed by `Rf_*(Lf^*(-) ⊗^𝐋 u)`. -/
theorem smallEtaleProjectionFormulaSndNatTrans_naturality {W₁ W₂ :
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))} (u : W₁ ⟶ W₂) :
    (smallEtaleDerivedTensor B S hS Y).flip.map ((derivedModulePushforward B S hS f).map u) ≫
        smallEtaleProjectionFormulaSndNatTrans f W₂ =
      smallEtaleProjectionFormulaSndNatTrans f W₁ ≫
        Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS f)
          (Functor.whiskerRight ((smallEtaleDerivedTensor B S hS X).flip.map u)
            (derivedModulePushforward B S hS f)) := by
  refine NatTrans.ext (funext fun E => ?_)
  have h := Stacks.ProjectionFormula.adjunctionTensorMapSnd_natural
    (smallEtaleDerivedModuleAdjunction B S hS f)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleDerivedPullbackTensorIso f).hom (𝟙 E) u
  simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h
  exact h

/-- **`smallEtaleProjectionFormulaSndNatTrans_comp` along an equation** `f ≫ g = q`, with the
comparison `Rf_* ⋙ Rg_* ⟶ Rq_*` the conjugate of the inverse of `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^* = Lq^*`.
-/
theorem smallEtaleProjectionFormulaSndNatTrans_comp_of_eq (q : X ⟶ Z) (hq : f ≫ g = q)
    (W : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedTensor B S hS Z).flip.map
        ((conjugateEquiv ((smallEtaleDerivedModuleAdjunction B S hS g).comp
            (smallEtaleDerivedModuleAdjunction B S hS f))
          (smallEtaleDerivedModuleAdjunction B S hS q)
          (smallEtaleDerivedModulePullbackCompIso B S hS f g ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS hq).inv).app W) ≫
      smallEtaleProjectionFormulaSndNatTrans q W =
    smallEtaleProjectionFormulaSndNatTrans g
        ((derivedModulePushforward B S hS f).obj W) ≫
      Functor.whiskerRight
        (Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS g)
            (smallEtaleProjectionFormulaSndNatTrans f W) ≫
          Functor.whiskerRight (smallEtaleDerivedModulePullbackCompIso B S hS f g ≪≫
              smallEtaleDerivedModulePullbackCongr B S hS hq).hom
            ((smallEtaleDerivedTensor B S hS X).flip.obj W ⋙
              derivedModulePushforward B S hS f))
        (derivedModulePushforward B S hS g) ≫
      Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS q ⋙
          (smallEtaleDerivedTensor B S hS X).flip.obj W)
        (conjugateEquiv ((smallEtaleDerivedModuleAdjunction B S hS g).comp
            (smallEtaleDerivedModuleAdjunction B S hS f))
          (smallEtaleDerivedModuleAdjunction B S hS q)
          (smallEtaleDerivedModulePullbackCompIso B S hS f g ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS hq).inv) := by
  subst hq
  have hr : smallEtaleDerivedModulePullbackCompIso B S hS f g ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS (rfl : f ≫ g = f ≫ g) =
        smallEtaleDerivedModulePullbackCompIso B S hS f g := Iso.trans_refl _
  rw [hr]
  exact smallEtaleProjectionFormulaSndNatTrans_comp f g W

end AlgebraicGeometry.Space

end

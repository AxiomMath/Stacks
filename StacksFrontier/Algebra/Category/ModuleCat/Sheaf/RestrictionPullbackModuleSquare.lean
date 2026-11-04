module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesComp
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.ModulePushforwardLocalization

/-!
# Inverse images of sheaves of modules along a square with restrictions

Let `Φ'` and `Φ` be finite-product-preserving functors of categories of sheaves of sets, and
`p₁`, `p₂` continuous functors of sites, with an isomorphism `ε : Φ' ⋙ p₂^* ≅ p₁^* ⋙ Φ`. Let
`a : R ⟶ Φ'_* O` and `b : p₂^* R ⟶ Φ_* (p₁^* O)` be maps of sheaves of rings which `ε`
identifies on underlying sheaves of sets. This file shows that the two composites

`p₂^* ∘ a^* ∘ Φ'_*` and `b^* ∘ Φ_* ∘ p₁^*`

of inverse images of sheaves of modules (Stacks 03D2), restrictions along `p₁`, `p₂` and
restrictions of scalars are isomorphic, by `ε` on underlying sheaves of sets.

## Main definitions

* `Stacks.Sheaves.ToposPullback.restrictionPullbackModuleSquareIso`: the isomorphism.

## Implementation notes

The additivity and the linearity of `ε` on sections are the naturality of the transported
operations (`CategoryTheory.Sheaf.moduleAddObj_naturality`), once the operations on both
composites are read as the operations of the original module transported along
`Φ' ⋙ p₂^*` and `p₁^* ⋙ Φ`.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.ToposPullback

universe ww v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {D₁ : Type u₃} [Category.{v₃} D₁] {D₂ : Type u₄} [Category.{v₄} D₂]
  {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
  {K₁ : GrothendieckTopology D₁} {K₂ : GrothendieckTopology D₂}
  [J₁.HasSheafCompose (forget RingCat.{ww})] [J₂.HasSheafCompose (forget RingCat.{ww})]
  [K₁.HasSheafCompose (forget RingCat.{ww})] [K₂.HasSheafCompose (forget RingCat.{ww})]
  [J₁.HasSheafCompose (forget AddCommGrpCat.{ww})] [J₂.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K₁.HasSheafCompose (forget AddCommGrpCat.{ww})] [K₂.HasSheafCompose (forget AddCommGrpCat.{ww})]
  {Φ' : Sheaf J₁ (Type ww) ⥤ Sheaf J₂ (Type ww)} [PreservesFiniteProducts Φ']
  {Φ : Sheaf K₁ (Type ww) ⥤ Sheaf K₂ (Type ww)} [PreservesFiniteProducts Φ]
  {p₁ : D₁ ⥤ C₁} [p₁.IsContinuous K₁ J₁] {p₂ : D₂ ⥤ C₂} [p₂.IsContinuous K₂ J₂]
  (ε : Φ' ⋙ p₂.sheafPushforwardContinuous (Type ww) K₂ J₂ ≅
    p₁.sheafPushforwardContinuous (Type ww) K₁ J₁ ⋙ Φ)
  {O : Sheaf J₁ RingCat.{ww}} {R : Sheaf J₂ RingCat.{ww}}
  (a : R ⟶ pullbackRingSheaf J₂ Φ' O)
  (b : (p₂.sheafPushforwardContinuous RingCat.{ww} K₂ J₂).obj R ⟶
    pullbackRingSheaf K₂ Φ ((p₁.sheafPushforwardContinuous RingCat.{ww} K₁ J₁).obj O))
  (hab : (p₂.sheafPushforwardContinuous (Type ww) K₂ J₂).map
      ((sheafCompose J₂ (forget RingCat.{ww})).map a) ≫ ε.hom.app (Sheaf.ringSheaf O) =
    (sheafCompose K₂ (forget RingCat.{ww})).map b)

/-- The source composite `p₂^* ∘ a^* ∘ Φ'_*`. -/
noncomputable abbrev restrictionPullbackModuleSquareLeft :
    SheafOfModules.{ww} O ⥤
      SheafOfModules.{ww} ((p₂.sheafPushforwardContinuous RingCat.{ww} K₂ J₂).obj R) :=
  pullbackModuleFunctor J₂ Φ' O ⋙ SheafOfModules.restrictScalars a ⋙
    restrictionModules K₂ J₂ p₂ R

/-- The target composite `b^* ∘ Φ_* ∘ p₁^*`. -/
noncomputable abbrev restrictionPullbackModuleSquareRight :
    SheafOfModules.{ww} O ⥤
      SheafOfModules.{ww} ((p₂.sheafPushforwardContinuous RingCat.{ww} K₂ J₂).obj R) :=
  restrictionModules K₁ J₁ p₁ O ⋙
    pullbackModuleFunctor K₂ Φ ((p₁.sheafPushforwardContinuous RingCat.{ww} K₁ J₁).obj O) ⋙
    SheafOfModules.restrictScalars b

include hab in
/-- The comparison on one sheaf of modules: `ε` on underlying sheaves of sets. -/
noncomputable def restrictionPullbackModuleSquareHom (M : SheafOfModules.{ww} O) :
    (restrictionPullbackModuleSquareLeft a).obj M ⟶
      (restrictionPullbackModuleSquareRight b).obj M :=
  ofSheafHom (ε.hom.app (Sheaf.moduleSheaf O M))
    (fun V x y ↦ by
      have hl : x + y = Sheaf.moduleAddObj O M
          (Φ' ⋙ p₂.sheafPushforwardContinuous (Type ww) K₂ J₂ ⋙ Sheaf.sectionsFunctor K₂ V)
          x y :=
        (Sheaf.sectionsFunctor_map_moduleAddHom _ _ V x y).symm.trans
          ((moduleAddObj_restrictionModules K₂ J₂ p₂ R _ (Sheaf.sectionsFunctor K₂ V) x y).trans
            (moduleAddObj_pullbackModuleObj J₂ Φ' O M
              (p₂.sheafPushforwardContinuous (Type ww) K₂ J₂ ⋙ Sheaf.sectionsFunctor K₂ V) x y))
      have hr : ∀ x' y' : (Sheaf.sectionsFunctor K₂ V).obj (Sheaf.moduleSheaf _
          ((restrictionPullbackModuleSquareRight b).obj M)),
          x' + y' = Sheaf.moduleAddObj O M
            (p₁.sheafPushforwardContinuous (Type ww) K₁ J₁ ⋙ Φ ⋙ Sheaf.sectionsFunctor K₂ V)
            x' y' := fun x' y' ↦
        (Sheaf.sectionsFunctor_map_moduleAddHom _ _ V x' y').symm.trans
          ((moduleAddObj_pullbackModuleObj K₂ Φ _ _ (Sheaf.sectionsFunctor K₂ V) x' y').trans
            (moduleAddObj_restrictionModules K₁ J₁ p₁ O M
              (Φ ⋙ Sheaf.sectionsFunctor K₂ V) x' y'))
      rw [hl, hr]
      exact Sheaf.moduleAddObj_naturality O M
        (Functor.whiskerRight ε.hom (Sheaf.sectionsFunctor K₂ V)) x y)
    (fun V r x ↦ by
      have hl : r • x = Sheaf.moduleSMulObj O M
          (Φ' ⋙ p₂.sheafPushforwardContinuous (Type ww) K₂ J₂ ⋙ Sheaf.sectionsFunctor K₂ V)
          ((p₂.sheafPushforwardContinuous (Type ww) K₂ J₂ ⋙ Sheaf.sectionsFunctor K₂ V).map
            ((sheafCompose J₂ (forget RingCat.{ww})).map a) r) x :=
        (Sheaf.sectionsFunctor_map_moduleSMulHom _ _ V r x).symm.trans
          ((moduleSMulObj_restrictionModules K₂ J₂ p₂ R _ (Sheaf.sectionsFunctor K₂ V) r x).trans
            ((moduleSMulObj_restrictScalars a _
              (p₂.sheafPushforwardContinuous (Type ww) K₂ J₂ ⋙ Sheaf.sectionsFunctor K₂ V)
                r x).trans
              (moduleSMulObj_pullbackModuleObj J₂ Φ' O M
                (p₂.sheafPushforwardContinuous (Type ww) K₂ J₂ ⋙ Sheaf.sectionsFunctor K₂ V)
                _ x)))
      have hr : ∀ x' : (Sheaf.sectionsFunctor K₂ V).obj (Sheaf.moduleSheaf _
          ((restrictionPullbackModuleSquareRight b).obj M)),
          r • x' = Sheaf.moduleSMulObj O M
            (p₁.sheafPushforwardContinuous (Type ww) K₁ J₁ ⋙ Φ ⋙ Sheaf.sectionsFunctor K₂ V)
            ((Sheaf.sectionsFunctor K₂ V).map ((sheafCompose K₂ (forget RingCat.{ww})).map b) r)
            x' := fun x' ↦
        (Sheaf.sectionsFunctor_map_moduleSMulHom _ _ V r x').symm.trans
          ((moduleSMulObj_restrictScalars b _ (Sheaf.sectionsFunctor K₂ V) r x').trans
            ((moduleSMulObj_pullbackModuleObj K₂ Φ _ _ (Sheaf.sectionsFunctor K₂ V) _ x').trans
              (moduleSMulObj_restrictionModules K₁ J₁ p₁ O M
                (Φ ⋙ Sheaf.sectionsFunctor K₂ V) _ x')))
      rw [hl, hr, ← hab]
      exact Sheaf.moduleSMulObj_naturality O M
        (Functor.whiskerRight ε.hom (Sheaf.sectionsFunctor K₂ V)) _ x)

/-- On underlying sheaves of sets, `restrictionPullbackModuleSquareHom ε a b hab M` is the
component of `ε` at the underlying sheaf of `M`. -/
@[simp]
lemma moduleSheafFunctor_map_restrictionPullbackModuleSquareHom (M : SheafOfModules.{ww} O) :
    (Sheaf.moduleSheafFunctor _).map (restrictionPullbackModuleSquareHom ε a b hab M) =
      ε.hom.app (Sheaf.moduleSheaf O M) := rfl

/-- The comparison `restrictionPullbackModuleSquareHom ε a b hab M` is an isomorphism. -/
instance isIso_restrictionPullbackModuleSquareHom (M : SheafOfModules.{ww} O) :
    IsIso (restrictionPullbackModuleSquareHom ε a b hab M) := by
  have : IsIso ((Sheaf.moduleSheafFunctor _).map
      (restrictionPullbackModuleSquareHom ε a b hab M)) := by
    rw [moduleSheafFunctor_map_restrictionPullbackModuleSquareHom]
    exact (ε.app (Sheaf.moduleSheaf O M)).isIso_hom
  exact isIso_of_reflects_iso _ (Sheaf.moduleSheafFunctor _)

/-- **The square of inverse images of sheaves of modules.** If `ε : Φ' ⋙ p₂^* ≅ p₁^* ⋙ Φ`
carries the structure map `a` to the structure map `b` on underlying sheaves of sets, then
`p₂^* ∘ a^* ∘ Φ'_* ≅ b^* ∘ Φ_* ∘ p₁^*`, by `ε` on underlying sheaves of sets. -/
noncomputable def restrictionPullbackModuleSquareIso :
    restrictionPullbackModuleSquareLeft (K₂ := K₂) (p₂ := p₂) a ≅
      restrictionPullbackModuleSquareRight (J₁ := J₁) (p₁ := p₁) b :=
  NatIso.ofComponents (fun M ↦ asIso (restrictionPullbackModuleSquareHom ε a b hab M))
    (fun {_M _M'} φ ↦ hom_ext_moduleSheafFunctor (by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      exact ε.hom.naturality ((Sheaf.moduleSheafFunctor O).map φ)))

/-- On underlying sheaves of sets, the component of `restrictionPullbackModuleSquareIso` at `M`
is the component of `ε` at the underlying sheaf of `M`. -/
@[simp]
lemma moduleSheafFunctor_map_restrictionPullbackModuleSquareIso_hom_app
    (M : SheafOfModules.{ww} O) :
    (Sheaf.moduleSheafFunctor _).map ((restrictionPullbackModuleSquareIso ε a b hab).hom.app M) =
      ε.hom.app (Sheaf.moduleSheaf O M) := rfl

end Stacks.Sheaves.ToposPullback

end

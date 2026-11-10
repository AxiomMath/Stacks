module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantModuleSheafSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem

/-!
# Direct images of sheaves of locally constant maps

Let `M` be a `Λ`-module. On the small étale site of a scheme `Y` the constant sheaf of `Λ`-modules
with value `M` is the sheaf `𝓛_Y(M)` of locally constant `M`-valued maps
(`AlgebraicGeometry.smallEtaleConstantSheafIsoLocallyConstantMapsModule`). For a morphism
`f : Y ⟶ X` the direct image `f_* 𝓛_Y(M)` therefore has as its sections over an étale `X`-scheme
`W` the locally constant `M`-valued maps on `W ×_X Y`. This file records the comparison maps
between such direct images: for a morphism `h : Y' ⟶ Y` over `X`, pulling locally constant maps
back along `W ×_X Y' ⟶ W ×_X Y` is a morphism `f_* 𝓛_Y(M) ⟶ f'_* 𝓛_{Y'}(M)` of sheaves of
`Λ`-modules on `X_étale`.

## Main definitions

* `Stacks.EtaleCohomology.locallyConstantPushforwardMap` — the comparison map attached to a
  morphism over `X`.

## Main results

* `Stacks.EtaleCohomology.locallyConstantPushforwardMap_comp` — the comparison maps compose.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] (M : Type (max (u + 1) r)) [AddCommGroup M] [Module Λ M]

/-- For a morphism `h : Y' ⟶ Y` over `X`, the morphisms `W ×_X Y' ⟶ W ×_X Y` induced on the base
changes of the étale `X`-schemes `W`, as a natural transformation of functors to schemes. -/
def pullbackMapNatTrans {X Y Y' : Scheme.{u}} (f : Y ⟶ X) (f' : Y' ⟶ X) (h : Y' ⟶ Y)
    (hh : h ≫ f = f') :
    smallEtaleBaseChange f' ⋙ Scheme.Etale.forget Y' ⋙ Over.forget Y' ⟶
      smallEtaleBaseChange f ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y where
  app W := pullback.map W.hom f' W.hom f (𝟙 _) h (𝟙 _) (by simp) (by simp [hh])
  naturality W₁ W₂ g := by
    have h₁ : pullback.fst W₁.hom f' ≫ g.left ≫ W₂.hom = pullback.snd W₁.hom f' ≫ f' := by
      rw [MorphismProperty.Over.w g, pullback.condition]
    have h₂ : pullback.fst W₁.hom f ≫ g.left ≫ W₂.hom = pullback.snd W₁.hom f ≫ f := by
      rw [MorphismProperty.Over.w g, pullback.condition]
    change pullback.lift (f := W₂.hom) (g := f') (pullback.fst W₁.hom f' ≫ g.left)
        (pullback.snd W₁.hom f') (by rw [Category.assoc, h₁]) ≫
        pullback.map W₂.hom f' W₂.hom f (𝟙 _) h (𝟙 _) (by simp) (by simp [hh]) =
      pullback.map W₁.hom f' W₁.hom f (𝟙 _) h (𝟙 _) (by simp) (by simp [hh]) ≫
        pullback.lift (f := W₂.hom) (g := f) (pullback.fst W₁.hom f ≫ g.left)
          (pullback.snd W₁.hom f) (by rw [Category.assoc, h₂])
    apply pullback.hom_ext
    · simp only [Category.assoc, Category.comp_id, pullback.lift_fst, pullback.lift_fst_assoc,
        pullback.map]
    · simp only [Category.assoc, Category.comp_id, pullback.lift_snd, pullback.lift_snd_assoc,
        pullback.map]

/-- The comparison of the direct images of the sheaves of locally constant `M`-valued maps along a
morphism `h : Y' ⟶ Y` over `X`: over an étale `X`-scheme `W` it pulls a locally constant map on
`W ×_X Y` back along the induced morphism `W ×_X Y' ⟶ W ×_X Y`. -/
def locallyConstantPushforwardMap {X Y Y' : Scheme.{u}} (f : Y ⟶ X) (f' : Y' ⟶ X)
    (h : Y' ⟶ Y) (hh : h ≫ f = f') :
    (etaleModuleDirectImage.{u, r} Λ f).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, r} Λ Y M) ⟶
      (etaleModuleDirectImage.{u, r} Λ f').obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, r} Λ Y' M) where
  hom := Functor.whiskerRight (NatTrans.op (pullbackMapNatTrans f f' h hh))
    (locallyConstantMapsModule.{u, max (u + 1) r} Λ M)

/-- The comparison map on sections over `W`. -/
theorem locallyConstantPushforwardMap_hom_app {X Y Y' : Scheme.{u}} (f : Y ⟶ X) (f' : Y' ⟶ X)
    (h : Y' ⟶ Y) (hh : h ≫ f = f') (W : X.Etale) :
    (locallyConstantPushforwardMap Λ M f f' h hh).hom.app (op W) =
      ModuleCat.ofHom (LocallyConstant.comapₗ Λ
        (pullback.map W.hom f' W.hom f (𝟙 _) h (𝟙 _) (by simp) (by simp [hh])).base.hom) :=
  rfl

/-- Base changes of a composite of morphisms over `X` along `w : W ⟶ X` compose. -/
theorem pullback_map_comp_pullback_map {X Y Y' Y'' W : Scheme.{u}} (w : W ⟶ X) (f : Y ⟶ X)
    (f' : Y' ⟶ X) (f'' : Y'' ⟶ X) (h : Y' ⟶ Y) (hh : h ≫ f = f') (h' : Y'' ⟶ Y')
    (hh' : h' ≫ f' = f'') :
    pullback.map w f'' w f' (𝟙 _) h' (𝟙 _) (by simp) (by simp [hh']) ≫
        pullback.map w f' w f (𝟙 _) h (𝟙 _) (by simp) (by simp [hh]) =
      pullback.map w f'' w f (𝟙 _) (h' ≫ h) (𝟙 _) (by simp)
        (by simp [hh, hh']) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Category.comp_id, pullback.lift_fst, pullback.map]
  · simp only [Category.assoc, Category.comp_id, pullback.lift_snd, pullback.lift_snd_assoc,
      pullback.map]

/-- The natural transformations of `pullbackMapNatTrans` compose. -/
theorem pullbackMapNatTrans_comp {X Y Y' Y'' : Scheme.{u}} (f : Y ⟶ X) (f' : Y' ⟶ X)
    (f'' : Y'' ⟶ X) (h : Y' ⟶ Y) (hh : h ≫ f = f') (h' : Y'' ⟶ Y') (hh' : h' ≫ f' = f'') :
    pullbackMapNatTrans f' f'' h' hh' ≫ pullbackMapNatTrans f f' h hh =
      pullbackMapNatTrans f f'' (h' ≫ h) (by rw [Category.assoc, hh, hh']) := by
  ext W
  exact pullback_map_comp_pullback_map W.hom f f' f'' h hh h' hh'

/-- The comparison maps compose. -/
theorem locallyConstantPushforwardMap_comp {X Y Y' Y'' : Scheme.{u}} (f : Y ⟶ X) (f' : Y' ⟶ X)
    (f'' : Y'' ⟶ X) (h : Y' ⟶ Y) (hh : h ≫ f = f') (h' : Y'' ⟶ Y') (hh' : h' ≫ f' = f'') :
    locallyConstantPushforwardMap Λ M f f' h hh ≫ locallyConstantPushforwardMap Λ M f' f'' h' hh' =
      locallyConstantPushforwardMap Λ M f f'' (h' ≫ h) (by rw [Category.assoc, hh, hh']) := by
  apply Sheaf.hom_ext
  change Functor.whiskerRight _ _ ≫ Functor.whiskerRight _ _ = Functor.whiskerRight _ _
  rw [← Functor.whiskerRight_comp, ← NatTrans.op_comp, pullbackMapNatTrans_comp]

/-- For a morphism `g : Y' ⟶ Y`, the first projections `W ×_Y Y' ⟶ W` of the base changes of the
étale `Y`-schemes `W`, as a natural transformation of functors to schemes. -/
def pullbackFstNatTrans {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    smallEtaleBaseChange g ⋙ Scheme.Etale.forget Y' ⋙ Over.forget Y' ⟶
      Scheme.Etale.forget Y ⋙ Over.forget Y where
  app W := pullback.fst W.hom g
  naturality _ _ φ := smallEtaleBaseChange_map_left_fst g φ

/-- The comparison `𝓛_Y(M) ⟶ g_* 𝓛_{Y'}(M)` for a morphism `g : Y' ⟶ Y`: over an étale
`Y`-scheme `W` it pulls a locally constant map on `W` back to `W ×_Y Y'`. -/
def locallyConstantToDirectImage {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    smallEtaleLocallyConstantMapsModuleSheaf.{u, r} Λ Y M ⟶
      (etaleModuleDirectImage.{u, r} Λ g).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, r} Λ Y' M) where
  hom := Functor.whiskerRight (NatTrans.op (pullbackFstNatTrans g))
    (locallyConstantMapsModule.{u, max (u + 1) r} Λ M)

/-- The comparison `𝓛_Y(M) ⟶ g_* 𝓛_{Y'}(M)` on sections over `W`. -/
theorem locallyConstantToDirectImage_hom_app {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (W : Y.Etale) :
    (locallyConstantToDirectImage Λ M g).hom.app (op W) =
      ModuleCat.ofHom (LocallyConstant.comapₗ Λ (pullback.fst W.hom g).base.hom) :=
  rfl

/-- A morphism of sheaves of modules on a small étale site which is bijective on the sections over
every étale scheme is an isomorphism. -/
theorem isIso_of_bijective_app {X : Scheme.{u}} {F G : EtaleModules.{u, r} Λ X} (φ : F ⟶ G)
    (h : ∀ W : X.Etale, Function.Bijective (φ.hom.app (op W))) : IsIso φ := by
  have : ∀ W : (X.Etale)ᵒᵖ, IsIso (φ.hom.app W) := fun W =>
    (ConcreteCategory.isIso_iff_bijective _).2 (h W.unop)
  have : IsIso ((sheafToPresheaf _ _).map φ) := NatIso.isIso_of_isIso_app φ.hom
  exact isIso_of_reflects_iso φ (sheafToPresheaf _ _)

end Stacks.EtaleCohomology

end

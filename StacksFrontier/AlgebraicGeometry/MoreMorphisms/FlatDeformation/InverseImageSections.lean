module

public import StacksFrontier.AlgebraicGeometry.SheafifyStalk.StalkMap

/-!
# Local sections of the inverse image of a sheaf of rings
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Thickenings.FlatDeformation

attribute [local implicit_reducible] TopCat.Presheaf.stalk

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (F : TopCat.Sheaf CommRingCat.{u} Y)

/-- The unit `F ⟶ f_* f⁻¹ F` on sections over `W`. -/
abbrev pullbackUnitApp (W : Opens Y) :
    F.presheaf.obj (op W) ⟶
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.obj (op ((Opens.map f).obj W)) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app F).hom.app (op W)

/-- The germ at `f x` of a section `σ`, carried to the stalk of `f⁻¹F` at `x`, is the germ of
the image of `σ` under the unit. -/
theorem germ_comp_stalkSheafPullbackIso_inv (W : Opens Y) (x : X) (hx : f x ∈ W) :
    F.presheaf.germ W (f x) hx ≫
        (Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} f F x).inv =
      pullbackUnitApp f F W ≫
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.germ ((Opens.map f).obj W) x
          hx := by
  rw [Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ TopCat.Presheaf.stalkPushforward CommRingCat.{u} f
    ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf x)
    (TopCat.Presheaf.stalkFunctor_map_germ W (f x) hx
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app F).hom)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (pullbackUnitApp f F W ≫ ·)
    (TopCat.Presheaf.stalkPushforward_germ CommRingCat.{u} f _ W x hx)

/-- The germ at `x` of the image of a section `σ` under the unit is the germ of `σ` at `f x`,
read through the identification of stalks. -/
theorem stalkSheafPullbackIso_hom_germ_unit (W : Opens Y) (x : X) (hx : f x ∈ W)
    (σ : F.presheaf.obj (op W)) :
    (Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} f F x).hom
        (((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.germ ((Opens.map f).obj W) x
          hx (pullbackUnitApp f F W σ)) =
      F.presheaf.germ W (f x) hx σ := by
  have h := congr($(germ_comp_stalkSheafPullbackIso_inv f F W x hx) σ)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  rw [← h, ← ConcreteCategory.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

/-- **Every local section of `f⁻¹F` is, near each point, the image of a section of `F` under the
unit `F ⟶ f_* f⁻¹ F`.** -/
theorem exists_eq_pullbackUnitApp (U : Opens X)
    (s : ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.obj (op U)) (x : X)
    (hx : x ∈ U) :
    ∃ (W : Opens Y) (_ : f x ∈ W) (σ : F.presheaf.obj (op W)) (V : Opens X) (_ : x ∈ V)
      (hVU : V ≤ U) (hVW : V ≤ (Opens.map f).obj W),
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.map (homOfLE hVU).op s =
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.map (homOfLE hVW).op
          (pullbackUnitApp f F W σ) := by
  obtain ⟨W, hW, σ, hσ⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf
    ((Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} f F x).hom
      (((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.germ U x hx s))
  have hgerm : ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.germ U x hx s =
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.germ ((Opens.map f).obj W) x
        hW (pullbackUnitApp f F W σ) := by
    apply (Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} f F
      x).commRingCatIsoToRingEquiv.injective
    show (Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} f F x).hom _ =
      (Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} f F x).hom _
    rw [stalkSheafPullbackIso_hom_germ_unit, hσ]
  obtain ⟨V, hxV, i₁, i₂, h⟩ := TopCat.Presheaf.germ_eq _ x hx hW _ _ hgerm
  exact ⟨W, hW, σ, V, hxV, leOfHom i₁, leOfHom i₂, h⟩

/-- The unit commutes with restriction. -/
theorem pullbackUnitApp_restrict {W W' : Opens Y} (h : W' ≤ W) (σ : F.presheaf.obj (op W)) :
    ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.map
        (homOfLE ((Opens.map f).monotone h)).op (pullbackUnitApp f F W σ) =
      pullbackUnitApp f F W' (F.presheaf.map (homOfLE h).op σ) :=
  (congr($((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app
    F).hom.naturality (homOfLE h).op)) σ)).symm

/-- A section of `F` whose image under the unit has zero germ at `x` has zero germ at `f x`. -/
theorem germ_eq_zero_of_germ_pullbackUnitApp (W : Opens Y) (x : X) (hx : f x ∈ W)
    (σ : F.presheaf.obj (op W))
    (h : ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj F).presheaf.germ ((Opens.map f).obj W) x
      hx (pullbackUnitApp f F W σ) = 0) :
    F.presheaf.germ W (f x) hx σ = 0 := by
  rw [← stalkSheafPullbackIso_hom_germ_unit, h, map_zero]

/-- Naturality of a morphism of sheaves of rings, on sections. -/
theorem sheafHom_app_map {Z : TopCat.{u}} {F₁ F₂ : TopCat.Sheaf CommRingCat.{u} Z} (φ : F₁ ⟶ F₂)
    {V W : Opens Z} (h : W ≤ V) (b : F₁.presheaf.obj (op V)) :
    φ.hom.app (op W) (F₁.presheaf.map (homOfLE h).op b) =
      F₂.presheaf.map (homOfLE h).op (φ.hom.app (op V) b) :=
  ConcreteCategory.congr_hom (φ.hom.naturality (homOfLE h).op) b

/-- Two restrictions of a section compose. -/
theorem presheaf_map_map {Z : TopCat.{u}} (F : TopCat.Sheaf CommRingCat.{u} Z) {U V W : Opens Z}
    (h₁ : V ≤ U) (h₂ : W ≤ V) (s : F.presheaf.obj (op U)) :
    F.presheaf.map (homOfLE h₂).op (F.presheaf.map (homOfLE h₁).op s) =
      F.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end Stacks.Thickenings.FlatDeformation

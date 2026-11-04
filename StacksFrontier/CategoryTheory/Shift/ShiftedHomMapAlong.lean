module

public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# Shifted morphisms transported along a functor and two comparison maps

Let `F : C ⥤ D` be a functor commuting with the shifts by an additive monoid `M`. A shifted
morphism `x : X ⟶ Y⟦a⟧` gives `x.map F : F X ⟶ (F Y)⟦a⟧`. Given maps `z : X' ⟶ F X` and
`κ : F Y ⟶ Y'` comparing its source and target with objects of `D`, this file defines the map

`x ↦ z ≫ x.map F ≫ κ⟦a⟧'`

and proves that transporting along `F` and then along `G` is transporting along any functor `H`
with a shift-compatible transformation `H ⟶ F ⋙ G`, and that transporting is compatible with the
composition of shifted morphisms.

## Main definitions

* `CategoryTheory.ShiftedHom.mapAlong`: the map `x ↦ z ≫ x.map F ≫ κ⟦a⟧'`.
* `CategoryTheory.ShiftedHom.mapAlongAddHom`: the same map, as an additive map.
* `CategoryTheory.ShiftedHom.shiftTargetAddEquiv`: the identification of shifted morphisms
  `X ⟶ (Y⟦b⟧)⟦a⟧` with shifted morphisms `X ⟶ Y⟦b + a⟧`.

## Main results

* `CategoryTheory.ShiftedHom.mapAlong_mapAlong`: transporting along `F` and then along `G`.
* `CategoryTheory.ShiftedHom.mapAlong_comp`: transporting a composite of shifted morphisms.
* `CategoryTheory.ShiftedHom.mapAlong_shiftTargetAddEquiv`: transporting is compatible with the
  identification `shiftTargetAddEquiv`.
-/

@[expose] public section

open CategoryTheory Category

namespace CategoryTheory.ShiftedHom

variable {M : Type*} [AddMonoid M] {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasShift C M] [HasShift D M] [HasShift E M]

/-- **A shifted morphism transported along a functor**, with its source and target compared with
given objects: for `z : X' ⟶ F X` and `κ : F Y ⟶ Y'`, the shifted morphism
`z ≫ x.map F ≫ κ⟦a⟧' : X' ⟶ Y'⟦a⟧`. -/
noncomputable def mapAlong (F : C ⥤ D) [F.CommShift M] {X Y : C} {X' Y' : D} (z : X' ⟶ F.obj X)
    (κ : F.obj Y ⟶ Y') {a : M} (x : ShiftedHom X Y a) : ShiftedHom X' Y' a :=
  z ≫ x.map F ≫ κ⟦a⟧'

/-- `mapAlong F z κ x` is `z ≫ F.map x ≫ (F.commShiftIso a).hom.app Y ≫ κ⟦a⟧'`. -/
lemma mapAlong_def (F : C ⥤ D) [F.CommShift M] {X Y : C} {X' Y' : D} (z : X' ⟶ F.obj X)
    (κ : F.obj Y ⟶ Y') {a : M} (x : ShiftedHom X Y a) :
    mapAlong F z κ x = z ≫ F.map x ≫ (F.commShiftIso a).hom.app Y ≫ κ⟦a⟧' := by
  simp [mapAlong, map]

/-- Transporting is natural in the target. -/
lemma mapAlong_comp_shift_map (F : C ⥤ D) [F.CommShift M] {X Y : C} {X' Y' Y'' : D}
    (z : X' ⟶ F.obj X) (κ : F.obj Y ⟶ Y') (g : Y' ⟶ Y'') {a : M} (x : ShiftedHom X Y a) :
    mapAlong F z κ x ≫ g⟦a⟧' = mapAlong F z (κ ≫ g) x := by
  simp [mapAlong]

/-- Transporting is natural in the source of the shifted morphism's target. -/
lemma mapAlong_shift_map (F : C ⥤ D) [F.CommShift M] {X Y Y₁ : C} {X' Y' : D}
    (z : X' ⟶ F.obj X) (g : Y ⟶ Y₁) (κ : F.obj Y₁ ⟶ Y') {a : M} (x : ShiftedHom X Y a) :
    mapAlong F z κ (x ≫ g⟦a⟧') = mapAlong F z (F.map g ≫ κ) x := by
  simp only [mapAlong_def, Functor.map_comp, assoc, Functor.commShiftIso_hom_naturality_assoc]

/-- **Transporting along two functors in succession.** Let `τ : H ⟶ F ⋙ G` be a transformation
compatible with the shifts. Transporting along `F` with `z, κ` and then along `G` with `z', κ'`
is transporting along `H` with any `z''` satisfying `z'' ≫ τ_X = z' ≫ G z`, and with
`τ_Y ≫ G κ ≫ κ'`. -/
lemma mapAlong_mapAlong (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.CommShift M] [G.CommShift M]
    [H.CommShift M] (τ : H ⟶ F ⋙ G) [NatTrans.CommShift τ M] {X Y : C} {X' Y' : D}
    {X'' Y'' : E} (z : X' ⟶ F.obj X) (κ : F.obj Y ⟶ Y') (z' : X'' ⟶ G.obj X')
    (κ' : G.obj Y' ⟶ Y'') (z'' : X'' ⟶ H.obj X) (hz : z'' ≫ τ.app X = z' ≫ G.map z) {a : M}
    (x : ShiftedHom X Y a) :
    mapAlong G z' κ' (mapAlong F z κ x) = mapAlong H z'' (τ.app Y ≫ G.map κ ≫ κ') x := by
  have h₁ : G.map (κ⟦a⟧') ≫ (G.commShiftIso a).hom.app Y' =
      (G.commShiftIso a).hom.app (F.obj Y) ≫ (G.map κ)⟦a⟧' :=
    G.commShiftIso_hom_naturality κ a
  have h₂ := NatTrans.shift_app_comm τ a Y
  have h₃ := τ.naturality x
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map] at h₂ h₃
  simp only [mapAlong_def, Functor.map_comp, assoc]
  rw [reassoc_of% h₁, ← reassoc_of% hz, ← reassoc_of% h₃, ← reassoc_of% h₂]

/-- **Transporting a composite of shifted morphisms.** If `g : Y ⟶ Z⟦b⟧` and `g' : Y' ⟶ Z'⟦b⟧`
are compatible with the comparison maps `κ_Y`, `κ_Z`, then transporting `x.comp g` is composing
the transport of `x` with `g'`. -/
lemma mapAlong_comp (F : C ⥤ D) [F.CommShift M] {X Y Z : C} {X' Y' Z' : D} (z : X' ⟶ F.obj X)
    (κY : F.obj Y ⟶ Y') (κZ : F.obj Z ⟶ Z') {a b c : M} (x : ShiftedHom X Y a)
    (g : ShiftedHom Y Z b) (g' : ShiftedHom Y' Z' b) (hg : g.map F ≫ κZ⟦b⟧' = κY ≫ g')
    (h : b + a = c) :
    mapAlong F z κZ (x.comp g h) = (mapAlong F z κY x).comp g' h := by
  have hκ : ((x.map F).comp (g.map F) h) ≫ κZ⟦c⟧' =
      (x.map F).comp (g.map F ≫ κZ⟦b⟧') h := by
    simp only [comp, assoc, Functor.map_comp]
    congr 2
    exact ((shiftFunctorAdd' D b a c h).inv.naturality κZ).symm
  simp only [mapAlong, map_comp, assoc, hκ, hg]
  simp only [comp, assoc, Functor.map_comp]

section Preadditive

variable [Preadditive C] [Preadditive D] [∀ a : M, (shiftFunctor D a).Additive]

/-- Transporting is additive. -/
@[simp]
lemma mapAlong_add (F : C ⥤ D) [F.CommShift M] [F.Additive] {X Y : C} {X' Y' : D}
    (z : X' ⟶ F.obj X) (κ : F.obj Y ⟶ Y') {a : M} (x y : ShiftedHom X Y a) :
    mapAlong F z κ (x + y) = mapAlong F z κ x + mapAlong F z κ y := by
  simp [mapAlong]

/-- Transporting maps the zero shifted morphism to zero. -/
@[simp]
lemma mapAlong_zero (F : C ⥤ D) [F.CommShift M] [F.Additive] {X Y : C} {X' Y' : D}
    (z : X' ⟶ F.obj X) (κ : F.obj Y ⟶ Y') {a : M} :
    mapAlong F z κ (0 : ShiftedHom X Y a) = 0 := by
  simp [mapAlong]

/-- `CategoryTheory.ShiftedHom.mapAlong` as an additive map. -/
noncomputable def mapAlongAddHom (F : C ⥤ D) [F.CommShift M] [F.Additive] {X Y : C} {X' Y' : D}
    (z : X' ⟶ F.obj X) (κ : F.obj Y ⟶ Y') (a : M) :
    ShiftedHom X Y a →+ ShiftedHom X' Y' a where
  toFun := mapAlong F z κ
  map_zero' := mapAlong_zero F z κ
  map_add' := mapAlong_add F z κ

/-- `mapAlongAddHom F z κ a` applied to `x` is `mapAlong F z κ x`. -/
@[simp]
lemma mapAlongAddHom_apply (F : C ⥤ D) [F.CommShift M] [F.Additive] {X Y : C} {X' Y' : D}
    (z : X' ⟶ F.obj X) (κ : F.obj Y ⟶ Y') (a : M) (x : ShiftedHom X Y a) :
    mapAlongAddHom F z κ a x = mapAlong F z κ x := rfl

end Preadditive

section ShiftTarget

variable [Preadditive C] [∀ a : M, (shiftFunctor C a).Additive]

/-- Shifted morphisms `X ⟶ (Y⟦b⟧)⟦a⟧` are shifted morphisms `X ⟶ Y⟦c⟧` for `b + a = c`: the
composition with the unit shifted morphism `𝟙 (Y⟦b⟧)` of degree `b`. -/
noncomputable def shiftTargetAddEquiv (X Y : C) (a b c : M) (h : b + a = c) :
    ShiftedHom X (Y⟦b⟧) a ≃+ ShiftedHom X Y c where
  toFun x := x.comp (𝟙 (Y⟦b⟧) : ShiftedHom (Y⟦b⟧) Y b) h
  invFun y := y ≫ (shiftFunctorAdd' C b a c h).hom.app Y
  left_inv x := by simp [comp]
  right_inv y := by simp [comp]
  map_add' x y := by simp [comp]

/-- `shiftTargetAddEquiv X Y a b c h x` is the composite of `x` with the unit shifted morphism
`𝟙 (Y⟦b⟧)` of degree `b`. -/
lemma shiftTargetAddEquiv_apply (X Y : C) (a b c : M) (h : b + a = c)
    (x : ShiftedHom X (Y⟦b⟧) a) :
    shiftTargetAddEquiv X Y a b c h x = x.comp (𝟙 (Y⟦b⟧) : ShiftedHom (Y⟦b⟧) Y b) h := rfl

/-- **Transporting is compatible with `shiftTargetAddEquiv`.** For a comparison `κ : F Y ⟶ Y'`,
the comparison of `F (Y⟦b⟧)` with `Y'⟦b⟧` is the commutation of `F` with the shift followed by
`κ⟦b⟧'`. -/
lemma mapAlong_shiftTargetAddEquiv (F : C ⥤ D) [F.CommShift M] [Preadditive D]
    [∀ a : M, (shiftFunctor D a).Additive] {X Y : C} {X' Y' : D}
    (z : X' ⟶ F.obj X) (κ : F.obj Y ⟶ Y') (a b c : M) (h : b + a = c)
    (x : ShiftedHom X (Y⟦b⟧) a) :
    mapAlong F z κ (shiftTargetAddEquiv X Y a b c h x) =
      shiftTargetAddEquiv X' Y' a b c h
        (mapAlong F z ((F.commShiftIso b).hom.app Y ≫ κ⟦b⟧') x) := by
  rw [shiftTargetAddEquiv_apply, shiftTargetAddEquiv_apply]
  refine mapAlong_comp F z _ κ x _ _ ?_ h
  simp [map]

end ShiftTarget

end CategoryTheory.ShiftedHom

end

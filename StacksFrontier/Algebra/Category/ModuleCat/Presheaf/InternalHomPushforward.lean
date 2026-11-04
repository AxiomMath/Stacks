module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom

/-!
# Restriction of the internal Hom along a functor

Let `G : C ⥤ D` be a functor, `O` a presheaf of commutative rings on `D`, `O'` one on `C` and
`φ : O' ⟶ G^*O` a morphism of presheaves of rings. Restriction along `G` (with scalars restricted
along `φ`) carries a morphism `F|_{G(V)} ⟶ F'|_{G(V)}` of modules on the slice `D/G(V)` to a
morphism of the restrictions on the slice `C/V`, by restriction along `Over.post G`. This gives
the comparison map
`G^*Hom_O(F, F') ⟶ Hom_{O'}(G^*F, G^*F')`
of presheaves of `O'`-modules (Stacks 04TT for the internal Hom, read along a functor of sites).

## Main definitions

* `PresheafOfModules.internalHomPushforwardMap`: the comparison map.

## Main results

* `PresheafOfModules.internalHomPushforwardMap_app_app`: its value on a morphism is that
  morphism evaluated at the image objects.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v₁ u₁ v₂ u₂ w t

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D] (G : C ⥤ D)
  (O : Dᵒᵖ ⥤ CommRingCat.{w}) (O' : Cᵒᵖ ⥤ CommRingCat.{w})
  (φ : Oforget O' ⟶ G.op ⋙ Oforget O)

/-- The ring morphism on the slice at `V` induced by `φ`. -/
def internalHomPushforwardRingHom (V : C) :
    ORestr O' V ⟶ (Over.post G (X := V)).op ⋙ ORestr O (G.obj V) :=
  Functor.whiskerLeft (Over.forget V).op φ

variable (F F' : PresheafOfModules.{t} (Oforget O))

/-- The comparison map on sections over `V`: restriction along `Over.post G`. -/
def internalHomPushforwardApp (V : C)
    (α : (restrFun O (G.obj V)).obj F ⟶ (restrFun O (G.obj V)).obj F') :
    (restrFun O' V).obj ((pushforward φ).obj F) ⟶ (restrFun O' V).obj ((pushforward φ).obj F') :=
  (pushforward (F := Over.post G (X := V)) (internalHomPushforwardRingHom G O O' φ V)).map α

/-- The value of `internalHomPushforwardApp` at an object `W` of the slice at `V` is the value of
`α` at the image of `W` under `Over.post G`. -/
@[simp]
theorem internalHomPushforwardApp_app (V : C)
    (α : (restrFun O (G.obj V)).obj F ⟶ (restrFun O (G.obj V)).obj F') (W : (Over V)ᵒᵖ)
    (x : F.obj (op (G.obj W.unop.left))) :
    (internalHomPushforwardApp G O O' φ F F' V α).app W x =
      α.app (op ((Over.post G).obj W.unop)) x :=
  rfl

/-- A morphism of restrictions to a slice takes the same value at two equal objects of the slice
with the same underlying object. -/
theorem app_over_mk_congr {U : D} {M M' : PresheafOfModules.{t} (Oforget O)}
    (α : (restrFun O U).obj M ⟶ (restrFun O U).obj M') {Y : D} {f₁ f₂ : Y ⟶ U}
    (h : f₁ = f₂) (x : M.obj (op Y)) :
    α.app (op (Over.mk f₁)) x = α.app (op (Over.mk f₂)) x := by
  subst h
  rfl

/-- The comparison map on sections over `V`, as a linear map. -/
def internalHomPushforwardLinearMap (V : Cᵒᵖ) :
    ((pushforward φ).obj (internalHom O F F')).obj V →ₗ[(Oforget O').obj V]
      (internalHom O' ((pushforward φ).obj F) ((pushforward φ).obj F')).obj V where
  toFun α := internalHomPushforwardApp G O O' φ F F' V.unop α
  map_add' α β := by
    refine PresheafOfModules.hom_ext fun W ↦ ?_
    rfl
  map_smul' r α := by
    refine PresheafOfModules.hom_ext fun W ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    change fRestr O (G.obj V.unop) ((φ.app V).hom r) (op ((Over.post G).obj W.unop)) •
        α.app (op ((Over.post G).obj W.unop)) x =
      (show (ORestr O (G.obj V.unop)).obj (op ((Over.post G).obj W.unop)) from
        (φ.app (op W.unop.left)).hom (fRestr O' V.unop r W)) •
        α.app (op ((Over.post G).obj W.unop)) x
    congr 1
    change ((Oforget O).map (G.map W.unop.hom).op).hom ((φ.app V).hom r) =
      (φ.app (op W.unop.left)).hom (((Oforget O').map W.unop.hom.op).hom r)
    rw [← RingCat.comp_apply, ← RingCat.comp_apply]
    exact congrArg (fun f ↦ f.hom r) (φ.naturality W.unop.hom.op).symm

/-- **The comparison map `G^*Hom_O(F, F') ⟶ Hom_{O'}(G^*F, G^*F')`.** -/
def internalHomPushforwardMap :
    (pushforward φ).obj (internalHom O F F') ⟶
      internalHom O' ((pushforward φ).obj F) ((pushforward φ).obj F') where
  app V := ConcreteCategory.ofHom (C := ModuleCat _)
    (internalHomPushforwardLinearMap G O O' φ F F' V)
  naturality {V V'} g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun α ↦ ?_)
    refine PresheafOfModules.hom_ext fun W ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    change α.app (op (Over.mk (G.map W.unop.hom ≫ G.map g.unop))) x =
      α.app (op (Over.mk (G.map (W.unop.hom ≫ g.unop)))) x
    exact app_over_mk_congr O α (G.map_comp _ _).symm x

/-- The comparison map `internalHomPushforwardMap` sends a section `α` over `V` to the morphism
whose value at an object `W` of the slice at `V` is the value of `α` at the image of `W` under
`Over.post G`. -/
theorem internalHomPushforwardMap_app_app (V : Cᵒᵖ)
    (α : (restrFun O (G.obj V.unop)).obj F ⟶ (restrFun O (G.obj V.unop)).obj F')
    (W : (Over V.unop)ᵒᵖ) (x : F.obj (op (G.obj W.unop.left))) :
    (((internalHomPushforwardMap G O O' φ F F').app V).hom α).app W x =
      α.app (op ((Over.post G).obj W.unop)) x :=
  rfl

/-- The restriction of a section of the internal Hom along `f : V ⟶ U`, evaluated at the terminal
object of the slice at `V`, on a restricted section. -/
theorem internalHom_map_app_terminal {U V : D} (f : V ⟶ U)
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj F') (m : F.obj (op U)) :
    (((internalHom O F F').map f.op).hom α :
      (restrFun O V).obj F ⟶ (restrFun O V).obj F').app (op (Over.mk (𝟙 V))) (F.map f.op m) =
      F'.map f.op (α.app (op (Over.mk (𝟙 U))) m) := by
  refine (app_over_mk_congr O α (Category.id_comp f) (F.map f.op m)).trans ?_
  exact PresheafOfModules.naturality_apply α
    (Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 U)).op m

end PresheafOfModules

end

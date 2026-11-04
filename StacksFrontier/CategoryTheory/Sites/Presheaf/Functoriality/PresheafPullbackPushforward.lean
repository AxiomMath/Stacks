module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import StacksCore.Tactic.EgaSgaAttribute

/-! # The pushforward of a representable presheaf

For a functor `u : C ⥤ D`, the pushforward `u_p : PSh(C) ⥤ PSh(D)` is the left Kan extension
along `u.op`. This file shows that it takes the presheaf `h_U` represented by `U : C` to the
presheaf `h_{u U}` represented by `u U`, by exhibiting `h_{u U}` as a left Kan extension of `h_U`
along `u.op`.

## Main results

* `presheafPullback04D2`, `presheafPushforward04D2`: the pullback `u^p` and pushforward `u_p` on
  presheaves.
* `yonedaPushforwardUnit`: the canonical unit `h_U ⟶ u.op ⋙ h_{u U}`.
* `isLeftKanExtension_yoneda_obj`: `h_{u U}` with that unit is a left Kan extension of `h_U`.
* `presheafPushforward_yoneda_iso`: `u_p h_U ≅ h_{u U}` (Stacks 04D2).

Tags covered: 04D2.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u₁ u₂

variable {C : Type u₁} [SmallCategory C] {D : Type u₂} [Category.{u₁} D] (u : C ⥤ D)

/-- The *pullback* `u^p : PSh(D) ⥤ PSh(C)` of presheaves along a functor
`u : C ⥤ D`, defined by precomposition with `u.op`. -/
@[sga "4 I 5.0" "special case", sga "4 I 8.11.1", sga "4 IV 4.6.1"]
def presheafPullback04D2 : (Dᵒᵖ ⥤ Type u₁) ⥤ (Cᵒᵖ ⥤ Type u₁) :=
  (Functor.whiskeringLeft _ _ _).obj u.op

/-- The *pushforward* `u_p : PSh(C) ⥤ PSh(D)`, defined as the left Kan extension along `u.op`. -/
noncomputable abbrev presheafPushforward04D2 : (Cᵒᵖ ⥤ Type u₁) ⥤ (Dᵒᵖ ⥤ Type u₁) :=
  u.op.lan

/-- The canonical natural transformation `yoneda.obj U ⟶ u.op ⋙ yoneda.obj (u.obj U)`
sending `φ : X.unop ⟶ U` to `u.map φ`. -/
def yonedaPushforwardUnit (U : C) :
    (yoneda.obj U : Cᵒᵖ ⥤ Type u₁) ⟶ u.op ⋙ yoneda.obj (u.obj U) where
  app _ := ↾fun φ => u.map φ
  naturality _ _ _ := by ext; simp

/-- The descent of `(G, β)` to `yoneda.obj (u.obj U)`, defined via Yoneda
as the natural transformation corresponding to `β.app (op U) (𝟙 U)`. -/
noncomputable def yonedaDescent (U : C) (G : Dᵒᵖ ⥤ Type u₁)
    (β : (yoneda.obj U : Cᵒᵖ ⥤ Type u₁) ⟶ u.op ⋙ G) :
    yoneda.obj (u.obj U) ⟶ G :=
  yonedaEquiv.symm (β.app (op U) (𝟙 U))

/-- The descent factors `β` through `yonedaPushforwardUnit u U`. -/
lemma yonedaPushforwardUnit_comp_yonedaDescent (U : C) (G : Dᵒᵖ ⥤ Type u₁)
    (β : (yoneda.obj U : Cᵒᵖ ⥤ Type u₁) ⟶ u.op ⋙ G) :
    yonedaPushforwardUnit u U ≫ Functor.whiskerLeft u.op (yonedaDescent u U G β) = β := by
  ext X φ
  have hn := β.naturality_apply φ.op (𝟙 U)
  simp only [op_unop, Functor.comp_obj, Functor.op_obj, yoneda_obj_map,
    Quiver.Hom.unop_op, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Category.comp_id, Functor.comp_map,
    Functor.op_map, yonedaPushforwardUnit, yonedaDescent, NatTrans.comp_app,
    Functor.whiskerLeft_app, yonedaEquiv_symm_app, TypeCat.Fun.toFun_apply, comp_apply] at hn ⊢
  exact hn.symm

/-- Any natural transformation `γ` satisfying the factorization equation equals the descent. -/
lemma yonedaDescent_uniq (U : C) (G : Dᵒᵖ ⥤ Type u₁)
    (β : (yoneda.obj U : Cᵒᵖ ⥤ Type u₁) ⟶ u.op ⋙ G)
    (γ : yoneda.obj (u.obj U) ⟶ G)
    (hγ : yonedaPushforwardUnit u U ≫ Functor.whiskerLeft u.op γ = β) :
    γ = yonedaDescent u U G β := by
  apply yonedaEquiv.injective
  have h : ((yonedaPushforwardUnit u U ≫ u.op.whiskerLeft γ).app (op U)) (𝟙 U) =
      β.app (op U) (𝟙 U) := by rw [hγ]
  simp only [Functor.comp_obj, Functor.op_obj, yonedaPushforwardUnit,
    NatTrans.comp_app, Functor.whiskerLeft_app, comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
    CategoryTheory.Functor.map_id, yonedaEquiv_apply, yonedaDescent, Equiv.apply_symm_apply] at h ⊢
  exact h

/-- **Stacks 04D2** (structural form): `yoneda.obj (u.obj U)`, equipped with
`yonedaPushforwardUnit u U`, is a left Kan extension of `yoneda.obj U` along `u.op`. -/
@[sga "4 I 5.4" "Clause 3", sga "4 IV 4.6.1" "partial"]
instance isLeftKanExtension_yoneda_obj (U : C) :
    (yoneda.obj (u.obj U)).IsLeftKanExtension (yonedaPushforwardUnit u U) :=
  .mk ⟨Limits.IsInitial.ofUniqueHom
    (fun s ↦ StructuredArrow.homMk (yonedaDescent u U s.right s.hom)
      (yonedaPushforwardUnit_comp_yonedaDescent u U s.right s.hom))
    fun s m ↦ StructuredArrow.hom_ext _ _ <|
      yonedaDescent_uniq u U s.right s.hom m.right (StructuredArrow.Hom.w m)⟩

/-- **Stacks 04D2.** The pushforward `u_p` sends `h_U` to `h_{u(U)}`.
Both `(presheafPushforward04D2 u).obj (yoneda.obj U)` and `yoneda.obj (u.obj U)` are
left Kan extensions of `yoneda.obj U` along `u.op`, so they are canonically isomorphic. -/
@[stacks 04D2, sga "4 I 5.4" "Clause 3"]
noncomputable def presheafPushforward_yoneda_iso (U : C) :
    (presheafPushforward04D2 u).obj (yoneda.obj U) ≅ yoneda.obj (u.obj U) :=
  Functor.leftKanExtensionUniqueOfIso _ (u.op.lanUnit.app (yoneda.obj U))
    (Iso.refl (yoneda.obj U)) (yoneda.obj (u.obj U)) (yonedaPushforwardUnit u U)

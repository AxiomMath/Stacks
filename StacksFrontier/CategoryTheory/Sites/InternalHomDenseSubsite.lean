module

public import StacksFrontier.Homology.Injectives.Sheaf.InternalHomExact
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite

/-!
# The internal Hom of abelian sheaves along a dense subsite

Let `G : C ⥤ D` exhibit `(C, J)` as a dense subsite of `(D, K)` and let `𝒢`, `ℱ` be abelian sheaves
on `D`. Restricting the internal Hom `ℋom(𝒢, ℱ)` (`internalHomSheaf`) along `G` gives the internal
Hom of the restrictions: over `Y` the sections of the former are the morphisms
`𝒢|_{G Y} ⟶ ℱ|_{G Y}` on the slice `D/G Y`, those of the latter the morphisms
`(G^* 𝒢)|_Y ⟶ (G^* ℱ)|_Y` on `C/Y`, and restriction along the localization `Over.post G`, again a
dense subsite inclusion (`Stacks.Sites.overPost_isDenseSubsite`), identifies the two because it is
an equivalence of sheaf categories.

## Main definitions

* `Stacks.Sites.internalHomRestrictAddEquiv`: the identification of sections over an object.
* `Stacks.Sites.internalHomSheafPushforwardIso`: `G^* ℋom(𝒢, ℱ) ≅ ℋom(G^* 𝒢, G^* ℱ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.Sites

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (G : C ⥤ D) [G.IsDenseSubsite J K]

/-- The functor `Over.post G : C/Y ⥤ D/G Y` exhibits `(C/Y, J.over Y)` as a dense subsite of
`(D/G Y, K.over (G Y))`. -/
local instance isDenseSubsite_overPost_internalHom (Y : C) :
    (Over.post (X := Y) G).IsDenseSubsite (J.over Y) (K.over (G.obj Y)) :=
  Stacks.Sites.overPost_isDenseSubsite G Y

variable (𝒢 ℱ : Sheaf K AddCommGrpCat.{max u v})

/-- **Sections of `ℋom(𝒢, ℱ)` over `G Y` are sections of `ℋom(G^* 𝒢, G^* ℱ)` over `Y`**:
restriction along the localization `Over.post G`, which is fully faithful on sheaves. -/
def internalHomRestrictAddEquiv (Y : C) :
    ((Over.forget (G.obj Y)).op ⋙ 𝒢.obj ⟶ (Over.forget (G.obj Y)).op ⋙ ℱ.obj) ≃+
      ((Over.forget Y).op ⋙ (G.op ⋙ 𝒢.obj) ⟶ (Over.forget Y).op ⋙ (G.op ⋙ ℱ.obj)) :=
  let hF := Functor.FullyFaithful.ofFullyFaithful ((Over.post (X := Y) G).sheafPushforwardContinuous
    AddCommGrpCat.{max u v} (J.over Y) (K.over (G.obj Y)))
  { toFun α := Functor.whiskerLeft (Over.post (X := Y) G).op α
    invFun β := (hF.preimage (X := (K.overPullback AddCommGrpCat.{max u v} (G.obj Y)).obj 𝒢)
      (Y := (K.overPullback AddCommGrpCat.{max u v} (G.obj Y)).obj ℱ)
      (ObjectProperty.homMk
        (X := ((Over.post (X := Y) G).sheafPushforwardContinuous AddCommGrpCat.{max u v} (J.over Y)
          (K.over (G.obj Y))).obj ((K.overPullback AddCommGrpCat.{max u v} (G.obj Y)).obj 𝒢))
        (Y := ((Over.post (X := Y) G).sheafPushforwardContinuous AddCommGrpCat.{max u v} (J.over Y)
          (K.over (G.obj Y))).obj ((K.overPullback AddCommGrpCat.{max u v} (G.obj Y)).obj ℱ))
        β)).hom
    left_inv α := by
      change (hF.preimage (((Over.post (X := Y) G).sheafPushforwardContinuous
        AddCommGrpCat.{max u v} (J.over Y) (K.over (G.obj Y))).map
        (ObjectProperty.homMk (X := (K.overPullback AddCommGrpCat.{max u v} (G.obj Y)).obj 𝒢)
          (Y := (K.overPullback AddCommGrpCat.{max u v} (G.obj Y)).obj ℱ) α))).hom = α
      rw [hF.preimage_map]
      rfl
    right_inv β := by
      change (((Over.post (X := Y) G).sheafPushforwardContinuous
        AddCommGrpCat.{max u v} (J.over Y) (K.over (G.obj Y))).map (hF.preimage
          (ObjectProperty.homMk
            (X := ((Over.post (X := Y) G).sheafPushforwardContinuous AddCommGrpCat.{max u v}
              (J.over Y) (K.over (G.obj Y))).obj
                ((K.overPullback AddCommGrpCat.{max u v} (G.obj Y)).obj 𝒢))
            (Y := ((Over.post (X := Y) G).sheafPushforwardContinuous AddCommGrpCat.{max u v}
              (J.over Y) (K.over (G.obj Y))).obj
                ((K.overPullback AddCommGrpCat.{max u v} (G.obj Y)).obj ℱ)) β))).hom = β
      rw [hF.map_preimage]
      rfl
    map_add' α α' := by
      ext Z x
      rfl }

/-- `internalHomRestrictAddEquiv` sends `α` to its whiskering along `(Over.post G).op`. -/
lemma internalHomRestrictAddEquiv_apply (Y : C)
    (α : (Over.forget (G.obj Y)).op ⋙ 𝒢.obj ⟶ (Over.forget (G.obj Y)).op ⋙ ℱ.obj) :
    internalHomRestrictAddEquiv (J := J) G 𝒢 ℱ Y α =
      Functor.whiskerLeft (Over.post (X := Y) G).op α :=
  rfl

/-- **`G^* ℋom(𝒢, ℱ) ≅ ℋom(G^* 𝒢, G^* ℱ)` on presheaves.** -/
def internalHomPresheafRestrictIso :
    G.op ⋙ internalHomPresheaf 𝒢.obj ℱ.obj ≅ internalHomPresheaf (G.op ⋙ 𝒢.obj) (G.op ⋙ ℱ.obj) :=
  NatIso.ofComponents (fun Y ↦ (internalHomRestrictAddEquiv (J := J) G 𝒢 ℱ Y.unop).toAddCommGrpIso)
    (fun {Y Y'} f ↦ by
      ext α
      refine NatTrans.ext (funext fun Z ↦ ?_)
      ext x
      change α.app (op ((Over.map (G.map f.unop)).obj ((Over.post G).obj Z.unop))) x =
        α.app (op ((Over.post G).obj ((Over.map f.unop).obj Z.unop))) x
      have h := ConcreteCategory.congr_hom (α.naturality
        (Over.homMk (U := (Over.post G).obj ((Over.map f.unop).obj Z.unop))
          (V := (Over.map (G.map f.unop)).obj ((Over.post G).obj Z.unop)) (𝟙 _)
          (by
            change 𝟙 _ ≫ G.map Z.unop.hom ≫ G.map f.unop = G.map (Z.unop.hom ≫ f.unop)
            rw [Category.id_comp, G.map_comp])).op) x
      change (𝒢.obj.map (𝟙 _) ≫ α.app (op ((Over.post G).obj ((Over.map f.unop).obj Z.unop)))) x =
        (α.app (op ((Over.map (G.map f.unop)).obj ((Over.post G).obj Z.unop))) ≫
          ℱ.obj.map (𝟙 _)) x at h
      have h' := h.symm
      simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h'
      exact h')

/-- **`G^* ℋom(𝒢, ℱ) ≅ ℋom(G^* 𝒢, G^* ℱ)`**, for `G` a dense subsite inclusion. -/
def internalHomSheafPushforwardIso :
    (G.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K).obj (internalHomSheaf K 𝒢 ℱ) ≅
      internalHomSheaf J ((G.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K).obj 𝒢)
        ((G.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K).obj ℱ) :=
  (fullyFaithfulSheafToPresheaf J AddCommGrpCat.{max u v}).preimageIso
    (internalHomPresheafRestrictIso (J := J) G 𝒢 ℱ)

/-- On sections over `Y`, the hom of `internalHomSheafPushforwardIso` sends `α` to its whiskering
along `(Over.post G).op`. -/
lemma internalHomSheafPushforwardIso_hom_app (Y : Cᵒᵖ)
    (α : (Over.forget (G.obj Y.unop)).op ⋙ 𝒢.obj ⟶ (Over.forget (G.obj Y.unop)).op ⋙ ℱ.obj) :
    (internalHomSheafPushforwardIso (J := J) G 𝒢 ℱ).hom.hom.app Y α =
      Functor.whiskerLeft (Over.post (X := Y.unop) G).op α :=
  rfl

section Congr

variable {C₀ : Type u} [Category.{v} C₀] (K₀ : GrothendieckTopology C₀)

/-- **The internal Hom of abelian sheaves along isomorphisms of both arguments.** -/
def internalHomSheafCongr {𝒢 𝒢' ℱ ℱ' : Sheaf K₀ AddCommGrpCat.{max u v}} (a : 𝒢 ≅ 𝒢')
    (b : ℱ ≅ ℱ') : internalHomSheaf K₀ 𝒢 ℱ ≅ internalHomSheaf K₀ 𝒢' ℱ' :=
  (fullyFaithfulSheafToPresheaf K₀ AddCommGrpCat.{max u v}).preimageIso
    (NatIso.ofComponents (fun X ↦ AddEquiv.toAddCommGrpIso
      { toFun := fun α ↦ Functor.whiskerLeft (Over.forget X.unop).op a.inv.hom ≫ α ≫
          Functor.whiskerLeft (Over.forget X.unop).op b.hom.hom
        invFun := fun α ↦ Functor.whiskerLeft (Over.forget X.unop).op a.hom.hom ≫ α ≫
          Functor.whiskerLeft (Over.forget X.unop).op b.inv.hom
        left_inv := fun α ↦ by
          refine NatTrans.ext (funext fun Y ↦ AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ ?_))
          change (b.hom ≫ b.inv).hom.app (op Y.unop.left)
            (α.app Y ((a.hom ≫ a.inv).hom.app (op Y.unop.left) x)) = α.app Y x
          rw [a.hom_inv_id, b.hom_inv_id]
          rfl
        right_inv := fun α ↦ by
          refine NatTrans.ext (funext fun Y ↦ AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ ?_))
          change (b.inv ≫ b.hom).hom.app (op Y.unop.left)
            (α.app Y ((a.inv ≫ a.hom).hom.app (op Y.unop.left) x)) = α.app Y x
          rw [a.inv_hom_id, b.inv_hom_id]
          rfl
        map_add' := fun α α' ↦ by
          refine NatTrans.ext (funext fun Y ↦ AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ ?_))
          change b.hom.hom.app (op Y.unop.left) ((α.app Y + α'.app Y)
              (a.inv.hom.app (op Y.unop.left) x)) =
            b.hom.hom.app (op Y.unop.left) (α.app Y (a.inv.hom.app (op Y.unop.left) x)) +
              b.hom.hom.app (op Y.unop.left) (α'.app Y (a.inv.hom.app (op Y.unop.left) x))
          rw [AddCommGrpCat.hom_add_apply, map_add] })
      (fun {X X'} f ↦ by
        ext α
        refine NatTrans.ext (funext fun Z ↦ ?_)
        ext x
        rfl))

/-- Precomposition in the first variable of the internal Hom, `α ↦ w ∘ α`. -/
abbrev internalHomSheafPrecomp {𝒢 𝒢' : Sheaf K₀ AddCommGrpCat.{max u v}} (w : 𝒢' ⟶ 𝒢)
    (ℱ : Sheaf K₀ AddCommGrpCat.{max u v}) :
    internalHomSheaf K₀ 𝒢 ℱ ⟶ internalHomSheaf K₀ 𝒢' ℱ :=
  (internalHomFunctor K₀ ℱ).map w.op

/-- **`internalHomSheafCongr` is natural in the first variable.** -/
lemma internalHomSheafPrecomp_comp_internalHomSheafCongr
    {𝒢 𝒢' 𝒢₁ 𝒢₁' ℱ ℱ₁ : Sheaf K₀ AddCommGrpCat.{max u v}} (a : 𝒢 ≅ 𝒢₁) (a' : 𝒢' ≅ 𝒢₁')
    (b : ℱ ≅ ℱ₁) (w : 𝒢' ⟶ 𝒢) (w₁ : 𝒢₁' ⟶ 𝒢₁) (hw : w ≫ a.hom = a'.hom ≫ w₁) :
    internalHomSheafPrecomp K₀ w ℱ ≫ (internalHomSheafCongr K₀ a' b).hom =
      (internalHomSheafCongr K₀ a b).hom ≫ internalHomSheafPrecomp K₀ w₁ ℱ₁ := by
  have hw' : a'.inv ≫ w = w₁ ≫ a.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply Sheaf.hom_ext
  ext X α
  refine NatTrans.ext (funext fun Y ↦ AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦ ?_))
  change b.hom.hom.app _ (α.app Y (w.hom.app _ (a'.inv.hom.app _ x))) =
    b.hom.hom.app _ (α.app Y (a.inv.hom.app _ (w₁.hom.app _ x)))
  have h := ConcreteCategory.congr_hom
    (congrArg (fun φ : 𝒢₁' ⟶ 𝒢 ↦ φ.hom.app (op Y.unop.left)) hw') x
  congr 2

end Congr

section Naturality

variable {C₁ : Type u} [Category.{v} C₁] {D₁ : Type u} [Category.{v} D₁]
  {J₁ : GrothendieckTopology C₁} {K₁ : GrothendieckTopology D₁}
  (G₁ : C₁ ⥤ D₁) [G₁.IsDenseSubsite J₁ K₁]

/-- **`internalHomSheafPushforwardIso` is natural in the first variable.** -/
lemma internalHomSheafPushforwardIso_naturality {𝒢 𝒢' : Sheaf K₁ AddCommGrpCat.{max u v}}
    (w : 𝒢' ⟶ 𝒢) (ℱ : Sheaf K₁ AddCommGrpCat.{max u v}) :
    (G₁.sheafPushforwardContinuous AddCommGrpCat.{max u v} J₁ K₁).map
        (internalHomSheafPrecomp K₁ w ℱ) ≫ (internalHomSheafPushforwardIso (J := J₁) G₁ 𝒢' ℱ).hom =
      (internalHomSheafPushforwardIso (J := J₁) G₁ 𝒢 ℱ).hom ≫
        internalHomSheafPrecomp J₁
          ((G₁.sheafPushforwardContinuous AddCommGrpCat.{max u v} J₁ K₁).map w) _ := by
  apply Sheaf.hom_ext
  ext X α
  rfl

end Naturality

end Stacks.Sites

end

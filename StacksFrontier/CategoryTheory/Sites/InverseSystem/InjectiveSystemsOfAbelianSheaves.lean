module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.FunctorialInjectiveEmbeddings
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.FiniteCoveringsInverseSystem
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.MorphismOfSites

/-!
# Comparison lemmas for direct images of abelian sheaves

Componentwise descriptions of the canonical comparison isomorphisms between the direct images
of abelian sheaves along a composite and along an identity, and the compatibility of the uniqueness
isomorphism of a left adjoint with an isomorphism of the right adjoints.

## Main results

* `CategoryTheory.sheafEqToHom_hom_app`: the sections of `eqToHom` between equal abelian sheaves.
* `CategoryTheory.sheafPushforwardContinuousComp'_refl_hom_app`,
  `CategoryTheory.sheafPushforwardContinuousComp'_refl_inv_app`: the comparison isomorphism
  `CategoryTheory.Functor.sheafPushforwardContinuousComp'` along `Iso.refl` is the identity.
* `CategoryTheory.sheafPushforwardContinuousComp'_hom_app_app`,
  `CategoryTheory.sheafPushforwardContinuousComp'_inv_app_app`: the sections of that comparison
  isomorphism along `eqToIso e` are restriction maps along `eqToHom`.
* `CategoryTheory.leftAdjointUniq_ofNatIsoRight_homEquiv_inv`: the adjunction bijection of
  `CategoryTheory.Adjunction.leftAdjointUniq` against `Adjunction.ofNatIsoRight`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w z

namespace CategoryTheory

/-- The component at `U` of the morphism `eqToHom h` between equal sheaves of abelian groups is the
`eqToHom` of the induced equality of sections over `U`. -/
lemma sheafEqToHom_hom_app {A : Type w} [SmallCategory A] (L : GrothendieckTopology A)
    {X Y : Sheaf L (AddCommGrpCat.{z})} (h : X = Y) (U : Aᵒᵖ) :
    (eqToHom h).hom.app U =
      eqToHom (congrArg (fun Z : Sheaf L (AddCommGrpCat.{z}) => Z.obj.obj U) h) := by
  subst h
  rfl

/-- For the identity isomorphism of `v ⋙ w`, the hom of `Functor.sheafPushforwardContinuousComp'`
is the identity at every abelian sheaf. -/
lemma sheafPushforwardContinuousComp'_refl_hom_app
    {X Y Z : Type w} [SmallCategory X] [SmallCategory Y] [SmallCategory Z]
    (v : X ⥤ Y) (w : Y ⥤ Z) (J : GrothendieckTopology X) (K : GrothendieckTopology Y)
    (L : GrothendieckTopology Z) [v.IsContinuous J K] [w.IsContinuous K L]
    [(v ⋙ w).IsContinuous J L] (M : Sheaf L (AddCommGrpCat.{z})) :
    (Functor.sheafPushforwardContinuousComp'
        (Iso.refl (v ⋙ w)) AddCommGrpCat.{z} J K L).hom.app M = 𝟙 _ := by
  ext U x
  simp only [Functor.comp_obj, Functor.sheafPushforwardContinuousComp', Iso.trans,
    Functor.sheafPushforwardContinuousComp, Iso.refl_hom, Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, Iso.refl_inv, NatTrans.op_id,
    ObjectProperty.ι_obj, Functor.whiskerRight_id', ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app, AddCommGrpCat.Hom.hom]
  rfl

/-- For the identity isomorphism of `v ⋙ w`, the inverse of
`Functor.sheafPushforwardContinuousComp'` is the identity at every abelian sheaf. -/
lemma sheafPushforwardContinuousComp'_refl_inv_app
    {X Y Z : Type w} [SmallCategory X] [SmallCategory Y] [SmallCategory Z]
    (v : X ⥤ Y) (w : Y ⥤ Z) (J : GrothendieckTopology X) (K : GrothendieckTopology Y)
    (L : GrothendieckTopology Z) [v.IsContinuous J K] [w.IsContinuous K L]
    [(v ⋙ w).IsContinuous J L] (M : Sheaf L (AddCommGrpCat.{z})) :
    (Functor.sheafPushforwardContinuousComp'
        (Iso.refl (v ⋙ w)) AddCommGrpCat.{z} J K L).inv.app M = 𝟙 _ := by
  ext U x
  simp only [Functor.comp_obj, Functor.sheafPushforwardContinuousComp', Iso.trans,
    Functor.sheafPushforwardContinuousComp, Iso.refl_hom, Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, Iso.refl_inv, NatTrans.op_id,
    ObjectProperty.ι_obj, Functor.whiskerRight_id', ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app, AddCommGrpCat.Hom.hom]
  rfl

/-- For an equality `e : v ⋙ w = vw`, the sections over `V` of the hom of
`Functor.sheafPushforwardContinuousComp' (eqToIso e)` at an abelian sheaf `N` are the restriction
map of `N` along `eqToHom` of the induced equality of objects. -/
lemma sheafPushforwardContinuousComp'_hom_app_app
    {X Y Z : Type w} [SmallCategory X] [SmallCategory Y] [SmallCategory Z]
    {v : X ⥤ Y} {w : Y ⥤ Z} {vw : X ⥤ Z} (e : v ⋙ w = vw)
    (J : GrothendieckTopology X) (K : GrothendieckTopology Y) (L : GrothendieckTopology Z)
    [v.IsContinuous J K] [w.IsContinuous K L] [vw.IsContinuous J L]
    (N : Sheaf L (AddCommGrpCat.{z})) (V : X) :
    ((Functor.sheafPushforwardContinuousComp'
          (eqToIso e) AddCommGrpCat.{z} J K L).hom.app N).hom.app (Opposite.op V) =
      N.obj.map (eqToHom (congrArg Opposite.op (Functor.congr_obj e V))) := by
  subst e
  rw [eqToIso_refl, sheafPushforwardContinuousComp'_refl_hom_app]
  ext x
  simp [eqToHom_refl, Functor.sheafPushforwardContinuous]

/-- For an equality `e : v ⋙ w = vw`, the sections over `V` of the inverse of
`Functor.sheafPushforwardContinuousComp' (eqToIso e)` at an abelian sheaf `N` are the restriction
map of `N` along `eqToHom` of the induced equality of objects. -/
lemma sheafPushforwardContinuousComp'_inv_app_app
    {X Y Z : Type w} [SmallCategory X] [SmallCategory Y] [SmallCategory Z]
    {v : X ⥤ Y} {w : Y ⥤ Z} {vw : X ⥤ Z} (e : v ⋙ w = vw)
    (J : GrothendieckTopology X) (K : GrothendieckTopology Y) (L : GrothendieckTopology Z)
    [v.IsContinuous J K] [w.IsContinuous K L] [vw.IsContinuous J L]
    (N : Sheaf L (AddCommGrpCat.{z})) (V : X) :
    ((Functor.sheafPushforwardContinuousComp'
          (eqToIso e) AddCommGrpCat.{z} J K L).inv.app N).hom.app (Opposite.op V) =
      N.obj.map (eqToHom (congrArg Opposite.op (Functor.congr_obj e.symm V))) := by
  subst e
  rw [eqToIso_refl, sheafPushforwardContinuousComp'_refl_inv_app]
  ext x
  simp [eqToHom_refl, Functor.sheafPushforwardContinuous]

/-- Given adjunctions `adj₁ : F₁ ⊣ G₁`, `adj₂ : F₂ ⊣ G₂`, `adj : F ⊣ G` and an isomorphism
`e : G₂ ⋙ G₁ ≅ G`, transporting `f : (F₁ ⋙ F₂).obj X ⟶ Y` along the inverse of
`Adjunction.leftAdjointUniq`, applying `adj.homEquiv` and composing with `e.inv` gives the adjoint
of `f` under the composite adjunction `adj₁.comp adj₂`. -/
lemma leftAdjointUniq_ofNatIsoRight_homEquiv_inv
    {C₀ : Type*} [Category C₀] {C₁ : Type*} [Category C₁]
    {C₂ : Type*} [Category C₂] {F₁ : C₀ ⥤ C₁} {G₁ : C₁ ⥤ C₀}
    {F₂ : C₁ ⥤ C₂} {G₂ : C₂ ⥤ C₁} {F : C₀ ⥤ C₂} {G : C₂ ⥤ C₀}
    (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) (adj : F ⊣ G)
    (e : G₂ ⋙ G₁ ≅ G) {X : C₀} {Y : C₂}
    (f : (F₁ ⋙ F₂).obj X ⟶ Y) :
    adj.homEquiv X Y
        ((Adjunction.leftAdjointUniq ((adj₁.comp adj₂).ofNatIsoRight e) adj).inv.app X ≫ f) ≫
      e.inv.app Y = (adj₁.comp adj₂).homEquiv X Y f := by
  let adjComp := adj₁.comp adj₂
  let adjE := adjComp.ofNatIsoRight e
  calc
    _ = adj.homEquiv X _ ((Adjunction.leftAdjointUniq adjE adj).inv.app X) ≫
          G.map f ≫ e.inv.app Y := by
      change (adj.homEquiv X Y
        ((Adjunction.leftAdjointUniq adjE adj).inv.app X ≫ f)) ≫ e.inv.app Y = _
      rw [adj.homEquiv_naturality_right]
      exact Category.assoc _ _ _
    _ = adjE.unit.app X ≫ G.map f ≫ e.inv.app Y := by
      rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_leftAdjointUniq_hom_app]
    _ = adjComp.unit.app X ≫ e.hom.app _ ≫ G.map f ≫ e.inv.app Y := by
      simp [adjE, adjComp, Adjunction.ofNatIsoRight]
    _ = adjComp.unit.app X ≫ (G₂ ⋙ G₁).map f := by simp
    _ = (adj₁.comp adj₂).homEquiv X Y f := by
      rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app]

end CategoryTheory

end

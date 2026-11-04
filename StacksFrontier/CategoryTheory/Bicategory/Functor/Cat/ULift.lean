module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Lifting the fibres of a `Cat`-valued pseudofunctor to a higher universe

Let `F` be a pseudofunctor from a locally discrete bicategory `LocallyDiscrete B₀` to
`Cat.{v, u}`. Replacing every fibre `F.obj b` by `ULift.{w} (F.obj b)`, which has the same
morphisms, and every transition functor by its conjugate under `ULift.upFunctor` and
`ULift.downFunctor`, gives a pseudofunctor to `Cat.{v, max u w}` with the same comparison
isomorphisms componentwise. This is the bicategorical counterpart of the category-level
`ULift`.

## Main definitions

* `CategoryTheory.Pseudofunctor.uliftObj`: the pseudofunctor with fibres `ULift (F.obj b)`.
* `CategoryTheory.Pseudofunctor.DescentData.uliftObj`: a descent datum for `F` read as a
  descent datum for `F.uliftObj`, with the same gluing morphisms.

## Main results

* `CategoryTheory.Pseudofunctor.uliftObj_mapComp'_hom_app` and
  `CategoryTheory.Pseudofunctor.uliftObj_mapComp'_inv_app`: the composition comparisons of
  `F.uliftObj` are those of `F`.
* `CategoryTheory.Pseudofunctor.uliftObj_toDescentData_obj_hom`: the canonical descent datum of
  the lift of an object has the gluing morphisms of the canonical descent datum of the object.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory

universe w v u v₀ u₀

namespace Pseudofunctor

attribute [local instance] uliftCategory

/-- An `eqToHom` of the lifted category is the `eqToHom` of the underlying objects. -/
private lemma eqToHom_ulift {C : Type u} [Category.{v} C] {X Y : ULift.{w} C} (h : X = Y) :
    eqToHom h = (eqToHom (congrArg ULift.down h) : X.down ⟶ Y.down) := by
  subst h
  rfl

variable {B₀ : Type u₀} [Category.{v₀} B₀] (F : Pseudofunctor (LocallyDiscrete B₀) Cat.{v, u})

/-- The pseudofunctor obtained from `F` by lifting the objects of every fibre to the universe
`max u w`: the fibre at `b` is `ULift.{w} (F.obj b)`, the transition functor along `f` is
`F.map f` conjugated by `ULift.upFunctor`, and the comparison isomorphisms are those of `F`. -/
noncomputable def uliftObj : Pseudofunctor (LocallyDiscrete B₀) Cat.{v, max u w} :=
  LocallyDiscrete.mkPseudofunctor
    (fun b ↦ Cat.of (ULift.{w} (F.obj (.mk b))))
    (fun f ↦ (ULift.downFunctor ⋙ (F.map f.toLoc).toFunctor ⋙ ULift.upFunctor).toCatHom)
    (fun b ↦ Cat.Hom.isoMk (Functor.isoWhiskerLeft ULift.downFunctor
      (Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId (.mk b))) ULift.upFunctor)))
    (fun f g ↦ Cat.Hom.isoMk (Functor.isoWhiskerLeft ULift.downFunctor
      (Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapComp f.toLoc g.toLoc))
        ULift.upFunctor)))
    (fun f g h ↦ by
      ext X
      rw [Cat.eqToHom_app, eqToHom_ulift]
      have := congrArg (fun η ↦ η.toNatTrans.app X.down)
        (F.map₂_associator f.toLoc g.toLoc h.toLoc)
      rw [Strict.associator_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom,
        Cat.eqToHom_app] at this
      exact this.symm)
    (fun f ↦ by
      ext X
      rw [Cat.eqToHom_app, eqToHom_ulift]
      have := congrArg (fun η ↦ η.toNatTrans.app X.down) (F.map₂_left_unitor f.toLoc)
      rw [Strict.leftUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom,
        Cat.eqToHom_app] at this
      exact this.symm)
    (fun f ↦ by
      ext X
      rw [Cat.eqToHom_app, eqToHom_ulift]
      have := congrArg (fun η ↦ η.toNatTrans.app X.down) (F.map₂_right_unitor f.toLoc)
      rw [Strict.rightUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom,
        Cat.eqToHom_app] at this
      exact this.symm)

/-- The composition comparisons of `F.uliftObj` are those of `F`, componentwise. -/
lemma uliftObj_mapComp'_hom_app {a b c : LocallyDiscrete B₀} (φ : a ⟶ b) (ψ : b ⟶ c)
    (χ : a ⟶ c) (h : φ ≫ ψ = χ) (X : (F.uliftObj.{w}).obj a) :
    ((F.uliftObj.{w}).mapComp' φ ψ χ h).hom.toNatTrans.app X =
      (F.mapComp' φ ψ χ h).hom.toNatTrans.app X.down := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp, Pseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- The inverse composition comparisons of `F.uliftObj` are those of `F`, componentwise. -/
lemma uliftObj_mapComp'_inv_app {a b c : LocallyDiscrete B₀} (φ : a ⟶ b) (ψ : b ⟶ c)
    (χ : a ⟶ c) (h : φ ≫ ψ = χ) (X : (F.uliftObj.{w}).obj a) :
    ((F.uliftObj.{w}).mapComp' φ ψ χ h).inv.toNatTrans.app X =
      (F.mapComp' φ ψ χ h).inv.toNatTrans.app X.down := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp, Pseudofunctor.mapComp'_eq_mapComp]
  rfl

end Pseudofunctor

namespace Pseudofunctor

attribute [local instance] uliftCategory

open Opposite LocallyDiscreteOpToCat

variable {C : Type u₀} [Category.{v₀} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u}}
  {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- `pullHom` for `F.uliftObj` is `pullHom` for `F`. -/
lemma uliftObj_pullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom (F := F.uliftObj.{w}) (M₁ := ULift.up M₁) (M₂ := ULift.up M₂) φ g gf₁ gf₂ hgf₁ hgf₂ =
      pullHom φ g gf₁ gf₂ hgf₁ hgf₂ :=
  congrArg₂ (fun a b ↦ a ≫ (F.map g.op.toLoc).toFunctor.map φ ≫ b)
    (F.uliftObj_mapComp'_hom_app _ _ _ _ (ULift.up M₁))
    (F.uliftObj_mapComp'_inv_app _ _ _ _ (ULift.up M₂))

/-- A descent datum for `F` is a descent datum for `F.uliftObj`, with the same gluing
morphisms. -/
def DescentData.uliftObj (D : F.DescentData f) : (F.uliftObj.{w}).DescentData f where
  obj i := ULift.up (D.obj i)
  hom _ q _ _ f₁ f₂ hf₁ hf₂ := D.hom q f₁ f₂ hf₁ hf₂
  pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    (uliftObj_pullHom _ g gf₁ gf₂ hgf₁ hgf₂).trans
      (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
  hom_self _ q _ g hg := D.hom_self q g hg
  hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ := D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃

/-- The canonical descent datum of the lift of an object is the lift of its canonical descent
datum: the gluing morphisms of `F.uliftObj` are those of `F`. -/
lemma uliftObj_toDescentData_obj_hom (M : F.obj (.mk (op S))) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    ((F.uliftObj.{w}).toDescentData f |>.obj (ULift.up M)).hom q f₁ f₂ hf₁ hf₂ =
      ((F.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂ :=
  congrArg₂ (· ≫ ·) (F.uliftObj_mapComp'_inv_app _ _ _ _ (ULift.up M))
    (F.uliftObj_mapComp'_hom_app _ _ _ _ (ULift.up M))

/-- A morphism from the canonical descent datum of the lift of `M` to a lifted descent datum
`D.uliftObj` is a morphism from the canonical descent datum of `M` to `D`, with the same
components. -/
def DescentData.homOfToDescentDataUliftObj {M : F.obj (.mk (op S))} {D : F.DescentData f}
    (φ : ((F.uliftObj.{w}).toDescentData f).obj (ULift.up M) ⟶ D.uliftObj.{w}) :
    (F.toDescentData f).obj M ⟶ D where
  hom i := φ.hom i
  comm _ q _ _ f₁ f₂ hf₁ hf₂ := by
    have h := φ.comm q f₁ f₂ hf₁ hf₂
    rwa [uliftObj_toDescentData_obj_hom] at h

/-- A morphism from a lifted descent datum `D.uliftObj` to the canonical descent datum of the
lift of `M` is a morphism from `D` to the canonical descent datum of `M`. -/
def DescentData.homToDescentDataOfUliftObj {M : F.obj (.mk (op S))} {D : F.DescentData f}
    (φ : D.uliftObj.{w} ⟶ ((F.uliftObj.{w}).toDescentData f).obj (ULift.up M)) :
    D ⟶ (F.toDescentData f).obj M where
  hom i := φ.hom i
  comm _ q _ _ f₁ f₂ hf₁ hf₂ := by
    have h := φ.comm q f₁ f₂ hf₁ hf₂
    rwa [uliftObj_toDescentData_obj_hom] at h

/-- An isomorphism between the canonical descent datum of the lift of `M` and a lifted descent
datum `D.uliftObj` is an isomorphism between the canonical descent datum of `M` and `D`. -/
def DescentData.isoOfToDescentDataUliftObjIso {M : F.obj (.mk (op S))} {D : F.DescentData f}
    (e : ((F.uliftObj.{w}).toDescentData f).obj (ULift.up M) ≅ D.uliftObj.{w}) :
    (F.toDescentData f).obj M ≅ D where
  hom := DescentData.homOfToDescentDataUliftObj e.hom
  inv := DescentData.homToDescentDataOfUliftObj e.inv
  hom_inv_id := by
    ext i
    exact congrArg (fun φ ↦ φ.hom i) e.hom_inv_id
  inv_hom_id := by
    ext i
    exact congrArg (fun φ ↦ φ.hom i) e.inv_hom_id

end Pseudofunctor

end CategoryTheory

end

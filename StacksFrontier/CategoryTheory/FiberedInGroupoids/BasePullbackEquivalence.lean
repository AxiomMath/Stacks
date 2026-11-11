module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.BasePullback
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.FibredOneMorphism

/-!
# Pulling back an equivalence over the base

Let `F : 𝒮' ⥤ 𝒮` be a functor. An equivalence `𝒵 ≃ 𝒵'` of categories over `𝒮` (a pair of
1-morphisms over `𝒮` with unit and counit lying over identities) induces an equivalence
`F^* 𝒵 ≃ F^* 𝒵'` over `𝒮'` of the pullbacks along `F`.

## Main definitions

* `CategoryTheory.BasedCategory.basePullbackMap`: the functor `F^* 𝒵 ⥤ F^* 𝒵'` induced by a
  functor `𝒵 ⥤ 𝒵'` over `𝒮`.
* `CategoryTheory.BasedCategory.basePullbackEquivalenceOver`: the equivalence over `𝒮'` of the
  pullbacks induced by an equivalence over `𝒮`.
-/

@[expose] public section

namespace CategoryTheory.BasedCategory

open StacksRepresentableCFG

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒮' : Type u₃} [Category.{v₃} 𝒮'] (F : 𝒮' ⥤ 𝒮)
  {𝒵 : BasedCategory.{v₂, u₂} 𝒮} {𝒵' : BasedCategory.{v₄, u₄} 𝒮}

/-- The functor `F^* 𝒵 ⥤ F^* 𝒵'` induced by a functor `G : 𝒵 ⥤ 𝒵'` over `𝒮`: it sends an object
`(T, z)` to `(T, G z)` and a morphism `(g, φ)` to `(g, G φ)`. -/
def basePullbackMap (G : 𝒵.obj ⥤ 𝒵'.obj) (hG : G ⋙ 𝒵'.p = 𝒵.p) :
    BasePullbackObj F 𝒵 ⥤ BasePullbackObj F 𝒵' where
  obj x := ⟨x.base, G.obj x.obj, (Functor.congr_obj hG x.obj).trans x.over⟩
  map f := ⟨f.base, G.map f.hom, Functor.isHomLift_map_of_comp_eq hG _ f.hom⟩
  map_id _ := BasePullbackObj.hom_ext rfl (G.map_id _)
  map_comp _ _ := BasePullbackObj.hom_ext rfl (G.map_comp _ _)

/-- The functor of pullbacks induced by a functor over `𝒮` is a functor over `𝒮'`. -/
lemma basePullbackMap_comp_p (G : 𝒵.obj ⥤ 𝒵'.obj) (hG : G ⋙ 𝒵'.p = 𝒵.p) :
    basePullbackMap F G hG ⋙ (basePullback F 𝒵').p = (basePullback F 𝒵).p :=
  rfl

/-- An isomorphism `x ≅ (T, z)` of `F^* 𝒵` over the identity of `T`, from an isomorphism of `𝒵`
lying over an identity. -/
def basePullbackVerticalIso (x : BasePullbackObj F 𝒵) {z : 𝒵.obj} (hz : 𝒵.p.obj z = F.obj x.base)
    (φ : x.obj ≅ z) (hφ : 𝒵.p.IsHomLift (𝟙 (F.obj x.base)) φ.hom) :
    x ≅ (⟨x.base, z, hz⟩ : BasePullbackObj F 𝒵) where
  hom := ⟨𝟙 x.base, φ.hom, by rw [F.map_id]; exact hφ⟩
  inv := ⟨𝟙 x.base, φ.inv, by
    rw [F.map_id, show φ.inv = CategoryTheory.inv φ.hom by simp]
    exact IsHomLift.lift_id_inv_isIso 𝒵.p (F.obj x.base) φ.hom⟩
  hom_inv_id := BasePullbackObj.hom_ext (Category.comp_id _) φ.hom_inv_id
  inv_hom_id := BasePullbackObj.hom_ext (Category.comp_id _) φ.inv_hom_id

/-- A morphism of `F^* 𝒵` whose base component is an identity lies over an identity. -/
lemma basePullback_isHomLift_id {x y : BasePullbackObj F 𝒵} (f : x ⟶ y) (h : x.base = y.base)
    (hf : f.base = eqToHom h) : (basePullback F 𝒵).p.IsHomLift (𝟙 x.base) f :=
  (basePullback_isHomLift_iff F 𝒵 (𝟙 x.base) f).mpr ⟨rfl, h.symm, by simp [hf]⟩

/-- **The pullback of an equivalence over `𝒮` is an equivalence over `𝒮'`.** An equivalence of
categories `𝒵 ≃ 𝒵'` over `𝒮` induces an equivalence `F^* 𝒵 ≃ F^* 𝒵'` over `𝒮'` of the pullbacks
along any functor `F : 𝒮' ⥤ 𝒮`. -/
def basePullbackEquivalenceOver (e : EquivalenceOver 𝒵.p 𝒵'.p) :
    EquivalenceOver (basePullback F 𝒵).p (basePullback F 𝒵').p where
  hom := ⟨basePullbackMap F e.hom.functor e.hom.w, basePullbackMap_comp_p F _ _⟩
  inv := ⟨basePullbackMap F e.inv.functor e.inv.w, basePullbackMap_comp_p F _ _⟩
  unitIso := NatIso.ofComponents
    (fun x => basePullbackVerticalIso F x _ (e.unitIso.app x.obj)
      ((congrArg (fun U => 𝒵.p.IsHomLift (𝟙 U) (e.unitIso.hom.app x.obj)) x.over).mp
        (e.isHomLift_unitIso_hom_app x.obj)))
    (fun f => BasePullbackObj.hom_ext (by simp [basePullbackVerticalIso, basePullbackMap])
      (e.unitIso.hom.naturality f.hom))
  counitIso := NatIso.ofComponents
    (fun x => basePullbackVerticalIso F
      ((basePullbackMap F e.inv.functor e.inv.w ⋙ basePullbackMap F e.hom.functor e.hom.w).obj x)
      x.over (e.counitIso.app x.obj)
      ((congrArg (fun U => 𝒵'.p.IsHomLift (𝟙 U) (e.counitIso.hom.app x.obj)) x.over).mp
        (e.isHomLift_counitIso_hom_app x.obj)))
    (fun f => BasePullbackObj.hom_ext (by simp [basePullbackVerticalIso, basePullbackMap])
      (e.counitIso.hom.naturality f.hom))
  unit_over := whiskerRight_eq_eqToHom _ _ _ fun x =>
    basePullback_isHomLift_id F _ rfl rfl
  counit_over := whiskerRight_eq_eqToHom _ _ _ fun x =>
    basePullback_isHomLift_id F _ rfl rfl

end CategoryTheory.BasedCategory

module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory

/-!
# Pulling back a based category along a functor of the bases

Let `F : 𝒮' ⥤ 𝒮` be a functor and let `p : 𝒵 ⥤ 𝒮` be a category over `𝒮`. The *pullback*
`F^* 𝒵` is the category over `𝒮'` whose objects are the pairs `(T, z)` of an object `T` of `𝒮'`
and an object `z` of `𝒵` lying over `F T`, and whose morphisms `(T', z') ⟶ (T, z)` are the pairs
`(g, φ)` of a morphism `g : T' ⟶ T` and a morphism `φ : z' ⟶ z` lying over `F g`. It is the strict
fibre product of `p` and `F` in the category of categories: its objects over `T` are the objects
of `𝒵` over `F T`.

## Main definitions

* `CategoryTheory.BasedCategory.basePullback F 𝒵`: the pullback `F^* 𝒵`, a based category
  over `𝒮'`.

## Main results

* `CategoryTheory.BasedCategory.isFiberedInGroupoids_basePullback`: if `𝒵` is fibred in
  groupoids over `𝒮`, then `F^* 𝒵` is fibred in groupoids over `𝒮'`.
-/

@[expose] public section

namespace CategoryTheory.BasedCategory

open _root_.CategoryTheory.Functor

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒮' : Type u₃} [Category.{v₃} 𝒮']

/-- An object of the pullback `F^* 𝒵`: an object `T` of `𝒮'` and an object of `𝒵` over
`F T`. -/
structure BasePullbackObj (F : 𝒮' ⥤ 𝒮) (𝒵 : BasedCategory.{v₂, u₂} 𝒮) where
  /-- The object of `𝒮'`. -/
  base : 𝒮'
  /-- The object of `𝒵`. -/
  obj : 𝒵.obj
  /-- The object of `𝒵` lies over `F` of the object of `𝒮'`. -/
  over : 𝒵.p.obj obj = F.obj base

namespace BasePullbackObj

variable {F : 𝒮' ⥤ 𝒮} {𝒵 : BasedCategory.{v₂, u₂} 𝒮}

/-- A morphism of the pullback `F^* 𝒵`: a morphism `g` of `𝒮'` and a morphism of `𝒵` lying over
`F g`. -/
@[ext]
structure Hom (x y : BasePullbackObj F 𝒵) where
  /-- The morphism of `𝒮'`. -/
  base : x.base ⟶ y.base
  /-- The morphism of `𝒵`. -/
  hom : x.obj ⟶ y.obj
  /-- The morphism of `𝒵` lies over `F` of the morphism of `𝒮'`. -/
  isHomLift : 𝒵.p.IsHomLift (F.map base) hom

attribute [instance] Hom.isHomLift

instance category : Category.{max v₃ v₂} (BasePullbackObj F 𝒵) where
  Hom := Hom
  id x := ⟨𝟙 x.base, 𝟙 x.obj, by
    rw [F.map_id]; exact IsHomLift.id x.over⟩
  comp f g := ⟨f.base ≫ g.base, f.hom ≫ g.hom, by rw [F.map_comp]; infer_instance⟩

@[ext]
lemma hom_ext {x y : BasePullbackObj F 𝒵} {f g : x ⟶ y} (hb : f.base = g.base)
    (hh : f.hom = g.hom) : f = g :=
  Hom.ext hb hh

@[simp]
lemma id_base (x : BasePullbackObj F 𝒵) : (𝟙 x : x ⟶ x).base = 𝟙 x.base := rfl

@[simp]
lemma id_hom (x : BasePullbackObj F 𝒵) : (𝟙 x : x ⟶ x).hom = 𝟙 x.obj := rfl

@[simp]
lemma comp_base {x y z : BasePullbackObj F 𝒵} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).base = f.base ≫ g.base := rfl

@[simp]
lemma comp_hom {x y z : BasePullbackObj F 𝒵} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

instance {x y : BasePullbackObj F 𝒵} (f : x ⟶ y) : 𝒵.p.IsHomLift (F.map f.base) f.hom :=
  Hom.isHomLift f

end BasePullbackObj

/-- The projection of the pullback `F^* 𝒵` to `𝒮'`. -/
def BasePullbackObj.proj (F : 𝒮' ⥤ 𝒮) (𝒵 : BasedCategory.{v₂, u₂} 𝒮) :
    BasePullbackObj F 𝒵 ⥤ 𝒮' where
  obj x := x.base
  map f := BasePullbackObj.Hom.base f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The pullback `F^* 𝒵` of a based category `𝒵` over `𝒮` along a functor `F : 𝒮' ⥤ 𝒮`: the
objects over `T` are the objects of `𝒵` over `F T`, and the morphisms over `g` are the morphisms
of `𝒵` over `F g`. -/
abbrev basePullback (F : 𝒮' ⥤ 𝒮) (𝒵 : BasedCategory.{v₂, u₂} 𝒮) :
    BasedCategory.{max v₃ v₂, max u₃ u₂} 𝒮' where
  obj := BasePullbackObj F 𝒵
  p := BasePullbackObj.proj F 𝒵

variable (F : 𝒮' ⥤ 𝒮) (𝒵 : BasedCategory.{v₂, u₂} 𝒮)

@[simp]
lemma basePullback_p_obj (x : BasePullbackObj F 𝒵) :
    (basePullback F 𝒵).p.obj x = x.base := rfl

@[simp]
lemma basePullback_p_map {x y : BasePullbackObj F 𝒵} (f : x ⟶ y) :
    (basePullback F 𝒵).p.map f = BasePullbackObj.Hom.base f := rfl

/-- A morphism of `F^* 𝒵` lies over `g` exactly when its base component is `g`, up to the
identifications of its source and target. -/
lemma basePullback_isHomLift_iff {T T' : 𝒮'} (g : T' ⟶ T) {x y : BasePullbackObj F 𝒵}
    (f : x ⟶ y) :
    (basePullback F 𝒵).p.IsHomLift g f ↔
      ∃ (hx : x.base = T') (hy : y.base = T),
        BasePullbackObj.Hom.base f = eqToHom hx ≫ g ≫ eqToHom hy.symm := by
  constructor
  · intro h
    exact ⟨IsHomLift.domain_eq (basePullback F 𝒵).p g f,
      IsHomLift.codomain_eq (basePullback F 𝒵).p g f, IsHomLift.fac' (basePullback F 𝒵).p g f⟩
  · rintro ⟨hx, hy, h⟩
    exact IsHomLift.of_fac' (basePullback F 𝒵).p g f hx hy h

/-- **The pullback of a category fibred in groupoids is fibred in groupoids.** If `𝒵` is fibred
in groupoids over `𝒮`, then so is its pullback `F^* 𝒵` over `𝒮'`, for any functor
`F : 𝒮' ⥤ 𝒮`. -/
theorem isFiberedInGroupoids_basePullback (h𝒵 : 𝒵.p.IsFiberedInGroupoids) :
    (basePullback F 𝒵).p.IsFiberedInGroupoids where
  exists_lift := by
    intro V U f (x : BasePullbackObj F 𝒵) hx
    change x.base = U at hx
    subst hx
    obtain ⟨y, φ, hφ⟩ := h𝒵.exists_lift (F.map f) x.obj x.over
    let y' : BasePullbackObj F 𝒵 := ⟨V, y, IsHomLift.domain_eq 𝒵.p (F.map f) φ⟩
    let φ' : BasePullbackObj.Hom y' x := ⟨f, φ, hφ⟩
    refine ⟨y', φ', ?_⟩
    change (basePullback F 𝒵).p.IsHomLift ((basePullback F 𝒵).p.map φ') φ'
    infer_instance
  unique_lift := by
    intro (x : BasePullbackObj F 𝒵) (y : BasePullbackObj F 𝒵) (z : BasePullbackObj F 𝒵)
      φ ψ f hf
    change z.base ⟶ y.base at f
    change f ≫ BasePullbackObj.Hom.base φ = BasePullbackObj.Hom.base ψ at hf
    have hfz : 𝒵.p.obj z.obj = F.obj z.base := z.over
    have hfy : 𝒵.p.obj y.obj = F.obj y.base := y.over
    let f' : 𝒵.p.obj z.obj ⟶ 𝒵.p.obj y.obj := eqToHom hfz ≫ F.map f ≫ eqToHom hfy.symm
    have hf' : f' ≫ 𝒵.p.map (BasePullbackObj.Hom.hom φ) =
        𝒵.p.map (BasePullbackObj.Hom.hom ψ) := by
      rw [IsHomLift.fac' 𝒵.p (F.map (BasePullbackObj.Hom.base φ)) (BasePullbackObj.Hom.hom φ),
        IsHomLift.fac' 𝒵.p (F.map (BasePullbackObj.Hom.base ψ)) (BasePullbackObj.Hom.hom ψ)]
      simp only [f', Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← F.map_comp_assoc, hf]
    obtain ⟨χ, ⟨hχ₁, hχ₂⟩, huniq⟩ := h𝒵.unique_lift (BasePullbackObj.Hom.hom φ)
      (BasePullbackObj.Hom.hom ψ) f' hf'
    have hχ : 𝒵.p.IsHomLift (F.map f) χ := IsHomLift.of_fac' 𝒵.p _ _ hfz hfy (by rw [hχ₁])
    refine ⟨(⟨f, χ, hχ⟩ : BasePullbackObj.Hom z y), ⟨rfl, BasePullbackObj.hom_ext hf hχ₂⟩, ?_⟩
    intro ω ⟨hg₁, hg₂⟩
    change BasePullbackObj.Hom.base ω = f at hg₁
    have hω₂ : BasePullbackObj.Hom.hom ω ≫ BasePullbackObj.Hom.hom φ =
        BasePullbackObj.Hom.hom ψ := congrArg BasePullbackObj.Hom.hom hg₂
    have hl : 𝒵.p.IsHomLift (F.map f) (BasePullbackObj.Hom.hom ω) :=
      hg₁ ▸ BasePullbackObj.Hom.isHomLift ω
    have := huniq (BasePullbackObj.Hom.hom ω)
      ⟨by rw [IsHomLift.fac' 𝒵.p (F.map f) (BasePullbackObj.Hom.hom ω)], hω₂⟩
    exact BasePullbackObj.hom_ext hg₁ this

end CategoryTheory.BasedCategory

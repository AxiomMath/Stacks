module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# `Ext^n(X, N(-))` as a linear functor, with the scalars acting through `N`

Let `𝒱` be an `R`-linear category, `𝒜` an abelian category with `Ext` groups, `X` an object
of `𝒜` and `N : 𝒱 ⥤ 𝒜` an additive functor. Then `V ↦ Ext^n(X, N V)` is an `R`-linear functor
`𝒱 ⥤ ModuleCat R` when `R` acts on `Ext^n(X, N V)` through `N`: `r` acts by composition with
`N(r • 𝟙_V)`. No `R`-linear structure on `𝒜` is assumed.

## Main definitions

* `CategoryTheory.Abelian.Ext.moduleOfFunctor`: the `R`-module structure on `Ext^n(X, N V)`
  through `N`.
* `CategoryTheory.Abelian.Ext.postcompFunctor`: the functor `V ↦ Ext^n(X, N V)`.

## Main results

* `CategoryTheory.Abelian.Ext.postcompFunctor_additive`,
  `CategoryTheory.Abelian.Ext.postcompFunctor_linear`: it is additive and `R`-linear.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u v' u' t

namespace CategoryTheory.Abelian.Ext

variable {R : Type t} [CommRing R] {𝒱 : Type u'} [Category.{v'} 𝒱] [Preadditive 𝒱] [Linear R 𝒱]
  {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasExt.{w} 𝒜]
  (X : 𝒜) (N : 𝒱 ⥤ 𝒜) [N.Additive] (n : ℕ)

/-- **The scalars on `Ext^n(X, N V)` through `N`**: `r` acts by composition with
`N(r • 𝟙_V)`. -/
@[instance_reducible]
def moduleOfFunctor (V : 𝒱) : Module R (Ext.{w} X (N.obj V) n) where
  smul r ξ := ξ.comp (mk₀ (N.map (r • 𝟙 V))) (add_zero n)
  one_smul ξ := by
    change ξ.comp (mk₀ (N.map ((1 : R) • 𝟙 V))) (add_zero n) = ξ
    rw [one_smul, N.map_id, comp_mk₀_id]
  mul_smul r s ξ := by
    change ξ.comp (mk₀ (N.map ((r * s) • 𝟙 V))) (add_zero n) =
      (ξ.comp (mk₀ (N.map (s • 𝟙 V))) (add_zero n)).comp (mk₀ (N.map (r • 𝟙 V))) (add_zero n)
    rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, ← N.map_comp, Linear.comp_smul,
      Category.comp_id, smul_smul]
  smul_zero r := zero_comp X n (mk₀ (N.map (r • 𝟙 V))) n (add_zero n)
  smul_add r ξ ξ' := by
    change (ξ + ξ').comp (mk₀ (N.map (r • 𝟙 V))) (add_zero n) =
      ξ.comp (mk₀ (N.map (r • 𝟙 V))) (add_zero n) + ξ'.comp (mk₀ (N.map (r • 𝟙 V))) (add_zero n)
    exact add_comp _ _ _ _
  add_smul r s ξ := by
    change ξ.comp (mk₀ (N.map ((r + s) • 𝟙 V))) (add_zero n) =
      ξ.comp (mk₀ (N.map (r • 𝟙 V))) (add_zero n) + ξ.comp (mk₀ (N.map (s • 𝟙 V))) (add_zero n)
    rw [add_smul, N.map_add, mk₀_add, comp_add]
  zero_smul ξ := by
    change ξ.comp (mk₀ (N.map ((0 : R) • 𝟙 V))) (add_zero n) = 0
    rw [zero_smul, N.map_zero, mk₀_zero, comp_zero]

/-- The scalars act through `N`. -/
theorem moduleOfFunctor_smul (V : 𝒱) (r : R) (ξ : Ext.{w} X (N.obj V) n) :
    @HSMul.hSMul R _ _ (@instHSMul R _ (moduleOfFunctor X N n V).toSMul) r ξ =
      ξ.comp (mk₀ (N.map (r • 𝟙 V))) (add_zero n) :=
  rfl

/-- Composition with `N f`, as a linear map for the scalars through `N`. -/
def postcompLinearMap {V V' : 𝒱} (f : V ⟶ V') :
    @LinearMap R R _ _ (RingHom.id R) (Ext.{w} X (N.obj V) n) (Ext.{w} X (N.obj V') n) _ _
      (moduleOfFunctor X N n V) (moduleOfFunctor X N n V') :=
  @LinearMap.mk R R _ _ (RingHom.id R) (Ext.{w} X (N.obj V) n) (Ext.{w} X (N.obj V') n) _ _
    (moduleOfFunctor X N n V) (moduleOfFunctor X N n V')
    { toFun := fun ξ ↦ ξ.comp (mk₀ (N.map f)) (add_zero n)
      map_add' := fun ξ ξ' ↦ add_comp _ _ _ _ }
    (fun r ξ ↦ by
      change (ξ.comp (mk₀ (N.map (r • 𝟙 V))) (add_zero n)).comp (mk₀ (N.map f)) (add_zero n) =
        (ξ.comp (mk₀ (N.map f)) (add_zero n)).comp (mk₀ (N.map (r • 𝟙 V'))) (add_zero n)
      rw [comp_assoc_of_third_deg_zero, comp_assoc_of_third_deg_zero, mk₀_comp_mk₀,
        mk₀_comp_mk₀, ← N.map_comp, ← N.map_comp, Linear.smul_comp, Linear.comp_smul,
        Category.id_comp, Category.comp_id])

/-- `postcompLinearMap` on elements. -/
theorem postcompLinearMap_apply {V V' : 𝒱} (f : V ⟶ V') (ξ : Ext.{w} X (N.obj V) n) :
    postcompLinearMap (R := R) X N n f ξ = ξ.comp (mk₀ (N.map f)) (add_zero n) :=
  rfl

/-- **The functor `V ↦ Ext^n(X, N V)`**, with the scalars acting through `N`. -/
def postcompFunctor : 𝒱 ⥤ ModuleCat.{w} R where
  obj V := @ModuleCat.of R _ (Ext.{w} X (N.obj V) n) _ (moduleOfFunctor X N n V)
  map {V V'} f := @ModuleCat.ofHom R _ _ _ _ (moduleOfFunctor X N n V) _
    (moduleOfFunctor X N n V') (postcompLinearMap X N n f)
  map_id V := by
    refine ModuleCat.hom_ext (DFunLike.ext _ _ fun ξ ↦ ?_)
    change ξ.comp (mk₀ (N.map (𝟙 V))) (add_zero n) = ξ
    rw [N.map_id, comp_mk₀_id]
  map_comp f g := by
    refine ModuleCat.hom_ext (DFunLike.ext _ _ fun ξ ↦ ?_)
    change ξ.comp (mk₀ (N.map (f ≫ g))) (add_zero n) =
      (ξ.comp (mk₀ (N.map f)) (add_zero n)).comp (mk₀ (N.map g)) (add_zero n)
    rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, N.map_comp]

/-- The functor acts on morphisms by composition with `N f`. -/
theorem postcompFunctor_map_hom_apply {V V' : 𝒱} (f : V ⟶ V') (ξ : Ext.{w} X (N.obj V) n) :
    ((postcompFunctor (R := R) X N n).map f).hom ξ = ξ.comp (mk₀ (N.map f)) (add_zero n) :=
  rfl

/-- `V ↦ Ext^n(X, N V)` is additive. -/
instance postcompFunctor_additive : (postcompFunctor (R := R) X N n).Additive where
  map_add {V V' f g} := by
    refine ModuleCat.hom_ext (DFunLike.ext _ _ fun ξ ↦ ?_)
    change ξ.comp (mk₀ (N.map (f + g))) (add_zero n) =
      ξ.comp (mk₀ (N.map f)) (add_zero n) + ξ.comp (mk₀ (N.map g)) (add_zero n)
    rw [N.map_add, mk₀_add]
    exact comp_add _ _ _ _

/-- `V ↦ Ext^n(X, N V)` is linear for the scalars through `N`. -/
instance postcompFunctor_linear : (postcompFunctor (R := R) X N n).Linear R where
  map_smul {V V'} f r := by
    have key : ∀ ξ : Ext.{w} X (N.obj V) n, ξ.comp (mk₀ (N.map (r • f))) (add_zero n) =
        (ξ.comp (mk₀ (N.map f)) (add_zero n)).comp (mk₀ (N.map (r • 𝟙 V'))) (add_zero n) := by
      intro ξ
      rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, ← N.map_comp, Linear.comp_smul,
        Category.comp_id]
    exact ModuleCat.hom_ext (DFunLike.ext _ _ key)

end CategoryTheory.Abelian.Ext

end

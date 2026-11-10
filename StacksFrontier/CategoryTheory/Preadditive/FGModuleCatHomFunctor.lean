module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Morphisms into an additive functor of finite-dimensional vector spaces

Let `F : FGModuleCat k ⥤ C` be an additive functor into a preadditive category and `X` an object
of `C`. The morphisms `X ⟶ F(V)` form a `k`-vector space, `c ∈ k` acting by composition with
`F(c • 𝟙_V)`, and `V ↦ Hom(X, F(V))` is an additive `k`-linear functor
`FGModuleCat k ⥤ ModuleCat k`. No linear structure on `C` is needed: the action of `k` comes from
the source category of `F`.

For `F(V) = (𝒪_X ⊗_k V)[1]` in a derived category and `X = NL_{X/k}` this is the functor
`V ↦ Ext¹(NL_{X/k}, 𝒪_X ⊗_k V)` against which the deformation classes of the proof of
[Stacks Project, Tag 0E41] are natural.

## Main definitions

* `CategoryTheory.Functor.homModuleOfAdditive`: the `k`-module `Hom(X, F(V))`.
* `CategoryTheory.Functor.homFunctorOfAdditive`: `V ↦ Hom(X, F(V))`, additive and `k`-linear.
-/

@[expose] public section

open CategoryTheory

universe w u

namespace CategoryTheory.Functor

variable {k : Type u} [Field k] {C : Type*} [Category.{w} C] [Preadditive C]
  (F : FGModuleCat.{u} k ⥤ C) [F.Additive] (X : C)

/-- **The `k`-module `Hom(X, F(V))`**, `c ∈ k` acting by composition with `F(c • 𝟙_V)`. -/
@[instance_reducible]
def homModuleOfAdditive (V : FGModuleCat.{u} k) : Module k (X ⟶ F.obj V) where
  smul c e := e ≫ F.map (c • 𝟙 V)
  one_smul e := by
    change e ≫ F.map ((1 : k) • 𝟙 V) = e
    rw [one_smul, F.map_id, Category.comp_id]
  mul_smul c d e := by
    change e ≫ F.map ((c * d) • 𝟙 V) = (e ≫ F.map (d • 𝟙 V)) ≫ F.map (c • 𝟙 V)
    rw [Category.assoc, ← F.map_comp, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
      mul_smul, smul_comm]
  smul_zero c := Limits.zero_comp
  smul_add c e f := Preadditive.add_comp _ _ _ _ _ _
  add_smul c d e := by
    change e ≫ F.map ((c + d) • 𝟙 V) = e ≫ F.map (c • 𝟙 V) + e ≫ F.map (d • 𝟙 V)
    rw [add_smul, F.map_add, Preadditive.comp_add]
  zero_smul e := by
    change e ≫ F.map ((0 : k) • 𝟙 V) = 0
    rw [zero_smul, F.map_zero, Limits.comp_zero]

/-- In `Hom(X, F(V))`, `c • e` is the composition `e ≫ F(c • 𝟙_V)`. -/
theorem homModuleOfAdditive_smul (V : FGModuleCat.{u} k) (c : k) (e : X ⟶ F.obj V) :
    letI := F.homModuleOfAdditive X V
    c • e = e ≫ F.map (c • 𝟙 V) :=
  rfl

/-- Postcomposition with `F(g)` is `k`-linear. -/
def homMapOfAdditive {V W : FGModuleCat.{u} k} (g : V ⟶ W) :
    letI := F.homModuleOfAdditive X V
    letI := F.homModuleOfAdditive X W
    (X ⟶ F.obj V) →ₗ[k] (X ⟶ F.obj W) :=
  letI := F.homModuleOfAdditive X V
  letI := F.homModuleOfAdditive X W
  { toFun := fun e => e ≫ F.map g
    map_add' := fun e e' => Preadditive.add_comp _ _ _ _ _ _
    map_smul' := fun c e => by
      change (e ≫ F.map (c • 𝟙 V)) ≫ F.map g = (e ≫ F.map g) ≫ F.map (c • 𝟙 W)
      rw [Category.assoc, Category.assoc, ← F.map_comp, ← F.map_comp, Linear.smul_comp,
        Linear.comp_smul, Category.id_comp, Category.comp_id] }

/-- **`V ↦ Hom(X, F(V))`**, as a functor to `k`-vector spaces. -/
def homFunctorOfAdditive : FGModuleCat.{u} k ⥤ ModuleCat.{w} k where
  obj V := letI := F.homModuleOfAdditive X V; ModuleCat.of k (X ⟶ F.obj V)
  map {V W} g :=
    letI := F.homModuleOfAdditive X V
    letI := F.homModuleOfAdditive X W
    ModuleCat.ofHom (F.homMapOfAdditive X g)
  map_id V := by
    let := F.homModuleOfAdditive X V
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    change (e : X ⟶ F.obj V) ≫ F.map (𝟙 V) = e
    rw [F.map_id, Category.comp_id]
  map_comp {V W Z} g h := by
    let := F.homModuleOfAdditive X V
    let := F.homModuleOfAdditive X Z
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    change (e : X ⟶ F.obj V) ≫ F.map (g ≫ h) = ((e : X ⟶ F.obj V) ≫ F.map g) ≫ F.map h
    rw [F.map_comp, Category.assoc]

/-- The functor `V ↦ Hom(X, F(V))` sends `g : V ⟶ W` to postcomposition with `F(g)`. -/
theorem homFunctorOfAdditive_map_apply {V W : FGModuleCat.{u} k} (g : V ⟶ W) (e : X ⟶ F.obj V) :
    (F.homFunctorOfAdditive X).map g e = e ≫ F.map g :=
  rfl

/-- The functor `V ↦ Hom(X, F(V))` is additive. -/
instance : (F.homFunctorOfAdditive X).Additive where
  map_add {V W g h} := by
    let := F.homModuleOfAdditive X V
    let := F.homModuleOfAdditive X W
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    change (e : X ⟶ F.obj V) ≫ F.map (g + h) =
      (e : X ⟶ F.obj V) ≫ F.map g + (e : X ⟶ F.obj V) ≫ F.map h
    rw [F.map_add]
    exact Preadditive.comp_add _ _ _ _ _ _

/-- The functor `V ↦ Hom(X, F(V))` is `k`-linear. -/
instance : (F.homFunctorOfAdditive X).Linear k where
  map_smul {V W} g c := by
    let := F.homModuleOfAdditive X V
    let := F.homModuleOfAdditive X W
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    have key : ∀ e' : X ⟶ F.obj V, e' ≫ F.map (c • g) = (e' ≫ F.map g) ≫ F.map (c • 𝟙 W) :=
      fun e' => by rw [Category.assoc, ← F.map_comp, Linear.comp_smul, Category.comp_id]
    exact key e

end CategoryTheory.Functor

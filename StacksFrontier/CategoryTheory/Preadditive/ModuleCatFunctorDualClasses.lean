module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Linear forms acting on morphisms into an additive functor of modules

Let `G : ModuleCat k ⥤ C` be an additive functor into a preadditive category and `X` an object of
`C`. Morphisms `X ⟶ G(k)` form a `k`-module, `c ∈ k` acting by composition with `G(c · 1)`
(`CategoryTheory.Functor.evalModule`). A morphism `ξ : X ⟶ G(V)` gives a `k`-linear map
`Hom_k(V, k) ⟶ Hom(X, G(k))`, `λ ↦ ξ ≫ G(λ)` (`CategoryTheory.Functor.dualClassMap`), natural in
`V` (`CategoryTheory.Functor.dualClassMap_comp`).

## Main definitions

* `CategoryTheory.Functor.scalarMap`: `G` applied to multiplication by `c` on `k`.
* `CategoryTheory.Functor.evalModule`: the `k`-module `Hom(X, G(k))`.
* `CategoryTheory.Functor.dualClassMap`: `λ ↦ ξ ≫ G(λ)`.

## Main results

* `CategoryTheory.Functor.dualClassMap_comp`: naturality of `dualClassMap` in `V`.

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Functor

variable {k : Type u} [CommRing k] {C : Type*} [Category.{v} C] [Preadditive C]
  (G : ModuleCat.{u} k ⥤ C) [G.Additive] (X : C)

/-- `G` applied to multiplication by `c` on `k`. -/
abbrev scalarMap (c : k) : G.obj (ModuleCat.of k k) ⟶ G.obj (ModuleCat.of k k) :=
  G.map (ModuleCat.ofHom (c • LinearMap.id))

omit [Preadditive C] [G.Additive] in
/-- `G(cd · 1)` is `G(d · 1)` followed by `G(c · 1)`. -/
theorem scalarMap_mul (c d : k) :
    G.scalarMap (c * d) = G.scalarMap d ≫ G.scalarMap c := by
  rw [scalarMap, scalarMap, scalarMap, ← G.map_comp, ← ModuleCat.ofHom_comp,
    LinearMap.smul_comp, LinearMap.id_comp, mul_smul]

/-- `G(c · 1)` is additive in `c`. -/
theorem scalarMap_add (c d : k) :
    G.scalarMap (c + d) = G.scalarMap c + G.scalarMap d := by
  rw [scalarMap, scalarMap, scalarMap, ← G.map_add, ← ModuleCat.ofHom_add, add_smul]

omit [Preadditive C] [G.Additive] in
/-- `G(1 · 1)` is the identity. -/
theorem scalarMap_one : G.scalarMap 1 = 𝟙 _ := by
  rw [scalarMap, one_smul, ModuleCat.ofHom_id, G.map_id]

/-- `G(0 · 1)` is zero. -/
theorem scalarMap_zero : G.scalarMap 0 = 0 := by
  rw [scalarMap, zero_smul, ModuleCat.ofHom_zero, G.map_zero]

/-- **The `k`-module `Hom(X, G(k))`**, `c ∈ k` acting by composition with `G(c · 1)`. -/
@[instance_reducible]
def evalModule : Module k (X ⟶ G.obj (ModuleCat.of k k)) where
  smul c e := e ≫ G.scalarMap c
  one_smul e := (e ≫= G.scalarMap_one).trans (Category.comp_id e)
  mul_smul c d e := (e ≫= G.scalarMap_mul c d).trans (Category.assoc _ _ _).symm
  smul_zero _ := Limits.zero_comp
  smul_add _ _ _ := Preadditive.add_comp _ _ _ _ _ _
  add_smul c d e := (e ≫= G.scalarMap_add c d).trans (Preadditive.comp_add _ _ _ _ _ _)
  zero_smul e := (e ≫= G.scalarMap_zero).trans Limits.comp_zero

/-- In `evalModule`, `c • e` is `e` followed by `G(c · 1)`. -/
theorem evalModule_smul (c : k) (e : X ⟶ G.obj (ModuleCat.of k k)) :
    letI := G.evalModule X
    c • e = e ≫ G.scalarMap c :=
  rfl

attribute [local instance] evalModule

variable {X} {V V' : ModuleCat.{u} k}

/-- **The linear forms on `V` acting on a morphism `ξ : X ⟶ G(V)`**: `λ ↦ ξ ≫ G(λ)`, a
`k`-linear map `Hom_k(V, k) ⟶ Hom(X, G(k))`. -/
def dualClassMap (ξ : X ⟶ G.obj V) :
    Module.Dual k V →ₗ[k] (X ⟶ G.obj (ModuleCat.of k k)) :=
  { toFun := fun l => ξ ≫ G.map (ModuleCat.ofHom l)
    map_add' := fun l l' => by
      rw [ModuleCat.ofHom_add, G.map_add, Preadditive.comp_add]
    map_smul' := fun c l => by
      rw [RingHom.id_apply, evalModule_smul, Category.assoc, scalarMap, ← G.map_comp,
        ← ModuleCat.ofHom_comp] }

/-- `dualClassMap ξ` sends a linear form `l` to `ξ ≫ G(l)`. -/
theorem dualClassMap_apply (ξ : X ⟶ G.obj V) (l : Module.Dual k V) :
    G.dualClassMap ξ l = ξ ≫ G.map (ModuleCat.ofHom l) :=
  rfl

/-- **Naturality in `V`**: pushing `ξ` along `f : V ⟶ V'` precomposes the linear forms with
`f`. -/
theorem dualClassMap_comp (ξ : X ⟶ G.obj V) (f : V ⟶ V') (l : Module.Dual k V') :
    G.dualClassMap (ξ ≫ G.map f) l = G.dualClassMap ξ (l ∘ₗ f.hom) := by
  rw [dualClassMap_apply, dualClassMap_apply, Category.assoc, ← G.map_comp]
  rfl

end CategoryTheory.Functor

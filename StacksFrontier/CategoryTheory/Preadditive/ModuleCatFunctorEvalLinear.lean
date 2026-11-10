module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.RingTheory.Finiteness.Defs
public import StacksFrontier.CategoryTheory.Preadditive.ModuleCatFunctorDualClasses

/-!
# The module `Hom(X, G(k))` for a functor respecting scalars

Let `G : Mod(k) ⥤ C` be an additive functor into a `k`-linear category. The `k`-module structure
`CategoryTheory.Functor.evalModule` on `Hom(X, G(k))` lets `c ∈ k` act by composition with
`G(c · 1)`. When `G` carries `c · 1` to `c · 1`, this is the module structure of the linear
category, so finiteness questions about `Hom(X, G(k))` may be asked in the linear category. In
the proof of [Stacks Project, Tag 0D1K] the vector spaces `Ext¹(NL_{X/k}, 𝒪_X)` and
`Ext⁰(NL_{X/k}, 𝒪_X)` arise in the first form and are shown finite in the second.

## Main results

* `CategoryTheory.Functor.evalModule_eq_of_scalarMap_eq`
* `CategoryTheory.Functor.moduleFinite_evalModule_of_scalarMap_eq`
* `CategoryTheory.Functor.scalarMap_comp_eq_smul_id`

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public section

open CategoryTheory

universe v v' u

namespace CategoryTheory.Functor

variable {k : Type u} [CommRing k] {C : Type*} [Category.{v} C] [Preadditive C]
  [CategoryTheory.Linear k C] (G : ModuleCat.{u} k ⥤ C) [G.Additive] (X : C)

/-- **`Functor.evalModule` is the linear structure** when `G` carries `c · 1` to `c · 1`. -/
theorem evalModule_eq_of_scalarMap_eq (h : ∀ c : k, G.scalarMap c = c • 𝟙 _) :
    G.evalModule X = Linear.homModule X (G.obj (ModuleCat.of k k)) :=
  Module.ext' _ _ fun c e => by
    change e ≫ G.scalarMap c = c • e
    rw [h, Linear.comp_smul, Category.comp_id]

/-- **Finiteness of `Hom(X, G(k))` for `Functor.evalModule`** follows from finiteness in the
linear category, when `G` carries `c · 1` to `c · 1`. -/
theorem moduleFinite_evalModule_of_scalarMap_eq (h : ∀ c : k, G.scalarMap c = c • 𝟙 _)
    (hf : Module.Finite k (X ⟶ G.obj (ModuleCat.of k k))) :
    letI := G.evalModule X
    Module.Finite k (X ⟶ G.obj (ModuleCat.of k k)) := by
  rw [evalModule_eq_of_scalarMap_eq G X h]
  exact hf

omit [G.Additive] in
/-- **Composing with a linear functor keeps `c · 1 ↦ c · 1`**: if `G(c · 1) = c · 1`, then
`(G ⋙ F)(c · 1) = c · 1` for every `k`-linear functor `F`. -/
theorem scalarMap_comp_eq_smul_id {D : Type*} [Category.{v'} D] [Preadditive D]
    [CategoryTheory.Linear k D] (F : C ⥤ D) [F.Additive] [F.Linear k]
    (h : ∀ c : k, G.scalarMap c = c • 𝟙 _) (c : k) :
    (G ⋙ F).scalarMap c = c • 𝟙 _ := by
  change F.map (G.scalarMap c) = _
  rw [h, F.map_smul, F.map_id]
  rfl

end CategoryTheory.Functor

end

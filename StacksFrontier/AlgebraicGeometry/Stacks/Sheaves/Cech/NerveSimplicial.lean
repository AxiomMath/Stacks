module

public import Mathlib.CategoryTheory.Category.Cat
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.NerveFibreProduct

/-!
# The Čech nerve of a covering as a simplicial object

Let `f : U ⥤ X` be a functor over a base category `C`, viewed as a covering of `X`, and let
`U_n` be the degree `n` piece of its Čech nerve, with projection `f_n : U_n ⥤ X`. The reindexing
functors `U_φ : U_n ⥤ U_m` along the maps `φ : [m] ⟶ [n]` compose on the nose and are
`1`-morphisms over `X`, so they form a simplicial object `U_•` in categories; and `f_0 = f`
under the identification `U_0 ≃ U`.

## Main definitions

* `Stacks.RelativeCech.coordinateZeroCompIso`: `f_0 = f`, the projection of `U_0` is `f`
  under `U_0 ≃ U`, through vertical comparison isomorphisms.
* `Stacks.RelativeCech.nerve`: the simplicial object `U_•` in categories.

## Main results

* `Stacks.RelativeCech.Tuple.reindex_id` and `Stacks.RelativeCech.Tuple.reindex_comp`: the
  reindexing functors compose on the nose.
* `Stacks.RelativeCech.nerve_map_comp_projection`: the maps of `U_•` are `1`-morphisms over `X`.

## References

* [Stacks Project, Tag 06X3](https://stacks.math.columbia.edu/tag/06X3)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.RelativeCech

universe vC vU vX uC uU uX

variable {C : Type uC} [Category.{vC} C] {U : Type uU} [Category.{vU} U]
  {X : Type uX} [Category.{vX} X] (p : X ⥤ C) (f : U ⥤ X)

/-- `f_0 = f`: under the identification `U_0 ≃ U` by the single coordinate
(`Stacks.RelativeCech.isEquivalence_coordinate_zero`), the projection `f_0 : U_0 ⥤ X` is `f`, the
isomorphism being given by the comparison isomorphisms of the tuples, which lie over identities
of the base (`Stacks.RelativeCech.coordinateZeroCompIso_hom_app_isHomLift`). -/
@[stacks 06X3 "f_0 = f"]
public def coordinateZeroCompIso :
    Tuple.coordinate p f (0 : Fin 1) ⋙ f ≅ Tuple.projection p f 0 :=
  NatIso.ofComponents (fun a => a.comparison 0) (fun g => Tuple.Hom.comparison_naturality g 0)

/-- The components of the identification `f_0 = f` lie over identities of the base. -/
public theorem coordinateZeroCompIso_hom_app_isHomLift (a : Tuple p f 0) :
    p.IsHomLift (𝟙 (p.obj a.target)) ((coordinateZeroCompIso p f).hom.app a) :=
  a.comparison_lift 0

/-- Reindexing Čech tuples along the identity is the identity functor, on the nose. -/
public theorem Tuple.reindex_id (n : ℕ) :
    Tuple.reindex p f (id : Fin (n + 1) → Fin (n + 1)) = 𝟭 (Tuple p f n) :=
  rfl

/-- Reindexing Čech tuples is strictly compatible with composition: `U_{ψ ∘ φ} = U_φ ∘ U_ψ`, with
no `2`-morphism needed. -/
public theorem Tuple.reindex_comp {l m n : ℕ} (φ : Fin (l + 1) → Fin (m + 1))
    (ψ : Fin (m + 1) → Fin (n + 1)) :
    Tuple.reindex p f (ψ ∘ φ) = Tuple.reindex p f ψ ⋙ Tuple.reindex p f φ :=
  rfl

/-- The simplicial object `U_•` of the Čech nerve of `f : U ⥤ X`: the category `U_n` of tuples in
degree `n`, and the reindexing functor `U_φ` along each map `φ : [m] ⟶ [n]`. These compose on the
nose (`Stacks.RelativeCech.Tuple.reindex_comp`) and are `1`-morphisms over `X`
(`Stacks.RelativeCech.projection_reindex`). -/
@[stacks 06X3 "the simplicial object U_•, whose maps compose on the nose over X"]
public def nerve : SimplicialObject Cat.{max vU vX, max uU uX vX} where
  obj n := Cat.of (Tuple p f n.unop.len)
  map φ := (Tuple.reindex p f φ.unop.toOrderHom).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The face and degeneracy maps of `U_•` are the reindexing functors. -/
public theorem nerve_map_toFunctor {m n : SimplexCategoryᵒᵖ} (φ : m ⟶ n) :
    ((nerve p f).map φ).toFunctor = Tuple.reindex p f φ.unop.toOrderHom :=
  rfl

/-- The reindexing functors of `U_•` are `1`-morphisms over `X`: they commute strictly with the
projections `f_n`. -/
@[stacks 06X3 "the maps of U_• are 1-morphisms over X"]
public theorem nerve_map_comp_projection {m n : SimplexCategoryᵒᵖ} (φ : m ⟶ n) :
    ((nerve p f).map φ).toFunctor ⋙ Tuple.projection p f n.unop.len =
      Tuple.projection p f m.unop.len :=
  rfl

end Stacks.RelativeCech

end

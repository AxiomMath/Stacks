module

public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.Functoriality

/-!
# Fibre homology is functorial for the chosen pullbacks of a fibred category

Let `p : C ⥤ D` be a fibred category whose fibres are small, let `F` be an abelian presheaf on
`C`, and for a morphism `h : V' ⟶ V` of the base let `h^* : C_V ⥤ C_{V'}` be the pullback functor
of the chosen pullbacks of `p`. Restricting `F` along the chosen cartesian lifts gives a
coefficient morphism from `F|_{C_V}` to the restriction of `F|_{C_{V'}}` along `h^*`, hence a map

```
H_n(C_V, F|_{C_V}) ⟶ H_n(C_{V'}, F|_{C_{V'}})
```

by Stacks 08PH. This file proves that those maps obey the identity and composition laws, so that
`V ↦ H_n(C_V, F|_{C_V})` is a presheaf on the base.

## Main results

* `Stacks.CategoryHomology.categoryHomologyMap_pullbackFunctor_id`: the identity law.
* `Stacks.CategoryHomology.categoryHomologyMap_pullbackFunctor_comp`: the composition law.

## Implementation notes

The coefficient morphisms are a parameter `t`, required by the hypothesis `ht` to be, on every
object of every fibre, restriction of `F` along the chosen cartesian lift.

The fibres of `p` must be small for `Stacks.CategoryHomology.categoryHomology` to apply, which is
why the morphisms of `C` are taken in the same universe as its objects.

`CategoryTheory.Functor.Fiber` is a plain `def` unfolding to a subtype, so after the chosen lift of
`g ≫ f` is replaced by its factorization the goal mentions `(x : p.Fiber U).1` and is no longer
type-correct at the `implicit` transparency level that `simp`'s matcher unifies at; `Fiber` and
`fiberInclusion` are therefore made locally `implicit_reducible`.

## References

* [Stacks Project, Tag 08PI](https://stacks.math.columbia.edu/tag/08PI)
* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.CategoryHomology

universe uD vD uC w

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{uC} C]
  (p : C ⥤ D) [p.IsFibered] (F : Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC})
  (t : ∀ {V V' : D} (h : V' ⟶ V),
    ((Functor.Fiber.fiberInclusion (p := p) (S := V)).op ⋙ F) ⟶
      ((Functor.chosenPullbacks p).pullbackFunctor h).op ⋙
        ((Functor.Fiber.fiberInclusion (p := p) (S := V')).op ⋙ F))
  (ht : ∀ {V V' : D} (h : V' ⟶ V) (x : p.Fiber V),
    (t h).app (.op x) = F.map (.op ((Functor.chosenPullbacks p).map h x)))

include ht in
/-- The map on fibre homology induced by the chosen pullback along an identity morphism is the
identity. -/
theorem categoryHomologyMap_pullbackFunctor_id (n : ℕ) (V : D) :
    categoryHomologyMap.{uC, uC, max w uD vD uC}
      ((Functor.chosenPullbacks p).pullbackFunctor (𝟙 V)) (t (𝟙 V)) n = 𝟙 _ := by
  rw [categoryHomologyMap_iso.{uC, uC, max w uD vD uC} _ _
    ((Functor.chosenPullbacks p).pullbackFunctorIdIso V) (t (𝟙 V)) (𝟙 _) ?_,
    categoryHomologyMap_id.{uC, max w uD vD uC}]
  refine NatTrans.ext (funext fun x => ?_)
  change (t (𝟙 V)).app x =
    𝟙 _ ≫ F.map ((Functor.Fiber.fiberInclusion.map
      ((Functor.chosenPullbacks p).objIdIso x.unop).hom).op)
  rw [Category.id_comp, Functor.ChoiceOfPullbacks.fiberInclusion_map_objIdIso_hom]
  exact ht (𝟙 V) x.unop

include ht in
/-- The map on fibre homology induced by the chosen pullback along `g ≫ f` is the map induced by
the chosen pullback along `f` followed by the map induced by the chosen pullback along `g`. -/
theorem categoryHomologyMap_pullbackFunctor_comp (n : ℕ) {W V U : D} (g : W ⟶ V) (f : V ⟶ U) :
    categoryHomologyMap.{uC, uC, max w uD vD uC}
        ((Functor.chosenPullbacks p).pullbackFunctor (g ≫ f)) (t (g ≫ f)) n =
      categoryHomologyMap.{uC, uC, max w uD vD uC}
          ((Functor.chosenPullbacks p).pullbackFunctor f) (t f) n ≫
        categoryHomologyMap.{uC, uC, max w uD vD uC}
          ((Functor.chosenPullbacks p).pullbackFunctor g) (t g) n := by
  rw [categoryHomologyMap_iso.{uC, uC, max w uD vD uC} _ _
    ((Functor.chosenPullbacks p).pullbackFunctorCompIso g f) (t (g ≫ f))
    (t f ≫ Functor.whiskerLeft ((Functor.chosenPullbacks p).pullbackFunctor f).op (t g)) ?_,
    categoryHomologyMap_comp.{uC, uC, uC, max w uD vD uC}]
  refine NatTrans.ext (funext fun x => ?_)
  change (t (g ≫ f)).app x =
    ((t f).app x ≫ (t g).app (.op ((Functor.chosenPullbacks p).obj f x.unop))) ≫
      F.map ((Functor.Fiber.fiberInclusion.map
        ((Functor.chosenPullbacks p).objCompIso g f x.unop).hom).op)
  rw [ht (g ≫ f) x.unop, ht f x.unop, ht g ((Functor.chosenPullbacks p).obj f x.unop),
    ← (Functor.chosenPullbacks p).objCompIso_hom_fac g f x.unop]
  simp only [CategoryTheory.op_comp, F.map_comp]
  exact (Category.assoc (obj := AddCommGrpCat.{max w uD vD uC}) _ _ _).symm

end Stacks.CategoryHomology

end

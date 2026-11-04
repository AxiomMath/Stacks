module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Zariski sheaves, open subfunctors and coverings by subfunctors

A functor of points on schemes is a Zariski sheaf when compatible sections on open covers glue
uniquely. A subfunctor is representable by open immersions when its pullback along every point
of the ambient functor is an open subscheme. A family of subfunctors covers the functor when
every section belongs locally to the respectively indexed members. The last notion applies
equally to schemes and to locally ringed spaces.

## Main definitions

* `AlgebraicGeometry.Covers`: an indexed family of subfunctors covers a functor.

## Implementation notes

Parts (1) and (2) of the source are Mathlib's sheaf and subfunctor predicates,
`CategoryTheory.Presheaf.IsSheaf` and `CategoryTheory.Subfunctor`. Part (3) is Mathlib's
relative morphism property for presheaves, `CategoryTheory.MorphismProperty.presheaf`,
specialized to open immersions and applied to the inclusion of the subfunctor; its Yoneda
pullback condition gives the universal factorization property of the corresponding open
subscheme. Those three are recorded against the tag rather than restated.

In part (4), an indexed open cover is given by open immersions whose underlying images cover
every point. This categorical formulation also works for functors on locally ringed spaces, and
is equivalent to choosing one open subspace for each index. The functor to topological spaces
and the open immersion property are explicit parameters so either ambient category can be used
without changing the covering predicate.

## References

* [Stacks Project, Tag 01JI](https://stacks.math.columbia.edu/tag/01JI)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry

universe u v w u' v'

add_to_stacks 01JI "part (1): Zariski sheaf property" CategoryTheory.Presheaf.IsSheaf
add_to_sga "3 IV 4.3.1" "more general" CategoryTheory.Presheaf.IsSheaf
add_to_sga "3 IV 4.3.18" CategoryTheory.Presheaf.IsSheaf
add_to_sga "4 II 2.1" "more general" CategoryTheory.Presheaf.IsSheaf
add_to_sga "4 II 2.7" CategoryTheory.Presheaf.IsSheaf
add_to_sga "4 II 6.1" CategoryTheory.Presheaf.IsSheaf
add_to_sga "4 II 6.2" CategoryTheory.Presheaf.IsSheaf
add_to_sga "4 II 6.3.2" "partial" CategoryTheory.Presheaf.IsSheaf
add_to_sga "4½ Arcata 1.2.3" "more general" CategoryTheory.Presheaf.IsSheaf
add_to_sga "7 VI 3.1(a)" "partial" CategoryTheory.Presheaf.IsSheaf
add_to_ega "0 3.1.2" CategoryTheory.Presheaf.IsSheaf
add_to_ega "0 3.1.4" CategoryTheory.Presheaf.IsSheaf
add_to_stacks 01JI "part (2): subfunctors" CategoryTheory.Subfunctor
add_to_stacks 01JI "part (3): representability by open immersions"
  CategoryTheory.MorphismProperty.presheaf

/-- An indexed family of subfunctors covers a functor if each section belongs,
after restriction to an indexed open covering, to the corresponding subfunctor. -/
@[stacks 01JI "part (4): covering by subfunctors"]
public abbrev Covers {C : Type u} [Category.{v} C] (toTop : C ⥤ TopCat.{u'})
    (isOpenImmersion : MorphismProperty C) (F : Cᵒᵖ ⥤ Type w) {I : Type v'}
    (H : I → Subfunctor F) : Prop :=
  ∀ (X : C) (s : F.obj (op X)), ∃ (U : I → C) (ι : ∀ i, U i ⟶ X),
    (∀ i, isOpenImmersion (ι i)) ∧
      (∀ x : toTop.obj X, ∃ (i : I) (y : toTop.obj (U i)), (toTop.map (ι i)) y = x) ∧
      (∀ i, F.map (ι i).op s ∈ (H i).obj (op (U i)))

end AlgebraicGeometry

end

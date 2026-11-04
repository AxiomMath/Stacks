module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ResolutionFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Computing a right derived functor by injective resolutions

Let `F : C ⥤ D` be an additive functor between abelian categories and suppose `C` has enough
injectives. A resolution functor for `C` descends to a functor
`j' : D⁺(C) ⥤ K⁺(InjectiveObject C)` which is a section, up to isomorphism, of the canonical
functor `K⁺(InjectiveObject C) ⥤ D⁺(C)`. Stacks 05U5 is the statement that the right derived
functor `RF` is then computed by applying `j'` and `F` degreewise: the triangle
`D⁺(C) ⥤ K⁺(InjectiveObject C) ⥤ D⁺(D)` and `RF` is `2`-commutative.

For the category of modules on a ringed site — the setting of the source — this is the
instance of that statement at the abelian category of sheaves of modules, which has enough
injectives; the statement itself is about an arbitrary abelian category with enough
injectives and is already proved as
`CategoryTheory.Functor.exists_iso_rightDerivedFunctorPlus_of_comp_Qh_iso_id`, where it
carries the tag of its Derived Categories counterpart 05TN. This file records that the same
declaration is the content of 05U5, rather than restating it.

## Main results

* `CategoryTheory.Functor.exists_iso_rightDerivedFunctorPlus_of_comp_Qh_iso_id` (in
  `StacksFrontier.Algebra.Homology.DerivedCategory.ResolutionFunctor`): the natural isomorphism
  `RF ≅ F ∘ j'`, together with the formula for its components.

## Implementation notes

The equality of functors in the displayed formula of the source is represented by a natural
isomorphism; the component formula pins it down to the canonical one, and its naturality is
part of the data of the isomorphism.

## References

* [Stacks Project, Tag 05U5](https://stacks.math.columbia.edu/tag/05U5)
* [Stacks Project, Tag 05TN](https://stacks.math.columbia.edu/tag/05TN)
-/

@[expose] public section

add_to_stacks 05U5
  CategoryTheory.Functor.exists_iso_rightDerivedFunctorPlus_of_comp_Qh_iso_id

end

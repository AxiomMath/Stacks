module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
import StacksCore.Tactic.StacksAttribute

/-!
# Higher right derived functors on a ringed site

Let `(C, O)` be a ringed site and let `F : Mod(O) ⥤ B` be a left exact functor into an
abelian category. Stacks 05U6 is the displayed equation defining the higher right derived
functors of `F`, namely `R^i F = H^i ∘ RF`, where `RF : D⁺(Mod(O)) ⥤ D⁺(B)` is the right
derived functor of `F` on bounded below derived categories and an object of `Mod(O)` is
regarded as a complex concentrated in degree `0`.

That equation is the *definition* of the higher right derived functors, and it is already
available in this repository at the generality it is stated at in the source: for any
additive functor between abelian categories whose source has enough injectives, as
`CategoryTheory.Functor.rightDerivedPlus`, where it carries the tag of its Derived
Categories counterpart 015A. The category of sheaves of modules on a ringed site is
abelian and has enough injectives, so the displayed equation of 05U6 is the specialization
of that definition; this file records that rather than restating it.

## Main results

* `CategoryTheory.Functor.rightDerivedPlus` (in
  `StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective`): the functor
  `R^i F`, defined as the degree-zero embedding followed by `RF` followed by `H^i`.

## Implementation notes

The source writes `R^iF = H^i ∘ RF` with the embedding `Mod(O) → D⁺(Mod(O))` left implicit;
the definition makes it explicit as `DerivedCategory.Plus.singleFunctor _ 0`. The source's
left exactness hypothesis on `F` is not needed for the definition — additivity is — and is
therefore not imposed here, exactly as in the general definition of 015A.

## References

* [Stacks Project, Tag 05U6](https://stacks.math.columbia.edu/tag/05U6)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
-/

@[expose] public section

add_to_stacks 05U6 CategoryTheory.Functor.rightDerivedPlus

end

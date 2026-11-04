module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomMapComparison

/-!
# Internal Hom of a termwise split short exact sequence of complexes

Let `(C, O)` be a ringed site and let

`0 ⟶ S₁ ⟶ S₂ ⟶ S₃ ⟶ 0`

be a short complex of complexes of `O`-modules which is split in every degree.  Applying the
internal Hom complex in either variable gives a short complex of complexes of `O`-modules which
is again split in every degree — by
`Stacks.Cohomology.InternalHom.internalHomComplex_termwiseSplit_first` and `..._second` — and a
termwise split short complex in an abelian category is short exact.

This file records that consequence.  It is the step the Stacks project's proof of 08JC consists
of: the assignment `(L, M) ↦ SheafHom(L, M)` "transforms a termwise split short exact sequence of
complexes in either variable into a termwise split short exact sequence", from which the
statement about distinguished triangles follows, since a short exact sequence of complexes gives
a distinguished triangle in the derived category by
`CategoryTheory.DerivedCategory.triangleOfSES_distinguished`.

## Main results

* `Stacks.Cohomology.InternalHom.internalHom_shortExact_second`: short exactness of the internal
  Hom complexes out of a fixed complex, in the covariant variable.
* `Stacks.Cohomology.InternalHom.internalHom_shortExact_first`: the same in the contravariant
  variable, where the order of the two maps is reversed.

## Implementation notes

The existential `w` is the vanishing of the composite, which the termwise split theorems produce
rather than take as a hypothesis, so it is passed along rather than reproved.  Short exactness is
then degreewise, by `CategoryTheory.ShortComplex.Splitting.shortExact` on each degree and
`HomologicalComplex.shortExact_of_degreewise_shortExact` to assemble.

Neither declaration carries `@[stacks 08JC]`.  Tag 08JC is the statement about *distinguished
triangles* in `D(O)`; these are its cochain-level input, and a tag attribute here would report
the whole of 08JC formalized off that input: only the presence of an attribute is read, never
the clause comment on it.  What remains is to carry these across the localisation: for a
distinguished triangle of `D(O)`, present it as the triangle of a termwise split short exact
sequence of complexes, apply the results below, and transport along the K-injective model
comparison `AlgebraicGeometry.RingedSite.derivedSheafHomComparison` together with its
naturality.  The identification
`Stacks.Cohomology.InternalHom.homMap_eq_sheafHomComplexMap` is what lets those two be composed,
since the comparison is stated for `AlgebraicGeometry.RingedSite.homMap` and the results below
for `Stacks.Cohomology.InternalHom.sheafHomComplexMap`.

## References

* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.InternalHom

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
    [HasWeakSheafify X.J AddCommGrpCat.{u}]

/-- **The cochain-level content of Stacks 08JC, covariant variable.**  Internal Hom out of a
fixed complex `K` carries a termwise split short complex of complexes of `O`-modules to a short
exact sequence of internal Hom complexes. -/
theorem internalHom_shortExact_second
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (hS : ∀ n, Nonempty
      ((S.map (HomologicalComplex.eval
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) n)).Splitting))
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ∃ w : sheafHomComplexMap X (𝟙 K) S.f ≫ sheafHomComplexMap X (𝟙 K) S.g = 0,
      (ShortComplex.mk (sheafHomComplexMap X (𝟙 K) S.f)
        (sheafHomComplexMap X (𝟙 K) S.g) w).ShortExact := by
  exact (internalHomComplex_termwiseSplit_second X S hS K).imp
    fun _ hw => HomologicalComplex.shortExact_of_degreewise_shortExact _
      fun n => (hw n).some.shortExact

/-- **The cochain-level content of Stacks 08JC, contravariant variable.**  Internal Hom into a
fixed complex `K` carries a termwise split short complex of complexes of `O`-modules to a short
exact sequence of internal Hom complexes, with the order of the two maps reversed. -/
theorem internalHom_shortExact_first
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (hS : ∀ n, Nonempty
      ((S.map (HomologicalComplex.eval
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) n)).Splitting))
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ∃ w : sheafHomComplexMap X S.g (𝟙 K) ≫ sheafHomComplexMap X S.f (𝟙 K) = 0,
      (ShortComplex.mk (sheafHomComplexMap X S.g (𝟙 K))
        (sheafHomComplexMap X S.f (𝟙 K)) w).ShortExact := by
  exact (internalHomComplex_termwiseSplit_first X S hS K).imp
    fun _ hw => HomologicalComplex.shortExact_of_degreewise_shortExact _
      fun n => (hw n).some.shortExact

end Stacks.Cohomology.InternalHom

end

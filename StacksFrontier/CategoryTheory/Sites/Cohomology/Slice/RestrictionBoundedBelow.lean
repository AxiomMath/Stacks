module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.QuasiIsomorphismLocality

/-!
# Restriction to a slice of the site preserves a lower cohomological bound

Let `(C, O)` be a ringed site, let `U` be an object of `C` and let `E` be a complex of
`O`-modules whose cohomology vanishes in every degree below `b`. Then the cohomology of the
degreewise restriction `E|_U` vanishes in every degree below `b` as well.

Restriction to a slice is exact, so it carries the degree-`i` cohomology of `E` to the degree-`i`
cohomology of `E|_U`; a zero object is carried to a zero object, which is the statement.

## Main results

* `AlgebraicGeometry.RingedSite.isGE_Q_obj_restrictComplex`: the bound `b` is inherited by the
  restriction.

## Implementation notes

The hypothesis and the conclusion are phrased for the classes of the two complexes in the
derived categories of `O`-modules and of `O|_U`-modules, through
`CategoryTheory.DerivedCategory.IsGE`.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A lower cohomological bound on a complex of `O`-modules is inherited by its restriction to
a slice of the site.** If the cohomology of `E` vanishes in every degree below `b`, then so does
the cohomology of `E|_U`. -/
public theorem isGE_Q_obj_restrictComplex (U : X.C)
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (b : ℤ)
    (h : (DerivedCategory.Q.obj E).IsGE b) :
    (DerivedCategory.Q.obj (restrictComplex X E U)).IsGE b := by
  have := Stacks.SheafOfModules.preservesHomology_overFunctor
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  rw [DerivedCategory.isGE_iff] at h ⊢
  intro i hi
  exact ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_isZero
    ((h i hi).of_iso ((DerivedCategory.homologyFunctorFactors _ i).app E).symm)).of_iso
    (((DerivedCategory.homologyFunctorFactors _ i).app (restrictComplex X E U)).trans
      ((E.sc i).mapHomologyIso
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)))

end AlgebraicGeometry.RingedSite

end

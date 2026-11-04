module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparison

/-!
# The derived dual of a strictly perfect complex is its naive dual

Let `(C, O)` be a ringed site and let `E` be a strictly perfect complex of `O`-modules —
bounded, with every term a direct summand of a finite free module. The derived dual
`E^∨ = RSheafHom(E, O)` of `AlgebraicGeometry.RingedSite.derivedDual` is then represented by the
*naive* dual, the internal Hom complex `SheafHom(E, O)` of Stacks 0A8Z taken into the structure
sheaf in degree zero.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedDualIsoSheafHomComplexUnit`: **the derived dual agrees
  with the naive termwise dual** on a strictly perfect complex.

## Implementation notes

This is [Stacks, Tag 08JH] read at the target `O`, with no new mathematical content: the
comparison `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison` out of the internal Hom
complex is invertible for a strictly perfect source by
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso`, and the derived dual is by
definition the derived internal Hom into
`AlgebraicGeometry.RingedSite.derivedStructureSheaf`, which is the class of
`AlgebraicGeometry.RingedSite.structureSheafComplex`. So the statement is the comparison at
`F = structureSheafComplex X`, promoted to an isomorphism, and its direction is from the naive
dual to the derived one, the direction the comparison has.

The derived internal Hom is taken at
`AlgebraicGeometry.RingedSite.derivedInternalHomOfBifunctor`, the
`AlgebraicGeometry.RingedSite.DerivedInternalHom` datum whose bifunctor is
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` itself, so that the target of the
comparison is the derived dual on the nose rather than up to a comparison of models.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The derived dual of a strictly perfect complex is its naive termwise dual.** For `E`
bounded with every term a direct summand of a finite free `O`-module, the internal Hom complex
`SheafHom(E, O)` of Stacks 0A8Z represents the derived dual `E^∨ = RSheafHom(E, O)`.

This is [Stacks, Tag 08JH] at the target `O`: the canonical comparison
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison` is invertible for a strictly perfect
source, and the derived dual is the derived internal Hom into the class of
`AlgebraicGeometry.RingedSite.structureSheafComplex`. -/
def derivedDualIsoSheafHomComplexUnit
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i : ℤ, IsFiniteFreeSummand X (E.X i)) :
    DerivedCategory.Q.obj (sheafHomComplex X E (structureSheafComplex X)).obj ≅
      derivedDual X (DerivedCategory.Q.obj E) :=
  haveI := strictlyPerfectHomComparison_isIso X (derivedInternalHomOfBifunctor X) E
    (structureSheafComplex X) hbdd hterm
  asIso (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) E
    (structureSheafComplex X))

/-- The isomorphism `derivedDualIsoSheafHomComplexUnit` is the canonical comparison of
[Stacks, Tag 08JH], so every identity available for that comparison applies to it. -/
theorem derivedDualIsoSheafHomComplexUnit_hom
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i : ℤ, IsFiniteFreeSummand X (E.X i)) :
    (derivedDualIsoSheafHomComplexUnit X E hbdd hterm).hom =
      strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) E
        (structureSheafComplex X) :=
  rfl

end AlgebraicGeometry.RingedSite

end

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionAsTranspose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedApplicationEvaluationSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexCompositionComparison

/-!
# Derived composition pinned to the transpose of the double contraction

Let `(C, O)` be a ringed site and let `K`, `L`, `M` be complexes of `O`-modules. The derived
composition of Stacks 0A8V, conjugated by three copies of the comparison of Stacks 08DM, is the
class of the transpose, under the cochain-level currying bijection of Stacks 0A90, of the double
contraction, with no K-flatness and no K-injectivity hypothesis anywhere.

## Main results

* `AlgebraicGeometry.RingedSite.homComplexDerivedComposition_eq_curryHomEquiv_doubleContraction`:
  the naive composition of Stacks 0A91, read in `D(O)`, is the class of the transpose of the
  double contraction.
* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_composition_doubleContraction`: the
  derived composition of Stacks 0A8V, conjugated by the comparison of Stacks 08DM, is the class of
  the transpose of the double contraction.

## Implementation notes

The comparison `strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) _ _` is written
out in the statements: the `maxRecDepth` failure it causes elsewhere appears only in a statement
that also mentions `derivedCurryHomEquiv`.

The site-level map of derived tensor products is `AlgebraicGeometry.RingedSite.derivedTensorMap`;
`Stacks.SheafOfModules.derivedTensorMap` is the ringed-space abbreviation and does not apply to a
`RingedSite`.

## References

* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The naive composition of Stacks 0A91, read in `D(O)`, is the class of the transpose of the
double contraction: the canonical map from the derived tensor product to the class of the total
tensor complex, followed by the class of the `curryHomEquiv`-transpose of
`AlgebraicGeometry.RingedSite.doubleContraction`. -/
theorem homComplexDerivedComposition_eq_curryHomEquiv_doubleContraction
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    homComplexDerivedComposition X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
        K L M =
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor
          (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj ≫
        DerivedCategory.Q.map
          (curryHomEquiv X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj
            (sheafHomComplex X K M).obj (doubleContraction X K L M)) := by
  rw [homComplexDerivedComposition, curryHomEquiv_doubleContraction]

/-- Derived composition of Stacks 0A8V, conjugated by the comparison of Stacks 08DM, is the
class of the transpose of the double contraction: for arbitrary complexes `K`, `L`, `M` of
`O`-modules — no K-flatness, no K-injectivity:

`(σ_{L,M} ⊗ σ_{K,L}) ≫ cmp_{QK,QL,QM} = toTensor ≫ Q(curryHomEquiv (doubleContraction)) ≫ σ_{K,M}`.
-/
theorem strictlyPerfectHomComparison_composition_doubleContraction
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    derivedTensorMap X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
          (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) L M)
          (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) K L) ≫
        derivedSheafHomComposition X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
          (derivedInternalHomOfBifunctor X) (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) =
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor
          (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj ≫
        DerivedCategory.Q.map
          (curryHomEquiv X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj
            (sheafHomComplex X K M).obj (doubleContraction X K L M)) ≫
          strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) K M := by
  rw [strictlyPerfectHomComparison_composition X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) (derivedInternalHomOfBifunctor X)
      K L M,
    homComplexDerivedComposition_eq_curryHomEquiv_doubleContraction X K L M, Category.assoc]

end AlgebraicGeometry.RingedSite

end

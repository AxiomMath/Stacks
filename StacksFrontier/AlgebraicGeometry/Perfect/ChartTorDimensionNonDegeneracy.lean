module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectNotFibrewise
public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimensionNestedRestriction

/-!
# The chart condition of Stacks 0DI2 at a named morphism and a nonzero object

`AlgebraicGeometry.Scheme.Hom.chartHasFiniteTorDimension_of_locallyHasFiniteTorDimension` is the
implication (1) ⟹ (2) of the Tor-dimension clause of Stacks 0DI2. Its hypothesis is condition
(1), locally finite Tor dimension over `f⁻¹𝒪_S`, which is satisfied by every zero object; so the
implication on its own leaves open whether anything it says is about a nonzero complex.

This file settles that by instantiating every binder of it at once: the morphism is the structure
map `Spec k[ε] ⟶ Spec k` of the dual numbers over a field, which is flat and locally of finite
presentation; the object is the residue field of `k[ε]` placed in degree zero, which is not a
zero object (`AlgebraicGeometry.not_isZero_dualNumberResidueComplex`); and the conclusion is
obtained on every affine open of `Spec k[ε]`, in particular on `⊤`.

## Main results

* `AlgebraicGeometry.not_isZero_and_chartHasFiniteTorDimension_dualNumberResidueComplex`: at
  `Spec k[ε] ⟶ Spec k`, the chart condition of clause (2) of Stacks 0DI2 holds on every affine
  open for an object that is not zero.
* `AlgebraicGeometry.not_isZero_and_chartHasFiniteTorDimension_top_dualNumberResidueComplex`: the
  same read on `⊤`, with no binder left.

## Implementation notes

The hypothesis is read off the first conjunct of
`AlgebraicGeometry.isPerfectRelativeTo_dualNumberResidueComplex_and_not_isPerfect`, whose second
component is, by the definition of `AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo`, exactly
condition (1) at the canonical certificate family. Nothing is reproved here.

Neither statement is a clause of Stacks 0DI2 and neither carries a `@[stacks]` attribute: they
assert nothing the source asserts. They are certificates that the registered clause is not
vacuous.

## References

* [The Stacks Project, Lemma 36.35.3 (0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [The Stacks Project, Example 36.35.2 (0DI1)](https://stacks.math.columbia.edu/tag/0DI1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **The chart condition of clause (2) of Stacks 0DI2 holds at a nonzero object.** Over the
structure morphism `Spec k[ε] ⟶ Spec k` of the dual numbers, the residue complex of `k[ε]` is
not a zero object and its restriction to every affine open has finite Tor dimension over
`f⁻¹𝒪_{Spec k}`.

Both components are instantiations: the first is
`AlgebraicGeometry.not_isZero_dualNumberResidueComplex`, and the second is
`AlgebraicGeometry.Scheme.Hom.chartHasFiniteTorDimension_of_locallyHasFiniteTorDimension` fed the
Tor-dimension half of
`AlgebraicGeometry.isPerfectRelativeTo_dualNumberResidueComplex_and_not_isPerfect`. -/
public theorem not_isZero_and_chartHasFiniteTorDimension_dualNumberResidueComplex
    (k : Type u) [Field k]
    (U : Opens (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace
      (dualNumberStructureMap k).base).carrier)
    (hU : IsAffineOpen (X := Spec (CommRingCat.of (DualNumber k))) U) :
    ¬ IsZero (dualNumberResidueComplex k) ∧
      Scheme.Hom.ChartHasFiniteTorDimension (dualNumberStructureMap k)
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace
            (dualNumberStructureMap k).base))
        (dualNumberResidueComplex k) U :=
  ⟨not_isZero_dualNumberResidueComplex k,
    Scheme.Hom.chartHasFiniteTorDimension_of_locallyHasFiniteTorDimension
      (dualNumberStructureMap k) (dualNumberResidueComplex k)
      (isPerfectRelativeTo_dualNumberResidueComplex_and_not_isPerfect k).1.2 U hU⟩

/-- **The same with no binder left**, read on the affine open `⊤` of `Spec k[ε]`. -/
public theorem not_isZero_and_chartHasFiniteTorDimension_top_dualNumberResidueComplex
    (k : Type u) [Field k] :
    ¬ IsZero (dualNumberResidueComplex k) ∧
      Scheme.Hom.ChartHasFiniteTorDimension (dualNumberStructureMap k)
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace
            (dualNumberStructureMap k).base))
        (dualNumberResidueComplex k) ⊤ :=
  not_isZero_and_chartHasFiniteTorDimension_dualNumberResidueComplex k ⊤
    (isAffineOpen_top (Spec (CommRingCat.of (DualNumber k))))

end AlgebraicGeometry

end

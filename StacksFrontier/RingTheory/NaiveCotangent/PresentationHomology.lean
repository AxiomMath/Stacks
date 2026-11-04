module

public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.Homology.DoubleHomology
public import StacksFrontier.RingTheory.NaiveCotangent.Defs
public import StacksFrontier.Homology.DoubleExtend

/-!
# The two homology modules of the naive cotangent complex are presentation independent

For a ring map `R → S` the naive cotangent complex `Algebra.naiveCotangentComplex R S` is
built from the *tautological* presentation `R[S] → S` of `Algebra.Generators.self R S`. Its
two homology modules are the kernel and the cokernel of `Algebra.Extension.cotangentComplex` of
that presentation. Both agree with the corresponding modules of an *arbitrary* presentation
`P : Algebra.Generators R S ι`:

* in degree `1` by Mathlib's `Algebra.Generators.equivH1Cotangent`, which is exactly the
  statement that `H₁(L_{S/R})` does not depend on the presentation;
* in degree `0` because *both* cokernels are `Ω[S⁄R]`: the sequence
  `I/I² → Ω_{P/R} ⊗_P S → Ω[S⁄R] → 0` is exact and the last map is surjective for every
  presentation (`Algebra.Extension.exact_cotangentComplex_toKaehler` and
  `Algebra.Extension.toKaehler_surjective`), so the cokernel of the differential is `Ω[S⁄R]`
  on the nose.

## Main definitions

* `Algebra.Extension.quotRangeCotangentComplexEquivKaehler`: for any extension,
  `Ω_{P/R} ⊗_P S` modulo the image of the differential is `Ω[S⁄R]`.
* `Algebra.Extension.h1CotangentEquivKer`: `Algebra.Extension.H1Cotangent` is the kernel of
  the differential.

## Main results

* `NaiveCotangent.naiveCotangentComplexHomologyOneEquiv`:
  `(Algebra.naiveCotangentComplex R S).homology 1 ≃ₗ[S] ker (NL P)` for any presentation `P`.
* `NaiveCotangent.naiveCotangentComplexHomologyZeroEquiv`:
  `(Algebra.naiveCotangentComplex R S).homology 0 ≃ₗ[S] coker (NL P)` for any presentation `P`.
* `NaiveCotangent.annihilator_homology_one_eq`,
  `NaiveCotangent.annihilator_homology_zero_eq`: the same two statements as equalities of
  annihilator ideals.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
* [Stacks Project, Tag 07BN](https://stacks.math.columbia.edu/tag/07BN)
-/

@[expose] public section

open CategoryTheory

namespace Algebra.Extension

universe w u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  (P : Extension.{w} R S)

/-- **The cokernel of the differential of `NL(α)` is `Ω[S⁄R]`, for every presentation.** The
three-term sequence `I/I² → Ω_{P/R} ⊗_P S → Ω[S⁄R] → 0` is exact with surjective last map, so
dividing the degree-`0` term by the image of the differential gives `Ω[S⁄R]`. -/
public noncomputable def quotRangeCotangentComplexEquivKaehler :
    (P.CotangentSpace ⧸ LinearMap.range P.cotangentComplex) ≃ₗ[S] Ω[S⁄R] :=
  (Submodule.quotEquivOfEq _ _
      (LinearMap.exact_iff.mp P.exact_cotangentComplex_toKaehler).symm).trans
    (P.toKaehler.quotKerEquivOfSurjective P.toKaehler_surjective)

/-- `Algebra.Extension.H1Cotangent` is the kernel of the differential of `NL(α)`. -/
public noncomputable def h1CotangentEquivKer :
    P.H1Cotangent ≃ₗ[S] LinearMap.ker P.cotangentComplex :=
  LinearEquiv.refl S _

end Algebra.Extension

namespace NaiveCotangent

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type w} (P : Algebra.Generators R S ι)

/-- **The degree-`1` homology of `NL_{S/R}` is the kernel of the differential of `NL(α)`, for
every presentation `α`.** Degree `1` of `Algebra.naiveCotangentComplex R S` is the kernel of
the differential of the tautological presentation, and
`Algebra.Generators.equivH1Cotangent` identifies that kernel with the one of `P`. -/
public noncomputable def naiveCotangentComplexHomologyOneEquiv :
    (Algebra.naiveCotangentComplex R S).homology 1 ≃ₗ[S]
      LinearMap.ker P.toExtension.cotangentComplex :=
  (doubleHomologyLinearEquivKer (R := S)
      (Algebra.Generators.self R S).toExtension.cotangentComplex
      ComplexShape.downNatRelOneZero one_ne_zero).trans
    (((Algebra.Extension.h1CotangentEquivKer _).symm.trans
      ((Algebra.Generators.self R S).equivH1Cotangent.trans
        P.equivH1Cotangent.symm)).trans (Algebra.Extension.h1CotangentEquivKer _))

/-- **The degree-`0` homology of `NL_{S/R}` is the cokernel of the differential of `NL(α)`,
for every presentation `α`.** Degree `0` of `Algebra.naiveCotangentComplex R S` is the
cokernel of the differential of the tautological presentation, and both cokernels are
`Ω[S⁄R]` by `Algebra.Extension.quotRangeCotangentComplexEquivKaehler`. -/
public noncomputable def naiveCotangentComplexHomologyZeroEquiv :
    (Algebra.naiveCotangentComplex R S).homology 0 ≃ₗ[S]
      (P.toExtension.CotangentSpace ⧸ LinearMap.range P.toExtension.cotangentComplex) :=
  (doubleHomologyLinearEquivQuotient (R := S)
      (Algebra.Generators.self R S).toExtension.cotangentComplex
      ComplexShape.downNatRelOneZero one_ne_zero).trans
    ((Algebra.Extension.quotRangeCotangentComplexEquivKaehler _).trans
      (Algebra.Extension.quotRangeCotangentComplexEquivKaehler P.toExtension).symm)

/-- Annihilating the degree-`1` homology of `NL_{S/R}` is annihilating the kernel of the
differential of `NL(α)`, for every presentation `α`. -/
public theorem annihilator_homology_one_eq :
    Module.annihilator S ((Algebra.naiveCotangentComplex R S).homology 1) =
      Module.annihilator S (LinearMap.ker P.toExtension.cotangentComplex) :=
  (naiveCotangentComplexHomologyOneEquiv P).annihilator_eq

/-- Annihilating the degree-`0` homology of `NL_{S/R}` is annihilating the cokernel of the
differential of `NL(α)`, for every presentation `α`. -/
public theorem annihilator_homology_zero_eq :
    Module.annihilator S ((Algebra.naiveCotangentComplex R S).homology 0) =
      Module.annihilator S
        (P.toExtension.CotangentSpace ⧸ LinearMap.range P.toExtension.cotangentComplex) :=
  (naiveCotangentComplexHomologyZeroEquiv P).annihilator_eq

end NaiveCotangent

end

module

public import StacksFrontier.RingTheory.Dualizing.TrivialDualityBundleConjugation
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialEvalDualityReduction

/-!
# Stacks 0BZH for a surjection with invertible kernel, and the polynomial evaluation duality

`Dualizing.InvertibleKernel.derivedHomIsoDerivedTensorConormalInverseShift` proves Stacks 0BZH
for a surjection `R → A` whose kernel is an invertible `R`-module under the hypothesis of
Stacks 0BZE in the form of invertibility of `Stacks0BZE.comparison` at every K-flat complex.
This file proves Stacks 0BZH for such a surjection without that hypothesis.

What replaces it is the differential graded form of Stacks 0BZE:
`Dualizing.InvertibleKernel.exists_derivedHom_iso_derivedTensor_factor_class_of_invertible_ker`
produces a differential graded `(R, A)`-bimodule `M` with
`RHom_R(A, -) ≅ Dualizing.derivedTensorBimoduleFunctor M`, and identifies the class of its right
module in `D(A)` with the conormal inverse shift `N[-1]`. The passage from that shape to the
derived change-of-rings shape of Stacks 06Y6 is
`Dualizing.nonempty_derivedTensorBimoduleFunctor_iso_canonical`. Replacing the tensor factor by
one with the same class in `D(A)` is Stacks 0BYK, in the bundle form
`Dualizing.InvertibleKernel.derivedTensorIsoOfDerivedIso`.

The consequence is `Dualizing.PolynomialEvalDuality`: the conclusion of Stacks 0BZH at the
evaluation surjections `B[x] ↠ B`. It follows through
`Dualizing.polynomialEvalDuality_of_nonempty_derivedHom_iso`.

## Main results

* `Dualizing.InvertibleKernel.nonempty_derivedHom_iso_canonicalDerivedTensor_conormalInverseShift`
  — **Stacks 0BZH at the canonical model**, for a surjection whose kernel is an invertible
  module.
* `Dualizing.InvertibleKernel.nonempty_derivedHom_iso_derivedTensor_conormalInverseShift` — the
  same at an arbitrary model of the derived change-of-rings tensor product.
* `Dualizing.polynomialEvalDuality` — **`Dualizing.PolynomialEvalDuality` holds.**

## Implementation notes

The two statements about a general surjection are phrased for a bare ring homomorphism
`f : R →+* A` with `letI := f.toAlgebra`, because that is the algebra structure
`CochainComplex.extendScalarsLarge` builds and therefore the one
`Dualizing.nonempty_derivedTensorBimoduleFunctor_iso_canonical` is stated at. The step to
`Dualizing.PolynomialEvalDuality`, whose hypothesis quantifies over an arbitrary algebra
structure on `B` over `B[x]` together with an equation naming its structure map, rewrites that
structure to `(Polynomial.evalRingHom b).toAlgebra` by `Algebra.algebra_ext`: an algebra
structure is determined by its structure homomorphism.

## References

* [Stacks Project, Tag 0BZH](https://stacks.math.columbia.edu/tag/0BZH)
* [Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [Stacks Project, Tag 0BYK](https://stacks.math.columbia.edu/tag/0BYK)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.DerivedTensor
open DifferentialGraded DifferentialGradedModule
open Polynomial

attribute [local instance 10000] HasDerivedCategory.standard

universe u v

namespace Dualizing.InvertibleKernel

variable {R A : Type u} [CommRing R] [CommRing A]

/-- **Stacks 0BZH at the canonical model.** For a surjection `f : R → A` whose kernel is an
invertible `R`-module, derived coextension of scalars `RHom_R(A, -) : D(R) ⥤ D(A)` is the
canonical derived change-of-rings tensor product of Stacks 06Y6 with the conormal inverse shift
`N[-1]`.

The differential graded form of Stacks 0BZE holds for such a map, by
`Dualizing.InvertibleKernel.exists_derivedHom_iso_derivedTensor_factor_class_of_invertible_ker`;
`Dualizing.nonempty_derivedTensorBimoduleFunctor_iso_canonical` converts its tensor factor to the
change-of-rings shape, and `Dualizing.InvertibleKernel.derivedTensorIsoOfDerivedIso` — Stacks
0BYK — replaces that factor by `N[-1]`, which has the same class in `D(A)`. -/
theorem nonempty_derivedHom_iso_canonicalDerivedTensor_conormalInverseShift (f : R →+* A)
    (hf : Function.Surjective f) (hI : Module.Invertible R (RingHom.ker f)) :
    letI := f.toAlgebra
    Nonempty (Dualizing.derivedHom.{u, u} f ≅
      (canonicalDerivedTensorChangeOfRings.{u, u, u} f
        (conormalInverseShift.{u, u} R A)).F) := by
  let := f.toAlgebra
  obtain ⟨M, ⟨eFun⟩, ⟨eClass⟩⟩ :=
    exists_derivedHom_iso_derivedTensor_factor_class_of_invertible_ker hf hI
  obtain ⟨eCanon⟩ := Dualizing.nonempty_derivedTensorBimoduleFunctor_iso_canonical f M
  exact ⟨eFun ≪≫ eCanon ≪≫ derivedTensorIsoOfDerivedIso f
    (((degreeZeroDerivedComponentIso (R := R) (A := A)).app M.rightModule).symm ≪≫ eClass)
    _ _⟩

/-- **Stacks 0BZH.** For a surjection `f : R → A` whose kernel is an invertible `R`-module,
derived coextension of scalars `RHom_R(A, -) : D(R) ⥤ D(A)` is derived tensoring over `R` with
the conormal inverse shift `N[-1]`, at any model of the derived change-of-rings tensor product
with that factor.

This is
`Dualizing.InvertibleKernel.nonempty_derivedHom_iso_canonicalDerivedTensor_conormalInverseShift`
transported to an arbitrary model along `Dualizing.InvertibleKernel.derivedTensorIsoOfDerivedIso`
at the identity of the tensor factor. -/
@[stacks 0BZH "at module universe equal to the ring universe, with no carried hypothesis"]
theorem nonempty_derivedHom_iso_derivedTensor_conormalInverseShift (f : R →+* A)
    (hf : Function.Surjective f) (hI : Module.Invertible R (RingHom.ker f)) :
    letI := f.toAlgebra
    ∀ T : DerivedTensorChangeOfRings f (conormalInverseShift.{u, u} R A),
      Nonempty (Dualizing.derivedHom.{u, u} f ≅ T.F) := by
  let := f.toAlgebra
  intro T
  obtain ⟨e⟩ := nonempty_derivedHom_iso_canonicalDerivedTensor_conormalInverseShift f hf hI
  exact ⟨e ≪≫ derivedTensorIsoOfDerivedIso f (Iso.refl _) _ T⟩

end Dualizing.InvertibleKernel

namespace Dualizing

/-- **`Dualizing.PolynomialEvalDuality` holds.** Derived coextension of scalars
`RHom_{B[x]}(B, -)` along an evaluation surjection is derived base change along that map, shifted
by `-1`, for any total left derived functor presenting the base change.

This is `Dualizing.polynomialEvalDuality_of_nonempty_derivedHom_iso` fed with
`Dualizing.InvertibleKernel.nonempty_derivedHom_iso_canonicalDerivedTensor_conormalInverseShift`
at the evaluation surjections, whose hypotheses are
`Dualizing.InvertibleKernel.surjective_and_invertible_ker_evalRingHom`. -/
theorem polynomialEvalDuality : PolynomialEvalDuality.{u} := by
  refine polynomialEvalDuality_of_nonempty_derivedHom_iso ?_
  intro S _ c inst hmap
  have hinst : inst = (Polynomial.evalRingHom c).toAlgebra :=
    Algebra.algebra_ext _ _ (fun r => RingHom.congr_fun hmap r)
  subst hinst
  let : Algebra S[X] S := (Polynomial.evalRingHom c).toAlgebra
  obtain ⟨hsurj, hinv⟩ :=
    InvertibleKernel.surjective_and_invertible_ker_evalRingHom c rfl
  exact InvertibleKernel.nonempty_derivedHom_iso_canonicalDerivedTensor_conormalInverseShift
    (Polynomial.evalRingHom c) hsurj hinv

namespace PolynomialPresentation

/-- **Stacks 0BZJ.** The algebraic upper shriek functors attached to any two polynomial
presentations of the same finite type homomorphism are naturally isomorphic, so `f^!` is well
defined up to isomorphism.

This is `Dualizing.PolynomialPresentation.upperShriekFunctor_iso` with its hypothesis `hBZH`
supplied by `Dualizing.polynomialEvalDuality`. -/
@[stacks 0BZJ]
theorem nonempty_upperShriekFunctor_iso {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (p q : PolynomialPresentation f) :
    Nonempty (p.upperShriekFunctor.{u, v} ≅ q.upperShriekFunctor.{u, v}) :=
  upperShriekFunctor_iso polynomialEvalDuality.{max v u} f p q

end PolynomialPresentation

end Dualizing

end

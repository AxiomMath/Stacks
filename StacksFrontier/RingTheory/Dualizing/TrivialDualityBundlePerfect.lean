module

public import StacksFrontier.RingTheory.Dualizing.TrivialDualityBundleConjugation
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityInvertibleKernel

/-!
# Stacks 0BZE in the derived change-of-rings shape

`Dualizing.exists_derivedHom_iso_derivedTensor` proves Stacks 0BZE for a map `R → A` making `A`
a perfect `R`-module, in the shape the source's proof produces: derived coextension of scalars is
derived tensoring with a *differential graded* `(R, A)`-bimodule, the two derived categories being
read through `DifferentialGradedModule.degreeZeroDerivedEquivalence`. This file states it in the
derived change-of-rings shape of Stacks 06Y6 instead:
`CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings`.

This file converts the one shape into the other. The conversion is
`Dualizing.nonempty_derivedTensorBimoduleFunctor_iso_canonical`, which identifies the derived
tensor product with a differential graded bimodule over the base ring with the derived
change-of-rings tensor product with its complex of homogeneous components, together with
Stacks 0BYK in bundle form, `Dualizing.InvertibleKernel.derivedTensorIsoOfDerivedIso`, which
replaces the tensor factor by any complex with the same class in `D(A)`. The class of the factor
is pinned by the second conjunct of `Dualizing.exists_derivedHom_iso_derivedTensor`: it is the
value `RHom_R(A, R)` of the functor at the free module of rank one.

## Main results

* `Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect` — **Stacks 0BZE in the
  derived change-of-rings shape of Tag 06Y6**, at any chosen complex representing
  `RHom_R(A, R)`, for a map making `A` a perfect `R`-module. Nothing is assumed beyond that
  perfectness.
* `Dualizing.derivedHomIsoCanonicalDerivedTensorOfPerfect` — **the same, as data**: the
  isomorphism is built, not merely shown to exist, at the canonical tensor factor
  `Dualizing.canonicalDerivedHomTensorComplex`, which comes from the Tate resolution along the
  tautological presentation. `Dualizing.canonicalDerivedHomTensorComplexClassIso` identifies its
  class in `D(A)` with `RHom_R(A, R)`.

## Implementation notes

The statement is phrased for a bare ring homomorphism `f : R →+* A` with `letI := f.toAlgebra`,
which is the algebra structure `CochainComplex.extendScalarsLarge` builds and therefore the one
`Dualizing.nonempty_derivedTensorBimoduleFunctor_iso_canonical` is stated at. The module universe
is the ring universe, the generality of the differential graded chapter (Tag 09JJ).

## References

* [Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 0BYK](https://stacks.math.columbia.edu/tag/0BYK)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.DerivedTensor
open DifferentialGraded DifferentialGradedModule

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {R A : Type u} [CommRing R] [CommRing A]

/-- **Stacks 0BZE in the derived change-of-rings shape of Tag 06Y6.** Let `f : R → A` make `A` a
perfect `R`-module and let `L` be a complex of `A`-modules whose class in `D(A)` is the value
`RHom_R(A, R)` of derived coextension of scalars at the free module of rank one. Then
`RHom_R(A, -) : D(R) ⥤ D(A)` is the canonical derived change-of-rings tensor product of
Stacks 06Y6 with `L`.

This is `Dualizing.exists_derivedHom_iso_derivedTensor` — Stacks 0BZE through a Tate resolution —
carried across `Dualizing.nonempty_derivedTensorBimoduleFunctor_iso_canonical` and then across
Stacks 0BYK to the chosen representative `L`. No hypothesis beyond the perfectness that
Stacks 0BZE itself assumes. -/
@[stacks 0BZE "in the derived change-of-rings shape of Tag 06Y6, at module universe equal to the \
ring universe, with no carried hypothesis"]
theorem nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect (f : R →+* A)
    (hperf : letI := f.toAlgebra
      StacksDraft.Perfect.IsPerfectModule.{u, u, u + 1} (R := R) A)
    (L : CochainComplex (ModuleCat.{u} A) ℤ)
    (hL : Nonempty (DerivedCategory.Q.obj L ≅
      (Dualizing.derivedHom.{u, u} f).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) :
    letI := f.toAlgebra
    Nonempty (Dualizing.derivedHom.{u, u} f ≅
      (canonicalDerivedTensorChangeOfRings.{u, u, u} f L).F) := by
  let := f.toAlgebra
  obtain ⟨M, ⟨eFun⟩, ⟨eClass⟩⟩ := exists_derivedHom_iso_derivedTensor hperf
  obtain ⟨eCanon⟩ := nonempty_derivedTensorBimoduleFunctor_iso_canonical f M
  obtain ⟨eL⟩ := hL
  exact ⟨eFun ≪≫ eCanon ≪≫ InvertibleKernel.derivedTensorIsoOfDerivedIso f
    (((degreeZeroDerivedComponentIso (R := R) (A := A)).app M.rightModule).symm ≪≫
      eClass.symm ≪≫ eL.symm) _ _⟩

/-! ### The same isomorphism, built rather than shown to exist

`Dualizing.exists_derivedHom_iso_derivedTensor` quantifies the differential graded bimodule
existentially, but its witness is a construction: the Tate resolution of
`DividedPowers.TateResolution.exists_tateResolution` along the tautological presentation
`R[X_a : a ∈ A] ↠ A`. Naming that resolution turns the whole route into data. -/

/-- **The canonical Tate resolution of `A` over `R`**, along the tautological presentation
`R[X_a : a ∈ A] → A`, `X_a ↦ a`. This is the witness of
`DividedPowers.TateResolution.exists_tateResolution`, named. -/
def canonicalTateResolution (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :=
  DividedPowers.TateResolution.tateResolution
    (MvPolynomial.aeval (R := R) (id : A → A)) (fun a => ⟨MvPolynomial.X a, by simp⟩)

/-- **The canonical differential graded resolution of `A` over `R`**: the canonical Tate
resolution, read as an object of Situation 0BZB. -/
def canonicalDGAResolution (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    DGAResolution R A :=
  DividedPowers.TateResolution.Resolution.toDGAResolution (canonicalTateResolution R A)

/-- **The canonical tensor factor of Stacks 0BZE**, as a complex of `A`-modules: the complex of
homogeneous components of the differential graded `(R, A)`-bimodule `N ⊗_E A` of the canonical
differential graded resolution. Its class in `D(A)` is `RHom_R(A, R)`, by
`Dualizing.canonicalDerivedHomTensorComplexClassIso`. -/
def canonicalDerivedHomTensorComplex (f : R →+* A) : CochainComplex (ModuleCat.{u} A) ℤ :=
  letI := f.toAlgebra
  degreeZeroComplex (canonicalDGAResolution R A).derivedHomTensorFactor.rightModule

/-- **Stacks 0BZE in the derived change-of-rings shape of Tag 06Y6, as data.** For `f : R → A`
making `A` a perfect `R`-module, `RHom_R(A, -) : D(R) ⥤ D(A)` *is* the canonical derived
change-of-rings tensor product of Stacks 06Y6 with the canonical tensor factor
`Dualizing.canonicalDerivedHomTensorComplex f`. No existential witness is chosen along the way:
the Tate resolution is the named one, `Dualizing.DGAResolution.derivedHomIsoDerivedTensor` is a
construction, and so is `Dualizing.derivedTensorBimoduleFunctorIsoCanonical`, so the isomorphism
is a function of `f` and `hperf`.

`Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect` is the form stated at an
arbitrary complex representing `RHom_R(A, R)`; that form is a proposition because passing from
this factor to another representative of the same object of `D(A)` goes through a fraction, in
`Dualizing.InvertibleKernel.derivedTensorIsoOfDerivedIso`. -/
@[stacks 0BZE "in the derived change-of-rings shape of Tag 06Y6, at module universe equal to the \
ring universe, with no carried hypothesis; the isomorphism is built, at the canonical tensor \
factor, rather than shown to exist at an arbitrary representative"]
def derivedHomIsoCanonicalDerivedTensorOfPerfect (f : R →+* A)
    (hperf : letI := f.toAlgebra
      StacksDraft.Perfect.IsPerfectModule.{u, u, u + 1} (R := R) A) :
    letI := f.toAlgebra
    Dualizing.derivedHom.{u, u} f ≅
      (canonicalDerivedTensorChangeOfRings.{u, u, u} f
        (canonicalDerivedHomTensorComplex f)).F := by
  letI := f.toAlgebra
  let S := canonicalDGAResolution R A
  exact S.derivedHomIsoDerivedTensor (S.isCompactBimodule_resolvingBimodule hperf)
      (DividedPowers.TateResolution.Resolution.computesDerivedHom_resolvingBimodule
        (canonicalTateResolution R A)) ≪≫
    derivedTensorBimoduleFunctorIsoCanonical f S.derivedHomTensorFactor

/-- **The canonical tensor factor represents `RHom_R(A, R)`.** The class in `D(A)` of
`Dualizing.canonicalDerivedHomTensorComplex f` is the value of derived coextension of scalars at
the free module of rank one. -/
def canonicalDerivedHomTensorComplexClassIso (f : R →+* A)
    (hperf : letI := f.toAlgebra
      StacksDraft.Perfect.IsPerfectModule.{u, u, u + 1} (R := R) A) :
    letI := f.toAlgebra
    DerivedCategory.Q.obj (canonicalDerivedHomTensorComplex f) ≅
      (Dualizing.derivedHom.{u, u} f).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) := by
  letI := f.toAlgebra
  let S := canonicalDGAResolution R A
  exact ((degreeZeroDerivedComponentIso (R := R) (A := A)).app
      S.derivedHomTensorFactor.rightModule).symm ≪≫
    (S.derivedHomTensorFactorIso (S.isCompactBimodule_resolvingBimodule hperf)
      (DividedPowers.TateResolution.Resolution.computesDerivedHom_resolvingBimodule
        (canonicalTateResolution R A))).symm

end Dualizing

end

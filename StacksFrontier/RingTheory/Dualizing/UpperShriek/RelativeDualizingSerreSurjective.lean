module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomHomologyDual
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.SurjectiveAnyPresentation
public import StacksFrontier.RingTheory.Serre.Surjection

/-!
# The `(S₂)` clause of Tag 0E9R for a surjection, at any presentation

Let `φ : R → A` be a surjection of Noetherian rings and let `ω^•_{A/R} = φ^!(R)` be the relative
dualizing complex, read at an arbitrary polynomial presentation of `φ`.  This file proves the
`(S₂)` clause of [Stacks, Tag 0E9R] for such a `φ`:

`H^0(ω^•_{A/R})` satisfies Serre's condition `(S₂)` as an `A`-module

whenever `R` satisfies `(S₂)` -- in particular whenever `R` is Cohen--Macaulay, which is
hypothesis (1) of the source.

The degree is `0` because for a surjection `r = 0` is the sharp value of the source's hypothesis
(2): `A` is a quotient of `R`, so `κ(𝔮) = κ(R ∩ 𝔮)` at every prime `𝔮` of `A`.  That `H^0` is
the extremal cohomology -- that `H^i(ω^•_{A/R}) = 0` for `i < 0` -- is clause (1) of the tag,
proved at the same sharp bound and at an arbitrary presentation in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingVanishingAnyPresentation`.

## Main results

* `Dualizing.upperShriekHomologyZeroLinearEquivDual` — the identification
  `H^0(ω^•_{A/R}) ≅ Hom_R(A, R)`, `R`-linearly, for a surjective `φ` at an arbitrary polynomial
  presentation.  This is what the elementary engine of
  `StacksFrontier.RingTheory.Serre.Surjection` was waiting for.
* `Dualizing.finite_upperShriekHomologyZero` — that module is finite over `A`.
* `Dualizing.propertySkModule_homology_zero_relativeDualizingComplex_of_surjective` — **the
  `(S₂)` clause of [Stacks, Tag 0E9R] for a surjective `φ`**, with hypothesis (1) in the form
  `(S₂)` for `R`.
* `Dualizing.propertySkModule_homology_zero_relativeDualizingComplex_of_isCohenMacaulayRing` —
  the same with hypothesis (1) as the source states it, `R` Cohen--Macaulay.

## Relation to the source

The identification is the source's own first step, read at a surjection.  There
`ω^•_{A/R} = RHom_R(A, R)` — [Stacks, Tag 0C0G] for a surjective `φ`, which this library has at
an arbitrary presentation as `Dualizing.upperShriekFunctor_iso_derivedHom_of_surjective` — and the
cohomology of derived Hom is `Ext`, [Stacks, Tag 0A71], so `H^0(ω^•_{A/R}) = Ext^0_R(A, R)`,
which is `Hom_R(A, R)` by [Stacks, Tag 06XS].  That chain is
`Dualizing.derivedHomHomologyZeroLinearEquivDual` of
`StacksFrontier.RingTheory.Dualizing.DerivedHomHomologyDual`.  The surjective case therefore needs
neither a dualizing complex on `R` nor the duality formula [Stacks, Tag 0E9L] in general: the
`(S₂)` of the dual comes from `R` itself by [Stacks, Tag 0AV6] and crosses the surjection by
`propertySkModule_of_surjective_algebraMap`.

The hypothesis is carried by `R`, not by `R_𝔭`, and the conclusion by `H^0(ω^•_{A/R})` over `A`,
not by `H^0(ω^•_{A/R})_𝔭` over `A_𝔭`.  The source reduces the second to the first by replacing
`R` with `R_𝔭`, which is base change for the relative dualizing complex, [Stacks, Tag 0BZV];
that tag is conditional in this library, so the reduction is not available and the statements
below are the global ones.  Serre's condition being local, the global conclusion does imply the
source's localized one at every `𝔭` once `R` -- rather than `R_𝔭` -- is assumed Cohen--Macaulay.

These results are special cases of the `(S₂)` clause of [Stacks, Tag 0E9R], which is proved in
full for a general finite type `φ`, localized at `𝔭` and under the source's hypotheses, as
`Dualizing.propertySkModule_localizedModule_homology_relativeDualizingComplex` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingCohenMacaulay`; they carry no
Tag 0E9R attribute.

## Implementation notes

`HasDerivedCategory.standard` is installed at priority `10000`, as in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialEvalDualityReduction`: the import closure
of [Stacks, Tag 0BZJ] contains the global locally small model of `D(Mod R)` of
`StacksFrontier.Homology.DerivedCategory.LocallySmall`, and every statement here is read at the
standard model, which is where `Dualizing.PolynomialPresentation.upperShriekFunctor` and
`Dualizing.derivedHom` live.  Without the priority a bare `DerivedCategory (ModuleCat R)` in a
statement below means the locally small model and nothing matches.

The `R`-module structure on `H^0(ω^•_{A/R})` is restriction of scalars along `algebraMap R A`; it
is introduced with `letI` in the proofs rather than declared as an instance, and the
identification is stated with `ModuleCat.restrictScalars` so that no instance is needed to read
it.

## References

* [Stacks Project, Tag 0E9R](https://stacks.math.columbia.edu/tag/0E9R)
* [Stacks Project, Tag 0C0G](https://stacks.math.columbia.edu/tag/0C0G)
* [Stacks Project, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
* [Stacks Project, Tag 0AV6](https://stacks.math.columbia.edu/tag/0AV6)
* [Stacks Project, Tag 0BZV](https://stacks.math.columbia.edu/tag/0BZV)
-/

@[expose] public section

open CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **`H^0(ω^•_{A/R}) ≅ Hom_R(A, R)` for a surjective `φ`, at an arbitrary presentation.**  Let
`φ : R → A` be a surjection of commutative rings and let `p` be any polynomial presentation of
`φ`.  Then taking cohomology in degree `0` of the relative dualizing complex `φ^!(R)` of `p`
gives the `R`-dual of `A`, `R`-linearly, the left-hand side read over `R` through `φ`.

For a surjective `φ` the upper shriek functor is derived coextension of scalars at every
presentation, [Stacks, Tag 0C0G] as
`Dualizing.upperShriekFunctor_iso_derivedHom_of_surjective`; and
`Dualizing.derivedHomHomologyZeroLinearEquivDual` reads off the zeroth cohomology of
`RHom_R(A, R)` as `Hom_R(A, R)` by [Stacks, Tag 0A71] and [Stacks, Tag 06XS]. -/
noncomputable def upperShriekHomologyZeroLinearEquivDual {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hsurj : Function.Surjective (algebraMap R A))
    (p : PolynomialPresentation (algebraMap R A)) :
    ((ModuleCat.restrictScalars.{u} (algebraMap R A)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          (p.upperShriekFunctor.{u, u}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
              (ModuleCat.of R (ULift.{u} R)))))) ≃ₗ[R] (A →ₗ[R] R) :=
  let e := (upperShriekFunctor_iso_derivedHom_of_surjective.{u, u}
    (algebraMap R A) hsurj p).some
  (((ModuleCat.restrictScalars.{u} (algebraMap R A)).mapIso
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso
          (e.app _))).toLinearEquiv).trans
    derivedHomHomologyZeroLinearEquivDual

/-- An `A`-module `R`-linearly isomorphic to `Hom_R(A, R)` is finite over `A`, if `R → A` is
surjective and `R` is Noetherian. -/
private theorem finite_of_linearEquiv_dual {R A : Type u} [CommRing R] [CommRing A]
    [IsNoetherianRing R] [Algebra R A] (hsurj : Function.Surjective (algebraMap R A))
    (N : Type*) [AddCommGroup N] [Module A N]
    (e : letI := Module.compHom N (algebraMap R A); N ≃ₗ[R] (A →ₗ[R] R)) :
    Module.Finite A N := by
  have : Module.Finite R A := Module.Finite.of_surjective (Algebra.linearMap R A) hsurj
  let := Module.compHom N (algebraMap R A)
  have : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite R N := Module.Finite.equiv e.symm
  exact Module.Finite.of_restrictScalars_finite R A _

/-- The `(S₂)` version of `finite_of_linearEquiv_dual`, when `R` satisfies `(S₂)`. -/
private theorem propertySkModule_two_of_linearEquiv_dual' {R A : Type u} [CommRing R]
    [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A] [Algebra R A]
    (hsurj : Function.Surjective (algebraMap R A)) (hR : PropertySkRing R 2)
    (N : Type*) [AddCommGroup N] [Module A N] [Module.Finite A N]
    (e : letI := Module.compHom N (algebraMap R A); N ≃ₗ[R] (A →ₗ[R] R)) :
    PropertySkModule A N 2 := by
  have : Module.Finite R A := Module.Finite.of_surjective (Algebra.linearMap R A) hsurj
  let := Module.compHom N (algebraMap R A)
  have : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact propertySkModule_two_of_linearEquiv_dual hsurj hR A N e

/-- **`H^0(ω^•_{A/R})` is a finite `A`-module for a surjective `φ`.**  By
`Dualizing.upperShriekHomologyZeroLinearEquivDual` it is `Hom_R(A, R)`, which is a finite
`R`-module because `R` is Noetherian and `A` is a finite `R`-module; and a finite `R`-module which
is an `A`-module is a finite `A`-module when `R → A` is surjective. -/
theorem finite_upperShriekHomologyZero {R A : Type u} [CommRing R] [CommRing A]
    [IsNoetherianRing R] [Algebra R A] (hsurj : Function.Surjective (algebraMap R A))
    (p : PolynomialPresentation (algebraMap R A)) :
    Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (p.upperShriekFunctor.{u, u}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R (ULift.{u} R))))) := by
  exact finite_of_linearEquiv_dual hsurj _ (upperShriekHomologyZeroLinearEquivDual hsurj p)

/-- **The `(S₂)` clause of [Stacks, Tag 0E9R] for a surjective `φ`, at an arbitrary polynomial
presentation.**  Let `φ : R → A` be a surjection of Noetherian rings satisfying `(S₂)` for `R`,
and let `p` be any polynomial presentation of `φ`.  Then `H^0(ω^•_{A/R})` satisfies Serre's
condition `(S₂)` as an `A`-module.

For a surjective `φ` the sharp value of the source's hypothesis (2) is `r = 0`, so `H^{-r}` is
`H^0`; that it is the extremal cohomology is clause (1), proved at the same bound as
`Dualizing.isZero_homology_relativeDualizingComplex_of_surjective`.  The proof is the elementary
route: `H^0(ω^•_{A/R}) ≅ Hom_R(A, R)` by
`Dualizing.upperShriekHomologyZeroLinearEquivDual`, the dual inherits `(S₂)` from `R` by
[Stacks, Tag 0AV6], and the surjection carries it to `A` by
`propertySkModule_of_surjective_algebraMap`.

Hypothesis (1) of the source is Cohen--Macaulayness of `R_𝔭`;
`Dualizing.propertySkModule_homology_zero_relativeDualizingComplex_of_isCohenMacaulayRing` is
this statement with that hypothesis, in its global form.  See the module documentation on why the
statement is global rather than localized at a prime of `R`. -/
theorem propertySkModule_homology_zero_relativeDualizingComplex_of_surjective
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] (hsurj : Function.Surjective (algebraMap R A)) (hR : PropertySkRing R 2)
    (p : PolynomialPresentation (algebraMap R A)) :
    letI : Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          (p.upperShriekFunctor.{u, u}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
              (ModuleCat.of R (ULift.{u} R))))) :=
      finite_upperShriekHomologyZero hsurj p
    PropertySkModule A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (p.upperShriekFunctor.{u, u}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R (ULift.{u} R))))) 2 := by
  have := finite_upperShriekHomologyZero hsurj p
  exact propertySkModule_two_of_linearEquiv_dual' hsurj hR _
    (upperShriekHomologyZeroLinearEquivDual hsurj p)

/-- **The `(S₂)` clause of [Stacks, Tag 0E9R] for a surjective `φ`, with `R` Cohen--Macaulay.**
`Dualizing.propertySkModule_homology_zero_relativeDualizingComplex_of_surjective` with the
hypothesis on `R` supplied by `Stacks.propertySkRing_of_isCohenMacaulayRing`:  a Cohen--Macaulay
ring satisfies `(Sₖ)` for every `k`.  This is hypothesis (1) of the source, read at `R` rather
than at `R_𝔭`; see the module documentation. -/
theorem propertySkModule_homology_zero_relativeDualizingComplex_of_isCohenMacaulayRing
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] (hsurj : Function.Surjective (algebraMap R A)) (hR : IsCohenMacaulayRing R)
    (p : PolynomialPresentation (algebraMap R A)) :
    letI : Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          (p.upperShriekFunctor.{u, u}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
              (ModuleCat.of R (ULift.{u} R))))) :=
      finite_upperShriekHomologyZero hsurj p
    PropertySkModule A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (p.upperShriekFunctor.{u, u}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R (ULift.{u} R))))) 2 :=
  propertySkModule_homology_zero_relativeDualizingComplex_of_surjective hsurj
    (Stacks.propertySkRing_of_isCohenMacaulayRing R hR 2) p

end Dualizing

end

module

public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityBundlePerfect
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.CompleteIntersection
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensor
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.OpenImmersion
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialEvalDualityProof
public import StacksFrontier.RingTheory.PseudoCoherentMap.CompleteIntersection
public import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectAnyPresentation
import StacksFrontier.RingTheory.PseudoCoherentMap.Flat

/-!
# The upper shriek formalism at module universe equal to the ring universe

`Dualizing.upperShriekFunctor_iso_derivedExtensionScalars_of_bijective` (Stacks 0C0H) carries
`Dualizing.PolynomialEvalDuality`, the conclusion of Stacks 0BZH at the evaluation surjections.
That hypothesis is proved, as `Dualizing.polynomialEvalDuality`, so this file states that case of
Stacks 0C0H, a bijective ring map, with nothing carried.

The file also records the readings of Stacks 0BZU and Stacks 0E4B at module universe equal to the
ring universe. Those two tags hold at an arbitrary module universe, in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensor` and
`StacksFrontier.RingTheory.Dualizing.UpperShriek.CompleteIntersection`; the statements here are those
read at `v = u`, which is the generality the rest of this module works in, together with
`Dualizing.PolynomialPresentation.tensorFormula`, which builds the isomorphism at the *canonical*
Tate tensor factor and so makes no choice at all.

## Main results

* `Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso_derivedTensorProduct` —
  **Stacks 0BZU at module universe equal to the ring universe.**
* `nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_isPerfectRingMap`, in that same
  namespace — **the same, with perfectness taken in the hypothesis shape of Stacks 0BZU itself**:
  that of a perfect homomorphism, rather than that of a perfect module over the polynomial
  algebra of the presentation.
* `Dualizing.PolynomialPresentation.tensorFormula` — **Stacks 0BZU with the isomorphism built at
  the canonical tensor factor**, with no existential witness chosen anywhere.
* `Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_lci`
  — **Stacks 0E4B at module universe equal to the ring universe.**
* `Dualizing.nonempty_upperShriekFunctor_iso_derivedExtensionScalars_of_bijective` — upper
  shriek along a bijective ring map, the case of Stacks 0C0H where the open immersion is an
  isomorphism, with no carried hypothesis.

## Implementation notes

*Why `v = u` is still worth stating.* Stacks 0BZE is proved by
`Dualizing.exists_derivedHom_iso_derivedTensor` through a Tate resolution, and the differential
graded chapter (Tag 09JJ) states that argument at module universe equal to the ring universe:
`DifferentialGradedModule.degreeZeroDerivedEquivalence` reads the two derived categories as
`derivedCategory' (degreeZero R A) ≌ DerivedCategory (ModuleCat.{u} A)` for `R A : Type u`. So
`Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect` is a `v = u` statement, and
it is what `Dualizing.PolynomialPresentation.tensorFormula` uses — through
`Dualizing.derivedHomIsoCanonicalDerivedTensorOfPerfect`, which names the Tate resolution and is
therefore data rather than an existential witness. That canonicity is available at `v = u` and
nowhere else, which is why the data-valued form of Stacks 0BZU lives here.

The *propositional* forms need no such restriction.
`Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect_anyModuleUniverse` of
`StacksFrontier.RingTheory.Dualizing.TrivialDualityBundlePerfectAnyModuleUniverse` renames the rings
along `ULift.ringEquiv` — for `R : Type u` the ring `ULift.{max v u} R` lives in the universe of
its own modules — and carries the three functors of the statement across the resulting
equivalence of derived categories: derived coextension of scalars by
`StacksDraft.DerivedRingEquivIso.derivedHomRingEquivIso`, and derived extension of scalars with
the derived change-of-rings tensor product by
`StacksDraft.DerivedRingEquivIso.derivedTensorBundleRingEquivIsoOfFactorIso`.

*What is still only `Nonempty`.* `Dualizing.PolynomialPresentation.tensorFormula` builds the
isomorphism, but at the tensor factor its own construction produces rather than at
`Dualizing.derivedTensorProductOver f (φ^!(R))`, whose factor is the representative of `φ^!(R)`
chosen by `objPreimage`. Passing between the two is
`Dualizing.InvertibleKernel.derivedTensorIsoOfDerivedIso`, which splits an isomorphism of `D(A)`
into a right fraction of quasi-isomorphisms by `DerivedCategory.right_fac` and so is a choice.
That is the one remaining non-canonical input of
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso_derivedTensorProduct`, and it
is the price of naming the factor `φ^!(R)` rather than a complex.

## References

* [Stacks Project, Tag 0BZU](https://stacks.math.columbia.edu/tag/0BZU)
* [Stacks Project, Tag 0E4B](https://stacks.math.columbia.edu/tag/0E4B)
* [Stacks Project, Tag 0C0H](https://stacks.math.columbia.edu/tag/0C0H)
* [Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.DerivedTensor

attribute [local instance 10000] HasDerivedCategory.standard

universe u v

namespace Dualizing.PolynomialPresentation

variable {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}

/-- **A flat ring map of finite presentation is perfect through every polynomial presentation of
its target**, with no Noetherian hypothesis.  This is
`Dualizing.PolynomialPresentation.isPerfectModule_of_flat` with finite presentation assumed
outright instead of deduced from finite type over a Noetherian base: a flat map of finite
presentation is a perfect ring map by [stacks 067J], and a perfect ring map is perfect through
every finite polynomial presentation of its target by the "any presentation" form of
[stacks 068Y].

Flatness and finite presentation are taken as hypotheses on the ring map rather than as instances
on the algebra, so that the statement applies at a coprojection `A → A ⊗[R] A`, whose algebra
structure is introduced locally. -/
theorem isPerfectModule_of_flat_of_finitePresentation {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat)
    (hfp : (algebraMap R A).FinitePresentation) :
    letI : Module p.Poly A := Module.compHom A p.toRingHom
    StacksDraft.Perfect.IsPerfectModule (R := p.Poly) A := by
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  let : Algebra.FinitePresentation R A := RingHom.finitePresentation_algebraMap.mp hfp
  let D := StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring R
  let α : p.Poly →ₐ[R] A := p.toAlgHom
  exact RingHom.isPerfectModule_of_isPerfectRingMap D.tensor D.comparison D.isLeftDerived
    ((RingHom.isPerfectRingMap_of_flat_of_finitePresentation R A).2
      D.tensor D.comparison D.isLeftDerived)
    p.variableCount α p.surjective

/-- **Stacks 0BZU, with no carried hypothesis.** Let `φ : R → A` be a ring homomorphism and `p` a
polynomial presentation of it whose polynomial algebra makes `A` a perfect
module. Then the algebraic upper shriek functor of `p` is derived tensor product over `R` with
the single object `φ^!(R)` of `D(A)`.

This is `Dualizing.PolynomialPresentation.upperShriekFunctor_iso_derivedTensorProduct` read at
module universe equal to the ring universe, which is the generality the rest of this module works
in; that statement holds at any module universe. -/
@[stacks 0BZU "at an arbitrary polynomial presentation, at module universe equal to the ring \
universe; the same statement at an arbitrary module universe is \
Dualizing.PolynomialPresentation.upperShriekFunctor_iso_derivedTensorProduct"]
theorem nonempty_upperShriekFunctor_iso_derivedTensorProduct
    (p : PolynomialPresentation f)
    (hp : letI : Module p.Poly A := Module.compHom A p.toRingHom
      StacksDraft.Perfect.IsPerfectModule.{u, u, u + 1} (R := p.Poly) A) :
    letI : MonoidalCategoryStruct (ModuleCat.{u} R) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, u}
    letI : MonoidalCategory (ModuleCat.{u} R) :=
      ModuleCat.liftedModuleMonoidal.{u, u}
    let R₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{u} R))
    Nonempty (p.upperShriekFunctor.{u, u} ≅
      derivedTensorProductOver.{u, u} f (p.upperShriekFunctor.{u, u}.obj R₀)) :=
  p.upperShriekFunctor_iso_derivedTensorProduct.{u, u} hp

/-- **Stacks 0BZU for a perfect homomorphism, with no carried hypothesis.** Let `φ : R → A` be a
perfect ring homomorphism and `p` a polynomial presentation of it. Then the
algebraic upper shriek functor of `p` is derived tensor product over `R` with the single object
`φ^!(R)` of `D(A)`.

This is the hypothesis shape of Stacks 0BZU itself: perfectness of `φ`, in the form of
`RingHom.IsPerfectRingMap` relative to a model of the derived tensor product on `D(R)`, rather
than perfectness of `A` over the polynomial algebra of `p`. Tag 068Y passes between the two, as
`RingHom.isPerfectModule_of_isPerfectRingMap`, which is what feeds
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso_derivedTensorProduct` here. So
this is
`Dualizing.PolynomialPresentation.upperShriekFunctor_iso_derivedTensorProduct_of_isPerfectRingMap`
read at module universe equal to the ring universe. -/
@[stacks 0BZU "for a perfect homomorphism of Noetherian rings, at an arbitrary polynomial \
presentation, at module universe equal to the ring universe; the same statement at an arbitrary \
module universe is \
Dualizing.PolynomialPresentation.upperShriekFunctor_iso_derivedTensorProduct_of_isPerfectRingMap"]
theorem nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_isPerfectRingMap
    (p : PolynomialPresentation f)
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (hf : letI : Algebra R A := f.toAlgebra
      RingHom.IsPerfectRingMap R A derivedTensor comparison isLeftDerived) :
    letI : MonoidalCategoryStruct (ModuleCat.{u} R) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, u}
    letI : MonoidalCategory (ModuleCat.{u} R) :=
      ModuleCat.liftedModuleMonoidal.{u, u}
    let R₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{u} R))
    Nonempty (p.upperShriekFunctor.{u, u} ≅
      derivedTensorProductOver.{u, u} f (p.upperShriekFunctor.{u, u}.obj R₀)) :=
  p.nonempty_upperShriekFunctor_iso_derivedTensorProduct
    (by
      let : Algebra R A := f.toAlgebra
      exact RingHom.isPerfectModule_of_isPerfectRingMap derivedTensor comparison isLeftDerived
        hf p.variableCount (AlgHom.mk p.toRingHom fun r ↦ congrArg (· r) p.commutes)
        p.surjective)

/-- **Stacks 0BZU with the isomorphism built, and no carried hypothesis.** Same hypotheses as
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso_derivedTensorProduct`, but the
conclusion is data: a complex of `A`-modules whose class in `D(A)` is `φ^!(R)` — by
`Dualizing.PolynomialPresentation.TensorFormula.classIso` — together with the isomorphism of the
algebraic upper shriek functor of `p` with derived tensor product over `R` with that complex.

The two inputs are `Dualizing.derivedHomIsoCanonicalDerivedTensorOfPerfect`, which is Tag 0BZE in
the change-of-rings shape with the isomorphism built at the canonical Tate tensor factor, and
`Dualizing.PolynomialPresentation.tensorFormulaOfDerivedHomIso`, which turns such an isomorphism
into the tensor formula. Neither extracts a witness from an existential. -/
@[stacks 0BZU "at an arbitrary polynomial presentation, at module universe equal to the ring \
universe, with no carried hypothesis, and with the isomorphism built rather than shown to exist \
— at the constructed tensor factor of Tag 08YU, whose class in D(A) is the value of upper shriek \
at R rather than a prescribed representative of it"]
def tensorFormula (p : PolynomialPresentation f)
    (hp : letI : Module p.Poly A := Module.compHom A p.toRingHom
      StacksDraft.Perfect.IsPerfectModule.{u, u, u + 1} (R := p.Poly) A) :
    TensorFormula.{u, u} p :=
  p.tensorFormulaOfDerivedHomIso.{u, u} (Dualizing.canonicalDerivedHomTensorComplex p.toRingHom)
    (Dualizing.derivedHomIsoCanonicalDerivedTensorOfPerfect p.toRingHom hp)

/-- **Stacks 0E4B, with no carried hypothesis.** Let `φ : R → A` be a local complete intersection
homomorphism and `p` a polynomial presentation of it. Then
`φ^!(K) = K ⊗_R^L ω_{A/R}` with `ω_{A/R} = φ^!(R)`, naturally in `K`.

This is `Dualizing.PolynomialPresentation.upperShriekFunctor_iso_derivedTensorProduct_of_lci`
read at module universe equal to the ring universe; that statement holds at any module
universe. -/
@[stacks 0E4B "the formula φ^!(K) = K ⊗_R^L ω_{A/R}, at an arbitrary polynomial presentation, at \
module universe equal to the ring universe; the same statement at an arbitrary module universe \
is Dualizing.PolynomialPresentation.upperShriekFunctor_iso_derivedTensorProduct_of_lci"]
theorem nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_lci
    (p : PolynomialPresentation f)
    (hf : f.IsLocalCompleteIntersection) :
    letI : MonoidalCategoryStruct (ModuleCat.{u} R) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, u}
    letI : MonoidalCategory (ModuleCat.{u} R) :=
      ModuleCat.liftedModuleMonoidal.{u, u}
    let R₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{u} R))
    Nonempty (p.upperShriekFunctor.{u, u} ≅
      derivedTensorProductOver.{u, u} f (p.upperShriekFunctor.{u, u}.obj R₀)) :=
  p.upperShriekFunctor_iso_derivedTensorProduct_of_lci.{u, u} hf

end Dualizing.PolynomialPresentation

namespace Dualizing

/-- **Upper shriek along a bijective ring map, with no carried hypothesis.** For a bijective
`f : R →+* S` the upper shriek functor attached to any polynomial presentation of `f` is derived
base change `- ⊗_R^L S`, read as the total left derived functor of extension of scalars.  This is
the case of [Stacks, Tag 0C0H] in which `Spec(S) → Spec(R)` is an isomorphism; the tag itself is
`Dualizing.nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_isOpenImmersion`.

This is `Dualizing.upperShriekFunctor_iso_derivedExtensionScalars_of_bijective` with its
hypothesis `hBZH` supplied by `Dualizing.polynomialEvalDuality`. -/
theorem nonempty_upperShriekFunctor_iso_derivedExtensionScalars_of_bijective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hbij : Function.Bijective f)
    (p : PolynomialPresentation f) :
    Nonempty (PolynomialPresentation.upperShriekFunctor.{u, v} p ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
        f).functor) :=
  upperShriekFunctor_iso_derivedExtensionScalars_of_bijective polynomialEvalDuality.{max v u}
    f hbij p

end Dualizing

end

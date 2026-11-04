module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.GorensteinFibres
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizing
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingFiniteTorDimension
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ProjectionCompatibilityResolved

/-!
# Properties of the relative dualizing complex

Let `φ : R → A` be a homomorphism of finite type of Noetherian rings and let
`ω_{A/R} = φ^!(R)` be its relative dualizing complex.  This file completes
[Stacks, Tag 0BZW]: the endomorphism statement (1)(c) for a perfect `φ`, read with perfectness
of `φ` as a ring map, and part (2) for a flat `φ`.

## Main results

* `Dualizing.upperShriekFunctor_unit_isIso_derivedHomothety_of_isPerfectRingMap` —
  **[Stacks, Tag 0BZW] (1)(c)**.
* `Dualizing.upperShriekFunctor_unit_isIso_derivedHomothety_of_flat` — the same for a flat `φ`,
  as part (2) of the source restates it.
* `Dualizing.isDualizingComplex_derivedExtensionScalars_relativeDualizing_of_flat` —
  **[Stacks, Tag 0BZW] (2)(b)**.

The other parts of the tag are
`Dualizing.upperShriekFunctor_unit_derivedCategoryBBounded_of_isPerfectRingMap` ((1)(a)),
`PolynomialPresentation.relativeDualizingComplex_hasFiniteTorDimension_of_isPerfectRingMap`
((1)(b)) and `PolynomialPresentation.relativeDualizingComplex_isRelativelyPerfect` ((2)(a)), both
in the namespace `Dualizing`.

## Implementation notes

Upper shriek depends on the presentation and is well defined only up to isomorphism
([Stacks, Tag 0BZJ]); every statement is made for an arbitrary polynomial presentation, all the
properties involved being invariant under isomorphism.

## References

* [Stacks Project, Tag 0BZW](https://stacks.math.columbia.edu/tag/0BZW)
* [Stacks Project, Tag 068Y](https://stacks.math.columbia.edu/tag/068Y)
* [Stacks Project, Tag 07VI](https://stacks.math.columbia.edu/tag/07VI)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

variable {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}

/-- **Stacks Project, Tag 0BZW (1)(c).**  Let `φ : R →+* A` be a perfect homomorphism of finite
type of Noetherian rings, presented by an arbitrary polynomial presentation `p`.  Then the
canonical map `A ⟶ RHom_A(ω_{A/R}, ω_{A/R})` of [Stacks, Tag 0A7C] — the derived homothety of the
adjunction of [Stacks, Tag 0A63] at `ω_{A/R} = φ^!(R)` — is an isomorphism.

The source's proof: a perfect ring map is perfect through the polynomial algebra `P` of every
presentation ([Stacks, Tag 068Y], `RingHom.isPerfectModule_of_isPerfectRingMap`), perfectness
survives the universe lift to the module universe in which upper shriek is formed
(`StacksDraft.Perfect.isPerfectModule_ulift`), and then
`Dualizing.upperShriekFunctor_unit_isIso_derivedHomothety_of_isPerfectModule` reads
`RHom_A(ω_{A/R}, ω_{A/R})` in `D(P)` as the double dual of `A` and concludes by
[Stacks, Tag 07VI].

Perfectness of `φ` is `RingHom.IsPerfectRingMap`, which carries the derived tensor product it is
stated with, as in (1)(a).  Noetherianity of `A` is not needed by the proof. -/
@[stacks 0BZW "(1)(c)"]
theorem upperShriekFunctor_unit_isIso_derivedHomothety_of_isPerfectRingMap [IsNoetherianRing R]
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
    IsIso (derivedHomothety (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v} A)
      (StacksDraft.DerivedHom.derivedTensorUnit.{u, v} A)
      (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, v} A)
      (p.upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R))))) := by
  let : Algebra R A := f.toAlgebra
  let : Module p.Poly A := Module.compHom A p.toRingHom
  have hperf : StacksDraft.Perfect.IsPerfectModule (R := p.Poly) A :=
    RingHom.isPerfectModule_of_isPerfectRingMap derivedTensor comparison isLeftDerived hf
      p.variableCount (AlgHom.mk p.toRingHom fun r ↦ congrArg (· r) p.commutes) p.surjective
  exact upperShriekFunctor_unit_isIso_derivedHomothety_of_isPerfectModule.{u, v} p
    (StacksDraft.Perfect.isPerfectModule_ulift A hperf)

/-- **The endomorphism statement of [Stacks, Tag 0BZW] (1)(c) for a flat `φ`**, which is how part
(2) of the source restates it.  A flat homomorphism of finite type of Noetherian rings is of finite
presentation, hence a perfect ring map by [Stacks, Tag 067J]; that is the hypothesis of
`Dualizing.upperShriekFunctor_unit_isIso_derivedHomothety_of_isPerfectRingMap`, the canonical
certified derived tensor product of the base being taken for the one it is stated with. -/
theorem upperShriekFunctor_unit_isIso_derivedHomothety_of_flat [IsNoetherianRing R]
    (p : PolynomialPresentation f) (hflat : f.Flat) :
    IsIso (derivedHomothety (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v} A)
      (StacksDraft.DerivedHom.derivedTensorUnit.{u, v} A)
      (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, v} A)
      (p.upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R))))) := by
  let : Algebra R A := f.toAlgebra
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  let : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp p.finiteType
  let : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let D := StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring R
  exact upperShriekFunctor_unit_isIso_derivedHomothety_of_isPerfectRingMap.{u, v} p
    D.tensor D.comparison D.isLeftDerived
    ((RingHom.isPerfectRingMap_of_flat_of_finitePresentation R A).2 D.tensor D.comparison
      D.isLeftDerived)

/-- **Stacks Project, Tag 0BZW (2)(b).**  Let `φ : R → A` be a flat homomorphism of finite type of
Noetherian rings, presented by an arbitrary polynomial presentation `p`, and let `R → k` be a
homomorphism to a field.  Then the derived base change of `ω^•_{A/R} = φ^!(R)` along the
coprojection `A → k ⊗_R A` is a dualizing complex for the fibre ring `k ⊗_R A`.

The source's proof: base change for the relative dualizing complex, [Stacks, Tag 0BZV] case (2)
at `R' = k`, identifies the derived base change with `ω^•_{A'/k}` for `A' = k ⊗_R A`, which is a
dualizing complex by [Stacks, Tag 0BZL]; this is
`Dualizing.isDualizingComplex_derivedExtensionScalars_upperShriekFunctor_unit_of_field`. -/
@[stacks 0BZW "(2)(b)"]
theorem isDualizingComplex_derivedExtensionScalars_relativeDualizing_of_flat
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] (k : Type u) [Field k] [Algebra R k]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat) :
    letI : IsNoetherianRing (TensorProduct R k A) := isNoetherianRing_baseChange k p
    IsDualizingComplex
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R k A).toRingHom).functor.obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) :=
  isDualizingComplex_derivedExtensionScalars_upperShriekFunctor_unit_of_field k p hflat

end Dualizing

end

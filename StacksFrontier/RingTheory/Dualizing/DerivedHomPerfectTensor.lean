module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeUnitBaseAlgebra
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomTensorIso
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ResolutionOfAnyAlgebra
public import StacksFrontier.RingTheory.Dualizing.DifferentialGradedResolutionForget
public import StacksFrontier.RingTheory.Dualizing.TateResolvingBimodule

/-! # Derived Hom from a perfect algebra is a derived tensor product

Let `R → A` be a map of commutative rings with `A` perfect as an `R`-module. Then
`R Hom(A, -) : D(R) ⥤ D(A)` is a derived tensor product: there is a differential graded
`(R, A)`-bimodule `M` with `R Hom(A, -) ≅ - ⊗_R^𝐋 M`. This is Stacks 0BZE.

The route is the source's own. A Tate resolution `(E, d)` of `A` over `R` puts us in
Situation 0BZB; its resolving bimodule is compact in `D(R)` because `A` is perfect, and its
graded dual computes `R Hom(E, R)` because `E^•` is bounded above and free in every degree. So
Stacks 0BZD applies and identifies `R Hom(E, -) : D(R) ⥤ D(E, d)` with derived tensoring with
the graded dual `N = Hom^•_R(E^•, R)`. Stacks 0BZC then identifies `R Hom(A, -)` with
`R Hom(E, -)` followed by the equivalence `- ⊗_E^𝐋 A`, and Stacks 0BZ5 — over the base ring, so
with nothing assumed — composes the two derived tensor products into one. The only hypothesis is
perfectness of `A`.

## Main definitions

* `Dualizing.DGAResolution.derivedHomTensorFactor`: the differential graded `(R, A)`-bimodule
  `M`, the composition `N ⊗_E A` of Stacks 0BZ3 of the graded dual of the resolution with the
  regular bimodule of its augmentation.

## Main results

* `Dualizing.DGAResolution.derivedHomIsoDerivedTensor`: **the conclusion of Stacks 0BZE for a
  resolution satisfying the two hypotheses of Stacks 0BZD**, which is the content of the proof.
* `Dualizing.exists_derivedHom_iso_derivedTensor`: **Stacks 0BZE**, with the resolution
  constructed and both hypotheses of Stacks 0BZD discharged.

## Implementation notes

The two derived categories of the degree-zero world are the derived categories of `R`-modules
and of `A`-modules, through `DifferentialGradedModule.degreeZeroDerivedEquivalence`; the tensor
factor `M` is a differential graded bimodule over the two algebras placed in degree zero, and
the conclusion reads `K ↦ K ⊗_R^𝐋 M` through those two equivalences. That is the form in which
Stacks 0BZ5 delivers the composite of the two derived tensor products.

The adjunction that Stacks 0BZC consumes is produced from Tag 09LT. Tag 09LT gives
`- ⊗_E^𝐋 E ⊣ R Hom(E, -)` for the resolving bimodule, and
`Dualizing.derivedTensorResolvingBimoduleForgetIso` — the tensor half of Stacks 0BYX for the
structure homomorphism `R → E` — identifies the left adjoint with the forgetful functor
`D(E, d) ⥤ D(R)`, which is what Stacks 0BZC asks for.

Stacks 0BZE is stated for the ring map alone: its conclusion does not mention the resolution of
Situation 0BZB, and the proof produces its own Tate resolution, so the ambient data of
Situation 0BZB is exactly the ring map, which is the `Algebra R A` instance. The resolution used
is the one along the tautological presentation `R[x_s : s ∈ A] → A`, which needs no finiteness
hypothesis at all; the variables are infinite in number, which the dual computation does not
mind — only freeness of the homogeneous pieces over `R` enters.

## References

* [Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE), the lemma.
* [Stacks Project, Tag 0BZB](https://stacks.math.columbia.edu/tag/0BZB), the situation,
  [Tag 0BZC](https://stacks.math.columbia.edu/tag/0BZC) and
  [Tag 0BZD](https://stacks.math.columbia.edu/tag/0BZD), the two lemmas it composes, and
  [Tag 0BZ5](https://stacks.math.columbia.edu/tag/0BZ5), the composition of derived tensor
  products.
* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN), the Tate resolution,
  and [Tag 0BZ0](https://stacks.math.columbia.edu/tag/0BZ0), whose second assertion is the input
  of Stacks 0BZD.
* [Stacks Project, Tag 09LT](https://stacks.math.columbia.edu/tag/09LT), the adjunction, and
  [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX), restriction of scalars as tensoring
  with the regular bimodule.
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGraded DifferentialGradedModule

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Dualizing

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The functor `K ↦ K ⊗_R^𝐋 M : D(R) ⥤ D(A)` attached to a differential graded
`(R, A)`-bimodule `M`, the two derived categories being read through
`DifferentialGradedModule.degreeZeroDerivedEquivalence`. -/
def derivedTensorBimoduleFunctor
    (M : Bimodule (baseAlgebra R) (DifferentialGradedAlgebra.degreeZero R A)) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (degreeZeroDerivedEquivalence (R := R) (A := R)).inverse ⋙
    Bimodule.derivedTensorFunctor M ⋙ (degreeZeroDerivedEquivalence (R := R) (A := A)).functor

namespace DGAResolution

variable (S : DGAResolution R A)

/-- **The tensor factor of Stacks 0BZE.** The differential graded `(R, A)`-bimodule
`N ⊗_E A` of Stacks 0BZ3, built from the graded dual `N = Hom^•_R(E^•, R)` of the resolution and
the regular `(E, A)`-bimodule of its augmentation. -/
def derivedHomTensorFactor :
    Bimodule (baseAlgebra R) (DifferentialGradedAlgebra.degreeZero R A) :=
  Bimodule.compTensorResolution (gradedDualBimodule S.E) (Bimodule.regular S.toTarget)

/-- **The equivalence of Situation 0BZB is extension of scalars followed by the degree-zero
equivalence.** -/
theorem derivedEquivalence_functor :
    S.derivedEquivalence.functor =
      Bimodule.derivedTensorFunctor (Bimodule.regular S.toTarget) ⋙
        (degreeZeroDerivedEquivalence (R := R) (A := A)).functor :=
  congrArg (fun F => F ⋙ (degreeZeroDerivedEquivalence (R := R) (A := A)).functor)
    (Bimodule.derivedExtensionEquivalence_functor S.toTarget S.quasiIso)

/-- **The conclusion of Stacks 0BZE in Situation 0BZB, from the two hypotheses of Stacks 0BZD.**
If the resolving bimodule of `E` is compact in `D(R)` and its graded dual computes
`R Hom(E^•, R)`, then `R Hom(A, -) : D(R) ⥤ D(A)` is derived tensoring over `R` with the
differential graded `(R, A)`-bimodule `N ⊗_E A`.

Tag 09LT and the tensor half of Stacks 0BYX make the forgetful functor `D(E, d) ⥤ D(R)` a left
adjoint, which Stacks 0BZC turns into the factorization of `R Hom(A, -)` through `D(E, d)`;
Stacks 0BZD rewrites the factor as a derived tensor product, and Stacks 0BZ5 over the base ring
composes the two. -/
def derivedHomIsoDerivedTensor
    (hcompact : IsCompactBimodule (resolvingBimodule S.E))
    (hdual : ComputesDerivedHom (resolvingBimodule S.E)) :
    Dualizing.derivedHom.{u, u, u} (algebraMap R A) ≅
      derivedTensorBimoduleFunctor S.derivedHomTensorFactor := by
  have adjG : derivedForget S.E ⊣
      (degreeZeroDerivedEquivalence (R := R) (A := R)).inverse ⋙
        (derivedHomData S.E (baseAlgebra R) (resolvingBimodule S.E).rightModule
          (resolvingBimodule S.E).leftAction).functor :=
    Adjunction.ofNatIsoLeft
      ((Bimodule.derivedTensorFunctor_adj_derivedHomFunctor (resolvingBimodule S.E)).comp
        (degreeZeroDerivedEquivalence (R := R) (A := R)).toAdjunction)
      (derivedTensorResolvingBimoduleForgetIso S.E)
  refine S.derivedHom_comp_derivedEquivalence_iso _ adjG ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (degreeZeroDerivedEquivalence (R := R) (A := R)).inverse ?_
  refine Functor.isoWhiskerLeft
      ((derivedHomData S.E (baseAlgebra R) (resolvingBimodule S.E).rightModule
        (resolvingBimodule S.E).leftAction).functor)
      (eqToIso S.derivedEquivalence_functor) ≪≫ ?_
  refine Functor.isoWhiskerRight
      (derivedHomIsoGradedDualTensor S.E hcompact hdual) _ ≪≫ ?_
  refine (Functor.associator _ _ _).symm ≪≫ ?_
  exact Functor.isoWhiskerRight
    (Bimodule.derivedTensorFunctorCompIsoDegreeZeroBase S.E
      (DifferentialGradedAlgebra.degreeZero R A) (gradedDualBimodule S.E)
      (Bimodule.regular S.toTarget))
    (degreeZeroDerivedEquivalence (R := R) (A := A)).functor

end DGAResolution

/-- **`R` placed in degree zero, read through the degree-zero equivalence.** The regular module
of the base algebra goes to `R[0]` in the derived category of `R`-modules: its complex of
homogeneous components is its underlying complex of `R`-modules, which is `R` in degree zero. -/
def baseRegularSingleIso (R : Type u) [CommRing R] :
    (degreeZeroDerivedEquivalence (R := R) (A := R)).functor.obj
        ((toHomotopyCategory (baseAlgebra R) ⋙ (quasiIsomorphisms' (baseAlgebra R)).Q).obj
          (regularModule (baseAlgebra R))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R) :=
  degreeZeroDerivedComponentIso.app (regularModule (baseAlgebra R)) ≪≫
    DerivedCategory.Q.mapIso (degreeZeroComponentForgetIso (regularModule (baseAlgebra R))) ≪≫
    DerivedCategory.Q.mapIso (degreeZeroRegularSingleIso R R)

/-- The quasi-inverse of the degree-zero equivalence carries `R[0]` back to the regular module of
the base algebra. -/
def baseRegularPreimageIso (R : Type u) [CommRing R] :
    (degreeZeroDerivedEquivalence (R := R) (A := R)).inverse.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      (toHomotopyCategory (baseAlgebra R) ⋙ (quasiIsomorphisms' (baseAlgebra R)).Q).obj
        (regularModule (baseAlgebra R)) :=
  (degreeZeroDerivedEquivalence (R := R) (A := R)).inverse.mapIso
      (baseRegularSingleIso R).symm ≪≫
    ((degreeZeroDerivedEquivalence (R := R) (A := R)).unitIso.app _).symm

namespace DGAResolution

variable (S : DGAResolution R A)

/-- **The tensor factor of Stacks 0BZE is `R Hom(A, R)`.** Evaluating the identification at
`R[0]` and using that the regular module is a unit for the relative tensor product identifies
the class of `N ⊗_E A` in `D(A)` with the value of `R Hom(A, -)` at `R`. -/
def derivedHomTensorFactorIso
    (hcompact : IsCompactBimodule (resolvingBimodule S.E))
    (hdual : ComputesDerivedHom (resolvingBimodule S.E)) :
    (Dualizing.derivedHom.{u, u, u} (algebraMap R A)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      (degreeZeroDerivedEquivalence (R := R) (A := A)).functor.obj
        ((toHomotopyCategory (DifferentialGradedAlgebra.degreeZero R A) ⋙
          (quasiIsomorphisms' (DifferentialGradedAlgebra.degreeZero R A)).Q).obj
            S.derivedHomTensorFactor.rightModule) :=
  (S.derivedHomIsoDerivedTensor hcompact hdual).app _ ≪≫
    (degreeZeroDerivedEquivalence (R := R) (A := A)).functor.mapIso
      ((Bimodule.derivedTensorFunctor S.derivedHomTensorFactor).mapIso
          (baseRegularPreimageIso R) ≪≫
        Bimodule.derivedTensorRegularIso S.derivedHomTensorFactor)

end DGAResolution

/-- **Stacks 0BZE.** Let `R → A` be a map of commutative rings making `A` a
perfect `R`-module. Then `R Hom(A, -) : D(R) ⥤ D(A)` is a derived tensor product:
there is a differential graded `(R, A)`-bimodule `M` with `R Hom(A, -) ≅ - ⊗_R^𝐋 M`, whose
class in `D(A)` is the value `R Hom(A, R)` of that functor at `R`. The two derived categories of
the degree-zero world are the derived categories of `R`-modules and of `A`-modules through
`DifferentialGradedModule.degreeZeroDerivedEquivalence`.

A Tate resolution of `A` over `R` exists for every `R`-algebra, along the tautological
polynomial presentation; it puts us in Situation 0BZB. Perfectness of `A` makes the resolving
bimodule compact in `D(R)`, and the homogeneous pieces of a Tate resolution are free over `R`,
which makes its graded dual compute `R Hom(E^•, R)`. Both hypotheses of Stacks 0BZD hold, so
`Dualizing.DGAResolution.derivedHomIsoDerivedTensor` applies. -/
@[stacks 0BZE "the functor R Hom(A, -) is derived tensoring over R with a differential graded \
(R, A)-bimodule whose class in D(A) is R Hom(A, R), read through the degree-zero equivalences"]
theorem exists_derivedHom_iso_derivedTensor
    (hperf : StacksDraft.Perfect.IsPerfectModule.{u, u, u + 1} (R := R) A) :
    ∃ M : Bimodule (baseAlgebra R) (DifferentialGradedAlgebra.degreeZero R A),
      Nonempty (Dualizing.derivedHom.{u, u, u} (algebraMap R A) ≅
        derivedTensorBimoduleFunctor M) ∧
      Nonempty ((Dualizing.derivedHom.{u, u, u} (algebraMap R A)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
        (degreeZeroDerivedEquivalence (R := R) (A := A)).functor.obj
          ((toHomotopyCategory (DifferentialGradedAlgebra.degreeZero R A) ⋙
            (quasiIsomorphisms' (DifferentialGradedAlgebra.degreeZero R A)).Q).obj
              M.rightModule)) := by
  obtain ⟨σ, φ, -, ⟨T⟩⟩ := DividedPowers.TateResolution.exists_tateResolution R A
  let S := DividedPowers.TateResolution.Resolution.toDGAResolution T
  have hcompact := S.isCompactBimodule_resolvingBimodule hperf
  have hdual : ComputesDerivedHom (resolvingBimodule S.E) :=
    DividedPowers.TateResolution.Resolution.computesDerivedHom_resolvingBimodule T
  exact ⟨S.derivedHomTensorFactor, ⟨S.derivedHomIsoDerivedTensor hcompact hdual⟩,
    ⟨S.derivedHomTensorFactorIso hcompact hdual⟩⟩

end Dualizing

end

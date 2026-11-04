module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorRestrictRight
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated

/-! # Restricting the right algebra of a bimodule restricts the derived tensor product

Let `(A, d)`, `(S, d)` and `(C, d)` be differential graded algebras over a commutative ring `R`,
let `N` be a differential graded `(A, S)`-bimodule and let `ψ : C → S` be a homomorphism of
differential graded algebras. Tensoring with `N|_ψ`, the bimodule `N` with its right action
restricted along `ψ`, is tensoring with `N` followed by restriction of scalars along `ψ`
(`DifferentialGraded.Bimodule.tensorCompFunctorRestrictRightIso`). This file carries that
identification to the homotopy categories and then to the derived categories:

`- ⊗_A^𝐋 (N|_ψ) ≅ (- ⊗_A^𝐋 N) ⋙ (- |_ψ) : D(A, d) ⥤ D(C, d)`.

The derived statement is not formal from the undervied one: the two functors are two left derived
functors, and they are compared by the universal property of Tag 09LS. Restriction of scalars is
exact and descends from the homotopy categories, so composing the derived tensor product with it
again gives a left derived functor — that is the absoluteness of a derived functor obtained from
resolutions — and the two derived functors then derive isomorphic functors, hence are isomorphic.

## Main definitions

* `DifferentialGraded.Bimodule.tensorHomotopyFunctorRestrictRightIso`: the identification on the
  homotopy categories, lifted from differential graded modules through the quotient by homotopy.
* `DifferentialGraded.Bimodule.tensorFunctorToDerivedCategoryRestrictRightIso`: the two functors
  being derived are isomorphic.
* `DifferentialGraded.Bimodule.derivedTensorFunctorRestrictRightIso`: **the identification on the
  derived categories.**

## Implementation notes

*Why the homotopy-level statement is a lift.* Both `- ⊗_A (N|_ψ)` and `(- ⊗_A N)|_ψ` on the
homotopy categories are descents through the quotient by homotopy of functors on differential
graded modules, compatibly with Tag 09LM
(`DifferentialGraded.Bimodule.tensorCompFunctor_quotient`) and with
`DifferentialGradedModule.restrictScalarsHomotopyFunctorIso`, so the module-level isomorphism
gives an isomorphism after precomposition with the quotient functor, and
`CategoryTheory.Quotient.natIsoLift` removes the precomposition.

*Where absoluteness comes in.* `(- ⊗_A^𝐋 N) ⋙ (- |_ψ)` is the left derived functor of
`(- ⊗_A N) ⋙ (- |_ψ)` by
`CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions`, whose
hypotheses are the resolutions by modules orthogonal on the left to the acyclic ones (Tag 09KP
with Tag 09KM) and the invertibility of the plain tensor functor on the quasi-isomorphisms
between them. Both are already available for the derived tensor product, which is how its own
universal property is obtained.

## References

* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS), the derived tensor
  product and its universal property as a left derived functor.
* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM), the plain tensor
  product and its compatibility with homotopy classes.
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX), restriction of scalars
  and its derived functor.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A S C : DifferentialGradedAlgebra.{u, u} R}

/-- **Tensoring with `N|_ψ` is tensoring with `N` followed by restriction along `ψ`, on the
homotopy categories.** Both sides descend from differential graded modules, where the
identification is
`DifferentialGraded.Bimodule.tensorCompFunctorRestrictRightIso`. -/
def tensorHomotopyFunctorRestrictRightIso (ψ : C.Hom S) (N : Bimodule A S) :
    tensorHomotopyFunctor (Bimodule.restrictRight ψ N) ≅
      tensorHomotopyFunctor N ⋙ restrictScalarsHomotopyFunctor ψ :=
  CategoryTheory.Quotient.natIsoLift _
    ((tensorCompFunctor_quotient (Bimodule.restrictRight ψ N)).symm ≪≫
      Functor.isoWhiskerRight (tensorCompFunctorRestrictRightIso ψ N) (toHomotopyCategory C) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (tensorCompFunctor N)
        (restrictScalarsHomotopyFunctorIso ψ).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (tensorCompFunctor_quotient N)
        (restrictScalarsHomotopyFunctor ψ) ≪≫
      Functor.associator _ _ _)

/-- The two functors being derived agree: plain tensoring with `N|_ψ` followed by localization is
plain tensoring with `N` followed by derived restriction along `ψ`. -/
def tensorFunctorToDerivedCategoryRestrictRightIso (ψ : C.Hom S) (N : Bimodule A S) :
    tensorFunctorToDerivedCategory (Bimodule.restrictRight ψ N) ≅
      tensorFunctorToDerivedCategory N ⋙ derivedRestriction ψ :=
  Functor.isoWhiskerRight (tensorHomotopyFunctorRestrictRightIso ψ N)
      (quasiIsomorphisms' C).Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tensorHomotopyFunctor N)
      (derivedRestrictionFactorization ψ).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Tensoring with `N` followed by derived restriction along `ψ` is a left derived functor of
plain tensoring with `N` followed by derived restriction: a left derived functor obtained from
resolutions stays one after composition with an arbitrary functor. -/
theorem derivedTensorFunctor_comp_derivedRestriction_isLeftDerivedFunctor (ψ : C.Hom S)
    (N : Bimodule A S) :
    (derivedTensorFunctor N ⋙ derivedRestriction ψ).IsLeftDerivedFunctor
      ((Functor.associator (quasiIsomorphisms' A).Q (derivedTensorFunctor N)
          (derivedRestriction ψ)).inv ≫
        Functor.whiskerRight (derivedTensorFunctorCounit N) (derivedRestriction ψ))
      (quasiIsomorphisms' A) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions
    (quasiIsomorphisms' A) (acyclic' A).leftOrthogonal
    (exists_quasiIso_leftOrthogonal_acyclic_homotopy A)
    (tensorFunctorToDerivedCategory N)
    (fun s hs hX hY =>
      isIso_tensorFunctorToDerivedCategory_map_of_leftOrthogonal N s hs hX hY)
    (quasiIsomorphisms' A).Q (derivedTensorFunctor N) (derivedTensorFunctorCounit N)
    (derivedRestriction ψ)

/-- **Restricting the right algebra of a bimodule restricts the derived tensor product**:
`- ⊗_A^𝐋 (N|_ψ) ≅ (- ⊗_A^𝐋 N)|_ψ` as functors `D(A, d) ⥤ D(C, d)`.

Both sides are left derived functors — the left-hand side by Tag 09LS, the right-hand side by the
absoluteness of a derived functor obtained from resolutions — of two isomorphic functors out of
`K(A, d)`, so they are isomorphic by the uniqueness of a left derived functor. -/
def derivedTensorFunctorRestrictRightIso (ψ : C.Hom S) (N : Bimodule A S) :
    derivedTensorFunctor (Bimodule.restrictRight ψ N) ≅
      derivedTensorFunctor N ⋙ derivedRestriction ψ :=
  have := derivedTensorFunctor_comp_derivedRestriction_isLeftDerivedFunctor ψ N
  Functor.leftDerivedNatIso (derivedTensorFunctor (Bimodule.restrictRight ψ N))
    (derivedTensorFunctor N ⋙ derivedRestriction ψ)
    (derivedTensorFunctorCounit (Bimodule.restrictRight ψ N))
    ((Functor.associator (quasiIsomorphisms' A).Q (derivedTensorFunctor N)
        (derivedRestriction ψ)).inv ≫
      Functor.whiskerRight (derivedTensorFunctorCounit N) (derivedRestriction ψ))
    (quasiIsomorphisms' A) (tensorFunctorToDerivedCategoryRestrictRightIso ψ N)

end DifferentialGraded.Bimodule

end

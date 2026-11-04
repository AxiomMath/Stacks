module

public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleRepresents
public import StacksFrontier.Algebra.DifferentialGraded.TensorProductLift

/-!
# Restriction of scalars along a composite

Let `φ : A → B` and `ψ : B → C` be homomorphisms of differential graded algebras over a
commutative ring `R`. Restricting a differential graded `C`-module along `ψ` and then along `φ`
gives the restriction along the composite `ψ ∘ φ : A → C`: the module, the grading, the
differential and the right action are all unchanged. On the homotopy categories the two functors
therefore lift the same functor through the quotient by homotopy, so they are equal, and on the
derived categories they lift the same functor through the localization at the quasi-isomorphisms,
so they are canonically isomorphic.

The isomorphism on derived categories is what
`DifferentialGraded.AlgebraSystem.restrComp` asks for of an inverse system of differential graded
algebras; before this file it had to be carried as data.

## Main results

* `DifferentialGradedModule.restrictScalars_comp` and
  `DifferentialGradedModule.restrictScalarsFunctor_comp`: restriction along a composite, on
  differential graded modules.
* `DifferentialGradedModule.restrictScalarsHomotopyFunctor_comp`: the same on the homotopy
  categories, an equality of functors.
* `DifferentialGradedModule.derivedRestrictionComp`: the same on the derived categories, a
  natural isomorphism, with `DifferentialGradedModule.derivedRestrictionComp_hom_app` computing
  it at the image of an object of the homotopy category.

## Implementation notes

Derived restriction of scalars is a lift through the localization functor, and a lift is unique
only up to a unique natural isomorphism, so the derived statement cannot be an equality; it is
obtained from the equality on homotopy categories by `CategoryTheory.Localization.liftNatIso`,
exactly as `DifferentialGradedModule.derivedRestrictionIdIso` is obtained for the identity
homomorphism. The homotopy-category comparison
`DifferentialGradedModule.derivedRestrictionCompFactorization` is recorded separately because it
is what the component formula is phrased in.

## References

* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra.{u, u} R}

/-- Restricting along `ψ` and then along `φ` is restricting along `ψ ∘ φ`: the underlying module,
the grading, the differential and the right action are unchanged. -/
theorem restrictScalars_comp (φ : A.Hom B) (ψ : B.Hom C)
    (N : DifferentialGradedModule.{u, u, u} C) :
    restrictScalars φ (restrictScalars ψ N) = restrictScalars (ψ.comp φ) N :=
  rfl

/-- Restriction of scalars along a composite is the composite of the restrictions, as functors on
differential graded modules. -/
theorem restrictScalarsFunctor_comp (φ : A.Hom B) (ψ : B.Hom C) :
    restrictScalarsFunctor ψ ⋙ restrictScalarsFunctor φ = restrictScalarsFunctor (ψ.comp φ) :=
  rfl

/-- Restriction of scalars along a composite is the composite of the restrictions, as functors on
the homotopy categories: both functors lift the same functor through the quotient by homotopy,
and a lift is unique. -/
theorem restrictScalarsHomotopyFunctor_comp (φ : A.Hom B) (ψ : B.Hom C) :
    restrictScalarsHomotopyFunctor ψ ⋙ restrictScalarsHomotopyFunctor φ =
      restrictScalarsHomotopyFunctor (ψ.comp φ) :=
  CategoryTheory.Quotient.lift_unique' (homotopyRel C) _ _ rfl

/-- The composite of the derived restrictions and derived restriction along the composite agree
after precomposition with the localization functor: both factor through restriction on the
homotopy categories, where the comparison is an equality. -/
def derivedRestrictionCompFactorization (φ : A.Hom B) (ψ : B.Hom C) :
    (quasiIsomorphisms' C).Q ⋙ derivedRestriction ψ ⋙ derivedRestriction φ ≅
      (quasiIsomorphisms' C).Q ⋙ derivedRestriction (ψ.comp φ) :=
  Functor.isoWhiskerRight (derivedRestrictionFactorization ψ) (derivedRestriction φ) ≪≫
    Functor.isoWhiskerLeft (restrictScalarsHomotopyFunctor ψ)
      (derivedRestrictionFactorization φ) ≪≫
    eqToIso (by rw [← Functor.assoc, restrictScalarsHomotopyFunctor_comp φ ψ]) ≪≫
    (derivedRestrictionFactorization (ψ.comp φ)).symm

/-- **Derived restriction of scalars along a composite is the composite of the derived
restrictions.** Both functors lift the same functor through the localization at the
quasi-isomorphisms, and a lift is unique up to a unique natural isomorphism. -/
def derivedRestrictionComp (φ : A.Hom B) (ψ : B.Hom C) :
    derivedRestriction ψ ⋙ derivedRestriction φ ≅ derivedRestriction (ψ.comp φ) :=
  Localization.liftNatIso (quasiIsomorphisms' C).Q (quasiIsomorphisms' C)
    ((quasiIsomorphisms' C).Q ⋙ derivedRestriction ψ ⋙ derivedRestriction φ)
    ((quasiIsomorphisms' C).Q ⋙ derivedRestriction (ψ.comp φ))
    (derivedRestriction ψ ⋙ derivedRestriction φ) (derivedRestriction (ψ.comp φ))
    (derivedRestrictionCompFactorization φ ψ)

/-- At the image of an object of the homotopy category the comparison of derived restrictions is
the homotopy-category comparison. -/
theorem derivedRestrictionComp_hom_app (φ : A.Hom B) (ψ : B.Hom C) (X : HomotopyCategory C) :
    (derivedRestrictionComp φ ψ).hom.app ((quasiIsomorphisms' C).Q.obj X) =
      (derivedRestrictionCompFactorization φ ψ).hom.app X := by
  simp [derivedRestrictionComp]

end DifferentialGradedModule

end

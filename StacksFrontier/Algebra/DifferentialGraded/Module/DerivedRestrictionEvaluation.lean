module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomFunctor
public import StacksCore.Tactic.StacksAttribute

/-! # The comparison of derived Hom out of the regular bimodule is evaluation at one

Let `φ : A → B` be a homomorphism of differential graded algebras over a commutative ring `R`.
Example 22.33.2 identifies derived Hom out of the regular differential graded `(A, B)`-bimodule
with derived restriction of scalars, and the identification is *pinned* by evaluation at the unit:
on the class of a differential graded `B`-module `N`, the canonical comparison of the derived
functor with the underived one, read through the factorisation of derived restriction, is the
localisation of the evaluation morphism `Hom^•_B(B, N) → N_A, f ↦ f(1)`.

This file proves exactly that compatibility, for an *arbitrary*
`DifferentialGradedModule.DerivedHomData` out of the regular bimodule:

`DifferentialGradedModule.derivedHom_comparison_eq_evaluationAtOne`.

## Main results

* `DifferentialGradedModule.DerivedHomData.comparison_app_comp_functorIsoDerivedRestriction`:
  the canonical comparison of any derived Hom datum out of the regular bimodule, followed by its
  identification with derived restriction, is the defining factorisation
  `DifferentialGradedModule.regularHomFactorization`. This is the uniqueness of a right derived
  functor read off on one object.
* `DifferentialGradedModule.regularHomFactorization_inv_app_comp_derivedRestrictionFactorization`:
  the two halves of that factorisation that run through derived restriction cancel, leaving the
  localisation of evaluation at one on homotopy categories.
* `DifferentialGradedModule.derivedHom_comparison_eq_evaluationAtOne`: the compatibility itself.

## Implementation notes

*The source objects are not equal, and the comparison iso is the repair.* Internal Hom out of the
regular bimodule is isomorphic to restriction of scalars
(`DifferentialGradedModule.homHomotopyFunctorRegularIso`) but not equal to it: the internal hom
module is `DifferentialGradedModule.homModulePresentation`, a presentation chosen by
`Classical.choose`, and the functor on homotopy categories is transported across the equivalence
`DifferentialGradedModule.homotopyCategoryEquivalence`, whose inverse is again a choice. So the
two morphisms being compared do not have the same source, and the compatibility can only be
stated after transporting along
`(DifferentialGradedModule.quasiIsomorphisms A).Q.map
  ((DifferentialGradedModule.homHomotopyFunctorRegularIso φ).hom.app _)`,
which is what the statement below does. The targets *do* agree on the nose, because restriction
of scalars on homotopy categories is a `CategoryTheory.Quotient.lift`.

*Why an arbitrary datum.* The statement is proved for every
`DifferentialGradedModule.DerivedHomData A B (regularModule B) (regularBimoduleStructure φ)`, with
the identification taken to be the canonical
`DifferentialGradedModule.DerivedHomData.functorIsoDerivedRestriction` and the factorisation the
canonical `DifferentialGradedModule.derivedRestrictionFactorization`; no choice of derived functor
is fixed.

## What this file does not contain

It does **not** contain the bundled datum `0BYX__derived_hom_restriction` —
the structure that records a bimodule, a descended restriction functor, an isomorphism with
derived Hom, and the evaluation compatibility all at once. That structure as stated
is uninhabitable: its `bimodule_action` field asserts a `HEq` between an element of the
degree-`(p + n)` piece of `B` and an element of `B` itself, which forces an equality of types
that already fails for `R = A = B = ℤ` concentrated in degree `0`. Accordingly no
declaration here claims that clause.

## References

* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX), Example 22.33.2; derived
  Hom is [Tag 09LI](https://stacks.math.columbia.edu/tag/09LI) and the internal hom functor is
  [Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ).
-/

@[expose] public noncomputable section

open CategoryTheory

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- Uniqueness of a right derived functor, read off on one object: the canonical comparison of a
derived Hom datum out of the regular bimodule, followed by its identification with derived
restriction of scalars, is the defining factorisation. -/
theorem DerivedHomData.comparison_app_comp_functorIsoDerivedRestriction (φ : A.Hom B)
    (D : DerivedHomData A B (regularModule B) (regularBimoduleStructure φ))
    (X : HomotopyCategory B) :
    D.comparison.app X ≫
        (DerivedHomData.functorIsoDerivedRestriction φ D).hom.app
          ((quasiIsomorphisms' B).Q.obj X) =
      (regularHomFactorization φ).inv.app X := by
  dsimp only [DerivedHomData.functorIsoDerivedRestriction,
    DerivedHomData.functorIsoOfFactorization, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso]
  have := D.isRightDerived
  have := Functor.isRightDerivedFunctor_of_inverts (quasiIsomorphisms' B)
    (derivedRestriction φ) (regularHomFactorization φ)
  rw [Functor.rightDerivedNatTrans_app]
  simp

/-- Evaluation at one is the identity morphism of the restricted module, so its class in the
derived category of `A` is the identity. -/
theorem quasiIsomorphisms_Q_map_toHomotopyCategory_map_evaluation_eq_id (φ : A.Hom B)
    (N : DifferentialGradedModule B) :
    (quasiIsomorphisms' A).Q.map
        ((toHomotopyCategory A).map ((evaluationAtOne φ).evaluation N)) = 𝟙 _ := by
  change (quasiIsomorphisms' A).Q.map
      ((toHomotopyCategory A).map (𝟙 (restrictScalars φ N))) = 𝟙 _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

/-- The defining factorisation of derived Hom out of the regular bimodule, componentwise: it is
the localisation of evaluation at one on homotopy categories, followed by the factorisation of
derived restriction. -/
theorem regularHomFactorization_inv_app (φ : A.Hom B) (X : HomotopyCategory B) :
    (regularHomFactorization φ).inv.app X =
      (quasiIsomorphisms' A).Q.map ((homHomotopyFunctorRegularIso φ).hom.app X) ≫
        (derivedRestrictionFactorization φ).inv.app X :=
  rfl

/-- The two factorisations of derived restriction cancel, leaving the localisation of evaluation
at one on homotopy categories. -/
theorem regularHomFactorization_inv_app_comp_derivedRestrictionFactorization
    (φ : A.Hom B) (X : HomotopyCategory B) :
    (regularHomFactorization φ).inv.app X ≫
        (derivedRestrictionFactorization φ).hom.app X =
      (quasiIsomorphisms' A).Q.map ((homHomotopyFunctorRegularIso φ).hom.app X) :=
  (Category.assoc
      ((quasiIsomorphisms' A).Q.map ((homHomotopyFunctorRegularIso φ).hom.app X))
      ((derivedRestrictionFactorization φ).inv.app X)
      ((derivedRestrictionFactorization φ).hom.app X)).trans
    (by rw [Iso.inv_hom_id_app]; exact Category.comp_id _)

/-- **Stacks 0BYX, Example 22.33.2.** The identification of derived Hom out of the regular
differential graded `(A, B)`-bimodule with derived restriction of scalars is pinned by evaluation
at the unit: on the class of a differential graded `B`-module `N`, the canonical comparison of the
derived functor with internal Hom, followed by the identification with derived restriction and the
factorisation of derived restriction, is the localisation of the evaluation morphism
`Hom^•_B(B, N) → N_A, f ↦ f(1)`, transported along the identification
`DifferentialGradedModule.homHomotopyFunctorRegularIso` of the two source objects.

The transport is not optional: internal Hom out of the regular bimodule is isomorphic to
restriction of scalars and not equal to it, so the two morphisms have different sources. -/
@[stacks 0BYX "the comparison of derived Hom out of the regular bimodule is evaluation at one"]
theorem derivedHom_comparison_eq_evaluationAtOne (φ : A.Hom B)
    (D : DerivedHomData A B (regularModule B) (regularBimoduleStructure φ))
    (N : DifferentialGradedModule B) :
    D.comparison.app ((toHomotopyCategory B).obj N) ≫
        (DerivedHomData.functorIsoDerivedRestriction φ D).hom.app
          ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj N)) ≫
        (derivedRestrictionFactorization φ).hom.app ((toHomotopyCategory B).obj N) =
      (quasiIsomorphisms' A).Q.map
          ((homHomotopyFunctorRegularIso φ).hom.app ((toHomotopyCategory B).obj N)) ≫
        (quasiIsomorphisms' A).Q.map
          ((toHomotopyCategory A).map ((evaluationAtOne φ).evaluation N)) := by
  rw [← Category.assoc, DerivedHomData.comparison_app_comp_functorIsoDerivedRestriction
    φ D, regularHomFactorization_inv_app_comp_derivedRestrictionFactorization φ]
  exact (Category.comp_id _).symm.trans
    (congrArg (fun g => (quasiIsomorphisms' A).Q.map
      ((homHomotopyFunctorRegularIso φ).hom.app ((toHomotopyCategory B).obj N)) ≫ g)
      (quasiIsomorphisms_Q_map_toHomotopyCategory_map_evaluation_eq_id φ N).symm)

end DifferentialGradedModule

end

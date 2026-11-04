module

public import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation
import all StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation

/-!
# Perfect ring maps through an arbitrary polynomial presentation

Let `A → B` be a ring map and `α : A[x_1, …, x_n] → B` a surjection of `A`-algebras.
[Stacks, Tag 068Y] says that `A → B` is perfect if and only if `B` is a perfect
`A[x_1, …, x_n]`-module, for any such presentation.
`RingHom.isPerfectRingMap_iff_exists_finite_projective_resolution` asserts that some presentation
witnesses perfectness; this file proves that a perfect ring map is perfect through every finite
polynomial presentation of its target.

Finite Tor dimension is quantified over a derived tensor product given as data, as in
`RingHom.IsPerfectRingMap`.

## Main results

* `RingHom.isPerfectModule_of_isPerfectRingMap`: if `A → B` is perfect and
  `α : A[x_1, …, x_n] → B` is any surjection of `A`-algebras, then `B` is a perfect
  `A[x_1, …, x_n]`-module.

## References

* [The Stacks Project, Lemma 15.83.2 (068Y)](https://stacks.math.columbia.edu/tag/068Y)
* [The Stacks Project, Lemma 15.64.3 (065H)](https://stacks.math.columbia.edu/tag/065H)
-/

@[expose] public section

open CategoryTheory

namespace RingHom

universe u

attribute [local instance] HasDerivedCategory.standard

/-- A perfect ring map is perfect through every finite polynomial presentation of its target:
if `A → B` is perfect and `α : A[x_1, …, x_n] → B` is any surjection of `A`-algebras, then `B` is
a perfect `A[x_1, …, x_n]`-module. -/
public theorem isPerfectModule_of_isPerfectRingMap
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    (comparison : ∀ N : ModuleCat.{u} A,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} A,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))
    (h : IsPerfectRingMap A B derivedTensor comparison isLeftDerived)
    (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B) (hα : Function.Surjective α) :
    letI : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
    StacksDraft.Perfect.IsPerfectModule (R := MvPolynomial (Fin n) A) B := by
  have := h.1
  have hpseudo : PseudoCoherence.IsPseudoCoherent
      ((ModuleCat.restrictScalars.{u} α.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))) :=
    (PseudoCoherence.isPseudoCoherentFrom_polynomialPresentation_independent (R := A)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) 0).2.mp
      ((Algebra.pseudoCoherent_iff_exists_polynomialPresentation A B).mp h.1) n α hα
  obtain ⟨a, b, hamp⟩ := h.2
  let : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
  have : Module.Flat A (MvPolynomial (Fin n) A) := Module.Flat.of_free
  let F := ModuleCat.restrictScalars.{u} α.toRingHom
  let G := ModuleCat.restrictScalars (algebraMap A (MvPolynomial (Fin n) A))
  let K := F.mapDerivedCategory.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))
  let e₁ : K ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) A)) 0).obj
      (ModuleCat.of (MvPolynomial (Fin n) A) B) :=
    (F.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of B B)
  let eR : G.mapDerivedCategory.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A B) :=
    G.mapDerivedCategory.mapIso e₁ ≪≫ restrictScalarsSingleIso α
  have hterm := StacksDraft.Perfect.hasTorAmplitudeIn_flatRepresentative_of_hasTorAmplitude
    comparison isLeftDerived _ a b hamp
  exact StacksDraft.Perfect.isPerfect_of_iso e₁.symm
    (StacksDraft.Perfect.isPerfect_and_torAmplitude_of_flat_of_fibre_globalDimension_le
      a b n (polynomial_fibre_globalDimension_le A n) K hpseudo
      fun E hbdd hflat he => hterm E hbdd hflat (he.map fun e => eR.symm ≪≫ e)).1

end RingHom

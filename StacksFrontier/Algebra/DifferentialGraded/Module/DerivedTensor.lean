module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedFunctorCriterion

/-!
# Derived tensor product with a differential graded bimodule

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. Tensoring with `N` on homotopy categories
(`- ⊗_A N : K(A) ⥤ K(B)`, Tag 09LM), followed by localization of the target at the
quasi-isomorphisms of `B`-modules, is the functor whose *left* derived functor
`- ⊗_A^L N : D(A, d) ⥤ D(B, d)` is Tag 09LS. (The diagram of homotopy and derived categories
does not commute, which is why a derived functor is needed at all.)

This file fixes the functor to be derived and reduces its left derivability to the one input it
needs: a supply of resolutions of differential graded `A`-modules by modules orthogonal on the
left to the acyclic ones. That input is Tag 09KP together with Tag 09KM.

## Main definitions

* `DifferentialGraded.Bimodule.tensorFunctorToDerivedCategory`: ordinary tensoring with `N` on
  the homotopy category, viewed as a functor with values in the derived category of `B`.

## Main results

* `DifferentialGraded.Bimodule.tensorFunctorToDerivedCategory_isLeftDerivable_of_resolutions`:
  left derivability in the source's essentially-constant pro-object sense (Tag 05SV).
* `DifferentialGraded.Bimodule.tensorFunctorToDerivedCategory_hasLeftDerivedFunctor_of_resolutions`:
  the right Kan extension along the localization, which is what constructs the derived tensor
  functor as a functor on `D(A, d)`.

Both are stated from the resolution hypothesis; neither asks anything of the functor, in
particular neither needs the exactness of Tag 09LR.

## Implementation notes

*Why two conclusions.* The two conditions are inequivalent and a consumer may need either. The
first is the source's own notion (Tag 05SV, via Tag 05S9): the left derived functor is *defined
at* every object, meaning the pro-object `Qis(A)/X ⥤ D(B, d)` is essentially constant. The
second is Mathlib's `Functor.HasLeftDerivedFunctor`, the existence of a right Kan extension
along the localization, which is what names `- ⊗_A^L N` as a functor on `D(A, d)` — something
essential constancy alone does not provide. No bridge between them is claimed; each is proved
separately from the same resolution hypothesis, through
`DifferentialGradedModule.isLeftDerivable_of_exists_quasiIso_leftOrthogonal` and
`hasLeftDerivedFunctor_of_exists_quasiIso_leftOrthogonal`.

*Universes.* The encoding of `StacksDraft.Ch22.Sec4.Tag09JJ` is universe-polymorphic in the base
ring, the algebra and the module separately: for `R : Type u` the algebra lies in `Type v` and a
module over it in `Type w`. The bimodule stack built on it
(`StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleDefs` onwards) is however stated at
`v = w = u`, so `DifferentialGraded.Bimodule A B` and every functor out of it — in particular
`tensorHomotopyFunctor`, hence `tensorFunctorToDerivedCategory` below — live at
`HomotopyCategory.{u, u, u}`. The two statements below are therefore instantiations at
`w = u` of the universe-polymorphic criteria of
`StacksFrontier.Algebra.DifferentialGraded.Module.DerivedFunctorCriterion`, and the resolution
hypothesis is annotated `DifferentialGradedModule.{u, u, u} A` to say so: it is the module
universe of the conclusion, which the functor already fixes. Widening these statements in `w` is
an addition of universe parameters to the bimodule stack rather than a change of content, and is
not done here.

## References

* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS); the criterion it
  applies is [Tag 06XN](https://stacks.math.columbia.edu/tag/06XN), the resolutions are
  [Tag 09KP](https://stacks.math.columbia.edu/tag/09KP), their orthogonality is
  [Tag 09KM](https://stacks.math.columbia.edu/tag/09KM), and the functor being derived is
  [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM).
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule

namespace DifferentialGraded.Bimodule

universe u

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- Ordinary tensoring with the bimodule `N`, viewed as a functor from the homotopy category of
differential graded `A`-modules to the derived category of differential graded `B`-modules. -/
abbrev tensorFunctorToDerivedCategory (N : Bimodule A B) :
    HomotopyCategory A ⥤ (quasiIsomorphisms' B).Localization :=
  tensorHomotopyFunctor N ⋙ (quasiIsomorphisms' B).Q

/-- **Stacks 09LS** from its input, in the pro-object sense. Tensoring with `N` is left
derivable with respect to the quasi-isomorphisms as soon as every differential graded `A`-module
receives a quasi-isomorphism from a module whose class in `K(A)` is orthogonal on the left to the
acyclic modules — which is Tag 09KP together with Tag 09KM. -/
theorem tensorFunctorToDerivedCategory_isLeftDerivable_of_resolutions (N : Bimodule A B)
    (hres : ∀ M : DifferentialGradedModule.{u, u, u} A,
      ∃ (P : DifferentialGradedModule.{u, u, u} A) (f : P ⟶ M),
      QuasiIso ((forgetToCochainComplex A).map f) ∧
        (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj P)) :
    (tensorFunctorToDerivedCategory N).IsLeftDerivable (quasiIsomorphisms' A) :=
  isLeftDerivable_of_exists_quasiIso_leftOrthogonal A _ hres

/-- **Stacks 09LS** from its input, in the Kan extension sense. Tensoring with `N` has a total
left derived functor with respect to the quasi-isomorphisms as soon as every differential graded
`A`-module receives a quasi-isomorphism from a module whose class in `K(A)` is orthogonal on the
left to the acyclic modules. -/
theorem tensorFunctorToDerivedCategory_hasLeftDerivedFunctor_of_resolutions (N : Bimodule A B)
    (hres : ∀ M : DifferentialGradedModule.{u, u, u} A,
      ∃ (P : DifferentialGradedModule.{u, u, u} A) (f : P ⟶ M),
      QuasiIso ((forgetToCochainComplex A).map f) ∧
        (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj P)) :
    (tensorFunctorToDerivedCategory N).HasLeftDerivedFunctor (quasiIsomorphisms' A) :=
  hasLeftDerivedFunctor_of_exists_quasiIso_leftOrthogonal A _ hres

end DifferentialGraded.Bimodule

end

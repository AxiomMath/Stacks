module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison

/-!
# `Ext` into a dualizing complex is the completion of a finite module

Let `A` be a commutative ring and `ω` an object of `D(A)`. The comparison
`StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso` identifies the functor
`Hom_{D(A)}(-, ω⟦i⟧)` with the universe-lifted degree-`i` cohomology of `RHom_A(-, ω)` on the
whole derived category. Reading that comparison at a single object and deleting the lift gives
an `A`-linear equivalence

`Ext^i_A(K, ω) ≃ₗ[A] H^i(RHom_A(K, ω))`

for an arbitrary `K` in `D(A)`. The library already had this for `K` a module placed in degree
zero (`Dualizing.extIntoOmegaAtLinearEquiv`); the point here is that no hypothesis on `K` is
needed, and that the right-hand side lives in the module universe of the derived category while
`Ext` does not.

Two consequences are recorded. When `A` is Noetherian, `ω` is dualizing and every cohomology
module of `K` is finite, `Ext^i_A(K, ω)` is a finite `A`-module — the degreewise form of
[Stacks, Tag 0A7C]. And the `I`-adic completion of `Ext^i_A(K, ω)` is the `I`-adic completion of
that finite module, which is what makes the left-hand side of local duality
([Stacks, Tag 0AAK]) the completion of something finite.

## Main results

* `Dualizing.extDerivedHomLinearEquiv` — `Ext^i_A(K, ω) ≃ₗ[A] H^i(RHom_A(K, ω))` for arbitrary
  `K`.
* `Dualizing.finite_ext_of_isDualizingComplex` — `Ext^i_A(K, ω)` is a finite `A`-module.
* `Dualizing.adicCompletionExtLinearEquiv` — the adic completion of `Ext^i_A(K, ω)` is the adic
  completion of `H^i(RHom_A(K, ω))`.

## References

* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

variable (A : Type u) [CommRing A]

/-- **`Ext` into a fixed object is the cohomology of derived Hom**, at an arbitrary object of the
derived category. This is the component of
`StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso` at `K`, with the universe lift
removed; `Dualizing.extIntoOmegaAtLinearEquiv` is the special case of a module in degree zero.
No hypothesis on `ω` is needed. -/
public def extDerivedHomLinearEquiv (ω : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    (K ⟶ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).obj ω) ≃ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
        ((dualizingDerivedHomFunctor.{u, v} A ω).obj (.op K))) :=
  ((StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso.{u, v} A ω i).app
    (.op K)).toLinearEquiv.trans ULift.moduleEquiv

/-- **`Ext^i_A(K, ω)` is a finite `A`-module** when `A` is Noetherian, `ω` is dualizing and `K`
has finite cohomology modules. This is the degreewise reading of [Stacks, Tag 0A7C]: derived Hom
into a dualizing complex preserves finiteness of the cohomology, and `Ext` is that cohomology by
`Dualizing.extDerivedHomLinearEquiv`. -/
public theorem finite_ext_of_isDualizingComplex [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω)
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (hK : ∀ j : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) j).obj K))
    (i : ℤ) :
    Module.Finite A (DerivedCategory.Ext K ω i) :=
  (dualizingDerivedHom_finiteCohomology.{u, v} A ω hω K hK i).equiv
    (extDerivedHomLinearEquiv.{u, v} A ω i K).symm

/-- **The adic completion of `Ext^i_A(K, ω)` is the adic completion of `H^i(RHom_A(K, ω))`.**
The left-hand side is a module in the universe of morphisms of the derived category and the
right-hand side one in the universe of its objects; the completion is transported along
`Dualizing.extDerivedHomLinearEquiv`. -/
public def adicCompletionExtLinearEquiv (I : Ideal A)
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    AdicCompletion I (DerivedCategory.Ext K ω i) ≃ₗ[A]
      AdicCompletion I
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
          ((dualizingDerivedHomFunctor.{u, v} A ω).obj (.op K))) :=
  (AdicCompletion.congr I (extDerivedHomLinearEquiv.{u, v} A ω i K)).restrictScalars A

end Dualizing

end

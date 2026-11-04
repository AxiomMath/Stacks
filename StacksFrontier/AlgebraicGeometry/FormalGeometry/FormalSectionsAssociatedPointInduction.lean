module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedPointInductionSerreOne
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletedComplementDerivedLimit

/-!
# Algebraizing formal sections without the third condition: Stacks 0EG2

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let `F` be a
coherent module on `U`. Stacks 0EIF makes the comparison map
`Stacks.Algebraization.comparisonMap A I 𝔞 F`, from `colim_V H⁰(V, F)` over the opens
`V ⊆ U` containing `U ∩ V(I)` to `lim_n H⁰(U, F/IⁿF)`, an isomorphism under three conditions:
`A` is `I`-adically complete with a dualizing complex; the associated points of `F` satisfy a
dimension bound; and either `F` is `(S₁)` off `V(I)` or `V(𝔞)` has dimension at most `2`.
Stacks 0EG2 says that the third condition can be dropped. This file proves it.

## Main results

* `Stacks.Algebraization.isIso_comparisonMap_of_associatedPointsClosureDimensionBound` —
  **Stacks 0EG2**.

## The proof

The proof is the source's induction on the number of associated points of `F` off `V(I)`,
`Stacks.Algebraization.isIso_comparisonMap_of_bootstrapHypotheses_of_completedComplement` of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/AssociatedPointInductionSerreOne.lean`. It applies
Stacks 0EIF only to modules satisfying condition (3)(a), splits off one associated point at a
time by the depth-one quotient of Stacks 0DX3
(`Stacks.Algebraization.exists_shortExact_serreOne_of_nonempty`), and concludes by the middle
clause of Stacks 0H48 (`Stacks.Algebraization.isIso_comparisonMap_middle_of_ends`). Its one
remaining input, `Stacks.Algebraization.CompletedComplementIsFormalSections` (Stacks 0BLX, 0A0K
and 0D60 in the affine shape the source's proof of Stacks 0EIF consumes), is supplied here by
`Stacks.Algebraization.completedComplementIsFormalSections`.

The source's preliminary reduction by Stacks 0DX3 to depth at least one, and its injectivity
argument by Krull's intersection theorem, are not separate steps here. Injectivity of the
comparison map holds unconditionally (`Stacks.Algebraization.mono_comparisonMap`), and Stacks
0DX3 enters through the depth-one quotient in the splitting.

## Implementation notes

The hypotheses are spelled out as separate arguments rather than bundled. Bundled, they are
`Stacks.Algebraization.BootstrapHypotheses`. Condition (2) is
`Stacks.Algebraization.AssociatedPointsClosureDimensionBound`, the predicate Stacks 0EIF uses for
the same condition.

## References

* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0H48](https://stacks.math.columbia.edu/tag/0H48)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
* [Stacks Project, Tag 0AW0](https://stacks.math.columbia.edu/tag/0AW0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- **Stacks 0EG2.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` and let `F` be a coherent
module on `U = Spec(A) ∖ V(𝔞)`. Assume

1. `A` is `I`-adically complete and has a dualizing complex, and
2. whenever `x` is an associated point of `F` outside `V(I)` whose closure meets `V(I)` outside
   `V(𝔞)`, every `z ∈ closure {x} ∩ V(𝔞)` has `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1`.

Then the comparison map `colim_V H⁰(V, F) ⟶ lim_n H⁰(U, F/IⁿF)`, where the colimit is over the
opens `V ⊆ U` containing `U ∩ V(I)`, is an isomorphism. -/
@[stacks 0EG2]
public theorem isIso_comparisonMap_of_associatedPointsClosureDimensionBound
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I a : Ideal A) (hIa : I ≤ a)
    (hcomplete : IsAdicComplete I A)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent]
    (hdim : AssociatedPointsClosureDimensionBound A I a F) :
    IsIso (comparisonMap A I a F) :=
  isIso_comparisonMap_of_bootstrapHypotheses_of_completedComplement A I a
    completedComplementIsFormalSections F ⟨hIa, hcomplete, hdualizing, hdim⟩

end Stacks.Algebraization

end

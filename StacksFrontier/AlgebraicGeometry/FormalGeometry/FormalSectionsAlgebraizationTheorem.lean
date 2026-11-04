module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletedComplementDerivedLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsHypothesesRealization

/-!
# Algebraizing formal sections: Stacks 0EIF

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let `F` be a
coherent module on `U`. Stacks 0EIF asserts that, under

1. `A` is `I`-adically complete and has a dualizing complex,
2. for an associated point `x` of `F` with `x ∉ V(I)` and `closure {x} ∩ V(I) ⊄ V(𝔞)`, every
   `z ∈ closure {x} ∩ V(𝔞)` has `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1`, and
3. either `F|_{U ∖ V(I)}` is `(S₁)`, or the values on `V(𝔞)` of some dimension function on
   `Spec(A)` differ by at most `2`,

the map `colim_V H⁰(V, F) ⟶ lim_n H⁰(U, F/IⁿF)`, the colimit over the opens `V ⊆ U` containing
`U ∩ V(I)`, is an isomorphism. The three conditions are bundled, against the library's own
objects, as `Stacks.Algebraization.FormalSectionsHypotheses`, and the map is
`Stacks.Algebraization.comparisonMap`.

## Main results

* `Stacks.Algebraization.isIso_comparisonMap_of_formalSectionsHypotheses` — **Stacks 0EIF**.

## Implementation notes

The proof is the source's. Stacks 0BK0 writes `F = M̃|_U`; conditions (2) and (3) give the
hypotheses of Stacks 0EFL at `s = 1` and `d = cd(A, I)` (the extreme values of the dimension
function come from condition (1) under (3)(a) and from the hypothesis under (3)(b)), whence an
ideal `J₀ ⊆ 𝔞` with `V(J₀) ∩ V(I) = V(𝔞) ∩ V(I)` such that `Γ(V, F) ⟶ H⁰(RΓ(V, F)^∧)` is an
isomorphism for `V = Spec(A) ∖ V(J₀)`, by comparing the localization triangle with its
completion (in the namespace `Stacks.Algebraization`,
`exists_ideal_isIso_homology_zero_completionUnit_of_formalSectionsHypotheses`). The
identification of `H⁰(RΓ(V, F)^∧)` with `lim_n H⁰(U, F/IⁿF)` is the Milnor sequence of the
derived limit of `Stacks.Algebraization.completedComplementIsFormalSections`, transported onto
the comparison map by
`Stacks.Algebraization.surjective_comparisonAt_of_completedComplementIsFormalSections`;
injectivity is `Stacks.Algebraization.mono_comparisonMap`.

`Stacks.Algebraization.completedComplementIsFormalSections`, the input in the affine shape the
last step of the source's proof consumes (Stacks 0BLX, 0A0K and 0D60 combined), is proved in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletedComplementDerivedLimit`.

The source's standing assumption `I ⊆ 𝔞` is the hypothesis `hIa`. The dualizing complex of
condition (1) is taken in the ring's own module universe, as everywhere in this library.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
* [Stacks Project, Tag 0922](https://stacks.math.columbia.edu/tag/0922)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- **Stacks 0EIF.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` and let `F` be a coherent
module on `U = Spec(A) ∖ V(𝔞)`. Assume that `A` is `I`-adically complete and has a dualizing
complex; that every associated point `x` of `F` outside `V(I)` whose closure meets `V(I)`
outside `V(𝔞)` has `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1` at every `z ∈ closure {x} ∩ V(𝔞)`;
and that either `F|_{U ∖ V(I)}` satisfies `(S₁)` or the values on `V(𝔞)` of a dimension function
on `Spec(A)` differ by at most `2` (`Stacks.Algebraization.FormalSectionsHypotheses`). Then the
map `colim_V H⁰(V, F) ⟶ lim_n H⁰(U, F/IⁿF)`, the colimit over the opens `V ⊆ U` containing
`U ∩ V(I)`, is an isomorphism. -/
@[stacks 0EIF]
public theorem isIso_comparisonMap_of_formalSectionsHypotheses {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I a : Ideal A) (hIa : I ≤ a)
    (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent]
    (h : FormalSectionsHypotheses A I a F) :
    IsIso (comparisonMap A I a F) :=
  isIso_comparisonMap_of_formalSectionsHypotheses_of_completedComplement
    completedComplementIsFormalSections I a hIa F h

end Stacks.Algebraization

end

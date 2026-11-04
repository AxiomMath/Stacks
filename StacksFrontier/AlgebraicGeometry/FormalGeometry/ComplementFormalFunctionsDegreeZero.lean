module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementSectionsComplete
public import StacksFrontier.Examples.Completion.CompleteModuleCategory
public import StacksFrontier.Homology.DerivedComplete.PrincipalFormalFunctionsDegreeZero

/-!
# The degree-zero formal-functions isomorphism for sections away from `V(𝔞)`

Let `A` be a Noetherian ring which is `f`-adically complete, let `𝔞` be a finitely generated
ideal with `f ∈ 𝔞`, let `M` be a finite `A`-module, and let `U = Spec(A) ∖ V(𝔞)`. Stacks 0EII
assumes that `H¹_𝔞(M)` and `H²_𝔞(M)` are annihilated by a power of `f`. Those two hypotheses are
exactly the two outer terms of the degree-zero formal-functions sequence of Stacks 0BLD, as
`StacksFrontier/AlgebraicGeometry/FormalGeometry/ComplementSectionsComplete.lean`
establishes: the first makes `Γ(U, M̃)` `f`-adically complete, the second kills the `f`-adic Tate
module of `H¹(U, M̃)`.

This file feeds both into
`Stacks.FormalFunctions.exists_iso_limit_tensorHomology_zero` at the one object `RΓ(U, M̃)` and
obtains the degree-zero formal-functions isomorphism
`Γ(U, M̃) ≅ lim_n H⁰(RΓ(U, M̃) ⊗ᴸ_A A/fⁿ)`,
with its `n`-th component the canonical map. The completeness statement has to be transported
from `Γ(U, M̃)` to `H⁰(RΓ(U, M̃))` along the `sectionsIso` field of the localization triangle data,
which is what identifies the two.

What separates this from Stacks 0EII itself is the right-hand side: 0EII asks for the limit of
`Γ(U, (M/fⁿM)̃)`, the sections of the actual quotient sheaves, while the sequence produces the
limit of `H⁰(RΓ(U, M̃) ⊗ᴸ_A A/fⁿ)`. The two towers differ by the `fⁿ`-torsion of `M̃`, which is
what the bounded-torsion hypothesis of Stacks 0BLD controls; relating them needs derived sections
on `U` to be an exact functor into the derived category.

## Main results

* `Stacks.Algebraization.isAdicComplete_homologyComplement` — the degree-zero cohomology of
  derived sections on `U` is `f`-adically complete.
* `Stacks.Algebraization.exists_iso_limit_tensorHomology_complement` — **the degree-zero
  formal-functions isomorphism at the object of Stacks 0EII.**

## References

* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- **The degree-zero cohomology of derived sections on `U = Spec(A) ∖ V(𝔞)` is `f`-adically
complete**, under the first hypothesis of Stacks 0EII. This is
`isAdicComplete_complementGlobalSections` transported along the identification of that cohomology
with the sections, which is the `sectionsIso` field of the localization triangle data. -/
theorem isAdicComplete_homologyComplement
    (A : Type u) [CommRing A] [IsNoetherianRing A] {I : Ideal A} {hI : I.FG} (f : A)
    (D : LocalizationTriangleData.{u, u} A I hI) (M : ModuleCat.{u} A) [Module.Finite A M]
    [IsAdicComplete (Ideal.span {f}) A] (c : ℕ)
    (h1 : ∀ x : localCohomologyModule A I hI M 1, f ^ c • x = 0) :
    IsAdicComplete (Ideal.span {f})
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (D.complement.obj M)) :=
  Stacks.Examples.isAdicComplete_of_linearEquiv (D.sectionsIso M)
    (isAdicComplete_complementGlobalSections A I hI f M c h1)

/-- **The degree-zero formal-functions isomorphism for sections away from `V(𝔞)`.** Let `A` be a
Noetherian ring which is `f`-adically complete, let `𝔞` be a finitely generated ideal, let `M` be
a finite `A`-module, and suppose `H¹_𝔞(M)` and `H²_𝔞(M)` are annihilated by `f ^ c`. Then the
module `Γ(U, M̃)` of sections on `U = Spec(A) ∖ V(𝔞)`, in its guise as the degree-zero cohomology
of derived sections, is the inverse limit of `H⁰(RΓ(U, M̃) ⊗ᴸ_A A/f^(n+1))` by the canonical maps.

The two hypotheses are precisely the two outer terms of the degree-zero sequence of Stacks 0BLD:
the first makes the left-hand term the sections themselves rather than their completion, the
second makes the right-hand Tate module vanish. -/
theorem exists_iso_limit_tensorHomology_complement
    (A : Type u) [CommRing A] [IsNoetherianRing A] {I : Ideal A} {hI : I.FG} (f : A)
    (D : LocalizationTriangleData.{u, u} A I hI) (M : ModuleCat.{u} A) [Module.Finite A M]
    [IsAdicComplete (Ideal.span {f}) A] (c : ℕ)
    (h1 : ∀ x : localCohomologyModule A I hI M 1, f ^ c • x = 0)
    (h2 : ∀ x : localCohomologyModule A I hI M 2, f ^ c • x = 0) :
    ∃ e : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (D.complement.obj M) ≅
        limit (Stacks.FormalFunctions.tensorHomologySystem A f (D.complement.obj M) 0),
      ∀ n : ℕ,
        e.hom ≫ limit.π (Stacks.FormalFunctions.tensorHomologySystem A f
            (D.complement.obj M) 0) ⟨n⟩ =
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
            (Stacks.FormalFunctions.derivedTensorUnit A f (D.complement.obj M) n) :=
  Stacks.FormalFunctions.exists_iso_limit_tensorHomology_zero A f (D.complement.obj M)
    (isAdicComplete_homologyComplement A f D M c h1)
    (isZero_adicTateModule_homology_complement D M f c h2)

end Stacks.Algebraization

end

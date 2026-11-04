module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalNonzerodivisor
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentComplementAffine

/-!
# The cohomology of the special fibre of a coherent adic system on the open complement

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X ∖ V(𝔞)`. Let `(F_n)` be a coherent `I`-adic system
on `U`. The proof of [Stacks, Tag 0DXW] needs the two `A`-modules `H⁰(U, F₁)` and `H¹(U, F₁)` to
be finite, and obtains that from the finiteness of `H¹_𝔞(A/fA)` and `H²_𝔞(A/fA)` by Local
Cohomology [Stacks, Tag 0BK0] and [Stacks, Tag 0BLT].

This file provides the two translations that step needs. By clause (3) of [Stacks, Tag 0BK0] the
finiteness of `H^p(U, F₁)` is the finiteness of `H^{p+1}_𝔞(N)` for any finite `A`-module `N`
with `Ñ|_U ≅ F₁`, and the sections of the system in degree zero are the degree-zero cohomology.

## Main results

* `Stacks.Algebraization.finite_openCohomology_iff_finite_localCohomology` — **[Stacks, Tag
  0BK0], clause (3), on the open complement**: for a finite `A`-module `N` presenting the
  special fibre, `H^p(U, F₁)` is a finite `A`-module exactly when `H^{p+1}_𝔞(N)` is.
* `Stacks.Algebraization.finite_globalSections_iff_finite_openCohomology_zero` — the sections of
  the system in degree zero are its degree-zero cohomology.

## Implementation notes

The open complement `U` of an algebraization situation and the open
`Stacks.LocalCohomology.complementZeroLocus` of the affine local-cohomology machinery are the
same element of `(Spec A).Opens`, definitionally, and so are the two functors
`Stacks.Algebraization.openCohomologyFunctor` and
`Stacks.LocalCohomology.complementSheafCohomology`: both derive the sections over `U` of a module
on the open subscheme and read the result over `A`. No transport between them appears below.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0DXW](https://stacks.math.columbia.edu/tag/0DXW)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- **[Stacks, Tag 0BK0], clause (3), at the special fibre of a coherent adic system.** Let `N`
be a finite `A`-module whose associated sheaf restricts on `U` to the first term `F₁` of the
system. Then `H^p(U, F₁)` is a finite `A`-module exactly when `H^{p+1}_𝔞(N)` is.

Both sides are read through the identification of the cohomology of `F₁` on the open subscheme
`U` with the derived sections over `U` of `Ñ` on `Spec A`, which is
`Stacks.LocalCohomology.complementSheafCohomologyTildeIso`. -/
theorem finite_openCohomology_iff_finite_localCohomology (N : ModuleCat.{u} S.A)
    [Module.Finite S.A N]
    (e : systemObj S F 0 ≅ Stacks.LocalCohomology.complementTilde S.A S.a N) (p : ℕ) :
    Module.Finite S.A ((openCohomologyFunctor S p).obj (systemObj S F 0)) ↔
      Module.Finite S.A (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} S.A
        (PrimeSpectrum.zeroLocus (S.a : Set S.A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj N) ((p + 1 : ℕ) : ℤ)) :=
  (Module.finite_iff_of_moduleCat_iso
      ((Stacks.LocalCohomology.complementSheafCohomology S.A S.a p).mapIso e ≪≫
        Stacks.LocalCohomology.complementSheafCohomologyTildeIso S.A S.a N p)).trans
    (Stacks.LocalCohomologySequence.finite_complementCohomologyBase_iff_finite_localCohomology
      (A := CommRingCat.of S.A) S.a N p)

/-- The degree-zero term of the system of sections of a coherent adic system on `U` is the
degree-zero cohomology of its first term: sections over `U` are left exact, so they agree with
their own zeroth right derived functor. -/
theorem finite_globalSections_iff_finite_openCohomology_zero :
    Module.Finite S.A ((openCohomologyFunctor S 0).obj (systemObj S F 0)) ↔
      Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)) :=
  Module.finite_iff_of_moduleCat_iso
    ((ModuleCat.restrictScalars (scalarMap S)).mapIso
      ((_root_.SheafOfModules.evaluation S.U.toScheme.ringCatSheaf
        (op (⊤ : S.U.toScheme.Opens))).rightDerivedZeroIsoSelf.app (systemObj S F 0)))

end Stacks.Algebraization

end

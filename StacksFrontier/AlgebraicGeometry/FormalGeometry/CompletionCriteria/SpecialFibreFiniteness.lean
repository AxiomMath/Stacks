module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationSituation
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison

/-!
# Finiteness of the low-degree cohomology of the special fibre on the open complement

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X ∖ V(𝔞)`. For `f ∈ A` the *special fibre* is
`A / fA`, and the sheaf it determines restricts on `U` to `𝒪_U / f 𝒪_U`.

The proof of [Stacks, Tag 0DXW] opens its verification of condition (c) of [Stacks, Tag 0EHH]
with the sentence: *applying Local Cohomology, Lemma 0BK0 throughout, the assumptions give
finiteness over `A` of `H⁰(U, 𝒪_U/f𝒪_U)` and `H¹(U, 𝒪_U/f𝒪_U)`*. The assumptions in question are
hypotheses (3) of [Stacks, Tag 0DXW] and (4) of [Stacks, Tag 0EKZ]: that `H¹_𝔞(A/fA)` and
`H²_𝔞(A/fA)` are finite `A`-modules.

This file carries out that step. Clause (3) of [Stacks, Tag 0BK0] identifies finiteness of
`H^p(U, M̃)` with finiteness of `H^{p+1}_𝔞(M)` for every finite `A`-module `M`; at `M = A/fA` and
`p = 0, 1` this is exactly the sentence above.

## Main definitions

* `Stacks.Algebraization.specialFibreLocalCohomology` — `H^i_𝔞(A/fA)`, in the supported-sections
  model of local cohomology, which is the shape hypothesis (4) of [Stacks, Tag 0EKZ] is stated
  in.
* `Stacks.Algebraization.specialFibreComplementCohomology` — `H^p(U, (A/fA)~)`, read as an
  `A`-module.

## Main results

* `Stacks.Algebraization.finite_specialFibreComplementCohomology_iff` — **[Stacks, Tag 0BK0],
  clause (3), at the special fibre**: `H^p(U, (A/fA)~)` is a finite `A`-module exactly when
  `H^{p+1}_𝔞(A/fA)` is.
* `Stacks.Algebraization.finite_specialFibreComplementCohomology_zero` and
  `Stacks.Algebraization.finite_specialFibreComplementCohomology_one` — the two conclusions of
  the sentence above, from hypotheses (3) of [Stacks, Tag 0DXW].

## Implementation notes

The ambient ring of the affine machinery of `Stacks.LocalCohomologySequence` is a
`CommRingCat`, while an algebraization situation carries a bare `Type u` with a `CommRing`
instance; `CommRingCat.of S.A` is the bridge, and the two instances the comparison needs —
Noetherianness of `CommRingCat.of S.A` and finiteness of the special fibre over it — are the
same instances read through it.

That the special fibre is a finite `A`-module is surjectivity of `A ⟶ A/fA`; it is not found by
instance search, so it is supplied.

The open complement `U` of an algebraization situation and the `AlgebraicGeometry.zeroLocusCompl`
of the affine machinery are the same open of `Spec(A)`, so no transport between them appears
here: the statements are about the `A`-module `H^p(U, (A/fA)~)` of the latter, and a consumer
reading cohomology on `S.U` meets the identification, not this file.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0DXW](https://stacks.math.columbia.edu/tag/0DXW)
* [Stacks Project, Tag 0EKZ](https://stacks.math.columbia.edu/tag/0EKZ)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u}) (f : S.A)

/-- **The local cohomology of the special fibre.** `H^i_𝔞(A/fA)`, in the supported-sections
model, which is the shape hypothesis (3) of [Stacks, Tag 0DXW] and hypothesis (4) of
[Stacks, Tag 0EKZ] are stated in. -/
abbrev specialFibreLocalCohomology (i : ℤ) : ModuleCat.{u} S.A :=
  Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} S.A
    (PrimeSpectrum.zeroLocus (S.a : Set S.A))
    ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj
      (ModuleCat.of S.A (S.A ⧸ Ideal.span {f}))) i

/-- **The cohomology of the special fibre on the open complement.** `H^p(U, (A/fA)~)`, read as an
`A`-module. On `U` the sheaf `(A/fA)~` is `𝒪_U / f 𝒪_U`. -/
abbrev specialFibreComplementCohomology (p : ℕ) : ModuleCat.{u} S.A :=
  Stacks.LocalCohomologySequence.complementCohomologyBase (A := CommRingCat.of S.A) S.a
    (ModuleCat.of S.A (S.A ⧸ Ideal.span {f})) p

/-- The special fibre is a finite `A`-module, being a quotient of `A`. -/
instance module_finite_specialFibre : Module.Finite S.A (S.A ⧸ Ideal.span {f}) :=
  Module.Finite.of_surjective (Submodule.mkQ (Ideal.span {f})) (Submodule.mkQ_surjective _)

/-- **[Stacks, Tag 0BK0], clause (3), at the special fibre.** The `A`-module `H^p(U, (A/fA)~)` is
finite exactly when `H^{p+1}_𝔞(A/fA)` is. -/
theorem finite_specialFibreComplementCohomology_iff (p : ℕ) :
    Module.Finite S.A (specialFibreComplementCohomology S f p) ↔
      Module.Finite S.A (specialFibreLocalCohomology S f ((p + 1 : ℕ) : ℤ)) := by
  have hnoeth : IsNoetherianRing (CommRingCat.of S.A) := inferInstanceAs (IsNoetherianRing S.A)
  have hfin : Module.Finite (CommRingCat.of S.A)
      (ModuleCat.of S.A (S.A ⧸ Ideal.span {f})) :=
    inferInstanceAs (Module.Finite S.A (S.A ⧸ Ideal.span {f}))
  exact Stacks.LocalCohomologySequence.finite_complementCohomologyBase_iff_finite_localCohomology
    (A := CommRingCat.of S.A) S.a (ModuleCat.of S.A (S.A ⧸ Ideal.span {f})) p

/-- **The first conclusion of the opening step of condition (c) of [Stacks, Tag 0DXW].**
Finiteness of `H¹_𝔞(A/fA)` gives finiteness of `H⁰(U, 𝒪_U/f𝒪_U)`. -/
theorem finite_specialFibreComplementCohomology_zero
    (hH1 : Module.Finite S.A (specialFibreLocalCohomology S f 1)) :
    Module.Finite S.A (specialFibreComplementCohomology S f 0) :=
  (finite_specialFibreComplementCohomology_iff S f 0).2 (by simpa using hH1)

/-- **The second conclusion of the opening step of condition (c) of [Stacks, Tag 0DXW].**
Finiteness of `H²_𝔞(A/fA)` gives finiteness of `H¹(U, 𝒪_U/f𝒪_U)`. -/
theorem finite_specialFibreComplementCohomology_one
    (hH2 : Module.Finite S.A (specialFibreLocalCohomology S f 2)) :
    Module.Finite S.A (specialFibreComplementCohomology S f 1) :=
  (finite_specialFibreComplementCohomology_iff S f 1).2 (by simpa using hH2)

end Stacks.Algebraization

end

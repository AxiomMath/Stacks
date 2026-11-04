module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.ComplementUnitSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.DepthCriterion

/-!
# Full faithfulness of completion on a punctured spectrum: the two criteria

Let `A` be a Noetherian ring, let `f ∈ 𝔞 ⊆ A` and let `U = Spec(A) ∖ V(𝔞)`. The chapter
*Algebraic and Formal Geometry* gives two criteria for the completion functor
`Coh(𝒪_U) ⟶ Coh(U, (f)𝒪_U)` to be fully faithful on the finite locally free objects:

* [Stacks, Tag 0EKS]: `A` is `f`-adically complete and `H¹_𝔞(A)`, `H²_𝔞(A)` are annihilated by
  a power of `f`;
* [Stacks, Tag 0EKT]: `A` has a dualizing complex, is `f`-adically complete, and
  `depth(A_𝔭) + dim((A/𝔭)_𝔮) > 2` for every prime `𝔭` with `f ∉ 𝔭` and every
  `𝔮 ∈ V(𝔭) ∩ V(𝔞)`.

Both are proved here at exactly the source's hypotheses.

The proofs are the source's. Stacks 0EKS combines Stacks 0EII, which makes
`Γ(U, 𝒪_U) ⟶ lim_n Γ(U, (A/fⁿA)~)` bijective, with the chain (1) ⇒ (4) of Stacks 0EKP. The
argument from Stacks 0EII is
`Stacks.Algebraization.completionFullyFaithful_of_isAdicComplete_of_annihilated`, which takes
that chain as an argument; the chain itself is
`Stacks.Algebraization.completionFullyFaithfulOnFiniteLocallyFree_of_bijective_sectionsToLimit`,
and it is supplied to that argument here. Stacks 0EKT reduces to Stacks 0EKS through Faltings'
annihilator theorem, Stacks 0EFC, in
`Stacks.Algebraization.completionFullyFaithful_of_isAdicComplete_of_depth`, and the same chain is
supplied to it.

## Main results

* `Stacks.Algebraization.completionFullyFaithfulOnFiniteLocallyFree_of_isAdicComplete_of_`
  `annihilated` — **Stacks 0EKS**.
* `Stacks.Algebraization.completionFullyFaithfulOnFiniteLocallyFree_of_isAdicComplete_of_depth`
  — **Stacks 0EKT**.

## Implementation notes

"`A` has a dualizing complex" is spelled
`∃ ω : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex ω`, with
`Dualizing.IsDualizingComplex` the predicate of [Stacks, Tag 0A7B]; this is the spelling of the
existence clauses of [Stacks, Tag 0BFR] in
`StacksFrontier/RingTheory/Dualizing/UbiquityStability.lean`.

## References

* [Stacks Project, Tag 0EKS](https://stacks.math.columbia.edu/tag/0EKS)
* [Stacks Project, Tag 0EKT](https://stacks.math.columbia.edu/tag/0EKT)
* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing
open Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- **[Stacks, Tag 0EKS].** Let `A` be a Noetherian ring, let `f ∈ 𝔞 ⊆ A` and let
`U = Spec(A) ∖ V(𝔞)`. If `A` is `f`-adically complete and `H¹_𝔞(A)` and `H²_𝔞(A)` are
annihilated by a power of `f`, then the completion functor `Coh(𝒪_U) ⟶ Coh(U, (f)𝒪_U)` is fully
faithful on the finite locally free objects.

The ideal sheaf `(f)𝒪_U` is `complementPrincipalIdealSheaf A 𝔞 f`, and full faithfulness on the
finite locally free objects is `CompletionFullyFaithfulOnFiniteLocallyFree`. The proof is
`completionFullyFaithful_of_isAdicComplete_of_annihilated`, Stacks 0EII followed by the chain
(1) ⇒ (4) of Stacks 0EKP, with that chain supplied by
`completionFullyFaithfulOnFiniteLocallyFree_of_bijective_sectionsToLimit`. -/
@[stacks 0EKS]
public theorem completionFullyFaithfulOnFiniteLocallyFree_of_isAdicComplete_of_annihilated
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Ideal A) (f : A) (hf : f ∈ a)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (h1 : ∃ n, ∀ x : localCohomologyModule A a (Ideal.fg_of_isNoetherianRing a)
      (ModuleCat.of A A) 1, f ^ n • x = 0)
    (h2 : ∃ n, ∀ x : localCohomologyModule A a (Ideal.fg_of_isNoetherianRing a)
      (ModuleCat.of A A) 2, f ^ n • x = 0) :
    CompletionFullyFaithfulOnFiniteLocallyFree (complementZeroLocus A a : Scheme)
      (complementPrincipalIdealSheaf A a f) :=
  completionFullyFaithful_of_isAdicComplete_of_annihilated A a f hf hcomplete h1 h2
    completionFullyFaithfulOnFiniteLocallyFree_of_bijective_sectionsToLimit

/-- **[Stacks, Tag 0EKT].** Let `A` be a Noetherian ring, let `f ∈ 𝔞 ⊆ A` and let
`U = Spec(A) ∖ V(𝔞)`. Assume

1. `A` has a dualizing complex and is complete with respect to `f`, and
2. `depth(A_𝔭) + dim((A/𝔭)_𝔮) > 2` for every prime `𝔭 ⊆ A` with `f ∉ 𝔭` and every
   `𝔮 ∈ V(𝔭) ∩ V(𝔞)`.

Then the completion functor `Coh(𝒪_U) ⟶ Coh(U, (f)𝒪_U)` is fully faithful on the finite locally
free objects.

Hypothesis (1) is `hdual` together with `hcomplete`. In hypothesis (2), `𝔮 ∈ V(𝔭) ∩ V(𝔞)` is
`𝔞 ≤ 𝔮` and `𝔭 ≤ 𝔮`, `(A/𝔭)_𝔮` is `A_𝔮 / 𝔭A_𝔮`, and the inequality is read in the extended
integers through `enatToEInt` and `krullDimToEInt`, as in
`completionFullyFaithful_of_isAdicComplete_of_depth`. The proof is that theorem — Faltings'
annihilator theorem, Stacks 0EFC, followed by Stacks 0EKS — with the chain (1) ⇒ (4) of
Stacks 0EKP supplied by `completionFullyFaithfulOnFiniteLocallyFree_of_bijective_sectionsToLimit`.
-/
@[stacks 0EKT]
public theorem completionFullyFaithfulOnFiniteLocallyFree_of_isAdicComplete_of_depth
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Ideal A) (f : A) (hf : f ∈ a)
    (hdual : ∃ omega : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex omega)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (hdepth : ∀ p q : PrimeSpectrum A, f ∉ p.asIdeal → a ≤ q.asIdeal →
      p.asIdeal ≤ q.asIdeal →
      enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl A)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > ((2 : ℤ) : EInt)) :
    CompletionFullyFaithfulOnFiniteLocallyFree (complementZeroLocus A a : Scheme)
      (complementPrincipalIdealSheaf A a f) := by
  obtain ⟨omega, homega⟩ := hdual
  exact completionFullyFaithful_of_isAdicComplete_of_depth A a f hf omega homega hcomplete hdepth
    completionFullyFaithfulOnFiniteLocallyFree_of_bijective_sectionsToLimit

end Stacks.Algebraization

end

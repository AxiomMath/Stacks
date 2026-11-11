module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GrothendieckExistenceNonSeparated
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorNonSeparatedCounterexample

/-!
# Counterexamples to algebraization of coherent sheaves without separatedness (Stacks 0ARF)

Stacks 0ARF lists three counterexamples, all coming from the failure of Grothendieck's existence
theorem on a non-separated scheme over a complete local ring:

1. Grothendieck's existence theorem (Stacks 088E) is false without the hypothesis that
   `X ⟶ Spec A` is separated;
2. the stack of coherent sheaves `Coh_{X/B}` of Stacks 09DS and 08WC is in general not algebraic
   without the separatedness hypothesis;
3. the functor `Quot_{F/X/B}` of Stacks 09TU is in general not an algebraic space without the
   separatedness hypothesis.

## Main results

* `AlgebraicGeometry.counterexamples_algebraization_of_not_isSeparated`: the three statements
  together. Part (1) is
  `Stacks.Algebraization.not_forall_isEquivalence_completionFunctorProperOver`, part (2) is
  `AlgebraicGeometry.Space.exists_coherentSituation_not_isAlgebraicStack` and part (3) is
  `AlgebraicGeometry.Space.exists_quotSituation_not_isAlgebraicSpace`.

## Implementation notes

All three witnesses are built on the spectrum of `k⟦t⟧` with its closed point doubled
(`Stacks.Examples.doubledClosedPoint`), which is of finite presentation and flat over `k⟦t⟧` but
not separated, rather than on the source's `Spec k⟦t⟧[x]` with its origin doubled; the statements
are existential, and both schemes are counterexamples for the same reason. In part (2) the
morphism is moreover flat, so it is a counterexample to Stacks 08WC as well as to Stacks 09DS.
In part (3) the module is `𝒪_X`, of finite presentation, so both assertions of Stacks 09TU fail.

## References

* [Stacks Project, Tag 0ARF](https://stacks.math.columbia.edu/tag/0ARF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

/-- **Stacks 0ARF.** Counterexamples to algebraization of coherent sheaves without separatedness:

1. Grothendieck's existence theorem (Stacks 088E) fails without separatedness: it is not true
   that for every Noetherian ring `A` complete with respect to an ideal `I` and every morphism
   `f : X ⟶ Spec A` locally of finite type and quasi-compact, the completion functor from coherent
   `𝒪_X`-modules with support proper over `A` to coherent `I`-adic systems with support proper
   over `A` is an equivalence;
2. there is a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`, of finite presentation
   and flat but not separated, whose stack of coherent sheaves `Coh_{X/Y}` is not an algebraic
   stack (so Stacks 09DS and 08WC fail without separatedness);
3. there is a Quot situation `f : X ⟶ B` over a scheme `S`, of finite presentation and flat but not
   separated, with `F` of finite presentation, such that the functor `Quot_{F/X/B}` has a model in
   the universe of the site but no model is an algebraic space (so Stacks 09TU fails without
   separatedness). -/
@[stacks 0ARF "all three counterexamples: (1) 088E fails without separatedness, (2) Coh_{X/Y} \
of 09DS and 08WC is not algebraic for a flat morphism of finite presentation which is not \
separated, (3) Quot_{F/X/B} of 09TU (F = O_X of finite presentation) is not an algebraic space \
for such a morphism; witness: Spec k[[t]] with its closed point doubled"]
theorem counterexamples_algebraization_of_not_isSeparated :
    (¬ ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
        {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f],
        (Stacks.Algebraization.completionFunctorProperOver A I f).IsEquivalence) ∧
    (∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (D : Space.CoherentSituation B S hS),
      Space.IsFlat B S hS D.f.hom ∧ ¬ Space.IsSeparated B S hS D.f.hom ∧
        ¬ Stack.IsAlgebraicStack.{u, w} B S hS D.coherentCFG.val) ∧
    (∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (D : Space.QuotSituation B S hS),
      Space.IsFlat B S hS D.f.hom ∧ ¬ Space.IsSeparated B S hS D.f.hom ∧
        D.F.IsFinitePresentationOnSite ∧ Nonempty (Space.QuotSitePresheafModel D) ∧
        ∀ N : Space.QuotSitePresheafModel D, ¬ IsAlgebraicSpace B S hS N.presheaf) :=
  ⟨Stacks.Algebraization.not_forall_isEquivalence_completionFunctorProperOver,
    Space.exists_coherentSituation_not_isAlgebraicStack,
    Space.exists_quotSituation_not_isAlgebraicSpace⟩

end AlgebraicGeometry

end

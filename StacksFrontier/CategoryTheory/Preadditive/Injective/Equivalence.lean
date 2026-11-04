module

public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Functorial injective embeddings transport along an equivalence

Stacks 0161 transports functorial injective embeddings along an adjunction `v ⊣ u` of additive
functors between abelian categories, subject to `v` preserving monomorphisms and reflecting
zero objects. An equivalence of abelian categories satisfies those hypotheses for free: its
adjoint equivalence has both functors additive as soon as either is, its inverse preserves
monomorphisms because it is an equivalence, and it reflects zero objects because the counit is
an isomorphism.

This file isolates that special case, which is what one uses whenever a category of interest
is only known to be equivalent to one for which the embeddings have already been constructed —
for instance to move between a presheaf category over a site and the same category over a
small model of the site, or between a category of modules and one over a universe-lifted ring.

## Main results

* `hasFunctorialInjectiveEmbeddings_of_equivalence`: if `A ≌ B` is an equivalence of abelian
  categories whose two functors are additive and `A` has functorial injective embeddings, then
  so does `B`.

## References

* [Stacks Project, Tag 0161](https://stacks.math.columbia.edu/tag/0161)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-- **Stacks 0161 for an equivalence.** If `e : A ≌ B` is an equivalence of abelian categories
whose two functors are additive, and `A` has functorial injective embeddings, then so does `B`:
apply `hasFunctorialInjectiveEmbeddings_of_adjunction` to the adjoint equivalence
`e.symm.toAdjunction`, whose inverse preserves monomorphisms and reflects zero objects. -/
theorem hasFunctorialInjectiveEmbeddings_of_equivalence
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive]
    (hA : HasFunctorialInjectiveEmbeddings A) :
    HasFunctorialInjectiveEmbeddings B := by
  have : EnoughInjectives A :=
    enoughInjectives_of_hasFunctorialInjectiveEmbeddings (𝒜 := A) hA
  exact hasFunctorialInjectiveEmbeddings_of_adjunction
    (A := A) (B := B) e.functor e.inverse e.symm.toAdjunction
    (by intro X Y f hf; infer_instance)
    (by intro X hX; exact (Functor.map_isZero e.functor hX).of_iso (e.counitIso.app X).symm) hA

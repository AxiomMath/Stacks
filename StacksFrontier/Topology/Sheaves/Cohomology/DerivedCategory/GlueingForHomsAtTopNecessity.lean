module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsAtOneOpen

/-!
# The glueing of morphisms at `⊤` needs a hypothesis on the collection

`Stacks.DerivedGlueing.HasGluingForHomsAt S ⊤` is the sheaf condition of [Stacks, Tag 0D66]
part (2) read at the whole space; it is the one granted hypothesis of
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_hasGluingForHomsAtTop`, the uniqueness half of
[Stacks, Tag 0D6C].

This file settles what shape a discharge of it can have.  `Stacks.DerivedGlueing.LocallyGiven`
puts **no** condition on its collection of opens — in particular the collection may be empty — and
at an empty collection the predicate at `⊤` says that a morphism over `⊤` is determined, and
exists, with no condition at all on it.  So it forces every `Hom`-set of `D(𝒪_X)` read over `⊤` to
be a subsingleton.  That is false for any ringed space whose derived category is not thin, so
`HasGluingForHomsAt S ⊤` is **not** provable for an arbitrary system: any discharge must consume a
hypothesis on `S.opens`, and the source's own hypothesis — that the collection covers `X` and that
the intersection of two members is a union of members, Situation [Stacks, Tag 0D67] — is of
exactly that kind.

## Main results

* `Stacks.DerivedGlueing.subsingleton_hom_of_hasGluingForHomsAt_top`: the glueing condition at `⊤`
  over a collection with no members makes every `Hom`-set over `⊤` a subsingleton.
* `Stacks.DerivedGlueing.subsingleton_hom_of_hasGluingForHomsAt_top_locallyGivenOfGlobal`: the
  same at a system that actually exists, the one prescribed by a single global object over the
  empty collection.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D6C](https://stacks.math.columbia.edu/tag/0D6C)

Tags covered: none.  These statements delimit a hypothesis of the development; they are not
clauses of a tag's statement.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- **Over a collection with no members, the glueing condition at `⊤` makes every `Hom`-set over
`⊤` a subsingleton.**  Every hypothesis of `Stacks.DerivedGlueing.HasGluingForHomsAt` quantifies
over the members of the collection, so all of them hold vacuously, and the conclusion asserts the
unique existence of a morphism subject to no condition.  Uniqueness is what is used. -/
theorem subsingleton_hom_of_hasGluingForHomsAt_top (S : LocallyGiven X)
    (hS : ∀ W : Opens X.carrier, W ∉ S.opens) (hglue : HasGluingForHomsAt S ⊤)
    (K L : OpenDerivedCategory X ⊤) :
    Subsingleton (K ⟶ L) := by
  obtain ⟨ψ, -, huniq⟩ := hglue K L (fun W => (hS W).elim) (fun W => (hS W).elim)
    fun W _ hW => (hS W hW).elim
  exact subsingleton_of_forall_eq ψ fun a => huniq a fun W hW => (hS W hW).elim

/-- **The same at a system that exists.**  `Stacks.DerivedGlueing.locallyGivenOfGlobal` over the
empty collection is a system of locally given derived objects whose collection has no members, so
the glueing condition at `⊤` for it would make every `Hom`-set of the derived category over `⊤` a
subsingleton.

This is why `Stacks.DerivedGlueing.HasGluingForHomsAt S ⊤` cannot be discharged for an arbitrary
`S`: a proof would apply here. -/
theorem subsingleton_hom_of_hasGluingForHomsAt_top_locallyGivenOfGlobal
    (M : OpenDerivedCategory X ⊤)
    (hglue : HasGluingForHomsAt (locallyGivenOfGlobal X ∅ M) ⊤)
    (K L : OpenDerivedCategory X ⊤) :
    Subsingleton (K ⟶ L) :=
  subsingleton_hom_of_hasGluingForHomsAt_top _ (fun W => Set.notMem_empty W) hglue K L

end Stacks.DerivedGlueing

end

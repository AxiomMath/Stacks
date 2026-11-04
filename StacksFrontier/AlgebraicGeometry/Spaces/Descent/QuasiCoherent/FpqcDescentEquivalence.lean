module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness

/-!
# The canonical descent functor of an fpqc covering, as an equivalence

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `(f i : X i ⟶ X)` be a
family of algebraic spaces over it.  Stacks 04W8 asserts two things about the canonical descent
functor of Stacks 04W5 for an fpqc covering: that it is fully faithful, and that every descent
datum of Stacks 04W3 relative to the covering is effective.  Together they say that the functor
is an **equivalence**, and this file is where the two are joined.

The full-faithfulness clause is unconditional:
`AlgebraicGeometry.Space.QuasiCoherentDescent`
`.nonempty_fullyFaithful_canonicalDescentFunctor_of_isFpqcCovering`.  What this file adds is the
dictionary between the effectivity clause and essential surjectivity, and the assembly of the
equivalence from the two clauses.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentFunctor'_obj_eq`: the value of
  the canonical descent functor formed with no hypothesis is the canonical descent datum of
  Stacks 04W5.
* `AlgebraicGeometry.Space.QuasiCoherentDescent`
  `.essSurj_canonicalDescentFunctor'_iff_forall_isEffective`: **essential surjectivity of the
  canonical descent functor is the effectivity of every descent datum relative to the family**,
  with no hypothesis on the family.
* `AlgebraicGeometry.Space.QuasiCoherentDescent`
  `.isEquivalence_canonicalDescentFunctor'_of_forall_isEffective`: **the canonical descent
  functor of an fpqc covering is an equivalence as soon as every descent datum relative to it is
  effective** — the full-faithfulness clause of Stacks 04W8 is supplied, not assumed.

## Implementation notes

`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentFunctor'` and
`…canonicalDescentFunctor` are the same functor — they differ only in the proofs filling the
`Prop`-valued fields of their values — but **the equation of the two functors is not what the
dictionary below is proved from**: the kernel does not come back from it, composition in the
category of descent data of Stacks 04W3 being a projection of a structure instance.  The passage is made at one object instead, by `…canonicalDescentFunctor'_obj_eq`,
where the step is a projection of a structure literal and is free.  The primed form is the one
the full-faithfulness clause is stated at, because it is formed with no hypothesis.

No `@[stacks]` attribute is registered here yet: the effectivity clause of Stacks 04W8 is
carried as a hypothesis below, and the tag belongs on a statement that assumes neither clause.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Xi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Xi i ⟶ X)

/-- The value of the canonical descent functor formed with no hypothesis is the canonical descent
datum of Stacks 04W5 of the module, the two data differing only in the proofs filling their
`Prop`-valued fields. -/
theorem canonicalDescentFunctor'_obj_eq
    (M : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) :
    (canonicalDescentFunctor' B S hS Xi f).obj M =
      canonicalDescentDatum B S hS Xi f M.obj M.property :=
  canonicalDescentDatum'_eq B S hS Xi f M.obj M.property

/-- **The effectivity of every descent datum relative to a family of algebraic spaces over `X` is
the essential surjectivity of the canonical descent functor of Stacks 04W5 for that family.**
Nothing is assumed about the family.

This is `AlgebraicGeometry.Space.QuasiCoherentDescent.isEffective_iff_essImage` read at the
canonical descent functor formed with no hypothesis, the passage between the two being
`…canonicalDescentFunctor'_obj_eq` at the module the essential image produces.  The equation of
the two *functors* is not used: it holds, but asking the kernel for it leads to a
deterministic timeout, composition in the category of descent data being a projection of a
structure instance. -/
theorem essSurj_canonicalDescentFunctor'_iff_forall_isEffective :
    (canonicalDescentFunctor' B S hS Xi f).EssSurj ↔
      ∀ D : DescentDatum B S hS Xi f, IsEffective B S hS Xi f D := by
  refine ⟨fun h D => ?_, fun h => ⟨fun D => ?_⟩⟩
  · obtain ⟨M, ⟨e⟩⟩ := h.mem_essImage D
    exact ⟨M.obj, M.property,
      ⟨e.symm ≪≫ eqToIso (canonicalDescentFunctor'_obj_eq B S hS Xi f M)⟩⟩
  · obtain ⟨M, hM, ⟨e⟩⟩ := h D
    exact ⟨⟨M, hM⟩,
      ⟨eqToIso (canonicalDescentFunctor'_obj_eq B S hS Xi f ⟨M, hM⟩) ≪≫ e.symm⟩⟩

/-- **The canonical descent functor of an fpqc covering of algebraic spaces is an equivalence as
soon as every descent datum relative to it is effective.**

The full-faithfulness clause of Stacks 04W8 is supplied and not assumed, by
`AlgebraicGeometry.Space.QuasiCoherentDescent`
`.nonempty_fullyFaithful_canonicalDescentFunctor_of_isFpqcCovering`; the effectivity clause is
the hypothesis `heff`, and it becomes essential surjectivity by
`…essSurj_canonicalDescentFunctor'_iff_forall_isEffective`. -/
theorem isEquivalence_canonicalDescentFunctor'_of_forall_isEffective
    (hf : IsFpqcCovering B S hS fun i => (f i).hom)
    (heff : ∀ D : DescentDatum B S hS Xi f, IsEffective B S hS Xi f D) :
    (canonicalDescentFunctor' B S hS Xi f).IsEquivalence :=
  have ⟨hff⟩ := nonempty_fullyFaithful_canonicalDescentFunctor_of_isFpqcCovering.{u, v}
    B S hS Xi f hf
  have := hff.full
  have := hff.faithful
  have := (essSurj_canonicalDescentFunctor'_iff_forall_isEffective B S hS Xi f).2 heff
  Functor.IsEquivalence.mk

end AlgebraicGeometry.Space.QuasiCoherentDescent

end

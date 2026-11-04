module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.Logic.Small.Basic
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Finiteness

/-!
# Shrinking the index of a directed colimit

[Stacks, Tag 0817] asserts that an integral quasi-coherent algebra on a quasi-compact and
quasi-separated scheme is a directed colimit of finite, finitely presented quasi-coherent
algebras, and its statement asks for the indexing preorder to lie in the *same* universe `u`
as the scheme.  Every route to that conclusion produces an index one universe higher:

* the finite type quasi-coherent subalgebras of `A`, which are the index of
  [Stacks, Tag 05JT], form a full subcategory of `CategoryTheory.Subobject A`, and
  `CategoryTheory.Subobject A` lives in `Type (u + 1)` because a subobject is an equivalence
  class of monomorphisms, whose type is `Type (u + 1)`;
* [Stacks, Tag 086N], which supplies the finite presentation that no subalgebra of `A` need
  satisfy, is itself stated with an index in `Type (u + 1)`.

So the conclusion at `Type u` does not follow from those two by composition, and a reader may
reasonably suspect the demand for `Type u` of being an error in the statement.  **It is not.**
This file isolates exactly what it costs: `exists_small_index` converts a directed colimit over
an index in *any* universe into one over an index in `Type w`, given only that the original
index is `w`-small.  So the gap between "a directed colimit indexed by the subalgebras of `A`"
and "a directed colimit indexed by a preorder in `Type u`" is one `Small` instance and nothing
else.

The construction is `Shrink` of the index, carrying the preorder pulled back along
`equivShrink`, which makes `equivShrink` an order isomorphism; `OrderIso.equivalence` turns that
into an equivalence of the induced categories, and
`CategoryTheory.Limits.IsColimit.whiskerEquivalence`
transports the colimit along it.  Nothing about schemes, sheaves or integrality enters, which is
why the general form is stated first: the same shrink is what tags 05JT and 086N need to reach
the index their own statements ask for.

## Main results

* `Stacks.SmallIndex.exists_small_index`: a directed colimit whose index is `w`-small may be
  reindexed by a directed preorder in `Type w`, preserving any property of the objects of the
  diagram.
* `Stacks.SmallIndex.exists_small_index_finite_finitePresentation`: the specialisation whose
  conclusion is, verbatim, that of [Stacks, Tag 0817].

## Implementation notes

The shrunk preorder is introduced as a local instance inside the proof rather than as a global
one: the conclusion quantifies existentially over the preorder, so no instance needs to be
available to a caller, and declaring one on `Shrink` would affect unrelated code.

`exists_small_index_finite_finitePresentation` carries the hypothesis that the given diagram
already consists of quasi-coherent, finite and finitely presented algebras, so it is strictly a
reindexing statement and asserts nothing about integrality.  It is therefore **not** a proof of
[Stacks, Tag 0817] and carries no attribute: the tag's hypotheses are integrality and
quasi-coherence of `A`, and a statement registered under the tag may not carry a hypothesis the
tag lacks.

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w v₁ u₁ u₂ u

namespace Stacks.SmallIndex

section General

variable {C : Type u₁} [Category.{v₁} C]

/-- **A directed colimit with a small index may be reindexed by a preorder in that universe.**
If `J` is a nonempty directed preorder which is `w`-small, and `A` is the colimit of a diagram
`G : J ⥤ C` under the cocone `t`, then `A` is also the colimit of a diagram indexed by a
nonempty directed preorder lying in `Type w`, and every object of the new diagram is an object
of the old one -- so any property `P` holding throughout `G` holds throughout the new diagram.

The index is `Shrink J` with the preorder pulled back along `equivShrink`, which makes
`equivShrink` an order isomorphism and hence, by `OrderIso.equivalence`, an equivalence of the
induced categories; the colimit transports along it. -/
theorem exists_small_index {J : Type u₂} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    [Small.{w} J] {G : J ⥤ C} {A : C} (t : G ⟶ (Functor.const J).obj A)
    (ht : IsColimit (Cocone.mk A t)) (P : C → Prop) (hP : ∀ j, P (G.obj j)) :
    ∃ (I : Type w) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ C) (s : F ⟶ (Functor.const I).obj A) (_ : IsColimit (Cocone.mk A s)),
      ∀ i, P (F.obj i) := by
  classical
  let _ : Preorder (Shrink.{w} J) := Preorder.lift (equivShrink J).symm
  -- `equivShrink` is an order isomorphism for the pulled-back order, by definition of the order.
  let eo : Shrink.{w} J ≃o J := ⟨(equivShrink J).symm, Iff.rfl⟩
  have : Nonempty (Shrink.{w} J) := ⟨equivShrink J (Classical.arbitrary J)⟩
  have : IsDirected (Shrink.{w} J) (· ≤ ·) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨j, hja, hjb⟩ := directed_of (· ≤ ·) (eo a) (eo b)
    exact ⟨eo.symm j, eo.le_symm_apply.mpr hja, eo.le_symm_apply.mpr hjb⟩
  refine ⟨Shrink.{w} J, inferInstance, inferInstance, inferInstance,
    eo.equivalence.functor ⋙ G, ((Cocone.mk A t).whisker eo.equivalence.functor).ι, ?_,
    fun i => hP _⟩
  exact ht.whiskerEquivalence eo.equivalence

end General

section AlgebraSheaf

open Stacks.RelativeSpec

/-- **The conclusion of [Stacks, Tag 0817] follows from any `u`-small directed system of
quasi-coherent, finite, finitely presented algebras with colimit `A`.**

This is `exists_small_index` specialised so that its conclusion is, verbatim, the conclusion of
the statement of [Stacks, Tag 0817]: an index in `Type u`, a nonempty directed preorder on it, a
diagram of algebra sheaves, a colimiting cocone with vertex `A`, and quasi-coherence, finiteness
and finite presentation of every object of the diagram.

It isolates precisely what the tag's demand for an index in `Type u` costs over the routes that
reach it: the routes through tags 05JT and 086N produce an index in `Type (u + 1)`, and the only
thing missing is that the index be `u`-small.  The tag is therefore not defective in asking for
`Type u`.

It is *not* a proof of the tag and carries no attribute: it assumes the directed system it would
have to construct, and it assumes finiteness and finite presentation rather than deducing them
from integrality of `A`. -/
theorem exists_small_index_finite_finitePresentation {X : Scheme.{u}} (A : AlgebraSheaf X)
    {J : Type u₂} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)] [Small.{u} J]
    {G : J ⥤ AlgebraSheaf X} (t : G ⟶ (Functor.const J).obj A)
    (ht : IsColimit (Cocone.mk A t))
    (hG : ∀ j, (G.obj j).IsQuasicoherent ∧ (G.obj j).IsFinite ∧
      (G.obj j).IsFinitePresentation) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (s : F ⟶ (Functor.const I).obj A)
      (_ : IsColimit (Cocone.mk A s)),
      ∀ i, (F.obj i).IsQuasicoherent ∧ (F.obj i).IsFinite ∧
        (F.obj i).IsFinitePresentation :=
  exists_small_index t ht
    (fun B => B.IsQuasicoherent ∧ B.IsFinite ∧ B.IsFinitePresentation) hG

end AlgebraSheaf

end Stacks.SmallIndex

end

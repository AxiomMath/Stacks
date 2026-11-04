module

public import Mathlib.Basic.Countable.Small
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Data.Set.Finite.Lattice

/-!
# The index universe of `ObjectProperty.ind` is a genuine parameter

`CategoryTheory.ObjectProperty.ind.{t} P X` says that `X` is the colimit of a filtered diagram
indexed by a small category *in the universe `t`*, all of whose values satisfy `P`. The universe
`t` is independent of the universes of the ambient category, so a predicate defined through
`ind` either pins `t` to one of the ambient universes or carries it as an extra universe
parameter.

This file settles which of the two is the faithful choice, by showing that `t` cannot be
dispensed with: `ind.{t} P` and `ind.{t'} P` are *different* predicates. Raising the index
universe is free (Mathlib's `ObjectProperty.of_essentiallySmall_index`, used in
`ind_of_univLE` below), but the converse fails, so the family `fun t ↦ ind.{t} P X` is a strictly
decreasing chain of conditions. Consequently a definition that leaves `t` free asserts the
conjunction over all `t`, which is strictly stronger than any one member of the chain, and a
lemma stated with one shared `t` across several ambient categories is not an instance of the
same lemma with each `t` pinned to its own ambient universe.

## Main results

* `CategoryTheory.ObjectProperty.ind_of_univLE`: raising the index universe is free.
* `CategoryTheory.ObjectProperty.ind_not_universe_invariant`: the index universe cannot be
  changed downwards. In the poset `Set (Type v)`, the property of being a finite set, and the
  object `Set.univ`, give an `ind.{v + 1}` presentation and no `ind.{v}` presentation.

## Implementation notes

The witness is as small as possible: the ambient category is a *preorder* category, where every
hom type is a proposition, so a colimit cocone is exactly a least upper bound and no colimit has
to be computed. `small_of_ind_finite_set` is the whole content: a presentation indexed in
`Type v` exhibits the presented set as a union of `Type v`-many finite sets, hence as a
`Small.{v}` set, whereas `Set.univ : Set (Type v)` is not `Small.{v}` by `not_small_type`.

The same phenomenon is what forces the index universe of the repository's ind-étale and
ind-Zariski predicates (`StacksDraft.IndEtale`, `Algebra.IsIndZariski`, and the `ind_etale`
field of `IsLocalRing.IsHenselization`) to be pinned to the carrier universe: the criterion that
characterises `ind` without naming an index category, Lemma 07C3
(`CommRingCat.ind_under_iff_exists_factorization`), is available only at the ambient universe.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t t' v

namespace CategoryTheory.ObjectProperty

/-- **Raising the index universe of `ind` is free.** A diagram indexed in `Type t` is
essentially small in any larger universe. -/
theorem ind_of_univLE {C : Type*} [Category* C] (P : ObjectProperty C) {X : C}
    (h : ind.{t} P X) : ind.{max t t'} P X := by
  obtain ⟨J, _, _, pres, hp⟩ := h
  exact of_essentiallySmall_index (J := J) pres hp

/-- A presentation of a set of types as a filtered colimit of finite sets, indexed by a category
in `Type v`, exhibits it as a union of `Type v`-many finite sets, hence as a `Small.{v}` set. -/
theorem small_of_ind_finite_set {s : Set (Type v)}
    (h : ind.{v} (fun u : Set (Type v) ↦ u.Finite) s) : Small.{v} ↥s := by
  obtain ⟨J, _, _, pres, hp⟩ := h
  have hub : ∀ j, pres.diag.obj j ≤ s := fun j ↦ leOfHom (pres.ι.app j)
  have hle : s ≤ ⋃ j, pres.diag.obj j :=
    leOfHom (pres.isColimit.desc
      { pt := ⋃ j, pres.diag.obj j
        ι := { app j := homOfLE (Set.subset_iUnion _ j) } })
  have hsmall : ∀ j : J, Small.{v} ↥(pres.diag.obj j) := fun j ↦
    have : Finite ↥(pres.diag.obj j) := (hp j).to_subtype
    Countable.toSmall _
  refine small_of_surjective (f := fun p : Σ j : J, ↥(pres.diag.obj j) ↦
    (⟨p.2.1, hub p.1 p.2.2⟩ : ↥s)) ?_
  intro y
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hle y.2)
  exact ⟨⟨j, ⟨y.1, hj⟩⟩, rfl⟩

/-- The whole of `Type v` is the filtered colimit of its finite subsets, a presentation whose
index category lives in `Type (v + 1)`. -/
theorem ind_finite_set_univ :
    ind.{v + 1} (fun u : Set (Type v) ↦ u.Finite) (Set.univ : Set (Type v)) := by
  refine ⟨Finset (Type v), inferInstance, inferInstance,
    { diag :=
        { obj s := (↑s : Set (Type v))
          map h := homOfLE (by exact_mod_cast leOfHom h) }
      ι := { app s := homOfLE (Set.subset_univ _) }
      isColimit :=
        { desc c := homOfLE (fun x _ ↦ leOfHom (c.ι.app {x}) (by simp)) } },
    fun s ↦ s.finite_toSet⟩

/-- **The index universe of `ObjectProperty.ind` cannot be lowered.** In the poset
`Set (Type v)`, with `P` the property of being a finite set, the object `Set.univ` satisfies
`ind.{v + 1} P` and does not satisfy `ind.{v} P`. So `ind.{t} P` and `ind.{t'} P` are different
predicates, and the index universe of a definition built from `ind` is a genuine parameter of
that definition rather than a notational choice. -/
theorem ind_not_universe_invariant :
    ind.{v + 1} (fun u : Set (Type v) ↦ u.Finite) (Set.univ : Set (Type v)) ∧
      ¬ ind.{v} (fun u : Set (Type v) ↦ u.Finite) (Set.univ : Set (Type v)) :=
  ⟨ind_finite_set_univ, fun h ↦ by
    have := small_of_ind_finite_set h
    exact not_small_type.{v, v} (small_of_surjective (Equiv.Set.univ (Type v)).surjective)⟩

end CategoryTheory.ObjectProperty

end

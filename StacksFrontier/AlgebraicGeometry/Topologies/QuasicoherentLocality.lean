module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence

/-!
# Quasi-coherence from global presentations on a covering family

A sheaf of modules on a site is quasi-coherent, in the sense of Stacks 03DL(6), when every object
of the site has a covering on whose members the restricted module has a global presentation.  The
clause of Stacks 03DN for quasi-coherence says that it is enough to exhibit *one* family of
objects which covers the final object and on whose members the module is globally presented: the
covering of an arbitrary object is then the sieve of objects of that family, and a global
presentation travels along an arbitrary morphism of the site.

That clause is already available as
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation`, for a
module whose sections lie in the universe of the coefficient rings.  This file frees the two
universes from each other.

## Main results

* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation`: **a sheaf of
  modules which has a global presentation on each member of a family covering the final object is
  quasi-coherent.**
* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation'`: the same,
  with the index type of the family in an arbitrary universe.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_iff_coversTop_hasGlobalPresentation`:
  **Stacks 03DN for quasi-coherence, with the universe of the module sections independent of the
  universe of the coefficient rings.**

## Implementation notes

The two universes have to be independent for the small étale site of an algebraic space.  The
construction of the largest quasi-coherent submodule, Stacks 04CK, quantifies over the subobject
lattice of a module, which is only small in a universe containing the site; so the modules it
takes direct sums of have sections in `max (u + 1) m` while the structure sheaf of the site is
`CommRingCat.{u}`-valued.  Both closure clauses of Stacks 03M1 that the construction consumes are
local statements about those modules, and neither
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation` nor
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite` applies to
them.

Only the direction proved here can be freed this way.  The direction which *produces* a
quasi-coherent restriction on each member from quasi-coherence of the module passes through the
slice at an object twice, and the comparison of the two readings of a module on an iterated slice
is where the universes get tied together; the direction proved here uses only
`Stacks.SheafOfModules.hasGlobalPresentation_overMap`, whose statement already has the universe
of the sections independent of the universe of the rings.

The covering family produced at an object `U` is `CategoryTheory.Sieve.ofObjects` of the given
family, read as a family of arrows indexed by its own members.  That sieve consists of the arrows
into `U` whose source admits *some* morphism to a member of the family, which is exactly what
`Stacks.SheafOfModules.hasGlobalPresentation_overMap` consumes.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- A sheaf of modules which has a global presentation on each member of a family covering the
final object is quasi-coherent, with the index type of the family in an arbitrary universe.  This
is `Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation` with the
index type `I : Type u` freed.

The index type is not the index type of the covering sieve that
`SheafOfModules.IsQuasicoherentOnSite` asks for — that one is read off the arrows of
`CategoryTheory.Sieve.ofObjects` of the family and lies in `Type (max u v)` whatever `I` is — so a
family covering the final object of one site may be transported to another site whose objects
live in a different universe. -/
theorem isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation'
    (M : SheafOfModules.{m} R) {I : Type*} {W : I → C} (hW : J.CoversTop W)
    (hP : ∀ i, (M.over (W i)).HasGlobalPresentation) :
    M.IsQuasicoherentOnSite := by
  classical
  refine ⟨fun U ↦ ⟨{f : Over U // Sieve.ofObjects W U f.hom}, fun a ↦ a.1.left,
    fun a ↦ a.1.hom, ?_, ?_⟩⟩
  · have hEq : Sieve.ofArrows (fun a : {f : Over U // Sieve.ofObjects W U f.hom} ↦ a.1.left)
        (fun a ↦ a.1.hom) = Sieve.ofObjects W U := by
      refine le_antisymm (fun Z g hg ↦ ?_) (fun Z g hg ↦ ?_)
      · obtain ⟨a, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
        exact (Sieve.ofObjects W U).downward_closed a.2 b
      · rw [Sieve.mem_ofArrows_iff]
        exact ⟨⟨Over.mk g, hg⟩, 𝟙 Z, by simp⟩
    rw [hEq]
    exact hW U
  · intro a
    obtain ⟨i, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff W a.1.hom).mp a.2
    exact hasGlobalPresentation_overMap M b (hP i)

/-- A sheaf of modules which has a global presentation on each member of a family covering the
final object is quasi-coherent.  This is the producing direction of the clause of Stacks 03DN for
quasi-coherence, with the universe of the module sections independent of the universe of the
coefficient rings. -/
theorem isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation
    (M : SheafOfModules.{m} R) {I : Type u} {W : I → C} (hW : J.CoversTop W)
    (hP : ∀ i, (M.over (W i)).HasGlobalPresentation) :
    M.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation' M hW hP

/-- **Stacks 03DN, quasi-coherence.**  A sheaf of modules is quasi-coherent if and only if it has
a global presentation on each member of some family of objects covering the final object.

This is `Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation` with
the universe of the module sections independent of the universe of the coefficient rings. -/
@[stacks 03DN "quasi_coherent"]
theorem isQuasicoherentOnSite_iff_coversTop_hasGlobalPresentation (M : SheafOfModules.{m} R) :
    M.IsQuasicoherentOnSite ↔
      ∃ (I : Type u) (W : I → C), J.CoversTop W ∧
        ∀ i : I, (M.over (W i)).HasGlobalPresentation := by
  refine ⟨fun hM ↦ ⟨{V : C | (M.over V).HasGlobalPresentation}, fun i ↦ i.1, fun U ↦ ?_,
    fun i ↦ i.2⟩, fun ⟨_, _, hW, hP⟩ ↦ isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation
      M hW hP⟩
  obtain ⟨I, V, f, hV, hP⟩ := hM.locally_hasGlobalPresentation U
  refine J.superset_covering ((Sieve.ofArrows_le_ofObjects V f).trans
    (Sieve.ofObjects_mono ?_)) hV
  rintro x ⟨i, rfl⟩
  exact ⟨⟨V i, hP i⟩, rfl⟩

end Stacks.SheafOfModules

end

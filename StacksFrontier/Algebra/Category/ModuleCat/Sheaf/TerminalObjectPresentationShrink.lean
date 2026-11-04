module

public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules

/-!
# A global presentation over a site with a final object is one at the universe of the sections

On a site whose objects lie in a larger universe than the sections of its sheaves of modules — the
flat-fppf site of an algebraic stack, say, with objects in `Type (u + 1)` and sections in
`Type u` — the global presentations of `SheafOfModules.HasGlobalPresentation` (the clause of
Stacks 03DL (6)) are indexed by types in the larger universe, while those of
`SheafOfModules.IsPresentedByGlobalSections` (Stacks 03DE (6) at a single universe) are indexed by
types in the universe of the sections. On a site with a final object the two agree: the global
sections of every sheaf of modules are small there
(`SheafOfModules.small_sections_of_isTerminal`), so a global presentation can be shrunk to a
`SheafOfModules.Presentation`
(`SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections`), whose cokernel
diagram is a presentation at the universe of the sections.

## Main results

* `SheafOfModules.isPresentedByGlobalSections_of_hasGlobalPresentation_of_isTerminal`.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

universe u v r

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- **On a site with a final object, a global presentation (Stacks 03DL (6)) is a presentation
by global sections at the universe of the sections (Stacks 03DE (6)).** The global sections are
small, so the presentation shrinks to a `SheafOfModules.Presentation`, a cokernel of a map between
free modules on types in the universe of the sections. -/
theorem isPresentedByGlobalSections_of_hasGlobalPresentation_of_isTerminal {T : C}
    (hT : IsTerminal T) {M : SheafOfModules.{r} R} (h : M.HasGlobalPresentation) :
    M.IsPresentedByGlobalSections := by
  have := fun N : SheafOfModules.{r} R => small_sections_of_isTerminal hT N
  obtain ⟨P⟩ := h.nonempty_presentation_of_small_sections
  exact ⟨_, _, free _, free _, ιFree, ιFree, ⟨isColimitFreeCofan _⟩, ⟨isColimitFreeCofan _⟩,
    _, _, _, ⟨P.isColimit⟩⟩

end SheafOfModules

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.GlobalSectionsBijective

/-!
# Global sections as a compatible family, and as an abelian group

A *section* of a sheaf of modules in the sense of `PresheafOfModules.sections` is a compatible
family of sections over every open, while `Γ(M, ⊤)` is a single element of the group of sections
over `⊤` and `(secF R ⊤).obj M` is that same group read in `AddCommGrpCat`. The three are
interchangeable, because `⊤` is the terminal open: a compatible family is determined by, and can
be built from, its value over `⊤`.

On a scheme, a sheaf of modules with at most one compatible family of sections therefore has at
most one section over `⊤`, and `Γ(⊤, -)` sends it to a zero object of `AddCommGrpCat`.

## Main definitions

* `Stacks.AmpleSectionConnected.sectionsEquivEvalTop`: the bijection between the compatible
  families of sections of a sheaf of modules on a scheme and its sections over `⊤`.

## Main results

* `Stacks.AmpleSectionConnected.subsingleton_eval_top_of_subsingleton_sections`: at most one
  compatible family of sections gives at most one section over `⊤`.
* `Stacks.AmpleSectionConnected.isZero_secF_top_of_subsingleton_sections`: at most one
  compatible family of sections gives a zero object `(secF R ⊤).obj M` of `AddCommGrpCat`.

## Implementation notes

The bijection is `Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal` at the terminal
object `CategoryTheory.Limits.isTerminalTop` of the opens.

## References

* [Stacks Project, Tag 0FD7](https://stacks.math.columbia.edu/tag/0FD7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AmpleSectionConnected

/-- **The sections of a sheaf of modules on a scheme are its sections over `⊤`.** This is
`Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal` at the terminal open. -/
noncomputable def sectionsEquivEvalTop (X : Scheme.{u}) (M : X.Modules) :
    M.sections ≃ Γ(M, ⊤) :=
  Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M isTerminalTop

/-- **A sheaf of modules with at most one compatible family of sections has at most one section
over `⊤`.** -/
theorem subsingleton_eval_top_of_subsingleton_sections (X : Scheme.{u}) (M : X.Modules)
    (h : Subsingleton M.sections) : Subsingleton Γ(M, ⊤) :=
  (sectionsEquivEvalTop X M).symm.subsingleton

/-- **A sheaf of modules with at most one compatible family of sections has zero global
sections**, as an object of `AddCommGrpCat`. -/
theorem isZero_secF_top_of_subsingleton_sections (X : Scheme.{u}) (M : X.Modules)
    (h : Subsingleton M.sections) : IsZero ((secF X.ringCatSheaf ⊤).obj M) :=
  AddCommGrpCat.isZero_iff_subsingleton.mpr (subsingleton_eval_top_of_subsingleton_sections X M h)

end Stacks.AmpleSectionConnected

end

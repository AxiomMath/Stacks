module

public import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic

/-!
# Sections over the terminal open and over the whole space

`Stacks.SheafOfModules.TwistAction.actionOf` multiplies by a section over the terminal object
`⊤_ (Opens X)` of the site of opens, while `AlgebraicGeometry.cohomologyOverField` and
`AlgebraicGeometry.globalSectionsOverField` are stated at `(⊤ : X.Opens)`.  The two opens are
equal (`AlgebraicGeometry.terminal_opens_eq_top`); this file gives the comparison on sections
as a restriction isomorphism.

## Main results

* `AlgebraicGeometry.restrictTerminalTopEquiv`: the restriction `Γ(M, ⊤_ (Opens X)) ≃+ Γ(M, ⊤)`
  is an isomorphism.

## Implementation notes

`AlgebraicGeometry.restrictTerminalTopEquiv` is the restriction map along
`terminal.from (⊤ : X.Opens)`; its inverse is restriction along the opposite comparison, and the
two composites are identities because the morphisms they are restrictions along are identities,
again by `Subsingleton.elim`.  It is *not* obtained by transporting along
`AlgebraicGeometry.terminal_opens_eq_top`: a transport of a section along an equality of opens
leaves an `Eq.mpr` in every downstream statement, while the restriction map is the honest
comparison and is what the sheaf axioms see.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The comparison morphism `⊤_ (Opens X) ⟶ ⊤` given by `le_top`. -/
abbrev topFromTerminal (X : Scheme.{u}) : (⊤_ (Opens X)) ⟶ (⊤ : X.Opens) := homOfLE le_top

/-- **Restriction from the terminal open to the whole space is an isomorphism on sections.** -/
def restrictTerminalTopEquiv (M : X.Modules) : Γ(M, ⊤_ (Opens X)) ≃+ Γ(M, ⊤) where
  toFun := M.presheaf.map (terminal.from (⊤ : X.Opens)).op
  invFun := M.presheaf.map (topFromTerminal X).op
  map_add' _ _ := map_add _ _ _
  left_inv x := by
    have h : (terminal.from (⊤ : X.Opens)).op ≫ (topFromTerminal X).op =
        𝟙 (op (⊤_ (Opens X))) := Subsingleton.elim _ _
    change M.presheaf.map (topFromTerminal X).op
      (M.presheaf.map (terminal.from (⊤ : X.Opens)).op x) = x
    rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp, h, M.presheaf.map_id]
    rfl
  right_inv x := by
    have h : (topFromTerminal X).op ≫ (terminal.from (⊤ : X.Opens)).op =
        𝟙 (op (⊤ : X.Opens)) := Subsingleton.elim _ _
    change M.presheaf.map (terminal.from (⊤ : X.Opens)).op
      (M.presheaf.map (topFromTerminal X).op x) = x
    rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp, h, M.presheaf.map_id]
    rfl

end AlgebraicGeometry

end

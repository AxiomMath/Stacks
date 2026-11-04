module

public import Mathlib.Topology.Sheaves.Limits
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByInitial

/-!
# Stacks 00AC — extension by the empty set is not left exact

Let `j : U → X` be the inclusion of an open subset and let `j_! : Sh(U, Type) ⥤ Sh(X, Type)` be
the extension by the initial object of Stacks 00A2 (2), i.e.
`TopCat.Presheaf.extendByInitialSheaf`.

For a point `x ∈ X` outside `U` the stalk `(j_!F)_x` is empty
(`TopCat.Presheaf.isEmpty_stalk_extendByInitialSheafify`, Stacks 00A3 (3)), so already the global
sections of `j_!F` are empty. A final object of `Sh(X, Type)` has a one-point set of sections over
every open, so `j_!F` is never final unless `U = X`. Since a left exact functor preserves the final
object — the limit over the empty diagram — this shows that `j_!` is *not* left exact.

## Main results

* `TopCat.Presheaf.isEmpty_sections_extendByInitialSheafify`: for `U ≠ ⊤` the set of global
  sections of `j_!F` is empty.
* `TopCat.Presheaf.isEmpty_isTerminal_extendByInitialSheaf`: for `U ≠ ⊤` the sheaf `j_!F` is never
  a final object of `Sh(X, Type)`; in particular `j_!` does not send the final object of `Sh(U)`
  to the final object of `Sh(X)`.
* `TopCat.Presheaf.not_preservesFiniteLimits_extendByInitialSheaf`: for `U ≠ ⊤` the functor `j_!`
  does not preserve finite limits, which is what Stacks 00AC means by "not left exact".
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.Presheaf

open ExtensionByInitial

variable {X : TopCat.{u}} (U : Opens X)

/-- An open subset that is not the whole space misses a point. -/
theorem exists_notMem_of_ne_top (hU : U ≠ ⊤) : ∃ x : X, x ∉ U := by
  by_contra h
  simp only [not_exists, not_not] at h
  refine hU (le_antisymm le_top ?_)
  intro x _
  exact h x

/-- **The global sections of `j_!F` are empty when `U ≠ X`.** A point `x ∉ U` has empty stalk
`(j_!F)_x = ∅` by Stacks 00A3 (3), and the germ map sends a global section to an element of that
stalk, so there are no global sections. -/
theorem isEmpty_sections_extendByInitialSheafify (hU : U ≠ ⊤) (F : Presheaf (Type u) (sp U)) :
    IsEmpty (((extendByInitialSheafify U).obj F).presheaf.obj (op ⊤)) := by
  obtain ⟨x, hx⟩ := exists_notMem_of_ne_top U hU
  have hstalk := isEmpty_stalk_extendByInitialSheafify U F hx
  exact Function.isEmpty
    (germ ((extendByInitialSheafify U).obj F).presheaf ⊤ x (Opens.mem_top x))

/-- **Stacks 00AC, first half.** For `U ≠ X` the sheaf `j_!F` is not a final object of
`Sh(X, Type)`, whatever the sheaf `F` on `U` is. In particular `j_!` does not transform a final
object of `Sh(U)` into a final object of `Sh(X)`.

A final object of a category of sheaves of sets has a one-point set of sections over every open,
because `Sheaf.forget` and evaluation at an open both preserve limits; but the global sections of
`j_!F` are empty by `isEmpty_sections_extendByInitialSheafify`. -/
@[stacks 00AC "j_! does not transform a final object of Sh(U) into a final object of Sh(X)"]
theorem isEmpty_isTerminal_extendByInitialSheaf (hU : U ≠ ⊤)
    (F : TopCat.Sheaf (Type u) (sp U)) :
    IsEmpty (IsTerminal ((extendByInitialSheaf U).obj F)) := by
  refine ⟨fun hF => ?_⟩
  have h1 : IsTerminal ((Sheaf.forget (Type u) X).obj ((extendByInitialSheaf U).obj F)) :=
    hF.isTerminalObj (Sheaf.forget (Type u) X) _
  have h2 : IsTerminal (((extendByInitialSheaf U).obj F).presheaf.obj (op ⊤)) :=
    h1.isTerminalObj ((evaluation (Opens X)ᵒᵖ (Type u)).obj (op ⊤)) _
  exact (isEmpty_sections_extendByInitialSheafify U hU F.presheaf).false
    (h2.from PUnit PUnit.unit)

/-- **Stacks 00AC.** For `U ≠ X` the functor `j_! : Sh(U, Type) ⥤ Sh(X, Type)` does not preserve
finite limits, i.e. it is not left exact.

The final object is the limit of the empty diagram, so a functor preserving finite limits would
send the final object of `Sh(U, Type)` to a final object of `Sh(X, Type)`, contradicting
`isEmpty_isTerminal_extendByInitialSheaf`. -/
@[stacks 00AC "j_! is not left exact as a functor between the categories of sheaves of sets"]
theorem not_preservesFiniteLimits_extendByInitialSheaf (hU : U ≠ ⊤) :
    ¬ PreservesFiniteLimits
      (extendByInitialSheaf U : TopCat.Sheaf (Type u) (sp U) ⥤ TopCat.Sheaf (Type u) X) := by
  intro h
  exact (isEmpty_isTerminal_extendByInitialSheaf U hU (⊤_ _)).false
    (terminalIsTerminal.isTerminalObj (extendByInitialSheaf U) _)

end TopCat.Presheaf

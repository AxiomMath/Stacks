module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckAxioms.CountableCoproducts

/-!
# Sequential colimits from countable coproducts and cokernels

In an abelian category the colimit of a sequence `F₀ ⟶ F₁ ⟶ ⋯` is the cokernel of
`1 - shift : ∐ₙ Fₙ ⟶ ∐ₙ Fₙ` (`Stacks.CountableCoproducts.exact_oneSubShift_piMap`, which needs no
exactness of colimits). So a property of objects which is closed under cokernels and under
countable coproducts is closed under colimits of sequences. This is how closure under colimits
over `ℕ` is reduced to the two cases a sections computation over a quasi-compact object can reach:
direct sums, whose sections are the direct sums of the sections (Stacks 0935), and cokernels.

## Main results

* `CategoryTheory.ObjectProperty.prop_colimit_nat_of_isClosedUnderCokernels`: the colimit of a
  sequence of objects satisfying `P` satisfies `P`.
* `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_nat_of_isClosedUnderCokernels`: the
  same for every colimit presentation, for `P` closed under isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

variable {A : Type*} [Category A] [Abelian A] (P : ObjectProperty A)

/-- **A property closed under cokernels and countable coproducts is closed under colimits of
sequences**: `colim Fₙ` is the cokernel of `1 - shift` on `∐ₙ Fₙ`. -/
theorem prop_colimit_nat_of_isClosedUnderCokernels [P.IsClosedUnderCokernels]
    [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] (F : ℕ ⥤ A) [HasCoproduct F.obj]
    [HasColimit F] (hF : ∀ n, P (F.obj n)) : P (colimit F) := by
  have hsum : P (∐ F.obj) := P.prop_colimit _ fun j => hF j.as
  have := Stacks.CountableCoproducts.epi_piMap F
  exact P.prop_of_isColimit_cokernelCofork
    (Stacks.CountableCoproducts.exact_oneSubShift_piMap F).gIsCokernel hsum hsum

/-- **A property closed under isomorphisms, cokernels and countable coproducts is closed under
colimits of sequences.** -/
theorem isClosedUnderColimitsOfShape_nat_of_isClosedUnderCokernels
    [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderCokernels]
    [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] [HasColimitsOfShape (Discrete ℕ) A] :
    P.IsClosedUnderColimitsOfShape ℕ where
  colimitsOfShape_le := by
    rintro X ⟨c⟩
    have : HasColimit c.diag := ⟨⟨⟨_, c.isColimit⟩⟩⟩
    exact P.prop_of_iso (IsColimit.coconePointUniqueUpToIso (colimit.isColimit c.diag)
      c.isColimit) (P.prop_colimit_nat_of_isClosedUnderCokernels c.diag c.prop_diag_obj)

end CategoryTheory.ObjectProperty

module

public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Objects of a slice lying over a base-change-stable class are closed under finite products

Let `W` be a class of morphisms of a category `T` with fibre products which contains the
identities, respects isomorphisms and is stable under composition and base change.  The objects
`Y ⟶ X` of the slice `T/X` lying in `W` are closed under finite products: a binary product in
`T/X` is a fibre product `Y ×_X Z`, whose structure morphism is the base change `Y ×_X Z ⟶ Y` of
`Z ⟶ X` followed by `Y ⟶ X`, and the terminal object is `𝟙 X`.

Unlike the closure under fibre products of
`CategoryTheory.Over.closedUnderLimitsOfShape_pullback`, no cancellation property of `W` is
needed, the fibre products occurring here being taken over the base `X` itself.  This applies to
flat morphisms, which do not have the cancellation property.

## Main results

* `CategoryTheory.MorphismProperty.isClosedUnderFiniteProducts_overObj`: the objects of `T/X`
  lying in `W` are closed under finite products.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

variable {T : Type*} [Category* T] [HasPullbacks T] (W : MorphismProperty T)
  [W.IsStableUnderBaseChange] [W.IsStableUnderComposition] (X : T)

/-- The objects of `T/X` lying in a class stable under composition and base change are closed
under binary products: the structure morphism of `Y ×_X Z` is the base change of that of `Z`
followed by that of `Y`. -/
@[ega "I 3.5.1" "(ii) ⇒ (i), special case",
  ega "I 5.5.12" "special case",
  sga "3 IV 3.4.1" "(a') with Y = Y' = S",
  sga "3 IV 4.6.3" "(a′)"]
instance isClosedUnderBinaryProducts_overObj :
    (W.overObj (X := X)).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro Y ⟨h⟩
    let c : BinaryFan (h.diag.obj ⟨WalkingPair.left⟩) (h.diag.obj ⟨WalkingPair.right⟩) :=
      (Cones.postcompose (diagramIsoPair h.diag).hom).obj ⟨Y, h.π⟩
    have hc : IsLimit c := (IsLimit.postcomposeHomEquiv (diagramIsoPair h.diag) _).symm h.isLimit
    have hw : c.fst.left ≫ (h.diag.obj ⟨WalkingPair.left⟩).hom = Y.hom :=
      CategoryTheory.Over.w c.fst
    change W Y.hom
    rw [← hw]
    exact W.comp_mem _ _
      (W.of_isPullback (Over.isPullback_of_binaryFan_isLimit c hc).flip (h.prop_diag_obj _))
      (h.prop_diag_obj _)

variable [W.ContainsIdentities] [W.RespectsIso]

/-- **The objects of `T/X` lying in a class of morphisms stable under composition and base change,
containing the identities and respecting isomorphisms, are closed under finite products.** -/
@[ega "I 3.5.1" "(ii) ⇒ (i), special case",
  sga "3 IV 3.4.1" "(a') with Y = Y' = S",
  sga "3 IV 4.6.3" "(a′)"]
theorem isClosedUnderFiniteProducts_overObj :
    (W.overObj (X := X)).IsClosedUnderFiniteProducts :=
  have := Over.ConstructProducts.over_binaryProduct_of_pullback (B := X)
  have : HasFiniteProducts (Over X) := hasFiniteProducts_of_has_binary_and_terminal
  have := Over.closedUnderLimitsOfShape_discrete_empty W (X := X)
  .mk'

end CategoryTheory.MorphismProperty

end

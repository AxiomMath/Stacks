module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import Mathlib.CategoryTheory.Shift.Opposite
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
import all StacksFrontier.Homology.PseudoCoherent.BaseChange

/-! # The counit of a total left derived functor commutes with the shift

Let `α : L ⋙ LF ⟶ F` exhibit `LF` as the total left derived functor of `F` along a
localization `L` at a class `W` of morphisms compatible with the shift. Then `LF` commutes
with the shift — this is `StacksDraft.PseudoCoherence.leftDerivedCommShift` — and the
comparison `α` is compatible with those commutation isomorphisms, i.e. it is a
`CategoryTheory.NatTrans.CommShift`.

This is the hypothesis `CategoryTheory.Functor.isTriangulated_of_rightExtension` needs in order
to conclude that a left derived functor is triangulated, so it is required by every construction
of an exact derived functor on an unbounded derived category.

## Main results

* `CategoryTheory.Functor.IsLeftDerivedFunctor.natTrans_commShift`: the comparison of a total
  left derived functor commutes with the shift.

## Implementation notes

Mathlib proves the statement for a *right* derived functor
(`CategoryTheory.Functor.IsRightDerivedFunctor.natTrans_commShift`), and
`StacksDraft.PseudoCoherence.leftDerivedCommShift` obtains the commutation isomorphisms of `LF`
itself by reading the left derived functor in the opposite categories, where it is a right
derived functor. The same dualization is used here, but Mathlib has no "unop" transport for
`NatTrans.CommShift`, so the single component equation is transported by hand: the right derived
counterpart is `CategoryTheory.Functor.IsRightDerivedFunctor.comp_map_commShiftIso_hom_app`,
whose image under `Quiver.Hom.unop` is the required identity.

The naive shift on an opposite category is `CategoryTheory.OppositeShift`, and the functor
`LF` read there is `CategoryTheory.OppositeShift.functor`; `Functor.commShiftUnop` is what
`leftDerivedCommShift` ends with, so the commutation isomorphism of `LF` is by construction
`NatIso.removeOp` of the opposite one, which is why the transported equation is about the
*inverse* isomorphisms.

Two spellings of the same transport have to be identified, and the identification holds only
at default transparency: the unopped right-derived equation is stated over `OppositeShift`,
the goal over `H` and `D`. A `change` therefore fails, and so does a binder ascription; the
working form is a `have` with the target type written out, which is a *term* coercion and so
is checked at default transparency. No `set_option` is needed. The body of
`leftDerivedCommShift` does have to be visible, since the goal mentions the commutation
isomorphism it produces, which is why `BaseChange` is additionally imported with `import all`.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor.IsLeftDerivedFunctor

open CategoryTheory CategoryTheory.Functor

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]
  (LF : H ⥤ D) {F : C ⥤ D} {L : C ⥤ H}
  (α : L ⋙ LF ⟶ F) (W : MorphismProperty C) [L.IsLocalization W]
  [LF.IsLeftDerivedFunctor α W]
  (M : Type*) [AddGroup M] [HasShift C M] [HasShift D M] [HasShift H M]
  [W.IsCompatibleWithShift M] [F.CommShift M] [L.CommShift M]

/-- The comparison `α : L ⋙ LF ⟶ F` of a total left derived functor commutes with the shift,
for the commutation isomorphisms of `StacksDraft.PseudoCoherence.leftDerivedCommShift`. -/
public lemma natTrans_commShift :
    letI := StacksDraft.PseudoCoherence.leftDerivedCommShift LF α W M
    NatTrans.CommShift α M := by
  let Wo : MorphismProperty (OppositeShift C M) := W.op
  let Lo := OppositeShift.functor M L
  let Fo := OppositeShift.functor M F
  let LFo := OppositeShift.functor M LF
  let αo : Fo ⟶ Lo ⋙ LFo := NatTrans.op α
  have : Lo.IsLocalization Wo := inferInstanceAs (L.op.IsLocalization W.op)
  have : Wo.IsCompatibleWithShift M := ⟨fun b => by
    ext X Y f
    exact MorphismProperty.IsCompatibleWithShift.iff W f.unop b⟩
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension LF α W
  have : LFo.IsRightDerivedFunctor αo Wo :=
    ⟨CategoryTheory.Functor.isLeftKanExtension_op LF α⟩
  let : LFo.CommShift M := Functor.IsRightDerivedFunctor.commShift LFo αo Wo M
  let := StacksDraft.PseudoCoherence.leftDerivedCommShift LF α W M
  refine ⟨fun b => ?_⟩
  ext X
  have h := congrArg Quiver.Hom.unop
    (Functor.IsRightDerivedFunctor.comp_map_commShiftIso_hom_app LFo αo Wo M b
      (Opposite.op X))
  replace h : ((LF.commShiftIso b).inv.app (L.obj X) ≫
      LF.map ((L.commShiftIso b).inv.app X)) ≫ α.app (X⟦b⟧) =
    (α.app X)⟦b⟧' ≫ (F.commShiftIso b).inv.app X := h
  dsimp
  rw [Functor.commShiftIso_comp_hom_app, ← cancel_epi (LF.map ((L.commShiftIso b).inv.app X)),
    ← cancel_epi ((LF.commShiftIso b).inv.app (L.obj X))]
  simp only [Category.assoc, ← LF.map_comp_assoc, Iso.inv_hom_id_app,
    LF.map_id, Category.id_comp]
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    Functor.comp_obj, Category.comp_id] using
    (h =≫ (F.commShiftIso b).hom.app X).symm

end CategoryTheory.Functor.IsLeftDerivedFunctor

end

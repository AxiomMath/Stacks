module

public import StacksFrontier.Algebra.Homology.DualComplexOfSignedMateDuals
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# The mate of a morphism is precomposition on the internal hom into the unit

Let `C` be a braided monoidal closed category and let `X` and `Y` carry left duals `X'` and `Y'`.
`CategoryTheory.rightDualIsoIhomUnit` identifies `X'` with `Hom(X, 𝟙)` and `Y'` with
`Hom(Y, 𝟙)`.  This file proves that under those identifications the **mate** `f^∨ : Y' ⟶ X'` of
`f : X ⟶ Y` is Mathlib's **precomposition** `MonoidalClosed.pre f` evaluated at the unit:

`CategoryTheory.ExactPairing.mate qX qY f = (MonoidalClosed.pre f).app (𝟙_ C)`.

Nothing in Mathlib relates `rightAdjointMate` to `MonoidalClosed.pre`: the mate is defined by
string diagrams out of the (co)evaluations and `pre` by conjugating the tensor-hom adjunctions,
and the two are never compared.  The comparison is what identifies the differential of the dual
complex of [Stacks, Tag 0FP9] — which is a signed `pre` by
`CochainComplex.internalHomComplex_d_π` — with the signed mate of
`CochainComplex.IsSignedMateDual`.

## Main results

* `CategoryTheory.ExactPairing.eq_of_whiskerRight_comp_evaluation`: a morphism into a right dual
  is determined by its contraction with the evaluation, and hence
  `CategoryTheory.ExactPairing.eq_mate`: anything satisfying the mate identity *is* the mate.
  Mathlib proves the identity for `rightAdjointMate` but never its characterising uniqueness.
* `CategoryTheory.ExactPairing.rightDualIsoIhomUnit_hom_whiskerRight_comp_ihomUnitEvaluation`:
  the canonical isomorphism of a left dual with `Hom(X, 𝟙)` carries the evaluation of the pairing
  to the internal-hom evaluation read through the braiding.
* `CategoryTheory.ExactPairing.mate_eq_pre_app`: **the mate is `pre`.**
* `CategoryTheory.ExactPairing.mate_exactPairingCongrRight`: how the mate moves under transport
  of the pairings along isomorphisms of the duals, which is what lets the previous result be
  read at a dual presented in any other spelling.

## Implementation notes

**Why uniqueness, and not a direct computation.**  `rightDualIsoIhomUnit` is built from
`Adjunction.rightAdjointUniq`, whose component at an object is a composite of units, counits and
a hom-set bijection; computing the mate through it directly means unfolding
`Adjunction.mkOfHomEquiv`.  Instead the mate is pinned down by the identity
`f^∨ ▷ X ≫ ε_X = Y' ◁ f ≫ ε_Y`, which determines it because `- ⊗ X ⊣ - ⊗ X'` makes
`u ↦ u ▷ X ≫ ε_X` injective (`Mathlib`'s
`tensorRightHomEquiv_whiskerRight_comp_evaluation`); only the *evaluation* of the transported
pairing then has to be computed, and for that one application of
`Adjunction.rightAdjointUniq_hom_app_counit` suffices.

**The braiding.**  `MonoidalClosed.ihom.ev X` is the counit of `X ⊗ - ⊣ Hom(X, -)`, so it has
source `X ⊗ Hom(X, 𝟙)`, while the evaluation of an exact pairing has source `X' ⊗ X`.  The
braiding mediates, and that is the only place braidedness is used — the same place
`CategoryTheory.tensorRightIhomAdjunction` uses it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category MonoidalCategory MonoidalClosed

namespace CategoryTheory.ExactPairing

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Uniqueness of a morphism into a right dual, given its contraction with the evaluation. -/
lemma eq_of_whiskerRight_comp_evaluation {X X' Z : C} (pX : ExactPairing X X') (u v : Z ⟶ X')
    (h : u ▷ X ≫ pX.evaluation' = v ▷ X ≫ pX.evaluation') : u = v := by
  let := hasRightDual pX
  have h' : u ▷ X ≫ ε_ X (Xᘁ) = v ▷ X ≫ ε_ X (Xᘁ) := h
  have hu := tensorRightHomEquiv_whiskerRight_comp_evaluation (X := X) (Y := Z) u
  have hv := tensorRightHomEquiv_whiskerRight_comp_evaluation (X := X) (Y := Z) v
  rw [h', hv] at hu
  exact (cancel_mono (λ_ X').inv).1 hu.symm

/-- **Anything satisfying the mate identity is the mate.**  Mathlib proves
`rightAdjointMate_comp_evaluation` but not that it characterises the mate. -/
lemma eq_mate {X Y X' Y' : C} (pX : ExactPairing X X') (pY : ExactPairing Y Y') (f : X ⟶ Y)
    (g : Y' ⟶ X') (h : g ▷ X ≫ pX.evaluation' = Y' ◁ f ≫ pY.evaluation') :
    g = mate pX pY f :=
  eq_of_whiskerRight_comp_evaluation pX g (mate pX pY f)
    (h.trans (mate_comp_evaluation pX pY f).symm)

/-- The mate for pairings transported along isomorphisms of the duals. -/
lemma mate_exactPairingCongrRight {X Y X' Y' X'' Y'' : C} (pX : ExactPairing X X')
    (pY : ExactPairing Y Y') (iX : X'' ≅ X') (iY : Y'' ≅ Y') (f : X ⟶ Y) :
    mate (@exactPairingCongrRight C _ _ X X'' X' pX iX)
        (@exactPairingCongrRight C _ _ Y Y'' Y' pY iY) f =
      iY.hom ≫ mate pX pY f ≫ iX.inv := by
  refine (eq_mate _ _ f _ ?_).symm
  change (iY.hom ≫ mate pX pY f ≫ iX.inv) ▷ X ≫ iX.hom ▷ X ≫ pX.evaluation' =
    Y'' ◁ f ≫ iY.hom ▷ Y ≫ pY.evaluation'
  rw [← MonoidalCategory.comp_whiskerRight_assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, MonoidalCategory.comp_whiskerRight_assoc,
    mate_comp_evaluation, MonoidalCategory.whisker_exchange_assoc]

section Closed

variable [BraidedCategory C] [MonoidalClosed C]

/-- The evaluation carried by the internal hom into the unit. -/
noncomputable def ihomUnitEvaluation (X : C) : (ihom X).obj (𝟙_ C) ⊗ X ⟶ 𝟙_ C :=
  (β_ X ((ihom X).obj (𝟙_ C))).inv ≫ (ihom.ev X).app (𝟙_ C)

/-- The counit of `- ⊗ X ⊣ Hom(X, -)` at the unit is the evaluation above, by definition. -/
lemma counit_tensorRightIhomAdjunction (X : C) :
    (tensorRightIhomAdjunction X).counit.app (𝟙_ C) = ihomUnitEvaluation X := rfl

omit [BraidedCategory C] [MonoidalClosed C] in
/-- The counit of the adjunction an exact pairing carries, unfolded. -/
lemma tensorRightAdjunction_counit_app (X Y Z : C) [ExactPairing X Y] :
    (tensorRightAdjunction X Y).counit.app Z =
      𝟙 (Z ⊗ Y) ▷ X ≫ (α_ Z Y X).hom ≫ Z ◁ ε_ X Y ≫ (ρ_ Z).hom := rfl

omit [BraidedCategory C] [MonoidalClosed C] in
/-- At the unit that counit is the evaluation of the pairing, up to the left unitor. -/
lemma counit_tensorRightAdjunction (X Y : C) [ExactPairing X Y] :
    (λ_ Y).inv ▷ X ≫ (tensorRightAdjunction X Y).counit.app (𝟙_ C) = ε_ X Y := by
  rw [tensorRightAdjunction_counit_app]
  monoidal

/-- **The canonical identification of a left dual with the internal hom into the unit carries the
evaluation to the internal-hom evaluation.**  This is the one computation through
`Adjunction.rightAdjointUniq` that the identification of the mate with `pre` needs. -/
lemma rightDualIsoIhomUnit_hom_whiskerRight_comp_ihomUnitEvaluation (X Y : C)
    [ExactPairing X Y] :
    (rightDualIsoIhomUnit X Y).hom ▷ X ≫ ihomUnitEvaluation X = ε_ X Y := by
  have key := Adjunction.rightAdjointUniq_hom_app_counit (tensorRightAdjunction X Y)
    (tensorRightIhomAdjunction X) (𝟙_ C)
  rw [← counit_tensorRightAdjunction X Y, ← key, ← counit_tensorRightIhomAdjunction]
  change ((λ_ Y).inv ≫ _) ▷ X ≫ _ = _
  rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rfl

/-- Hence the pairing of `X` with `Hom(X, 𝟙)` transported from any left dual has
`CategoryTheory.ExactPairing.ihomUnitEvaluation` for its evaluation — independently of which
dual it was transported from. -/
lemma evaluation_exactPairingRightDualIhomUnit (X Y : C) [ExactPairing X Y] :
    (exactPairingCongrRight (rightDualIsoIhomUnit X Y).symm :
        ExactPairing X ((ihom X).obj (𝟙_ C))).evaluation' = ihomUnitEvaluation X := by
  change (rightDualIsoIhomUnit X Y).inv ▷ X ≫ ε_ X Y = _
  rw [← rightDualIsoIhomUnit_hom_whiskerRight_comp_ihomUnitEvaluation X Y,
    ← MonoidalCategory.comp_whiskerRight_assoc, Iso.inv_hom_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp]

/-- **The mate is precomposition.**  For duals realised as internal homs into the unit, with the
evaluation the internal-hom evaluation read through the braiding, the mate of `f : X ⟶ Y` is
`(pre f).app (𝟙_ C)`. -/
lemma mate_eq_pre_app {X Y : C} (qX : ExactPairing X ((ihom X).obj (𝟙_ C)))
    (qY : ExactPairing Y ((ihom Y).obj (𝟙_ C))) (hX : qX.evaluation' = ihomUnitEvaluation X)
    (hY : qY.evaluation' = ihomUnitEvaluation Y) (f : X ⟶ Y) :
    mate qX qY f = (pre f).app (𝟙_ C) := by
  refine (eq_mate qX qY f _ ?_).symm
  rw [hX, hY, ihomUnitEvaluation, ihomUnitEvaluation,
    BraidedCategory.braiding_inv_naturality_left_assoc, id_tensor_pre_app_comp_ev,
    BraidedCategory.braiding_inv_naturality_right_assoc]

end Closed

end CategoryTheory.ExactPairing

end

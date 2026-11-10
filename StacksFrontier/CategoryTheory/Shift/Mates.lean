module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Mates of shift-compatible squares are shift-compatible

Let

```
      L₁                  R₁
   C --→ D             C ←-- D
 G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
   E --→ F             E ←-- F
      L₂                  R₂
```

be a square of functors whose horizontal sides are adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂`, all six
functors commuting with a shift by `A`, and let the two adjunctions be compatible with that shift
(`CategoryTheory.Adjunction.CommShift`). Then the mates correspondence
`CategoryTheory.mateEquiv` carries shift-compatible transformations to shift-compatible
transformations, in both directions.

This is immediate once the mate is unfolded: `CategoryTheory.mateEquiv` is a composite of
associators, unitors, whiskerings and the unit and the counit of the two adjunctions, and each of
those has `CategoryTheory.NatTrans.CommShift`. What makes a separate statement worth having is
that instance search cannot do the unfolding — the mate is an application of a function given by
an `Equiv` literal, and no amount of instance-reducible unfolding gets to the composite. Stating
it for abstract functors also keeps the search small: applied directly to a concrete square built
out of derived functors, the same search runs over nine factors whose endpoints are large
composites and does not terminate.

## Main results

* `CategoryTheory.NatTrans.commShift_mateEquiv_symm`: the mate `G ⋙ L₂ ⟶ L₁ ⋙ H` of a
  shift-compatible `R₁ ⋙ G ⟶ H ⋙ R₂`.
* `CategoryTheory.NatTrans.commShift_mateEquiv`: the mate `R₁ ⋙ G ⟶ H ⋙ R₂` of a
  shift-compatible `G ⋙ L₂ ⟶ L₁ ⋙ H`.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Category CategoryTheory.Functor Adjunction

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type*} [AddMonoid A]
  {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  [HasShift C A] [HasShift D A] [HasShift E A] [HasShift F A]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  [G.CommShift A] [H.CommShift A] [L₁.CommShift A] [R₁.CommShift A]
  [L₂.CommShift A] [R₂.CommShift A]
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.CommShift A] [adj₂.CommShift A]

namespace NatTrans

/-- **A shift-compatible transformation stays shift-compatible when its target is read as a
composite with the identity.** The two `CategoryTheory.Functor.CommShift` structures on `X` and
on `𝟭 ⋙ X` are equal, but not as terms, so a `NatTrans.CommShift` instance for the one spelling
is not found for the other; this is the bridge. It is needed because a 2-square whose right-hand
side is the identity functor has its target spelled `𝟭 ⋙ R₂` inside
`CategoryTheory.TwoSquare`, while the transformation handed to it is stated with target `R₂`. -/
instance commShift_id_comp_target {X Y : C ⥤ D} [X.CommShift A] [Y.CommShift A] (τ : X ⟶ Y)
    [NatTrans.CommShift τ A] :
    NatTrans.CommShift (show X ⟶ 𝟭 C ⋙ Y from τ) A := by
  apply NatTrans.CommShift.of_core
  intro a
  constructor
  ext Z
  simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.shift_app_comm τ a Z

/-- **The mate of a shift-compatible 2-square is shift-compatible.** The mate is
`adj₁.unit`, then the given square whiskered with `L₁` and `L₂`, then `adj₂.counit`, with
associators and unitors in between; `CategoryTheory.Adjunction.CommShift` supplies the
compatibility of the unit and of the counit, and the rest have it unconditionally.

The square is taken as a bare natural transformation rather than as a term of type
`CategoryTheory.TwoSquare`: `TwoSquare` is an ordinary definition, so a hypothesis
`NatTrans.CommShift β A` on a `β : TwoSquare R₁ H G R₂` is not matched by instance search
against the whiskering of `β` that occurs in the mate. -/
instance commShift_mateEquiv_symm (β : R₁ ⋙ G ⟶ H ⋙ R₂) [NatTrans.CommShift β A] :
    NatTrans.CommShift
      ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ β)) A := by
  rw [mateEquiv_symm_apply]
  dsimp only [TwoSquare.mk]
  infer_instance

/-- **The mate in the other direction of a shift-compatible 2-square is shift-compatible.** -/
instance commShift_mateEquiv (α : G ⋙ L₂ ⟶ L₁ ⋙ H) [NatTrans.CommShift α A] :
    NatTrans.CommShift (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)) A := by
  rw [mateEquiv_apply]
  dsimp only [TwoSquare.mk]
  infer_instance

end NatTrans

end CategoryTheory

end

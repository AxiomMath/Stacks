module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.RestrictionExact.MateFree

/-!
# Units and counits across a square of four adjunctions

Four adjunctions `Lᵢ ⊣ Rᵢ` arranged in a square, with an isomorphism `e : R₁ ⋙ R₂ ≅ R₃ ⋙ R₄`
between the two composite right adjoints, give an isomorphism `L₂ ⋙ L₁ ≅ L₄ ⋙ L₃` between the two
composite left adjoints: that is
`Stacks.CategoryTheory.leftAdjointsCommOfRightAdjointsComm`.  This file supplies the piece that
makes such a square usable on units and counits, namely the comparison
`R₄ ⋙ L₂ ⟶ L₃ ⋙ R₁` in the *mixed* direction and the two identities relating it to the units and
counits of the four adjunctions.

## Main definitions

* `Stacks.CategoryTheory.beckChevalley`: the Beck--Chevalley comparison
  `R₄ ⋙ L₂ ⟶ L₃ ⋙ R₁`, the mate of `e.inv` taken along the two *vertical* adjunctions
  `adj₂` and `adj₃`.
* `Stacks.CategoryTheory.leftMate`: the comparison `L₂ ⋙ L₁ ⟶ L₄ ⋙ L₃`, the mate of the former
  along the two *horizontal* adjunctions `adj₄` and `adj₁`.

## Main results

* `Stacks.CategoryTheory.beckChevalley_app`: the component of the Beck--Chevalley comparison as
  the explicit three-fold composite `unit of adj₃`, `e.inv`, `counit of adj₂`.
* `Stacks.CategoryTheory.isIso_leftMate`: **the left comparison is invertible**, with no
  Beck--Chevalley condition assumed.  The iterated mate of a square all four of whose functors are
  left adjoints is the conjugate of that square, and the conjugate of an isomorphism is an
  isomorphism.
* `Stacks.CategoryTheory.leftMate_app_eq`: **the left comparison is
  `Stacks.CategoryTheory.leftAdjointsCommOfRightAdjointsComm`.**  So the latter, which is
  constructed through `CategoryTheory.Adjunction.leftAdjointUniq` and therefore has no direct component
  formula, acquires the two identities below.
* `Stacks.CategoryTheory.map_unit_comp_beckChevalley` and
  `Stacks.CategoryTheory.map_beckChevalley_comp_counit`: the unit and the counit of `adj₄`,
  transported by `L₂` resp. `L₃`, agree with the unit resp. counit of `adj₁` up to the two
  comparisons.
* `Stacks.CategoryTheory.isIso_map_unit_iff` and
  `Stacks.CategoryTheory.isIso_map_counit_iff`: **invertibility transfers**, in both directions,
  as soon as the Beck--Chevalley comparison is invertible at the object in question.  This is the
  only remaining hypothesis: everything else here is unconditional.

## Route

Mathlib's `CategoryTheory.mateEquiv` is the bijection
`(G ⋙ L' ⟶ L ⋙ H) ≃ (R ⋙ G ⟶ H ⋙ R')` for two adjunctions `L ⊣ R`, `L' ⊣ R'`, and
`CategoryTheory.unit_mateEquiv_symm` and `CategoryTheory.mateEquiv_counit_symm` are exactly the
two identities wanted, once the right instantiation is found.  Writing the square so that the two
restrictions are the *vertical* functors and the two direct images the *horizontal* ones, the
comparison needed is the mate of `e.inv` along the verticals, and its own mate along the
horizontals is the left comparison.

Invertibility of that second mate is `CategoryTheory.iterated_mateEquiv_conjugateEquiv_symm`: the
iterated mate of a square of left adjoints is the `CategoryTheory.conjugateEquiv` of the square,
and `CategoryTheory.conjugateEquiv_symm_iso` makes the conjugate of an isomorphism invertible.
That is why no Beck--Chevalley condition enters on the left.

The identification with `leftAdjointsCommOfRightAdjointsComm` is by uniqueness: both are
morphisms out of the left adjoint `L₂ ⋙ L₁`, so
`CategoryTheory.Adjunction.homEquiv` is injective on them, and
`CategoryTheory.unit_conjugateEquiv_symm` and
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` compute both images.  The two differ by
conjugating a map by `e`, which is naturality of `e.hom`.

## What is not done

**Nothing here is about [Stacks, Tag 01SB] and no `stacks` attribute is attached**; this is pure
category theory.  What it does *not* supply is invertibility of
`Stacks.CategoryTheory.beckChevalley` itself, which is a genuine Beck--Chevalley condition and
false for a general square.  For the square that Tag 01SB needs it is proved in
`StacksFrontier/AlgebraicGeometry/QcohRestrictEquiv/PushforwardRestrict.lean`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Stacks.CategoryTheory

variable {A : Type u₁} {B : Type u₂} {B' : Type u₃} {E : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} B'] [Category.{v₄} E]
  {L₁ : B ⥤ A} {R₁ : A ⥤ B} {L₂ : E ⥤ B} {R₂ : B ⥤ E}
  {L₃ : B' ⥤ A} {R₃ : A ⥤ B'} {L₄ : E ⥤ B'} {R₄ : B' ⥤ E}

/-- The Beck--Chevalley comparison `R₄ ⋙ L₂ ⟶ L₃ ⋙ R₁` attached to a commuting square of right
adjoints: the mate of `e.inv` along the two vertical adjunctions. -/
def beckChevalley (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (e : R₁ ⋙ R₂ ≅ R₃ ⋙ R₄) :
    TwoSquare R₄ L₃ L₂ R₁ :=
  (mateEquiv adj₃ adj₂).symm (TwoSquare.mk _ _ _ _ e.inv)

/-- The comparison `L₂ ⋙ L₁ ⟶ L₄ ⋙ L₃` of the two composite left adjoints: the mate of
`Stacks.CategoryTheory.beckChevalley` along the two horizontal adjunctions. -/
def leftMate (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (e : R₁ ⋙ R₂ ≅ R₃ ⋙ R₄) : TwoSquare L₂ L₄ L₁ L₃ :=
  (mateEquiv adj₄ adj₁).symm (beckChevalley adj₂ adj₃ e)

/-- The component of the Beck--Chevalley comparison: the unit of `adj₃`, then `e.inv`, then the
counit of `adj₂`. -/
theorem beckChevalley_app (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (e : R₁ ⋙ R₂ ≅ R₃ ⋙ R₄) (M : B') :
    (beckChevalley adj₂ adj₃ e).app M =
      L₂.map (R₄.map (adj₃.unit.app M)) ≫ L₂.map (e.inv.app (L₃.obj M)) ≫
        adj₂.counit.app (R₁.obj (L₃.obj M)) := by
  simp [beckChevalley, mateEquiv]

/-- The left comparison is the `CategoryTheory.conjugateEquiv` of `e.inv` for the two composite
adjunctions. -/
theorem leftMate_eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (e : R₁ ⋙ R₂ ≅ R₃ ⋙ R₄) :
    (leftMate adj₁ adj₂ adj₃ adj₄ e).natTrans =
      (conjugateEquiv (adj₄.comp adj₃) (adj₂.comp adj₁)).symm e.inv :=
  congrArg TwoSquare.natTrans
    (iterated_mateEquiv_conjugateEquiv_symm adj₄ adj₁ adj₂ adj₃ (TwoSquare.mk _ _ _ _ e.inv))

/-- **The comparison of the two composite left adjoints is invertible**, with no Beck--Chevalley
condition: it is the conjugate of the isomorphism `e.inv`. -/
instance isIso_leftMate (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (e : R₁ ⋙ R₂ ≅ R₃ ⋙ R₄) : IsIso (leftMate adj₁ adj₂ adj₃ adj₄ e).natTrans := by
  rw [leftMate_eq]
  infer_instance

/-- **The left comparison is `Stacks.CategoryTheory.leftAdjointsCommOfRightAdjointsComm`.**  Both
are morphisms out of the left adjoint `L₂ ⋙ L₁`, and `CategoryTheory.Adjunction.homEquiv` sends
them to the same morphism. -/
theorem leftMate_app_eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (e : R₁ ⋙ R₂ ≅ R₃ ⋙ R₄) :
    (leftMate adj₁ adj₂ adj₃ adj₄ e).natTrans =
      (leftAdjointsCommOfRightAdjointsComm adj₁ adj₂ adj₃ adj₄ e).hom := by
  have hnat : ∀ {Y Z : A} (φ : Y ⟶ Z),
      e.hom.app Y ≫ R₄.map (R₃.map φ) ≫ e.inv.app Z = R₂.map (R₁.map φ) := by
    intro Y Z φ
    have h := e.hom.naturality φ
    simp only [Functor.comp_map] at h
    rw [← Category.assoc, ← h, Category.assoc, e.hom_inv_id_app, Category.comp_id]
  rw [leftMate_eq]
  refine NatTrans.ext (funext fun G => ((adj₂.comp adj₁).homEquiv _ _).injective ?_)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    ← unit_conjugateEquiv_symm (adj₄.comp adj₃) (adj₂.comp adj₁) e.inv G,
    ← Adjunction.unit_leftAdjointUniq_hom_app
      ((adj₂.comp adj₁).ofNatIsoRight e) (adj₄.comp adj₃) G]
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app, Functor.comp_map,
    Functor.whiskerLeft_app, NatTrans.comp_app, Category.assoc]
  rw [hnat]
  rfl

/-- **The unit of `adj₄`, restricted by `L₂`, is the unit of `adj₁` up to the two comparisons.** -/
theorem map_unit_comp_beckChevalley (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (adj₄ : L₄ ⊣ R₄) (e : R₁ ⋙ R₂ ≅ R₃ ⋙ R₄) (G : E) :
    L₂.map (adj₄.unit.app G) ≫ (beckChevalley adj₂ adj₃ e).app (L₄.obj G) =
      adj₁.unit.app (L₂.obj G) ≫ R₁.map ((leftMate adj₁ adj₂ adj₃ adj₄ e).app G) :=
  unit_mateEquiv_symm adj₄ adj₁ (beckChevalley adj₂ adj₃ e) G

/-- **The counit of `adj₄`, restricted by `L₃`, is the counit of `adj₁` up to the two
comparisons.** -/
theorem map_beckChevalley_comp_counit (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (adj₄ : L₄ ⊣ R₄) (e : R₁ ⋙ R₂ ≅ R₃ ⋙ R₄) (M : B') :
    L₁.map ((beckChevalley adj₂ adj₃ e).app M) ≫ adj₁.counit.app (L₃.obj M) =
      (leftMate adj₁ adj₂ adj₃ adj₄ e).app (R₄.obj M) ≫ L₃.map (adj₄.counit.app M) :=
  mateEquiv_counit_symm adj₄ adj₁ (beckChevalley adj₂ adj₃ e) M

/-- **Invertibility of the unit transfers across the square**, in both directions, as soon as the
Beck--Chevalley comparison is invertible at the object concerned. -/
theorem isIso_map_unit_iff (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (adj₄ : L₄ ⊣ R₄) (e : R₁ ⋙ R₂ ≅ R₃ ⋙ R₄) (G : E)
    (hbc : IsIso ((beckChevalley adj₂ adj₃ e).app (L₄.obj G))) :
    IsIso (L₂.map (adj₄.unit.app G)) ↔ IsIso (adj₁.unit.app (L₂.obj G)) := by
  have : IsIso ((leftMate adj₁ adj₂ adj₃ adj₄ e).app G) :=
    inferInstanceAs (IsIso ((leftMate adj₁ adj₂ adj₃ adj₄ e).natTrans.app G))
  rw [← isIso_comp_right_iff (L₂.map (adj₄.unit.app G)) ((beckChevalley adj₂ adj₃ e).app _),
    map_unit_comp_beckChevalley adj₁ adj₂ adj₃ adj₄ e G, isIso_comp_right_iff]

/-- **Invertibility of the counit transfers across the square**, in both directions, as soon as
the Beck--Chevalley comparison is invertible at the object concerned. -/
theorem isIso_map_counit_iff (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (adj₄ : L₄ ⊣ R₄) (e : R₁ ⋙ R₂ ≅ R₃ ⋙ R₄) (M : B')
    (hbc : IsIso ((beckChevalley adj₂ adj₃ e).app M)) :
    IsIso (L₃.map (adj₄.counit.app M)) ↔ IsIso (adj₁.counit.app (L₃.obj M)) := by
  have : IsIso ((leftMate adj₁ adj₂ adj₃ adj₄ e).app (R₄.obj M)) :=
    inferInstanceAs (IsIso ((leftMate adj₁ adj₂ adj₃ adj₄ e).natTrans.app (R₄.obj M)))
  rw [← isIso_comp_left_iff ((leftMate adj₁ adj₂ adj₃ adj₄ e).app (R₄.obj M))
      (L₃.map (adj₄.counit.app M)),
    ← map_beckChevalley_comp_counit adj₁ adj₂ adj₃ adj₄ e M, isIso_comp_left_iff]

end Stacks.CategoryTheory

end

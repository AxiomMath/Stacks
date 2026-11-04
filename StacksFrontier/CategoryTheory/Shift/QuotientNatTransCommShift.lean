module

public import Mathlib.CategoryTheory.Shift.Quotient

/-! # Detecting the commutation with the shift of a transformation of functors out of a quotient

Let `r` be a relation on the morphisms of a category `C` compatible with a shift by an additive
group `M`, and let `τ : G₁ ⟶ G₂` be a transformation of functors out of the quotient category,
both commuting with the shift. Then `τ` commutes with the shift as soon as its restriction
`Quotient.functor r ⋙ G₁ ⟶ Quotient.functor r ⋙ G₂` does: the two conditions differ by the
commutation isomorphism of the quotient functor, which is invertible.

## Main results

* `CategoryTheory.NatTrans.commShift_of_whiskerLeft_quotientFunctor`
-/

@[expose] public section

namespace CategoryTheory.NatTrans

open CategoryTheory Category

universe v v' u u' w

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {r : HomRel C}
  (M : Type w) [AddMonoid M] [HasShift C M] [HasShift D M] [r.IsCompatibleWithShift M]
  {G₁ G₂ : Quotient r ⥤ D} [G₁.CommShift M] [G₂.CommShift M] (τ : G₁ ⟶ G₂)

/-- **A transformation of functors out of a quotient category commutes with the shift as soon as
its restriction along the quotient functor does.** -/
theorem commShift_of_whiskerLeft_quotientFunctor
    [NatTrans.CommShift (Functor.whiskerLeft (Quotient.functor r) τ) M] :
    NatTrans.CommShift τ M := by
  refine ⟨fun a => Quotient.natTrans_ext _ _ (NatTrans.ext (funext fun X => ?_))⟩
  have key := NatTrans.shift_app_comm (Functor.whiskerLeft (Quotient.functor r) τ) a X
  have hnat : G₁.map (((Quotient.functor r).commShiftIso a).hom.app X) ≫
        τ.app ((shiftFunctor (Quotient r) a).obj ((Quotient.functor r).obj X)) =
      τ.app ((Quotient.functor r).obj ((shiftFunctor C a).obj X)) ≫
        G₂.map (((Quotient.functor r).commShiftIso a).hom.app X) :=
    τ.naturality (((Quotient.functor r).commShiftIso a).hom.app X)
  have hnat2 := hnat =≫ (G₂.commShiftIso a).hom.app ((Quotient.functor r).obj X)
  simp only [assoc] at hnat2
  dsimp at key ⊢
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app,
    ← hnat2] at key
  rw [assoc] at key
  exact (cancel_epi (G₁.map (((Quotient.functor r).commShiftIso a).hom.app X))).1 key

end CategoryTheory.NatTrans

end

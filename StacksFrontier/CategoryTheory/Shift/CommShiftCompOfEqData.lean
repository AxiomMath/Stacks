module

public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Composing shift-compatible transformations across two equal commutation data

`CategoryTheory.NatTrans.CommShift τ M` receives the `CategoryTheory.Functor.CommShift`
structures of the source and target of `τ` as instance arguments.  At a junction of a chain of
transformations the datum delivered by the left-hand factor and the datum demanded by the
right-hand one can be the same structure spelled two ways; the lemma here composes across such a
junction, the equality being discharged once.

## Main results

* `CategoryTheory.NatTrans.commShift_comp_of_eq_data`.
-/

@[expose] public section

namespace CategoryTheory

namespace NatTrans

/-- **Two shift-compatible transformations compose even when the middle functor is presented with
two different, but equal, commutation data.**  At a junction of a chain, the datum delivered by
the left-hand factor and the datum demanded by the right-hand one are the same structure spelled
two ways, and the equality is discharged once here by `rfl` rather than being asked of instance
search. -/
theorem commShift_comp_of_eq_data {C D : Type*} [Category* C] [Category* D]
    {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M] {F₁ F₂ F₃ : C ⥤ D}
    {dF₁ : F₁.CommShift M} {d d' : F₂.CommShift M} {dF₃ : F₃.CommShift M}
    (τ : F₁ ⟶ F₂) (σ : F₂ ⟶ F₃)
    (hτ : @NatTrans.CommShift _ _ _ _ F₁ F₂ τ M _ _ _ dF₁ d)
    (hσ : @NatTrans.CommShift _ _ _ _ F₂ F₃ σ M _ _ _ d' dF₃)
    (hd : d = d' := by rfl) :
    @NatTrans.CommShift _ _ _ _ F₁ F₃ (τ ≫ σ) M _ _ _ dF₁ dF₃ := by
  subst hd
  let := dF₁
  let := d
  let := dF₃
  have := hτ
  have := hσ
  infer_instance

end NatTrans

end CategoryTheory

module

public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# A subfunctor whose inclusion factors through another

If the inclusion of a subfunctor `W` of `F` factors through the inclusion of a second subfunctor
`Z`, then `W ≤ Z`.

## Main results

* `CategoryTheory.Subfunctor.le_of_comp_eq_ι`: a subfunctor whose inclusion factors through the
  inclusion of a second subfunctor is contained in it.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- A subfunctor whose inclusion factors through a second subfunctor is contained in it. -/
public theorem Subfunctor.le_of_comp_eq_ι {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type*}
    {W Z : Subfunctor F} (g : W.toFunctor ⟶ Z.toFunctor) (hg : g ≫ Z.ι = W.ι) : W ≤ Z := by
  intro U x hx
  have h : ((g.app U ⟨x, hx⟩ : Z.toFunctor.obj U) : F.obj U) = x :=
    congrArg (fun k : W.toFunctor ⟶ F ↦ k.app U ⟨x, hx⟩) hg
  exact h ▸ (g.app U ⟨x, hx⟩).2

end CategoryTheory

end

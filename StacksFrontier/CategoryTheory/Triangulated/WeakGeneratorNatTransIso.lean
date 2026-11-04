module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Algebra.DifferentialGraded.Module.WeakGeneratorIsoCriterion

/-!
# A transformation of left adjoints is detected on a weak generator

Let `D` be a pretriangulated category with a weak triangulated generator `G`, and let
`Ψ : P ⟶ Q` be a natural transformation between two functors `D ⥤ E` which both have right
adjoints. If `Ψ` is invertible at every translate of an object of `G`, then `Ψ` is invertible.

No compatibility of `Ψ` with the translation, and no exactness of `P` or `Q`, is needed.

## Main results

* `CategoryTheory.ObjectProperty.IsWeakTriangulatedGenerator.isIso_of_isIso_app_of_adjunction`:
  a natural transformation between functors with right adjoints is an isomorphism if its
  components at the translates of a weak triangulated generator are isomorphisms.
-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {E : Type*} [Category* E]

/-- If `G` is a weak triangulated generator of `D` and `P Q : D ⥤ E` have right adjoints, then a
natural transformation `Ψ : P ⟶ Q` whose component at every translate of an object of `G` is an
isomorphism is itself an isomorphism. -/
theorem ObjectProperty.IsWeakTriangulatedGenerator.isIso_of_isIso_app_of_adjunction
    {G : ObjectProperty D} (hG : G.IsWeakTriangulatedGenerator)
    {P Q : D ⥤ E} {P' Q' : E ⥤ D} (adjP : P ⊣ P') (adjQ : Q ⊣ Q') (Ψ : P ⟶ Q)
    (hΨ : ∀ ⦃X : D⦄, (G.shiftClosure ℤ) X → IsIso (Ψ.app X)) :
    IsIso Ψ := by
  let Ψ' := conjugateEquiv adjQ adjP Ψ
  suffices h : ∀ Y : E, IsIso (Ψ'.app Y) by
    have := h
    have : IsIso Ψ' := NatIso.isIso_of_isIso_app Ψ'
    exact conjugateEquiv_of_iso adjQ adjP Ψ
  intro Y
  refine hG.isIso_of_bijective_comp_shiftClosure (Ψ'.app Y) fun X hX => ?_
  have := hΨ hX
  have key : (fun f : X ⟶ Q'.obj Y => f ≫ Ψ'.app Y) =
      (adjP.homEquiv X Y) ∘ (fun g : Q.obj X ⟶ Y => Ψ.app X ≫ g) ∘ (adjQ.homEquiv X Y).symm := by
    funext f
    apply (adjP.homEquiv X Y).symm.injective
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      conjugateEquiv_counit, ← Category.assoc, Ψ.naturality, Category.assoc]
  rw [key]
  refine (adjP.homEquiv X Y).bijective.comp ((?_ : Function.Bijective _).comp
    (adjQ.homEquiv X Y).symm.bijective)
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun g => inv (Ψ.app X) ≫ g, fun g => ?_, fun g => ?_⟩
  · simp
  · simp

end CategoryTheory

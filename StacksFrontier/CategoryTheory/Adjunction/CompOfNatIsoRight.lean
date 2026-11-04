module

public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality

/-!
# Composing two adjunctions whose right adjoints have been transported

Let `a₁ : L₁ ⊣ P₁` and `a₂ : L₂ ⊣ P₂` be composable adjunctions and let `i₁ : P₁ ≅ Q₁` and
`i₂ : P₂ ≅ Q₂` be isomorphisms of their right adjoints.  There are two ways to obtain an
adjunction `L₁ ⋙ L₂ ⊣ Q₂ ⋙ Q₁`: transport each factor along its isomorphism and compose, or
compose first and transport the composite right adjoint along the horizontal composite of the two
isomorphisms.  This file proves that the two agree.

## Main results

* `Stacks.CategoryTheory.comp_ofNatIsoRight`: the two adjunctions are equal.
* `Stacks.CategoryTheory.conjugateEquiv_comp_comp_ofNatIsoRight`: a conjugate transformation
  between two composite right adjoints, transported.  Knowing the conjugate taken between the
  composites of the *transported* factors, this computes the conjugate taken between the
  composites of the factors themselves:  it is the known one with the two horizontal composites
  of the transporting isomorphisms put around it.

## Implementation notes

The only content is one instance of naturality of `i₁.hom` at a component of the unit of `a₂`:
the unit of a composite inserts `P₁` between the two units, and the two readings differ by
whether `i₁` is applied before or after that `P₁` is passed.  Everything else is
`CategoryTheory.Adjunction.comp_unit_app` and
`CategoryTheory.Adjunction.ofNatIsoRight_unit`, and an adjunction is determined by its unit by
`CategoryTheory.Adjunction.ext`.

The statement is used to move a conjugate transformation between two presentations of a
*composite* right adjoint:  the conjugate calculus of
`StacksFrontier/CategoryTheory/Adjunction/ConjugateNaturality.lean` transports along
`CategoryTheory.Adjunction.ofNatIsoRight` of each of the two adjunctions it is taken between,
and a square of adjunctions presents those two as composites of transported factors.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

universe v₀ v₁ v₂ u₀ u₁ u₂

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]

/-- **Transporting the right adjoints of two composable adjunctions and composing is composing
and transporting along the horizontal composite.**  For `a₁ : L₁ ⊣ P₁`, `a₂ : L₂ ⊣ P₂` and
isomorphisms `i₁ : P₁ ≅ Q₁`, `i₂ : P₂ ≅ Q₂`, the composite of the two transported adjunctions is
the transport of the composite adjunction along `P₂ ◁ i₁` followed by `i₂ ▷ Q₁`. -/
theorem comp_ofNatIsoRight {L₁ : C₀ ⥤ C₁} {P₁ Q₁ : C₁ ⥤ C₀} {L₂ : C₁ ⥤ C₂} {P₂ Q₂ : C₂ ⥤ C₁}
    (a₁ : L₁ ⊣ P₁) (a₂ : L₂ ⊣ P₂) (i₁ : P₁ ≅ Q₁) (i₂ : P₂ ≅ Q₂) :
    (a₁.ofNatIsoRight i₁).comp (a₂.ofNatIsoRight i₂) =
      (a₁.comp a₂).ofNatIsoRight
        (Functor.isoWhiskerLeft P₂ i₁ ≪≫ Functor.isoWhiskerRight i₂ Q₁) := by
  refine Adjunction.ext (NatTrans.ext (funext fun c ↦ ?_))
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.trans_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp,
    Category.assoc]
  exact congrArg (fun t ↦ a₁.unit.app c ≫ t) (by simp)

/-- **A conjugate transformation between two composite right adjoints, transported.**  Given two
systems `a₁, a₂` and `b₁, b₂` of composable adjunctions and isomorphisms `i₁, i₂, j₁, j₂` of
their four right adjoints, a conjugate taken between the composites of the *transported*
adjunctions determines the conjugate taken between the composites of the adjunctions themselves:
the latter is the former with the two horizontal composites of the isomorphisms put around it.

This is `Stacks.CategoryTheory.comp_ofNatIsoRight` on each of the two composite adjunctions
followed by `Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight`.  Every category, functor,
adjunction and isomorphism is a variable, so that an instance of the statement at concrete
functors is a single application with no rewriting left to do there. -/
theorem conjugateEquiv_comp_comp_ofNatIsoRight {E : Type*} [Category E]
    {L₁ : C₀ ⥤ C₁} {P₁ Q₁ : C₁ ⥤ C₀} {L₂ : C₁ ⥤ E} {P₂ Q₂ : E ⥤ C₁}
    {M₁ : C₀ ⥤ C₂} {R₁ T₁ : C₂ ⥤ C₀} {M₂ : C₂ ⥤ E} {R₂ T₂ : E ⥤ C₂}
    (a₁ : L₁ ⊣ P₁) (a₂ : L₂ ⊣ P₂) (b₁ : M₁ ⊣ R₁) (b₂ : M₂ ⊣ R₂)
    (i₁ : P₁ ≅ Q₁) (i₂ : P₂ ≅ Q₂) (j₁ : R₁ ≅ T₁) (j₂ : R₂ ≅ T₂)
    (τ : M₁ ⋙ M₂ ⟶ L₁ ⋙ L₂) (β : Q₂ ⋙ Q₁ ⟶ T₂ ⋙ T₁)
    (hβ : conjugateEquiv ((a₁.ofNatIsoRight i₁).comp (a₂.ofNatIsoRight i₂))
        ((b₁.ofNatIsoRight j₁).comp (b₂.ofNatIsoRight j₂)) τ = β) :
    conjugateEquiv (a₁.comp a₂) (b₁.comp b₂) τ =
      (Functor.isoWhiskerLeft P₂ i₁ ≪≫ Functor.isoWhiskerRight i₂ Q₁).hom ≫ β ≫
        (Functor.isoWhiskerLeft R₂ j₁ ≪≫ Functor.isoWhiskerRight j₂ T₁).inv := by
  rw [comp_ofNatIsoRight, comp_ofNatIsoRight, conjugateEquiv_ofNatIsoRight] at hβ
  exact ((Iso.eq_comp_inv _).mpr ((Iso.inv_comp_eq _).mp hβ)).trans (Category.assoc _ _ _)

end Stacks.CategoryTheory

end

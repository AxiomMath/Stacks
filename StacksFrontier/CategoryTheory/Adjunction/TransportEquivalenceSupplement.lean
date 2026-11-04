module

public import StacksFrontier.CategoryTheory.Adjunction.TransportEquivalence

/-!
# Transporting a left adjoint along an equivalence of the target

If `P₀ ⊣ W ⋙ R` and `W` is an equivalence, then `P₀ ⋙ W ⊣ R`.

## Main definitions

* `CategoryTheory.Adjunction.ofConjugateTarget`: The adjunction `P₀ ⋙ W ⊣ R` obtained from an
  adjunction `P₀ ⊣ W ⋙ R` with `W` an equivalence.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory.Adjunction
universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃
variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
section
universe w₁ w₂ w₃ t₁ t₂ t₃

/-- If `P₀ ⊣ W ⋙ R` with `W` an equivalence, then `P₀ ⋙ W` is a left adjoint of `R`. -/
noncomputable def ofConjugateTarget
    {A : Type t₁} [Category.{w₁} A] {B₀ : Type t₂} [Category.{w₂} B₀]
    {E : Type t₃} [Category.{w₃} E]
    (W : B₀ ⥤ E) (R : E ⥤ A) (P₀ : A ⥤ B₀) [W.IsEquivalence] (adj₀ : P₀ ⊣ W ⋙ R) :
    P₀ ⋙ W ⊣ R :=
  (adj₀.comp W.asEquivalence.toAdjunction).ofNatIsoRight
    (W.asEquivalence.invFunIdAssoc R)

end
end CategoryTheory.Adjunction
end

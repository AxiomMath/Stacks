module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# Transporting a derived left adjoint along exact equivalences

Let `G : A₂ ⥤ A₁` and `G' : B₂ ⥤ B₁` be exact functors of abelian categories, let
`E₁ : A₁ ≌ B₁` and `E₂ : A₂ ≌ B₂` be exact equivalences, and let `σ : G ⋙ E₁ ≅ E₂ ⋙ G'`.
A left adjoint `L'` of `G'` on the unbounded derived categories is carried to a left adjoint

`L = E₁ ⋙ L' ⋙ E₂⁻¹ : D(A₁) ⥤ D(A₂)`

of `G` on the derived categories, and if the unit of `L' ⊣ G'` is invertible so is the unit of
`L ⊣ G`. This is how a derived functor constructed in one model of a pair of abelian categories
is read in another, for instance across a change of the universe of a sheaf of rings.

## Main definitions

* `Stacks.DerivedAdjunctionTransport.mapDerivedCategoryCommIso`: `σ` on the derived categories.
* `Stacks.DerivedAdjunctionTransport.leftAdjoint`: `L = E₁ ⋙ L' ⋙ E₂⁻¹`.
* `Stacks.DerivedAdjunctionTransport.adjunction`: `L ⊣ G` on the derived categories.

## Main results

* `Stacks.DerivedAdjunctionTransport.isIso_adjunction_unit`: the unit of `L ⊣ G` is invertible
  when the unit of `L' ⊣ G'` is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedAdjunctionTransport

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {A₁ A₂ B₁ B₂ : Type*} [Category A₁] [Category A₂] [Category B₁] [Category B₂]
  [Abelian A₁] [Abelian A₂] [Abelian B₁] [Abelian B₂]
  [HasDerivedCategory A₁] [HasDerivedCategory A₂] [HasDerivedCategory B₁]
  [HasDerivedCategory B₂]
  (E₁ : A₁ ≌ B₁) (E₂ : A₂ ≌ B₂)
  [E₁.functor.Additive] [PreservesFiniteLimits E₁.functor] [PreservesFiniteColimits E₁.functor]
  [E₁.inverse.Additive] [PreservesFiniteLimits E₁.inverse] [PreservesFiniteColimits E₁.inverse]
  [E₂.functor.Additive] [PreservesFiniteLimits E₂.functor] [PreservesFiniteColimits E₂.functor]
  [E₂.inverse.Additive] [PreservesFiniteLimits E₂.inverse] [PreservesFiniteColimits E₂.inverse]
  (G : A₂ ⥤ A₁) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (G' : B₂ ⥤ B₁) [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  (σ : G ⋙ E₁.functor ≅ E₂.functor ⋙ G')

/-- The commutation `σ : G ⋙ E₁ ≅ E₂ ⋙ G'` read on the unbounded derived categories. -/
def mapDerivedCategoryCommIso :
    G.mapDerivedCategory ⋙ E₁.functor.mapDerivedCategory ≅
      E₂.functor.mapDerivedCategory ⋙ G'.mapDerivedCategory :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso G E₁.functor).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ σ ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso E₂.functor G'

/-- `G` on the derived categories, recovered from `G'` by conjugating with the two derived
equivalences. -/
def mapDerivedCategoryConjugateIso :
    E₂.functor.mapDerivedCategory ⋙ G'.mapDerivedCategory ⋙ E₁.inverse.mapDerivedCategory ≅
      G.mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mapDerivedCategoryCommIso E₁ E₂ G G' σ).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Dualizing.mapDerivedCategoryEquivalenceOfEquivalence E₁).unitIso.symm ≪≫
    Functor.rightUnitor _

variable (L' : DerivedCategory B₁ ⥤ DerivedCategory B₂)

/-- **The transported left adjoint** `E₁ ⋙ L' ⋙ E₂⁻¹ : D(A₁) ⥤ D(A₂)`. -/
abbrev leftAdjoint : DerivedCategory A₁ ⥤ DerivedCategory A₂ :=
  E₁.functor.mapDerivedCategory ⋙ L' ⋙ E₂.inverse.mapDerivedCategory

variable {L'} (adj' : L' ⊣ G'.mapDerivedCategory)

/-- **The transported adjunction** `E₁ ⋙ L' ⋙ E₂⁻¹ ⊣ G` on the derived categories. -/
def adjunction : leftAdjoint E₁ E₂ L' ⊣ G.mapDerivedCategory :=
  (((Dualizing.mapDerivedCategoryEquivalenceOfEquivalence E₁).toAdjunction.comp adj').comp
    (Dualizing.mapDerivedCategoryEquivalenceOfEquivalence E₂).symm.toAdjunction).ofNatIsoRight
    (mapDerivedCategoryConjugateIso E₁ E₂ G G' σ)

/-- **The unit of the transported adjunction is invertible when the unit of `L' ⊣ G'` is**: the
transported left adjoint is a composite of a fully faithful functor with two equivalences. -/
theorem isIso_adjunction_unit (h : IsIso adj'.unit) :
    IsIso (adjunction E₁ E₂ G G' σ adj').unit := by
  have := h
  have hL' : (leftAdjoint E₁ E₂ L').FullyFaithful :=
    (Dualizing.mapDerivedCategoryEquivalenceOfEquivalence E₁).fullyFaithfulFunctor.comp
      (adj'.fullyFaithfulLOfIsIsoUnit.comp
        (Dualizing.mapDerivedCategoryEquivalenceOfEquivalence E₂).fullyFaithfulInverse)
  have := hL'.full
  have := hL'.faithful
  infer_instance

end Stacks.DerivedAdjunctionTransport

end

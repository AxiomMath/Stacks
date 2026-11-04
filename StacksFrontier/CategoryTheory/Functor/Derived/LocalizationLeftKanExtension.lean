module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Localization.Predicate
import StacksCore.Tactic.StacksAttribute

/-!
# Right derived functors along the localization of cochain complexes

A right derived functor on an unbounded derived category is most easily produced on the
homotopy category, where K-injective complexes represent the derived functor, while the
universal property is usually stated relative to the localization of *cochain complexes* at the
quasi-isomorphisms. This file relates the two.

This rests on one general fact: a functor out of a localization is the left Kan
extension, along that localization functor, of anything isomorphic to its precomposition.
That is `CategoryTheory.Functor.isLeftKanExtension_of_isIso_of_isLocalization`; it holds
because precomposition with a localization functor is fully faithful. Transitivity of left
Kan extensions along `CochainComplex → HomotopyCategory → DerivedCategory` then converts a
right derived functor relative to `DerivedCategory.Qh` into one relative to
`DerivedCategory.Q`.

## Main definitions

* `CategoryTheory.Functor.cochainRightDerivedUnit`: the unit at the level of cochain
  complexes obtained from a unit at the level of the homotopy category.

## Main results

* `CategoryTheory.Functor.isLeftKanExtension_of_isIso_of_isLocalization`: a functor out of a
  localization left-Kan-extends any functor isomorphic to its precomposition.
* `CategoryTheory.Functor.isRightDerivedFunctor_cochainRightDerivedUnit`: a right derived
  functor relative to `DerivedCategory.Qh` and the homotopy-category quasi-isomorphisms is
  also one relative to `DerivedCategory.Q` and the quasi-isomorphisms of cochain complexes.
-/

@[expose] public section

namespace CategoryTheory.Functor

open CategoryTheory Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]

/-- A functor out of a localization is the left Kan extension, along the localization
functor, of any functor isomorphic to its precomposition: precomposition with a localization
functor is fully faithful, so the required factorisations exist and are unique.

This is Mathlib's `CategoryTheory.Functor.isRightDerivedFunctor_of_inverts` read through
`CategoryTheory.Functor.isRightDerivedFunctor_iff_isLeftKanExtension`, `IsRightDerivedFunctor`
being *defined* to carry `IsLeftKanExtension`. -/
theorem isLeftKanExtension_of_isIso_of_isLocalization
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    {F : C ⥤ H} (G : D ⥤ H) (α : F ⟶ L ⋙ G) [IsIso α] :
    G.IsLeftKanExtension α := by
  rw [← Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ W]
  exact Functor.isRightDerivedFunctor_of_inverts W _ (asIso α).symm

end

section

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{u₂} 𝒜]
  {H : Type u₃} [Category.{v₃} H]

/-- The unit of a right derived functor, read at the level of cochain complexes: the given
isomorphism onto the homotopy-category functor, the homotopy-level unit, and the canonical
identification of `quotient ⋙ Qh` with `Q`. -/
noncomputable def cochainRightDerivedUnit
    {F₀ : CochainComplex 𝒜 ℤ ⥤ H} {F₁ : HomotopyCategory 𝒜 (ComplexShape.up ℤ) ⥤ H}
    (α : F₀ ⟶ HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ) ⋙ F₁)
    {G : DerivedCategory 𝒜 ⥤ H} (β : F₁ ⟶ DerivedCategory.Qh ⋙ G) :
    F₀ ⟶ DerivedCategory.Q ⋙ G :=
  α ≫ whiskerLeft (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)) β ≫
    (associator _ _ _).inv ≫ whiskerRight (DerivedCategory.quotientCompQhIso 𝒜).hom G

/-- The component of `cochainRightDerivedUnit α β` at a cochain complex `K` is the component of `α`
at `K`, followed by that of `β` at the image of `K` in the homotopy category and the image under
`G` of the identification of `quotient ⋙ Qh` with `Q` at `K`. -/
@[simp]
lemma cochainRightDerivedUnit_app
    {F₀ : CochainComplex 𝒜 ℤ ⥤ H} {F₁ : HomotopyCategory 𝒜 (ComplexShape.up ℤ) ⥤ H}
    (α : F₀ ⟶ HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ) ⋙ F₁)
    {G : DerivedCategory 𝒜 ⥤ H} (β : F₁ ⟶ DerivedCategory.Qh ⋙ G)
    (K : CochainComplex 𝒜 ℤ) :
    (cochainRightDerivedUnit α β).app K = α.app K ≫
      β.app ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj K) ≫
        G.map ((DerivedCategory.quotientCompQhIso 𝒜).hom.app K) := by
  simp [cochainRightDerivedUnit]

/-- The cochain-level unit is invertible at a complex at which both the comparison with the
homotopy-category functor and the homotopy-level unit are invertible. -/
lemma isIso_cochainRightDerivedUnit_app
    {F₀ : CochainComplex 𝒜 ℤ ⥤ H} {F₁ : HomotopyCategory 𝒜 (ComplexShape.up ℤ) ⥤ H}
    (α : F₀ ⟶ HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ) ⋙ F₁)
    {G : DerivedCategory 𝒜 ⥤ H} (β : F₁ ⟶ DerivedCategory.Qh ⋙ G)
    (K : CochainComplex 𝒜 ℤ) [IsIso (α.app K)]
    [IsIso (β.app ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj K))] :
    IsIso ((cochainRightDerivedUnit α β).app K) := by
  rw [cochainRightDerivedUnit_app]
  infer_instance

/-- A right derived functor relative to `DerivedCategory.Qh` and the quasi-isomorphisms of
the homotopy category is also a right derived functor relative to `DerivedCategory.Q` and the
quasi-isomorphisms of cochain complexes, with unit `cochainRightDerivedUnit`. -/
theorem isRightDerivedFunctor_cochainRightDerivedUnit
    {F₀ : CochainComplex 𝒜 ℤ ⥤ H} {F₁ : HomotopyCategory 𝒜 (ComplexShape.up ℤ) ⥤ H}
    (α : F₀ ⟶ HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ) ⋙ F₁) [IsIso α]
    {G : DerivedCategory 𝒜 ⥤ H} (β : F₁ ⟶ DerivedCategory.Qh ⋙ G)
    [G.IsRightDerivedFunctor β (HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ))] :
    G.IsRightDerivedFunctor (cochainRightDerivedUnit α β)
      (HomologicalComplex.quasiIso 𝒜 (ComplexShape.up ℤ)) := by
  have h₁ : F₁.IsLeftKanExtension α :=
    isLeftKanExtension_of_isIso_of_isLocalization _
      (HomologicalComplex.homotopyEquivalences 𝒜 (ComplexShape.up ℤ)) _ _
  have h₂ : G.IsLeftKanExtension β := by
    rwa [← isRightDerivedFunctor_iff_isLeftKanExtension _ _
      (HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ))]
  rw [isRightDerivedFunctor_iff_isLeftKanExtension]
  exact (isLeftKanExtension_iff_postcompose (α := α) DerivedCategory.Q
    (DerivedCategory.quotientCompQhIso 𝒜) β (cochainRightDerivedUnit α β) rfl).mp h₂

end

end CategoryTheory.Functor

end

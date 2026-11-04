module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Filtered.FinallySmall

/-! # Density of a compact generating subcategory

Let `P` be a property of objects of a category `C` all of whose objects are categorically
compact (Stacks 0FWX, which is Mathlib's `IsFinitelyPresentable`), and assume every object
of `C` is a filtered colimit of objects satisfying `P`, i.e. `P.ind` holds everywhere.
This file records that the inclusion `P.ι` of the corresponding full subcategory is then a
dense functor, and that each comma category `CostructuredArrow P.ι X` is filtered and admits
a final functor from a small filtered category.

These are the geometric inputs to Stacks 0FWY: density says that `X` is *canonically* the
colimit of the `P`-objects over it, so a functor out of `C` that commutes with filtered
colimits is determined by its restriction to the subcategory.
-/

@[expose] public section

open CategoryTheory Category Limits ObjectProperty Cardinal

universe w v u

namespace CategoryTheory.ObjectProperty

attribute [local instance] fact_isRegular_aleph0

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- If `X` is the colimit of a small filtered diagram of categorically compact objects
satisfying `P`, then the induced functor into `CostructuredArrow P.ι X` is final: every
arrow into `X` from a `P`-object factors through the diagram, and two such factorisations
become equal further along. -/
theorem ColimitOfShape.final_toCostructuredArrow
    (hP : P ≤ isFinitelyPresentable.{w} C)
    {J : Type w} [SmallCategory J] [IsFiltered J] {X : C} (p : P.ColimitOfShape J X) :
    p.toCostructuredArrow.Final := by
  have : IsCardinalFiltered J ℵ₀ := (isCardinalFiltered_aleph0_iff J).2 ‹_›
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun f ↦ ?_, fun {f j} g₁ g₂ ↦ ?_⟩
  · have : IsFinitelyPresentable.{w} (P.ι.obj f.left) := hP _ f.left.2
    obtain ⟨j, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit p.isColimit f.hom
    exact ⟨j, ⟨CostructuredArrow.homMk (ObjectProperty.homMk g)⟩⟩
  · have : IsFinitelyPresentable.{w} f.left.obj := hP _ f.left.2
    obtain ⟨k, a, h⟩ := IsCardinalPresentable.exists_eq_of_isColimit' ℵ₀ p.isColimit
      g₁.left.hom g₂.left.hom ((CostructuredArrow.w g₁).trans (CostructuredArrow.w g₂).symm)
    exact ⟨k, a, by cat_disch⟩

variable (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X)

include hP hgen

/-- Every `X : C` has a small filtered `P`-colimit presentation whose induced functor into
`CostructuredArrow P.ι X` is final. -/
private theorem exists_colimitOfShape_final (X : C) :
    ∃ (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J) (p : P.ColimitOfShape J X),
      p.toCostructuredArrow.Final := by
  obtain ⟨J, _, _, pres, hpres⟩ := hgen X
  let p : P.ColimitOfShape J X := { toColimitPresentation := pres, prop_diag_obj := hpres }
  exact ⟨J, inferInstance, inferInstance, p, ColimitOfShape.final_toCostructuredArrow P hP p⟩

/-- The category of `P`-objects over a fixed `X : C` is filtered. -/
theorem isFiltered_costructuredArrow_ι (X : C) : IsFiltered (CostructuredArrow P.ι X) := by
  obtain ⟨J, _, _, p, _⟩ := exists_colimitOfShape_final P hP hgen X
  exact IsFiltered.of_final p.toCostructuredArrow

/-- The category of `P`-objects over a fixed `X : C` admits a final functor from a `w`-small
category, so colimits indexed by it are computed by `w`-small colimits. -/
theorem finallySmall_costructuredArrow_ι [LocallySmall.{w} P.FullSubcategory] (X : C) :
    FinallySmall.{w} (CostructuredArrow P.ι X) := by
  obtain ⟨J, _, _, p, _⟩ := exists_colimitOfShape_final P hP hgen X
  exact finallySmall_of_final_of_essentiallySmall p.toCostructuredArrow

/-- The inclusion of the full subcategory of `P`-objects is dense: every `X : C` is the
colimit of the canonical diagram of `P`-objects over `X`. -/
theorem isDense_ι : P.ι.IsDense := by
  refine ⟨fun X ↦ ?_⟩
  obtain ⟨J, _, _, p, _⟩ := exists_colimitOfShape_final P hP hgen X
  exact ⟨(Functor.Final.isColimitWhiskerEquiv (F := p.toCostructuredArrow) _).1
    (IsColimit.ofIsoColimit p.isColimit (Cocone.ext (Iso.refl _)))⟩

end CategoryTheory.ObjectProperty

module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Generator.Presheaf

/-!
# A category of diagrams with Grothendieck abelian values is Grothendieck abelian

Let `C` be a category with objects in `Type u` and morphisms in `Type v`, and let `D` be an
abelian category which is Grothendieck abelian relative to `max u v`. Then the category of
diagrams `Cᵒᵖ ⥤ D` is Grothendieck abelian relative to `max u v` as well.

## Main results

* `CategoryTheory.locallySmall_presheafCategory`: the diagram category is locally small relative
  to `max u v`.
* `CategoryTheory.isGrothendieckAbelian_presheafCategory`: the diagram category is Grothendieck
  abelian relative to `max u v`.

## Implementation notes

`CategoryTheory.AB5OfSize` is a structure quantifying over shapes, so its field is supplied
rather than inferred. `CategoryTheory.Presheaf.hasSeparator` asks for coproducts in `D` indexed
separately by `Type u` and by `Type v`; these are obtained from the coproducts of size `max u v`.
Mathlib's instance for a category of sheaves (`CategoryTheory.Sheaf.instIsGrothendieckAbelian`)
does not apply, since it needs `CategoryTheory.HasSheafify`.

## References

* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uD vD v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] (D : Type uD) [Category.{vD} D] [Abelian D]
  [IsGrothendieckAbelian.{max u v} D]

/-- The diagram category `Cᵒᵖ ⥤ D` is locally small relative to `max u v`. -/
theorem locallySmall_presheafCategory : LocallySmall.{max u v} (Cᵒᵖ ⥤ D) where
  hom_small F G := by
    let emb (f : F ⟶ G) (i : Shrink.{max u v} Cᵒᵖ) :=
      (equivShrink.{max u v} _) (f.app ((equivShrink _).symm i))
    have hemb : Function.Injective emb := fun f g h ↦ by
      ext i
      obtain ⟨i, rfl⟩ := (equivShrink.{max u v} _).symm.surjective i
      simpa [emb] using congrFun h i
    exact small_of_injective hemb

/-- The diagram category `Cᵒᵖ ⥤ D` with values in a Grothendieck abelian category is Grothendieck
abelian relative to `max u v`. -/
instance isGrothendieckAbelian_presheafCategory :
    IsGrothendieckAbelian.{max u v} (Cᵒᵖ ⥤ D) where
  locallySmall := locallySmall_presheafCategory C D
  ab5OfSize := { ofShape := fun _ _ _ => inferInstance }
  hasSeparator :=
    letI : HasCoproducts.{v} D := fun J =>
      hasColimitsOfShape_of_equivalence (Discrete.equivalence (Equiv.ulift.{u, v} (α := J)))
    letI : HasCoproducts.{u} D := fun J =>
      hasColimitsOfShape_of_equivalence (Discrete.equivalence (Equiv.ulift.{v, u} (α := J)))
    Presheaf.hasSeparator C D

end CategoryTheory

end

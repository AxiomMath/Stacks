module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# `Ext` in degree zero is a morphism group

`DerivedCategory.Ext X Y i` is `CategoryTheory.ShiftedHom X Y i`, that is `X ⟶ Y⟦i⟧`, so in
degree `0` it is `X ⟶ Y` up to the isomorphism `Y⟦0⟧ ≅ Y`. The identification is
`CategoryTheory.ShiftedHom.homEquiv`, and it commutes with precomposition by a fixed morphism,
that being a single associativity. So a surjectivity statement about `Ext⁰_𝒜(−, Y)` and the
same statement about `Hom_{D(𝒜)}(−, Y)` are interchangeable.

This is the step from the cohomological conditions of Stacks 07YM, which are stated for `Ext`
groups, to the tangent-space description of versality, which is stated for morphisms of the
derived category.

## Main results

* `DerivedCategory.surjective_extZero_comp_iff_surjective_comp`.

## References

* [Stacks Project, Tag 06XQ](https://stacks.math.columbia.edu/tag/06XQ)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- Precomposition with `ξ` is surjective on degree-zero `Ext` groups into `Y` exactly when it
is surjective on morphisms into `Y`. In degree `0` an `Ext` class *is* a morphism, by
`CategoryTheory.ShiftedHom.homEquiv`, and the identification commutes with precomposition. -/
@[stacks 06XQ "degree zero"]
public theorem surjective_extZero_comp_iff_surjective_comp
    {E X : DerivedCategory C} (ξ : E ⟶ X) (Y : DerivedCategory C) :
    Function.Surjective (fun α : DerivedCategory.Ext X Y 0 => ξ ≫ α) ↔
      Function.Surjective (fun f : X ⟶ Y => ξ ≫ f) := by
  set eX := ShiftedHom.homEquiv (X := X) (Y := Y) (0 : ℤ) rfl
  set eE := ShiftedHom.homEquiv (X := E) (Y := Y) (0 : ℤ) rfl
  have hfun : (fun α : DerivedCategory.Ext X Y 0 => ξ ≫ α) =
      eE ∘ (fun f : X ⟶ Y => ξ ≫ f) ∘ eX.symm := by
    funext α
    obtain ⟨f, rfl⟩ := eX.surjective α
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact (Category.assoc ξ f _).symm
  rw [hfun, Equiv.comp_surjective, Equiv.surjective_comp]

end DerivedCategory

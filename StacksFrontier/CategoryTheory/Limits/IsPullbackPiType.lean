module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# A cartesian square of types stays cartesian after taking functions out of a fixed type

A cartesian square in `Type u` remains cartesian after applying `Θ → -` for a fixed type `Θ`,
and likewise after applying `I → L → -`. Both are proved from the elementary characterization
`CategoryTheory.Limits.Types.isPullback_iff`: the commutativity, the injectivity and the
existence statements all hold pointwise in `Θ`, the last one by choosing a preimage at each
point.

## Main results

* `CategoryTheory.Limits.Types.isPullback_pi`: **`Θ → -` preserves cartesian squares of
  types.**
* `CategoryTheory.Limits.Types.isPullback_matrix`: **`I → L → -` preserves cartesian squares of
  types**, which is the form a square of matrices over four rings is read in.

## Implementation notes

`Θ → -` is `CategoryTheory.coyoneda.obj (op Θ)` and Mathlib's
`CategoryTheory.IsPullback.map` together with `CategoryTheory.coyoneda_preservesLimits` would
give the first statement — but its conclusion is a cartesian square of the *Hom-types* `Θ ⟶ Xᵢ`,
and in this development `Θ → X` and `Θ ⟶ X` are not interchangeable: the `isDefEq` transparency
setting blocks unfolding `Quiver.Hom` on `Type u`, so a consumer stating its square on honest
function types cannot use that conclusion without a transport. The elementary proof avoids the
transport altogether, and `CategoryTheory.asHom` (`↾`) is applied once to each of the four maps
so that the statement is about morphisms of types, which is where a cartesian square lives.

The second statement is the first applied twice; it is stated separately because the iterated
application produces the two maps in a nested form, and consumers need the flat one.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Limits.Types

/-- **Taking functions out of a fixed type preserves cartesian squares of types.** If a square
of types is cartesian then so is the square obtained by applying `Θ → -` to it, with each map
acting pointwise. -/
theorem isPullback_pi {X₁ X₂ X₃ X₄ : Type u} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄}
    {b : X₃ ⟶ X₄} (h : IsPullback t l r b) (Θ : Type u) :
    IsPullback (↾fun (g : Θ → X₁) (θ : Θ) => t (g θ)) (↾fun (g : Θ → X₁) (θ : Θ) => l (g θ))
      (↾fun (g : Θ → X₂) (θ : Θ) => r (g θ)) (↾fun (g : Θ → X₃) (θ : Θ) => b (g θ)) := by
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext g θ
    exact ConcreteCategory.congr_hom h.w (g θ)
  · intro g₁ g₂ ⟨h₁, h₂⟩
    funext θ
    exact Types.ext_of_isPullback h (congrFun h₁ θ) (congrFun h₂ θ)
  · intro g₂ g₃ hg
    choose g hg₂ hg₃ using fun θ => Types.exists_of_isPullback h (g₂ θ) (g₃ θ) (congrFun hg θ)
    exact ⟨g, funext hg₂, funext hg₃⟩

/-- **Taking matrices preserves cartesian squares of types.** If a square of types is cartesian
then so is the square of `I`-by-`L` matrices over it, with each map acting entrywise. This is
`CategoryTheory.Limits.Types.isPullback_pi` applied twice. -/
theorem isPullback_matrix {X₁ X₂ X₃ X₄ : Type u} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄}
    {b : X₃ ⟶ X₄} (h : IsPullback t l r b) (I L : Type u) :
    IsPullback (↾fun (M : I → L → X₁) (i : I) (k : L) => t (M i k))
      (↾fun (M : I → L → X₁) (i : I) (k : L) => l (M i k))
      (↾fun (M : I → L → X₂) (i : I) (k : L) => r (M i k))
      (↾fun (M : I → L → X₃) (i : I) (k : L) => b (M i k)) :=
  isPullback_pi (isPullback_pi h L) I

end CategoryTheory.Limits.Types

end

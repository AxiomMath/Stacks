module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import Mathlib.CategoryTheory.Category.ULift

/-!
# Raising the morphism universe of a category fibred in groupoids

`CategoryTheory.ULiftHom.{w} 𝒮` is the category with the same objects as `𝒮` whose morphisms are
the morphisms of `𝒮` wrapped in `ULift.{w}`; it is the universe-polymorphic repackaging of `𝒮`
that `CategoryTheory.ULiftHom.down` identifies with `𝒮` again. Composing the structure functor
`p : 𝒮 ⥤ 𝒞` with `CategoryTheory.ULiftHom.down` therefore presents the same category over `𝒞`
with its morphism universe raised, and the two clauses of Stacks 003S are unaffected by the
repackaging: the objects are literally the same and the morphisms differ by a bijection which
`CategoryTheory.ULiftHom.down` inverts.

This is what makes a category over `𝒞` fibred in groupoids usable as an object of the
2-category `CategoryTheory.CatFiberedInGroupoids` of Stacks 02XS at a morphism universe larger
than its own: that 2-category fixes one morphism universe for all of its objects, and a cospan
of categories fibred in groupoids whose morphism universes differ cannot be formed inside it
without such a repackaging.

## Main results

* `CategoryTheory.Functor.IsHomLift.uliftHomDown`: a morphism lies over the same morphism of the
  base after the repackaging.
* `CategoryTheory.Functor.IsFiberedInGroupoids.uliftHomDown`: **Stacks 003S** is inherited by the
  repackaged category over `𝒞`.

## References

* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 02XS](https://stacks.math.columbia.edu/tag/02XS)
-/

@[expose] public section

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- A morphism of `𝒮`, read as a morphism of `CategoryTheory.ULiftHom 𝒮`, lies over the same
morphism of the base: the repackaged structure functor has the same value on it. -/
theorem Functor.IsHomLift.uliftHomDown (p : 𝒮 ⥤ 𝒞) {R S : 𝒞} {a b : 𝒮}
    (f : R ⟶ S) (φ : a ⟶ b) (h : p.IsHomLift f φ) :
    ((ULiftHom.down : ULiftHom.{w} 𝒮 ⥤ 𝒮) ⋙ p).IsHomLift f
      (ULift.up φ : ULiftHom.objUp a ⟶ ULiftHom.objUp b) := by
  obtain ⟨⟩ := h
  exact .map _

/-- **Stacks 003S** for a repackaged category over `𝒞`: if `p : 𝒮 ⥤ 𝒞` is fibred in groupoids,
then so is the composite of `CategoryTheory.ULiftHom.down` with `p`, which is the same category
over `𝒞` with its morphism universe raised.

Lifts are transported by wrapping them with `ULift.up`, and the existence and uniqueness of
fill-ins by unwrapping with `ULift.down`; the base morphisms are untouched. -/
theorem Functor.IsFiberedInGroupoids.uliftHomDown {p : 𝒮 ⥤ 𝒞}
    (h : p.IsFiberedInGroupoids) :
    ((ULiftHom.down : ULiftHom.{w} 𝒮 ⥤ 𝒮) ⋙ p).IsFiberedInGroupoids where
  exists_lift {_V _U} f x hx := by
    obtain ⟨y, φ, hφ⟩ := h.exists_lift f (ULiftHom.objDown x) hx
    exact ⟨ULiftHom.objUp y, ULift.up φ, Functor.IsHomLift.uliftHomDown p f φ hφ⟩
  unique_lift {_x _y _z} φ ψ f hf := by
    obtain ⟨χ, ⟨hmap, hfac⟩, huniq⟩ := h.unique_lift φ.down ψ.down f hf
    refine ⟨ULift.up χ, ⟨hmap, congrArg ULift.up hfac⟩, fun χ' hχ' ↦ ?_⟩
    exact congrArg ULift.up (huniq χ'.down ⟨hχ'.1, congrArg ULift.down hχ'.2⟩)

end CategoryTheory

end

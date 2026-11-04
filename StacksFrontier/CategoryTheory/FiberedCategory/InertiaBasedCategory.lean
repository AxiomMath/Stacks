module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import StacksCore.CategoryTheory.Inertia

/-!
# The relative inertia as a category over the base

Let `𝒮` be a category and let `f : 𝒳 ⥤ᵇ 𝒴` be a 1-morphism of categories over `𝒮`, i.e. a
functor `𝒳.obj ⥤ 𝒴.obj` with `f ⋙ 𝒴.p = 𝒳.p`. The relative inertia `I_{𝒳/𝒴}`
(`CategoryTheory.RelativeInertia`, Stacks 034I) is then itself a category over `𝒮`: its
structure functor is `π ⋙ 𝒳.p`, i.e. `CategoryTheory.relativeInertiaStruct`, and the
forgetful functor `π` is a 1-morphism of categories over `𝒮` from it to `𝒳`, strictly so.

This file provides exactly that packaging. It is the source and the first projection of the
inertia square of Stacks 04Z6, and it is the construction whose algebraicity is the subject of
Stacks 050Q; the absolute inertia `I_𝒳` is the case `𝒴 = 𝟭 𝒮`, for which
`CategoryTheory.RelativeInertia.basedCategory` applied to `⟨𝒳.p, rfl⟩` is definitionally
`BasedCategory.ofFunctor (RelativeInertia.π 𝒳.p ⋙ 𝒳.p)`, so no separate name is needed.

## Main definitions

* `CategoryTheory.RelativeInertia.basedCategory`: the relative inertia of a 1-morphism of
  categories over `𝒮`, as a category over `𝒮`.
* `CategoryTheory.RelativeInertia.basedProjection`: the forgetful functor `π`, as a
  1-morphism of categories over `𝒮`.

## Implementation notes

Both are stated over an arbitrary base category rather than over the big fppf site of a
scheme, because nothing in either construction uses the site: the inertia of a 1-morphism and
its forgetful functor are purely categorical, and the site enters only in the algebraicity
statements about them (Stacks 050Q). At the universes of Stacks 050Q — base `𝒮 : Type (u + 1)`
with `Category.{u}` and `𝒳 𝒴 : BasedCategory.{u, u + 1} 𝒮` — the object universe `max u₂ v₂` of
`basedCategory` reduces to `u + 1`, so the two definitions here specialise on the nose to the
inertia and the projection of that tag.

The source and target of `f` are allowed independent universes, as a `BasedFunctor` already
does; only the source's universes appear in the result, since the inertia of `f` is built from
morphisms of `𝒳` alone.

## References

* [Stacks Project, Tag 034I](https://stacks.math.columbia.edu/tag/034I)
* [Stacks Project, Tag 04Z6](https://stacks.math.columbia.edu/tag/04Z6)
* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
-/

@[expose] public section

namespace CategoryTheory.RelativeInertia

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

/-- The relative inertia `I_{𝒳/𝒴}` of a 1-morphism `f : 𝒳 ⥤ᵇ 𝒴` of categories over `𝒮`, as a
category over `𝒮`. Its objects are the pairs `(x, α)` with `x` an object of `𝒳` and `α` an
automorphism of `x` with `f α = 𝟙`, and it lies over `𝒮` by `(x, α) ↦ 𝒳.p x`. -/
def basedCategory (f : 𝒳 ⥤ᵇ 𝒴) : BasedCategory.{v₂, max u₂ v₂} 𝒮 :=
  BasedCategory.ofFunctor (RelativeInertia.π f.toFunctor ⋙ 𝒳.p)

/-- The forgetful functor `π : I_{𝒳/𝒴} ⥤ 𝒳`, `(x, α) ↦ x`, as a 1-morphism of categories over
`𝒮`. It is strictly over `𝒮`: the structure functor of `basedCategory f` is by definition
`π ⋙ 𝒳.p`. -/
def basedProjection (f : 𝒳 ⥤ᵇ 𝒴) : basedCategory f ⥤ᵇ 𝒳 where
  toFunctor := RelativeInertia.π f.toFunctor
  w := rfl

/-- The underlying category of `basedCategory f` is the relative inertia of `f`. -/
@[simp] lemma basedCategory_obj (f : 𝒳 ⥤ᵇ 𝒴) :
    (basedCategory f).obj = RelativeInertia f.toFunctor := rfl

/-- The structure functor of `basedCategory f` is `π ⋙ 𝒳.p`. -/
lemma basedCategory_p (f : 𝒳 ⥤ᵇ 𝒴) :
    (basedCategory f).p = RelativeInertia.π f.toFunctor ⋙ 𝒳.p := rfl

/-- The underlying functor of `basedProjection f` is the forgetful functor `π`. -/
@[simp] lemma basedProjection_toFunctor (f : 𝒳 ⥤ᵇ 𝒴) :
    (basedProjection f).toFunctor = RelativeInertia.π f.toFunctor := rfl

end CategoryTheory.RelativeInertia

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpecOfGlobalFunctions

/-!
# The functor of points of an arbitrary scheme as a sheaf of large sets

Let `S` be a scheme contained in a big fppf site `B`. For a scheme `Z` over `S` — of **arbitrary
size**, in particular not required to be an object of the size-bounded site — the functor of
points `T ↦ Mor(T, Z)` is a sheaf on the big fppf site of `S`; that is
`AlgebraicGeometry.Space.isSheaf_schemePoints`, and it is fpqc descent for morphisms into `Z`
with no size restriction, since the fppf topology on *all* schemes is subcanonical.

That statement is about a presheaf of `Type u`. The sheaves in which formal algebraic spaces
live are sheaves of `Type (u + 1)`, one universe higher, because their presentations are indexed
by a directed preorder in `Type (u + 1)`. This file records the universe-lifted functor of
points and its sheaf condition in that larger category, as a functor of the target scheme, so
that a morphism of sheaves *into* an arbitrary scheme can be constructed by the universal
property of a colimit of sheaves.

## Main definitions

* `AlgebraicGeometry.Space.largeSchemePointsPresheaf`: the functor sending a scheme `Z` to the
  presheaf `T ↦ ULift (Mor(T, Z))` on the big fppf site of `S`.
* `AlgebraicGeometry.Space.largeSchemePoints`: the same functor with values in sheaves.
* `AlgebraicGeometry.Space.largeSchemePointsSection`: a morphism of schemes `T ⟶ Z`, read as a
  section of that sheaf over `T`.

## Main results

* `AlgebraicGeometry.Space.isSheaf_largeSchemePointsPresheaf`: **the functor of points of a
  scheme of arbitrary size is a sheaf of large sets on the big fppf site of `S`.**

## Implementation notes

No size bound is imposed on `Z`, and this is the point: the subcanonicity of the site's own
topology, `AlgebraicGeometry.bigFppfOver_subcanonical`, gives the sheaf condition only for the
representable presheaf of an *object of the site*, and a scheme whose ring of functions exceeds
the site's cutoff is not one. What replaces it is continuity of the forgetful functor from the
site to all schemes, `AlgebraicGeometry.BigFppfOver.toScheme_isContinuous`, together with
subcanonicity of the fppf topology on all schemes: the restriction along a continuous functor of
a sheaf is a sheaf, in any universe of values.

The universe lift is the one of `CategoryTheory.uliftFunctor`, and the sheaf condition passes
through it by `CategoryTheory.Presieve.isSheaf_comp_uliftFunctor_iff`, which is an equivalence,
so nothing is lost or assumed in raising the universe.

Sections are produced and consumed through `AlgebraicGeometry.Space.largeSchemePointsSection`
rather than through a bare `ULift.up`, so that the type ascription is fixed once here; the
restriction and postcomposition formulas below then hold by definition.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 023Q](https://stacks.math.columbia.edu/tag/023Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The functor of points of a scheme, restricted to the big fppf site of `S` and lifted to
the universe of large sets, as a functor of the target scheme. Its value at `Z` sends an object
`T` of the site to `ULift (Mor(T, Z))`. -/
abbrev largeSchemePointsPresheaf : Scheme.{u} ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (BigFppfOver.toScheme B S hS).op ⋙
    (Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1}

/-- **The functor of points of a scheme of arbitrary size is a sheaf of large sets on the big
fppf site of `S`.** The forgetful functor from the site to all schemes is continuous for the
fppf topology and the fppf topology on schemes is subcanonical, so the restriction of the
representable presheaf of `Z` is a sheaf; the universe lift preserves the sheaf condition. -/
theorem isSheaf_largeSchemePointsPresheaf (Z : Scheme.{u}) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      ((largeSchemePointsPresheaf B S hS).obj Z) := by
  have h : Presieve.IsSheaf (BigFppfOver.topology B S hS) (schemePoints B S hS Z) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_schemePoints B S hS Z)
  refine (isSheaf_iff_isSheaf_of_type _ _).2 ?_
  exact Presieve.isSheaf_comp_uliftFunctor.{u, u + 1} _ h

/-- The functor of points of a scheme of arbitrary size, as a functor from schemes to the
sheaves of large sets on the big fppf site of `S`. -/
abbrev largeSchemePoints :
    Scheme.{u} ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)) where
  obj Z := ⟨(largeSchemePointsPresheaf B S hS).obj Z,
    isSheaf_largeSchemePointsPresheaf B S hS Z⟩
  map f := ObjectProperty.homMk ((largeSchemePointsPresheaf B S hS).map f)

/-- A morphism of schemes from an object of the site to `Z`, read as a section over that object
of the functor of points of `Z`. -/
abbrev largeSchemePointsSection {Z : Scheme.{u}} {T : BigFppfOver B S hS}
    (f : (BigFppfOver.toScheme B S hS).obj T ⟶ Z) :
    ((largeSchemePoints B S hS).obj Z).obj.obj (op T) :=
  ULift.up f

/-- Restricting a section of the functor of points along a morphism of the site precomposes the
corresponding morphism of schemes. -/
theorem largeSchemePoints_obj_map_section {Z : Scheme.{u}} {T T' : BigFppfOver B S hS}
    (u : T' ⟶ T) (f : (BigFppfOver.toScheme B S hS).obj T ⟶ Z) :
    ((largeSchemePoints B S hS).obj Z).obj.map u.op (largeSchemePointsSection B S hS f) =
      largeSchemePointsSection B S hS ((BigFppfOver.toScheme B S hS).map u ≫ f) :=
  rfl

/-- The morphism of sheaves induced by a morphism of schemes postcomposes the morphism of
schemes corresponding to a section. -/
theorem largeSchemePoints_map_hom_app_section {Z Z' : Scheme.{u}} (g : Z ⟶ Z')
    {T : BigFppfOver B S hS} (f : (BigFppfOver.toScheme B S hS).obj T ⟶ Z) :
    ((largeSchemePoints B S hS).map g).hom.app (op T)
        (largeSchemePointsSection B S hS f) =
      largeSchemePointsSection B S hS (f ≫ g) :=
  rfl

end AlgebraicGeometry.Space

end

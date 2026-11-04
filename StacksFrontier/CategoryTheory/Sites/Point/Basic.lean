module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Points of a site: Mathlib's definition satisfies the Stacks axioms

Stacks defines a *point* of a site `C` to be a functor `u : C ⥤ Set` such that

1. for every covering `{U_i → U}` the map `∐ u(U_i) → u(U)` is surjective;
2. for every covering `{U_i → U}` and every morphism `V → U` the maps
   `u(U_i ×_U V) → u(U_i) ×_{u(U)} u(V)` are bijective;
3. the stalk functor `Sh(C) ⥤ Set`, `F ↦ F_p`, is left exact.

Mathlib's `CategoryTheory.GrothendieckTopology.Point` bundles the fiber functor with a
*cofilteredness* condition on its category of elements, a smallness condition, and a
joint-surjectivity condition on covering sieves. This file checks that the Stacks axioms
hold for it: (1) is `Point.fiber_jointly_surjective_of_ofArrows`, obtained from the
sieve-shaped field `jointly_surjective`; (2) and (3) are *consequences* of cofilteredness
in Mathlib rather than assumptions, and are recorded here as
`Point.fiber_pullbackComparison_bijective` and `Point.sheafFiber_leftExact`.

The Mathlib structure is inhabited, so this is not a vacuous characterisation: points are
constructed by `GrothendieckTopology.pointBot`, `Point.ofIsCofiltered`, `Point.over`,
`Point.map` and `Point.comap`.
-/

@[expose] public section

namespace CategoryTheory.GrothendieckTopology

open Limits Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)

add_to_stacks 00Y5 "Mathlib's definition of a point of a site: the fiber functor
  `u : C ⥤ Type w` together with the conditions making it a point. Mathlib assumes
  joint surjectivity on covering sieves (Stacks axiom (1)) and cofilteredness of the
  category of elements of the fiber, from which Stacks axioms (2) and (3) — exactness of
  the fiber and of the stalk functor on sheaves — follow rather than being assumed; see
  `Point.fiber_jointly_surjective_of_ofArrows`, `Point.fiber_pullbackComparison_bijective`
  and `Point.sheafFiber_leftExact` below." CategoryTheory.GrothendieckTopology.Point

/-- **Stacks 00Y5 (1)** for Mathlib's notion of a point: for a covering family
`{U_i → U}_{i ∈ I}` of a site `C` and a point `Φ`, the map `∐ u(U_i) → u(U)` is
surjective, i.e. every element of `u(U)` is the image of an element of some `u(U_i)`.

Mathlib's `Point.jointly_surjective` field is stated for covering *sieves*, giving only
some `g : Y ⟶ U` in the sieve; here the factorisation of `g` through one of the `f i`,
which is what membership in `Sieve.ofArrows` means, is used to land in `u(U_i)`. -/
@[stacks 00Y5 "(1)"]
theorem Point.fiber_jointly_surjective_of_ofArrows {I : Type*} {U : C} {Ui : I → C}
    (f : ∀ i, Ui i ⟶ U) (hf : Sieve.ofArrows Ui f ∈ J U) (x : Φ.fiber.obj U) :
    ∃ (i : I) (y : Φ.fiber.obj (Ui i)), Φ.fiber.map (f i) y = x := by
  obtain ⟨Y, g, hg, y, hy⟩ := Φ.jointly_surjective _ hf x
  obtain ⟨Z, a, h, ⟨i⟩, rfl⟩ := hg
  exact ⟨i, Φ.fiber.map a y, by simpa using hy⟩

/-- **Stacks 00Y5 (2)** for Mathlib's notion of a point: the fiber functor turns fibre
products into fibre products, i.e. the comparison map
`u(X ×_Z Y) → u(X) ×_{u(Z)} u(Y)` is bijective.

Stacks assumes this for the members of a covering; Mathlib derives it — from
cofilteredness of the category of elements of `u` — for *every* pair of morphisms with
common target, which is the stronger statement proved here. -/
@[stacks 00Y5 "(2)"]
theorem Point.fiber_pullbackComparison_bijective [LocallySmall.{w} C]
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    Function.Bijective (pullbackComparison Φ.fiber f g) :=
  (isIso_iff_bijective _).mp inferInstance

/-- **Stacks 00Y5 (3)** for Mathlib's notion of a point: the stalk functor
`Sh(C) ⥤ Set`, `F ↦ F_p`, is left exact.

`Point.sheafFiber` is Mathlib's stalk functor, `sheafToPresheaf J _ ⋙ Φ.presheafFiber`,
the filtered colimit of the sections of `F` over the category of elements of `u`. -/
@[stacks 00Y5 "(3)"]
theorem Point.sheafFiber_leftExact [LocallySmall.{w} C] :
    PreservesFiniteLimits (Φ.sheafFiber (A := Type w)) :=
  inferInstance

end CategoryTheory.GrothendieckTopology

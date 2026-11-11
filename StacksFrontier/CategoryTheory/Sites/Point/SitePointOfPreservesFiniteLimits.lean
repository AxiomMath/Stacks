module

public import StacksFrontier.CategoryTheory.Sites.Point.Basic
public import StacksFrontier.CategoryTheory.Sites.Point.OfPreservesFiniteLimits
public import StacksFrontier.CategoryTheory.Sites.Point.SitePoint
import StacksCore.Tactic.StacksAttribute

/-!
# Points of a site with finite limits, in the sense of the Stacks project

Let `C` be a site in which finite limits exist. Stacks 00YC says that a functor `u : C ⥤ Sets`
is a point of `C` (Stacks 00Y5, `GrothendieckTopology.SitePoint`) if and only if

1. `u` commutes with finite limits, and
2. if `{U_i → U}` is a covering, then `∐ u(U_i) → u(U)` is surjective.

## Main results

* `GrothendieckTopology.SitePoint.preservesFiniteLimits_fiber`: the functor of a point
  commutes with finite limits. A point is a point in Mathlib's sense with the same functor
  (`SitePoint.toPoint`), whose category of neighbourhoods is cofiltered, and a functor to sets
  with cofiltered category of elements commutes with the finite limits of `C`.
* `GrothendieckTopology.SitePoint.ofPreservesFiniteLimits`: the point with functor `u`, for `u`
  satisfying (1) and (2). Condition (2) of 00Y5 is that `u` preserves fibre products, and
  condition (3), left exactness of the stalk functor on sheaves, holds because the stalk functor
  of `u` is the stalk functor of the point of Mathlib with fiber `u`
  (`GrothendieckTopology.Point.ofPreservesFiniteLimits`).
* `GrothendieckTopology.SitePoint.exists_fiber_eq_iff`: Stacks 00YC, `u` is the functor of a
  point if and only if it satisfies (1) and (2).
* `GrothendieckTopology.SitePoint.equivFiber`: the points of `C` correspond bijectively to the
  functors satisfying (1) and (2).
-/

@[expose] public section

namespace CategoryTheory.GrothendieckTopology.SitePoint

open Limits

universe w

variable {C : Type w} [SmallCategory C] [HasFiniteLimits C] {J : GrothendieckTopology C}

/-- **Stacks 00YC, condition (1).** On a site with finite limits, the functor `u` of a point
commutes with finite limits. -/
instance preservesFiniteLimits_fiber (p : J.SitePoint) : PreservesFiniteLimits p.fiber :=
  inferInstanceAs (PreservesFiniteLimits p.toPoint.fiber)

/-- **Stacks 00YC, condition (2).** For a point `p` and a covering `{U_i → U}` the map
`∐ u(U_i) → u(U)` is surjective. This is condition (1) of Stacks 00Y5. -/
theorem fiber_surjective (p : J.SitePoint) {I : Type w} {U : C} {Ui : I → C}
    (f : ∀ i, Ui i ⟶ U) (hf : Sieve.ofArrows Ui f ∈ J U) (x : p.fiber.obj U) :
    ∃ (i : I) (y : p.fiber.obj (Ui i)), p.fiber.map (f i) y = x :=
  p.surjective f hf x

/-- The point of the site in Mathlib's sense with fiber functor `u`, for `u` commuting with
finite limits and such that `∐ u(U_i) → u(U)` is surjective for every covering `{U_i → U}`. -/
noncomputable abbrev pointOfPreservesFiniteLimits (u : C ⥤ Type w) [PreservesFiniteLimits u]
    (hu : ∀ {I : Type w} {U : C} {Ui : I → C} (f : ∀ i, Ui i ⟶ U),
      Sieve.ofArrows Ui f ∈ J U → ∀ x : u.obj U,
        ∃ (i : I) (y : u.obj (Ui i)), u.map (f i) y = x) :
    J.Point.{w} :=
  haveI : InitiallySmall.{w} u.Elements := initiallySmall_of_essentiallySmall _
  Point.ofPreservesFiniteLimits u (Functor.CoveringJointlySurjective.of_ofArrows (J := J) hu)

/-- On a site with finite limits, the point (Stacks 00Y5) with functor `u : C ⥤ Type w`, for `u`
commuting with finite limits and such that `∐ u(U_i) → u(U)` is surjective for every covering
`{U_i → U}`. -/
noncomputable def ofPreservesFiniteLimits (u : C ⥤ Type w) [PreservesFiniteLimits u]
    (hu : ∀ {I : Type w} {U : C} {Ui : I → C} (f : ∀ i, Ui i ⟶ U),
      Sieve.ofArrows Ui f ∈ J U → ∀ x : u.obj U,
        ∃ (i : I) (y : u.obj (Ui i)), u.map (f i) y = x) :
    J.SitePoint where
  fiber := u
  surjective := hu
  bijective f _ _ g i :=
    (pointOfPreservesFiniteLimits u hu).fiber_pullbackComparison_bijective (f i) g
  leftExact := inferInstanceAs (PreservesFiniteLimits
    (pointOfPreservesFiniteLimits u hu).sheafFiber)

@[simp]
lemma ofPreservesFiniteLimits_fiber (u : C ⥤ Type w) [PreservesFiniteLimits u]
    (hu : ∀ {I : Type w} {U : C} {Ui : I → C} (f : ∀ i, Ui i ⟶ U),
      Sieve.ofArrows Ui f ∈ J U → ∀ x : u.obj U,
        ∃ (i : I) (y : u.obj (Ui i)), u.map (f i) y = x) :
    (ofPreservesFiniteLimits u hu).fiber = u :=
  rfl

/-- **Stacks 00YC.** Let `C` be a site in which finite limits exist. A functor
`u : C ⥤ Type w` is a point of `C` (Stacks 00Y5) if and only if

1. `u` commutes with finite limits, and
2. for every covering `{U_i → U}` the map `∐ u(U_i) → u(U)` is surjective. -/
@[stacks 00YC "the equivalence, for the points of Stacks 00Y5"]
theorem exists_fiber_eq_iff (u : C ⥤ Type w) :
    (∃ p : J.SitePoint, p.fiber = u) ↔
      PreservesFiniteLimits u ∧
        ∀ {I : Type w} {U : C} {Ui : I → C} (f : ∀ i, Ui i ⟶ U),
          Sieve.ofArrows Ui f ∈ J U → ∀ x : u.obj U,
            ∃ (i : I) (y : u.obj (Ui i)), u.map (f i) y = x := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨inferInstance, fun f hf x => p.surjective f hf x⟩
  · rintro ⟨_, hu⟩
    exact ⟨ofPreservesFiniteLimits u hu, rfl⟩

/-- Two points of a site with the same functor are equal. -/
theorem ext_fiber {p q : J.SitePoint} (h : p.fiber = q.fiber) : p = q := by
  obtain ⟨u, _, _, _⟩ := p
  obtain ⟨u', _, _, _⟩ := q
  cases h
  rfl

/-- **Stacks 00YC.** On a site in which finite limits exist, the points of Stacks 00Y5
correspond bijectively, by `p ↦ u`, to the functors `u : C ⥤ Type w` which commute with finite
limits and for which `∐ u(U_i) → u(U)` is surjective for every covering `{U_i → U}`. -/
@[stacks 00YC "the bijection between points and the functors satisfying (1) and (2)"]
noncomputable def equivFiber :
    J.SitePoint ≃ {u : C ⥤ Type w // PreservesFiniteLimits u ∧
        ∀ {I : Type w} {U : C} {Ui : I → C} (f : ∀ i, Ui i ⟶ U),
          Sieve.ofArrows Ui f ∈ J U → ∀ x : u.obj U,
            ∃ (i : I) (y : u.obj (Ui i)), u.map (f i) y = x} where
  toFun p := ⟨p.fiber, inferInstance, fun f hf x => p.surjective f hf x⟩
  invFun u :=
    haveI := u.property.1
    ofPreservesFiniteLimits u.val u.property.2
  left_inv _ := ext_fiber rfl
  right_inv _ := Subtype.ext rfl

end CategoryTheory.GrothendieckTopology.SitePoint

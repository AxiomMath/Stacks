module

public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Sites.Point.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Points of a site with finite limits

Let `C` be a site in which finite limits exist. Then a point of `C` is given by a functor
`u : C ⥤ Set` such that

1. `u` commutes with finite limits, and
2. if `{U_i → U}` is a covering, then `∐ u(U_i) → u(U)` is surjective.

A point of a site in Mathlib's sense, `CategoryTheory.GrothendieckTopology.Point`, is a functor
whose category of elements is cofiltered and initially small and which satisfies clause (2) for
covering sieves. When `C` has finite limits the two descriptions agree, with the same underlying
functor `u`.

## Main results

* `GrothendieckTopology.Point.eq_of_fiber_eq`: a point is determined by its fiber functor.
* `GrothendieckTopology.Point.ofPreservesFiniteLimits`: the point of `C` with fiber `u`, for `u`
  satisfying (1) and (2).
* `GrothendieckTopology.Point.equivFiber`: the bijection between `Point J` and the initially
  small functors satisfying (1) and (2).
* `Functor.CoveringJointlySurjective.ofArrows` and `Functor.CoveringJointlySurjective.of_ofArrows`:
  clause (2) for covering sieves is equivalent to clause (2) for covering families.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe w v u

variable {C : Type u} [Category.{v} C]

/-- Joint surjectivity of `u` on covering sieves: every section of `u` over `U` is, locally on a
covering sieve of `U`, in the image of `u`. -/
def Functor.CoveringJointlySurjective (u : C ⥤ Type w) (J : GrothendieckTopology C) : Prop :=
  ∀ ⦃U : C⦄ (R : Sieve U), R ∈ J U → ∀ x : u.obj U,
    ∃ (Y : C) (f : Y ⟶ U) (_ : R f) (y : u.obj Y), u.map f y = x

namespace Functor.CoveringJointlySurjective

variable {u : C ⥤ Type w} {J : GrothendieckTopology C}

/-- If `u` is jointly surjective on covering sieves, then for a covering family `{U_i → U}` the
map `∐ u(U_i) → u(U)` is surjective: every `x : u(U)` is `u(f i) y` for some `i` and some
`y : u(U_i)`. -/
theorem ofArrows (hu : u.CoveringJointlySurjective J) {I : Type*} {U : C} {Ui : I → C}
    (f : ∀ i, Ui i ⟶ U) (hf : Sieve.ofArrows Ui f ∈ J U) (x : u.obj U) :
    ∃ (i : I) (y : u.obj (Ui i)), u.map (f i) y = x := by
  obtain ⟨Y, g, hg, y, hy⟩ := hu _ hf x
  obtain ⟨Z, a, h, ⟨i⟩, rfl⟩ := hg
  exact ⟨i, u.map a y, by simpa using hy⟩

/-- If `∐ u(U_i) → u(U)` is surjective for every covering family `{U_i → U}` indexed in
`Type (max u v)`, then `u` is jointly surjective on covering sieves. -/
theorem of_ofArrows
    (hu : ∀ {I : Type max u v} {U : C} {Ui : I → C} (f : ∀ i, Ui i ⟶ U),
      Sieve.ofArrows Ui f ∈ J U → ∀ x : u.obj U,
        ∃ (i : I) (y : u.obj (Ui i)), u.map (f i) y = x) :
    u.CoveringJointlySurjective J := by
  intro U R hR x
  obtain ⟨I, Y, f, rfl⟩ := R.exists_eq_ofArrows
  obtain ⟨i, y, hy⟩ := hu f hR x
  exact ⟨Y i, f i, Sieve.ofArrows_mk _ _ i, y, hy⟩

end Functor.CoveringJointlySurjective

namespace GrothendieckTopology.Point

variable {J : GrothendieckTopology C}

/-- Two points of a site with the same fiber functor are equal. -/
theorem eq_of_fiber_eq {Φ Φ' : Point.{w} J} (h : Φ.fiber = Φ'.fiber) : Φ = Φ' := by
  obtain ⟨f, _, _, _⟩ := Φ
  obtain ⟨f', _, _, _⟩ := Φ'
  simp only [] at h
  subst h
  rfl

/-- `Point.fiber` is injective: distinct points of a site have distinct fiber functors. -/
theorem fiber_injective :
    Function.Injective (fun Φ : Point.{w} J => Φ.fiber) :=
  fun _ _ => eq_of_fiber_eq

/-- The fiber functor of a point is jointly surjective on covering sieves. -/
theorem coveringJointlySurjective_fiber (Φ : Point.{w} J) :
    Φ.fiber.CoveringJointlySurjective J :=
  fun _ _ hR x => Φ.jointly_surjective _ hR x

variable [HasFiniteLimits C]

/-- On a site in which finite limits exist, the point with fiber functor `u : C ⥤ Type w`, for
`u` commuting with finite limits, with initially small category of elements, and jointly
surjective on covering sieves. -/
@[stacks 00YC, simps, sga "4 IV 6.3" "left exact ⇒ point"]
def ofPreservesFiniteLimits (u : C ⥤ Type w) [PreservesFiniteLimits u]
    [InitiallySmall.{w} u.Elements] (hu : u.CoveringJointlySurjective J) :
    Point.{w} J where
  fiber := u
  isCofiltered := u.isCofiltered_elements
  jointly_surjective R hR x := hu R hR x

variable [LocallySmall.{w} C]

/-- Let `C` be a site in which finite limits exist. Then the points of `C`
correspond bijectively to the functors `u : C ⥤ Type w` such that

1. `u` commutes with finite limits, and
2. `∐ u(U_i) → u(U)` is surjective for every covering `{U_i → U}`
   (in the sieve form `Functor.CoveringJointlySurjective`), and whose category of elements is
   initially small,

the bijection being `Φ ↦ Φ.fiber` in one direction and `ofPreservesFiniteLimits` in the
other. -/
@[stacks 00YC, sga "4 IV 6.3" "characterization"]
noncomputable def equivFiber :
    Point.{w} J ≃ {u : C ⥤ Type w //
      InitiallySmall.{w} u.Elements ∧ PreservesFiniteLimits u ∧
        u.CoveringJointlySurjective J} where
  toFun Φ := ⟨Φ.fiber, Φ.initiallySmall, inferInstance,
    Φ.coveringJointlySurjective_fiber⟩
  invFun u :=
    haveI := u.property.left
    haveI := u.property.right.left
    ofPreservesFiniteLimits u.val u.property.right.right
  left_inv _ := eq_of_fiber_eq rfl
  right_inv _ := Subtype.ext rfl

end GrothendieckTopology.Point

end CategoryTheory

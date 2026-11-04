module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPoints
public import StacksFrontier.AlgebraicGeometry.Flatness.Representability
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Representing the generic-rank functor: the formal part

For a smooth family with geometrically irreducible fibres, the functor `H_p` of Stacks 05MR tests
whether a finite type quasi-coherent module is free of rank `p` near each fibre's generic point.
This file supplies the formal glue for its representability, which does not depend on the
construction of a representing subscheme: the functor is subterminal, so a morphism into the
base represents it exactly when the schemes over the base satisfying the condition are those
whose structure morphism factors through it.

## Main definitions

* `AlgebraicGeometry.FreeAtGenericPointsSituation.FactorizationCriterion` is the elementary
  form of the representability assertion: a morphism into the base through which exactly the
  base changes satisfying the generic-point condition factor.

## Main results

* `AlgebraicGeometry.FreeAtGenericPointsSituation.representableByOfFactorizationCriterion`
  turns the elementary form into a `CategoryTheory.Functor.RepresentableBy`, and
  `AlgebraicGeometry.FreeAtGenericPointsSituation.factorizationCriterion_of_representableBy`
  recovers the elementary form from a representation, so the two are equivalent.

Tag 05UC itself is
`AlgebraicGeometry.FreeAtGenericPointsSituation.exists_immersion_representableBy` and
`AlgebraicGeometry.FreeAtGenericPointsSituation.finitePresentation_hom_of_representableBy`.

## Implementation notes

The functor's values are `ULift (PLift _)` of a proposition, hence subsingletons, and the
morphisms of `Over S` into an object with monomorphic structure morphism form a subsingleton
too. A natural bijection between two subsingletons is determined by its mere existence, which
is why `FactorizationCriterion` — an equivalence of propositions — already produces a
`RepresentableBy`: no compatibility with composition has to be checked.

## References

* [Stacks Project, Tag 05UC](https://stacks.math.columbia.edu/tag/05UC)
-/

@[expose] public section

open CategoryTheory

universe v u

namespace AlgebraicGeometry

namespace FreeAtGenericPointsSituation

/-- Morphisms into an object of a slice category with monomorphic structure morphism are
unique: their components to the source agree after composition with that structure
morphism. -/
theorem subsingleton_over_hom_of_mono {C : Type*} [Category C] {X : C} {W : Over X}
    (hW : Mono W.hom) (T : Over X) : Subsingleton (T ⟶ W) :=
  ⟨fun a b ↦ Over.OverMorphism.ext ((cancel_mono W.hom).mp (by rw [Over.w, Over.w]))⟩

/-- A subterminal functor on a slice category is represented by an object with monomorphic
structure morphism as soon as the two have the same sections at every object: both sides are
subsingletons, so the bijections exist and their compatibility with composition is
automatic. -/
noncomputable def representableByOfSubsingleton {C : Type*} [Category C] {X : C}
    (G : (Over X)ᵒᵖ ⥤ Type v) [∀ T, Subsingleton (G.obj T)] (W : Over X) (hW : Mono W.hom)
    (h : ∀ T : Over X, Nonempty (G.obj (Opposite.op T)) ↔ Nonempty (T ⟶ W)) :
    G.RepresentableBy W where
  homEquiv {T} :=
    letI := subsingleton_over_hom_of_mono hW T
    { toFun := fun a ↦ ((h T).mpr ⟨a⟩).some
      invFun := fun x ↦ ((h T).mp ⟨x⟩).some
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _ }
  homEquiv_comp _ _ := Subsingleton.elim _ _

variable (D : FreeAtGenericPointsSituation.{u}) (p : ℕ)

/-- The generic-rank functor is subterminal: its values are `ULift (PLift _)` of a
proposition. -/
instance subsingleton_freeAtGenericPointsFunctor_obj (T : (Over D.S)ᵒᵖ) :
    Subsingleton ((D.freeAtGenericPointsFunctor p).obj T) :=
  inferInstanceAs (Subsingleton (ULift.{u} (PLift (D.Condition p T.unop))))

/-- The elementary form of the representability assertion for the generic-rank functor: a
morphism `i : Z ⟶ S` such that a scheme over `S` satisfies the generic-point freeness
condition exactly when its structure morphism factors through `i`. -/
abbrev FactorizationCriterion {Z : Scheme.{u}} (i : Z ⟶ D.S) : Prop :=
  ∀ T : Over D.S, D.Condition p T ↔ ∃ g : T.left ⟶ Z, g ≫ i = T.hom

/-- A morphism satisfying the factorization criterion represents the generic-rank functor. -/
noncomputable def representableByOfFactorizationCriterion {Z : Scheme.{u}} (i : Z ⟶ D.S)
    (hmono : Mono i) (hi : D.FactorizationCriterion p i) :
    (D.freeAtGenericPointsFunctor p).RepresentableBy (Over.mk i) :=
  representableByOfSubsingleton _ (Over.mk i) hmono (fun T ↦ by
    constructor
    · intro h
      obtain ⟨g, hg⟩ := (hi T).mp h.some.down.down
      exact ⟨Over.homMk g hg⟩
    · intro h
      exact ⟨⟨⟨(hi T).mpr ⟨h.some.left, Over.w h.some⟩⟩⟩⟩)

/-- Conversely, the structure morphism of an object representing the generic-rank functor
satisfies the factorization criterion, so the criterion is an exact reformulation of
representability and not merely sufficient for it. -/
theorem factorizationCriterion_of_representableBy {W : Over D.S}
    (e : (D.freeAtGenericPointsFunctor p).RepresentableBy W) :
    D.FactorizationCriterion p W.hom := by
  intro T
  constructor
  · intro h
    exact ⟨(e.homEquiv.symm ⟨⟨h⟩⟩ : T ⟶ W).left, Over.w _⟩
  · intro h
    obtain ⟨g, hg⟩ := h
    exact (e.homEquiv (Over.homMk g hg)).down.down

end FreeAtGenericPointsSituation

end AlgebraicGeometry

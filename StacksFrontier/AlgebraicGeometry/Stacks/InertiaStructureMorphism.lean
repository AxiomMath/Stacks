module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance

/-!
# The inertia of an algebraic stack is the relative inertia of its structure morphism

For an algebraic stack `𝒳` over `S`, the inertia `I_𝒳` (pairs `(x, α)` with `α` an automorphism
of `x` lying over an identity of the site) and the relative inertia `I_{𝒳/S}` of the structure
1-morphism `𝒳 ⟶ S` (pairs `(x, α)` with `α` mapping to an identity of `S`) are the same category
over `𝒳`: the structure 1-morphism is `p` followed by an equivalence, so `α` maps to an identity
of `S` exactly when it lies over an identity of the site. This file records the comparison and
transports the relative properties of Properties of Stacks, Section 04XB, from the projection of
`I_𝒳` to that of `I_{𝒳/S}`.

## Main definitions

* `AlgebraicGeometry.Stack.relativeInertiaStructureMorphismToInertia`: the comparison.

## Main results

* `AlgebraicGeometry.Stack.relativeProperty_relativeInertiaProjection_structureMorphism`: a
  relative property of `I_𝒳 ⟶ 𝒳` holds for `I_{𝒳/S} ⟶ 𝒳`.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- An automorphism of an object of `𝒳` maps to an identity under the structure 1-morphism
exactly when it lies over an identity of the site. -/
theorem structureMorphism_map_eq_id_iff {x : 𝒳.val.val.obj} (α : x ⟶ x) :
    (CatFiberedInGroupoids.homFunctor (structureMorphism B S hS 𝒳).hom).map α = 𝟙 _ ↔
      𝒳.val.val.p.map α = 𝟙 _ :=
  let e := (Over.iteratedSliceEquiv (Over.mk (𝟙 (B.obj hS)))).inverse
  ⟨fun h => e.map_injective (h.trans (e.map_id _).symm),
    fun h => (congrArg e.map h).trans (e.map_id _)⟩

/-- **The comparison from the relative inertia of the structure 1-morphism to the inertia.** It
is the identity on underlying objects, automorphisms and morphisms. -/
def relativeInertiaStructureMorphismToInertia :
    (relativeInertiaStack B S hS (structureMorphism B S hS 𝒳)).val.val ⥤ᵇ
      (inertiaAlgebraicStack B S hS 𝒳).val.val where
  toFunctor :=
    { obj := fun A => ⟨A.obj, A.auto,
        (structureMorphism_map_eq_id_iff B S hS 𝒳 A.auto.asIso.hom).1 A.cond⟩
      map := fun φ => ⟨φ.hom, φ.comm⟩ }
  w := rfl

/-- The comparison `relativeInertiaStructureMorphismToInertia` is faithful. -/
instance : (relativeInertiaStructureMorphismToInertia B S hS 𝒳).toFunctor.Faithful where
  map_injective {_ _} _ _ h := RelativeInertiaHom.ext
    (congrArg RelativeInertiaHom.hom h : _)

/-- The comparison `relativeInertiaStructureMorphismToInertia` is full. -/
instance : (relativeInertiaStructureMorphismToInertia B S hS 𝒳).toFunctor.Full where
  map_surjective {_ _} g := ⟨⟨g.hom, g.comm⟩, rfl⟩

/-- The comparison `relativeInertiaStructureMorphismToInertia` is essentially surjective. -/
instance : (relativeInertiaStructureMorphismToInertia B S hS 𝒳).toFunctor.EssSurj where
  mem_essImage A := ⟨⟨A.obj, A.auto,
    (structureMorphism_map_eq_id_iff B S hS 𝒳 A.auto.asIso.hom).2 A.cond⟩, ⟨Iso.refl _⟩⟩

/-- The comparison `relativeInertiaStructureMorphismToInertia` is an equivalence of categories. -/
instance : (relativeInertiaStructureMorphismToInertia B S hS 𝒳).toFunctor.IsEquivalence where

/-- **A relative property of the inertia projection holds for the relative inertia projection of
the structure 1-morphism** (Properties of Stacks, Section 04XB, read through Stacks 0457). -/
theorem relativeProperty_relativeInertiaProjection_structureMorphism
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
      (_hy : y ⋙ 𝒳.val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) (inertiaAlgebraicStack B S hS 𝒳).val.val.p
          𝒳.val.val.p y
          (CatFiberedInGroupoids.homFunctor (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
      (_hy : y ⋙ 𝒳.val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom)
          (relativeInertiaStack B S hS (structureMorphism B S hS 𝒳)).val.val.p
          𝒳.val.val.p y
          (CatFiberedInGroupoids.homFunctor
            (relativeInertiaProjection B S hS (structureMorphism B S hS 𝒳)).hom))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  have : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  exact relativeProperty_of_equivalences B S hS P
    (relativeInertiaProjection B S hS (structureMorphism B S hS 𝒳)).hom.hom
    (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom.hom
    (relativeInertiaStructureMorphismToInertia B S hS 𝒳) (BasedFunctor.id 𝒳.val.val)
    (Iso.refl _) hP

end AlgebraicGeometry.Stack

end

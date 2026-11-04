module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# A family of maps of sheaves is a product as soon as it is one on sections

A product of sheaves is computed on sections: the inclusion of sheaves into presheaves creates
limits, and limits of presheaves are pointwise. So to recognise a given object of a category of
sheaves, together with a family of maps out of it, as a product, it suffices to recognise it as
such on sections over every object of the site.

## Main results

* `CategoryTheory.isLimitFanOfSections`: the recognition statement.

## Implementation notes

The two reductions are `CategoryTheory.Limits.isLimitOfReflects` for the inclusion of sheaves
into presheaves, which reflects limits because it creates them, and
`CategoryTheory.Limits.evaluationJointlyReflectsLimits` for the presheaf category. Neither of
the two diagram comparisons involved is definitional — `Discrete.functor f ⋙ G` and
`Discrete.functor (fun i => G.obj (f i))` differ on the morphisms of the discrete index
category — so both go through `CategoryTheory.Limits.IsLimit.equivOfNatIsoOfIso`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe w v₁ u₁ v₂ u₂

variable {I : Type w} {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {A : Type u₂} [Category.{v₂} A] [HasLimitsOfShape (Discrete I) A]

/-- A sheaf together with a family of maps out of it is a product of a family of sheaves as soon
as, on sections over every object of the site, it is a product of their sections. -/
noncomputable def isLimitFanOfSections {f : I → Sheaf J A} {P : Sheaf J A} (p : ∀ i, P ⟶ f i)
    (h : ∀ X : Cᵒᵖ, IsLimit (Fan.mk (P.obj.obj X) fun i => (p i).hom.app X)) :
    IsLimit (Fan.mk P p) := by
  refine isLimitOfReflects (sheafToPresheaf J A) ?_
  refine (IsLimit.equivOfNatIsoOfIso
    ((Discrete.natIso fun _ => Iso.refl _ :
        Discrete.functor (fun i => (f i).obj) ≅ Discrete.functor f ⋙ sheafToPresheaf J A))
    (Fan.mk P.obj fun i => (p i).hom)
    ((sheafToPresheaf J A).mapCone (Fan.mk P p)) (Cone.ext (Iso.refl _) ?_)) ?_
  · intro j
    obtain ⟨j⟩ := j
    simp
  · refine evaluationJointlyReflectsLimits _ fun X => ?_
    refine (IsLimit.equivOfNatIsoOfIso
      ((Discrete.natIso fun _ => Iso.refl _ :
          Discrete.functor (fun i => (f i).obj.obj X) ≅
            Discrete.functor (fun i => (f i).obj) ⋙ (evaluation Cᵒᵖ A).obj X))
      (Fan.mk (P.obj.obj X) fun i => (p i).hom.app X)
      (((evaluation Cᵒᵖ A).obj X).mapCone (Fan.mk P.obj fun i => (p i).hom))
      (Cone.ext (Iso.refl _) ?_)) (h X)
    intro j
    obtain ⟨j⟩ := j
    simp

end CategoryTheory

end

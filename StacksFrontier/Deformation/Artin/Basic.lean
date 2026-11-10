module

public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.Schlessinger.AssociatedFunctor
public import StacksFrontier.Deformation.Schlessinger.Basic
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses

/-!
# Schlessinger's conditions for a deformation category (Stacks: Artin's axioms)

A deformation category over `𝒞_Λ` is a predeformation category satisfying the
Rim–Schlessinger condition (RS). Condition (RS) already implies Schlessinger's
conditions (S1) and (S2) for the deformation category itself; the content of this
file is that these two conditions also hold for the associated functor of fibrewise
isomorphism classes, which is the covariant quotient of the deformation category by
isomorphism in each fibre.

## Main results

* `Deformation.Artin.schlessingerConditionS1_isomorphismClasses_of_isDeformationCategory`
  — the functor of isomorphism classes of a deformation category satisfies (S1).
* `Deformation.Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory`
  — it also satisfies (S2).

The two conditions for the deformation category itself are the general
Rim–Schlessinger implications `Deformation.schlessingerConditionS1_of_satisfiesRS`
and `Deformation.schlessingerConditionS2_of_satisfiesRS`, which are registered here
rather than restated.

## Implementation notes

The hypotheses in the source concerning a locally Noetherian base scheme and a
finite-type field-valued object are needed only to produce a deformation category;
the implications themselves do not require them.

## References

* [Stacks Project, Tag 07WV](https://stacks.math.columbia.edu/tag/07WV)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Deformation.Artin

add_to_stacks 07WV "condition (S1) for the deformation category"
  Deformation.schlessingerConditionS1_of_satisfiesRS
add_to_stacks 07WV "condition (S2) for the deformation category"
  Deformation.schlessingerConditionS2_of_satisfiesRS

universe u v w u₁ v₁

/-- The functor of isomorphism classes associated to a deformation category
satisfies Schlessinger's condition (S1). -/
@[stacks 07WV "condition (S1) for isomorphism classes"]
public theorem schlessingerConditionS1_isomorphismClasses_of_isDeformationCategory
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{v₁, u₁}
      (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p) :
    SchlessingerConditionS1
      (Functor.Elements.π
        (isomorphismClassesData 𝓕 h𝓕.predeformation.cofibered).classes) :=
  schlessingerConditionS1_of_isIsomorphismClasses
    (isomorphismClassesData 𝓕 h𝓕.predeformation.cofibered).projection
    (isomorphismClassesData 𝓕 h𝓕.predeformation.cofibered).quotient
    (schlessingerConditionS1_of_satisfiesRS h𝓕.satisfiesRS)

/-- The functor of isomorphism classes associated to a deformation category
satisfies Schlessinger's condition (S2). -/
@[stacks 07WV "condition (S2) for isomorphism classes"]
public theorem schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{v₁, u₁}
      (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (h𝓕 : IsDeformationCategory 𝓕.p) :
    SchlessingerConditionS2
      (Functor.Elements.π
        (isomorphismClassesData 𝓕 h𝓕.predeformation.cofibered).classes) :=
  schlessingerConditionS2_of_isIsomorphismClasses 𝓕 h𝓕.predeformation.cofibered
    (schlessingerConditionS2_of_satisfiesRS h𝓕.satisfiesRS) (Or.inl h𝓕.predeformation)

end Deformation.Artin

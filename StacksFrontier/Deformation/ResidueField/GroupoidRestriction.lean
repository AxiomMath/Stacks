module

public import StacksFrontier.Deformation.Groupoid.Smooth
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.ResidueField.Comparison
public import StacksFrontier.Deformation.SchlessingerConditions.SmoothMorphisms

/-!
# Change of residue field for groupoids in functors

For a finite tower `Λ → k → l`, a groupoid in functors `G` on `𝒞_{Λ,k}` restricts along the
comparison functor `T ↦ T ×_l k` of Stacks 07W8 to a groupoid in functors on `𝒞_{Λ,l}`. Since the
comparison functor preserves surjections, the restriction of a smooth groupoid is smooth.

## Main results

* `Deformation.isSmooth_restrict_comparisonFunctor`: smoothness is preserved.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Deformation

variable (S : ChangeOfFieldsSituation.{u, u, u})

/-- Smoothness of a morphism of functors is preserved by restriction along the comparison
functor `T ↦ T ×_l k`, which preserves surjections. -/
public theorem isSmooth_elementsBasedFunctor_whiskerLeft_comparisonFunctor
    {P Q : ArtinianLocalAlgCat.{u, u, u} S.Λ S.k ⥤ Type u} (α : P ⟶ Q)
    (hα : IsSmooth (elementsBasedFunctor α)) :
    IsSmooth (elementsBasedFunctor (Functor.whiskerLeft (comparisonFunctor S).functor α)) :=
  (isSmooth_elementsBasedFunctor_iff _).2 fun _ _ f hf ↦
    (isSmooth_elementsBasedFunctor_iff α).1 hα _ (comparisonFunctor_map_surjective S f hf)

/-- **The restriction of a smooth groupoid in functors along the comparison functor is
smooth.** -/
public theorem isSmooth_restrict_comparisonFunctor
    (G : GroupoidInFunctors.{_, u, u} (ArtinianLocalAlgCat.{u, u, u} S.Λ S.k))
    (hG : GroupoidInFunctors.IsSmooth G) :
    GroupoidInFunctors.IsSmooth (G.restrict (comparisonFunctor S).functor) :=
  ⟨isSmooth_elementsBasedFunctor_whiskerLeft_comparisonFunctor S G.source hG.1,
    isSmooth_elementsBasedFunctor_whiskerLeft_comparisonFunctor S G.target hG.2⟩

end Deformation

end

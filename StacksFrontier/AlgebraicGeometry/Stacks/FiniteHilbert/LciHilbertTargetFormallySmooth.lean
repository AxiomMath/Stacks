module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.CoverDeformationExists
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciHilbertDeformation

/-!
# The local complete intersection locus is formally smooth on objects over the target

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
which is representable by algebraic spaces, flat and locally of finite presentation. Then
`p : ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` is formally smooth on objects. This is **Stacks 06D9**.

## Main results

* `AlgebraicGeometry.Stack.isFormallySmoothOnObjects_lciFiniteHilbertToTarget`: **Stacks 06D9**.

## Implementation notes

The first-order lifting problem is solved in
`StacksFrontier/AlgebraicGeometry/Stacks/FiniteHilbert/LciHilbertDeformation.lean` from the
deformation problem of the cover, `AlgebraicGeometry.Stack.FiniteHilbert.HasCoverDeformations`,
which is Stacks 06D8 at the algebraic spaces the proof meets. That problem is solved for every
big fppf site by `AlgebraicGeometry.Stack.FiniteHilbert.hasCoverDeformations`, so nothing is
carried here: the hypotheses are exactly those of the source.

Flatness and local finite presentation of `F` are the relative properties of Stacks 03YK: every
algebraic space representing the base change of `F` along a scheme-valued point of `𝒴` is flat,
respectively locally of finite presentation, over the base. This is the spelling of the sibling
Stacks 06DA, `AlgebraicGeometry.Stack.isSurjectiveOnObjects_lciFiniteHilbertCoproductToTarget`.

## References

* [Stacks Project, Tag 06D9](https://stacks.math.columbia.edu/tag/06D9)
* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

/-- **Stacks 06D9.** Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over
`(Sch/S)_fppf` which is representable by algebraic spaces, flat and locally of finite
presentation. Then `p : ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` is formally smooth on objects (Stacks 06D0).

This is
`AlgebraicGeometry.Stack.isFormallySmoothOnObjects_lciFiniteHilbertToTarget_of_coverDeformations`
with its deformation problem solved by
`AlgebraicGeometry.Stack.FiniteHilbert.hasCoverDeformations`, the space-level Stacks 06D8. -/
@[stacks 06D9]
theorem isFormallySmoothOnObjects_lciFiniteHilbertToTarget
    (hFrep : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFflat : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsFlat B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (hFlfp : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsLocallyOfFinitePresentation B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom) :
    IsFormallySmoothOnObjects B S hS
      (lciFiniteHilbertFibered (isFiberedInGroupoids_lciFiniteHilbertCategory
        (FiniteHilbert.hasOpenLciLocus (d := d) hFrep hFflat hFlfp)))
      (stackFibered B S hS 𝒴)
      (lciFiniteHilbertToTargetFibered (isFiberedInGroupoids_lciFiniteHilbertCategory
        (FiniteHilbert.hasOpenLciLocus (d := d) hFrep hFflat hFlfp))) :=
  isFormallySmoothOnObjects_lciFiniteHilbertToTarget_of_coverDeformations hFrep hFflat hFlfp
    (FiniteHilbert.hasCoverDeformations B S hS d)

end AlgebraicGeometry.Stack

end
